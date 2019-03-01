#include <string.h>
#include <math.h>
#include <assert.h>
#include <stdlib.h>
#include <stdio.h>

#include <config.h>
//#include <string> 
//using namespace std; 


bool collect_buffer(int pos_cls[NUM_VARS][BUF_CLS_SIZE], int neg_cls[NUM_VARS][BUF_CLS_SIZE], 
  int lit, int x);

bool deduction3(int l1, int l2, int var1, int var2, int x, int *l_ded);
bool deduction4(int l1, int l2, int l3, int var1, int var2, int var3, int x, int *l_ded);

void sort4 (int array[4]); 

void sort4_idx (int array[4], int idx[4]); 

#pragma ACCEL kernel
void solver_kernel(
        int* c1, int* c2, int* c3, int* result){

#pragma ACCEL interface variable=c1 bus_bitwidth=512 depth = 1065
#pragma ACCEL interface variable=c2 bus_bitwidth=512 depth = 1065
#pragma ACCEL interface variable=c3 bus_bitwidth=512 depth = 1065
#pragma ACCEL interface variable=result depth=1 
/************************ Variable Declaration **************************/
  int satisfiable; 
  int unsatisfiable = 0; 
  //Table and buffers
  int local_clauses[NUM_TOT_CLAUSES][4] = {0};
  int learn_cls_nxtidx= NUM_ORG_CLAUSES;

  char var_truth_table[NUM_VARS] = {U}; // T, F, U (Undef), TF(assigned to T first), FT(assigned to F first)
  int dec_lvl[NUM_VARS] = {-1};
  int dec_var[BUF_DEC_LVL]= {0}; // Variable idx at each decision lvl, we assume at most 100 decision level
  int buf_ded[BUF_DED_SIZE] = {0};
  int buf_ded_cls[BUF_DED_SIZE] = {-1}; 
  int parent_cls[NUM_VARS] = {0}; 

  int least_parent[NUM_VARS] = {0};
  int dec_lst_lvl[BUF_DEC_LVL] = {-1}; 

  int l_ded[BUF_CLS_SIZE];
  int cls_ded[BUF_CLS_SIZE]; 
  bool conflict[BUF_CLS_SIZE];
  
  int pos_cls[NUM_VARS][BUF_CLS_SIZE] = {-1}; 
  int neg_cls[NUM_VARS][BUF_CLS_SIZE] = {-1}; 
  int pos_cls_end[NUM_VARS];
  int neg_cls_end[NUM_VARS];

  //Idx and ptr 
  int new_var_idx = 1;
  int curr_lvl = -1; 
  int buf_ded_curr = -1;
  int buf_ded_end = -1;

  //Other global variables
  int state = DECISION; 
  int prev_state = DECISION; 
  int num_extra;
  int conf_var; 
  int conf_cls; 
  int conf_parents[4], conf_parents_tmp[4], conf_parent_tmp4, conf_parent_tmp5; 
  int parent_lvl[4]; 
  int conf_lst_lvl[4]; 
  int back_lvl = 0; 
  int learned_lit;

  //Temporary variabels
  bool tot_conflict = 0; //PROP, DED
  bool conf_ded; //PROP
  //int tmp_conf_cls; //BACKTRACK
  int prev_assigned_value; // BACKTRACK
  int prop_var; //PROP
  int curr_lst;
  int loc0, loc1, loc2, loc3, loc4, loc5, loc6, loc7;

/*************************** Initializing array ***************************/

//#pragma ACCEL parallel flatten
  for (int x = 0; x< NUM_VARS; x++){
    for (int y = 0; y< BUF_CLS_SIZE; y++){
      pos_cls[x][y] = EMPTY; 
      neg_cls[x][y] = EMPTY; 
    }
  }

/*************************** Loading Clauses ***************************/
  //Load data
  printf("Start to load data \n");
  for (int x = 0; x < NUM_ORG_CLAUSES; ++x) {
    local_clauses[x][0] = c1[x];
    local_clauses[x][1] = c2[x];
    local_clauses[x][2] = c3[x];
    local_clauses[x][3] = 0;

    collect_buffer(pos_cls, neg_cls, c1[x], x);
    collect_buffer(pos_cls, neg_cls, c2[x], x);
    collect_buffer(pos_cls, neg_cls, c3[x], x);
  }

  for (int x = 0; x < NUM_VARS; x++){
    for (int y = 0; y < BUF_CLS_SIZE; y++){
      if (pos_cls[x][y] == EMPTY){
        pos_cls_end[x] = y; break;
      }
    }

    for (int y = 0; y < BUF_CLS_SIZE; y++){
      if (neg_cls[x][y] == EMPTY){
        neg_cls_end[x] = y; break;
      }
    }
  }
/*
  for (int x = 0; x < NUM_VARS; x++){
    printf("Pos buf Var(%d): ", x);
    for (int y = 0; y < BUF_CLS_SIZE; y++){
      printf("%d ", pos_cls[x][y]);
    }
    printf("\nEnd ptr is %d\n", pos_cls_end[x]);

    printf("Neg buf Var(%d): ", x);
    for (int y = 0; y < BUF_CLS_SIZE; y++){
      printf("%d ", neg_cls[x][y]);
    }
    printf("\nEnd ptr is %d\n", neg_cls_end[x]);
  }

  for (int x = 0; x < NUM_TOT_CLAUSES; ++x) {
    printf("Local %d %d %d %d\n", local_clauses[x][0], local_clauses[x][1], local_clauses[x][2], local_clauses[x][3]);
  }
*/
  for (int x = 0; x< NUM_VARS; x++){
     var_truth_table[x] = U; 
  }

/********************************* FSM **********************************/
  while (state != EXIT){
    switch(state){
      case DECISION: 

        while (new_var_idx < NUM_VARS){
          if (var_truth_table[new_var_idx] != U){
            //printf("Skip var %d(Value - %d)\n", new_var_idx, var_truth_table[new_var_idx]); 
            new_var_idx ++; 
          }else{
            break; 
          }
        } 
        
        if (new_var_idx == NUM_VARS){
          state = SOLVED; 
        }else {
          state = PROP;
          curr_lvl ++; 
//        printf("Decide Var(%d) - at lvl %d\n", new_var_idx, curr_lvl);

	  var_truth_table[new_var_idx] = T;

          if (pos_cls[new_var_idx][5] != -1){
            var_truth_table[new_var_idx] = T;
          }else {
            var_truth_table[new_var_idx] = F;
          }

          dec_lvl[new_var_idx] = curr_lvl; 
          dec_var[curr_lvl] = new_var_idx; 
          least_parent[new_var_idx] = new_var_idx;
        }

        prev_state = DECISION; 
        break;

      case PROP:
        if (prev_state == DECISION || prev_state == BACKTRACK_DEC){
          prop_var = new_var_idx;
        }else if (prev_state == DEDUCTION){
          prop_var = abs(buf_ded[buf_ded_curr]);
        }else if (prev_state == BACKTRACK_DED){
          prop_var = abs(learned_lit);
        }
        //printf("Prop ded Var(%d): %d\n", prop_var, var_truth_table[prop_var]);

        /****************** pos_buf & neg_buf *****************/
        #pragma ACCEL parallel flatten
        for (int x = 0; x < BUF_CLS_SIZE; x++){
          int l1, l2, l3, var1, var2, var3;
          if( (var_truth_table[prop_var] == T || var_truth_table[prop_var] == FT) && neg_cls[prop_var][x] != EMPTY){
            l1 = (local_clauses[neg_cls[prop_var][x]][0] == -prop_var)? 
              local_clauses[neg_cls[prop_var][x]][1] : local_clauses[neg_cls[prop_var][x]][0];
            l2 = (local_clauses[neg_cls[prop_var][x]][2] == -prop_var || local_clauses[neg_cls[prop_var][x]][3] == -prop_var)? 
              local_clauses[neg_cls[prop_var][x]][1] : local_clauses[neg_cls[prop_var][x]][2];
            l3 = (local_clauses[neg_cls[prop_var][x]][3] == -prop_var)? 
              local_clauses[neg_cls[prop_var][x]][2] : local_clauses[neg_cls[prop_var][x]][3];
            var1 = var_truth_table[abs(l1)];
            var2 = var_truth_table[abs(l2)];
            var3 = var_truth_table[abs(l3)];
	    if (l2 == 0){//2-lit cls
              l2 = -prop_var; 
              var2 = var_truth_table[abs(l2)];
              conflict[x] = deduction3(l1, l2, var1, var2, x, l_ded);
	    }else if (l3 == 0){ //3-lit cls
              conflict[x] = deduction3(l1, l2, var1, var2, x, l_ded);
            }else{ //4-lit cls
              conflict[x] = deduction4(l1, l2, l3, var1, var2, var3, x, l_ded);
            }
            cls_ded[x] = neg_cls[prop_var][x];
            //if (conflict[x]){ printf("Found conflict @cls(%d)\n", neg_cls[prop_var][x]);}
          }else if ((var_truth_table[prop_var] == F  || var_truth_table[prop_var] == TF) && pos_cls[prop_var][x] != EMPTY){
            l1 = (local_clauses[pos_cls[prop_var][x]][0] == prop_var)? 
              local_clauses[pos_cls[prop_var][x]][1] : local_clauses[pos_cls[prop_var][x]][0];
            l2 = (local_clauses[pos_cls[prop_var][x]][2] == prop_var || local_clauses[pos_cls[prop_var][x]][3] == prop_var)? 
              local_clauses[pos_cls[prop_var][x]][1] : local_clauses[pos_cls[prop_var][x]][2];
            l3 = (local_clauses[pos_cls[prop_var][x]][3] == prop_var)? 
              local_clauses[pos_cls[prop_var][x]][2] : local_clauses[pos_cls[prop_var][x]][3];
            var1 = var_truth_table[abs(l1)];
            var2 = var_truth_table[abs(l2)];
            var3 = var_truth_table[abs(l3)];
	    if (l2 == 0){//2-lit cls
              l2 = prop_var; 
              var2 = var_truth_table[abs(l2)];
              conflict[x] = deduction3(l1, l2, var1, var2, x, l_ded);
	    }else if (l3 == 0){ //3-lit cls
              conflict[x] = deduction3(l1, l2, var1, var2, x, l_ded);
            }else{ //4-lit cls
              conflict[x] = deduction4(l1, l2, l3, var1, var2, var3, x, l_ded);
            }
            cls_ded[x] = pos_cls[prop_var][x];
            //if (conflict[x]){ printf("Found conflict @cls(%d)\n", pos_cls[prop_var][x]);}
          }else {
            conflict[x] = 0;
            l_ded[x] = 0;
            cls_ded[x] = 0;
          }
        }

        state = DEDUCTION;
        break;

      case DEDUCTION: 
        //printf("State = DED; ");
        prev_state = DEDUCTION; 
        conf_ded = 0;  

        for (int x = 0; x < BUF_CLS_SIZE; x++){
          int var_ded = abs(l_ded[x]);
          if (conflict[x]){
            conf_ded=1; 
            conf_var = prop_var;
            conf_cls = (var_truth_table[conf_var] == T || var_truth_table[conf_var] == FT)? neg_cls[conf_var][x] : pos_cls[conf_var][x];
            //printf("Found conflict Var(%d) due to cls(%d) with parent_cls(%d)\n", conf_var, conf_cls,parent_cls[conf_var]);
            break; 
          }else if (l_ded[x] != 0){ 
            if (var_truth_table[var_ded] == U){
              buf_ded_end ++;
              buf_ded[buf_ded_end] = l_ded[x]; 
              buf_ded_cls[buf_ded_end] = cls_ded[x]; 
              //Change ded value here
              dec_lvl[var_ded] = curr_lvl;  
              parent_cls[var_ded] = cls_ded[x]; 
              var_truth_table[var_ded] = l_ded[x] > 0 ? T : F;
              //Change lstparent below
              int tmp1 = abs(local_clauses[cls_ded[x]][0]);
              int tmp2 = abs(local_clauses[cls_ded[x]][1]);
              int tmp3 = abs(local_clauses[cls_ded[x]][2]);
              int tmp4 = abs(local_clauses[cls_ded[x]][3]);
              int lstparent1 = (tmp1 == var_ded) ? (dec_lvl[tmp2] == curr_lvl ? least_parent[tmp2]:tmp2) : (dec_lvl[tmp1] == curr_lvl ? least_parent[tmp1]:tmp1);
              int lstparent2 = ((tmp3 == var_ded) || (tmp4 == var_ded)) ? (dec_lvl[tmp2] == curr_lvl ? least_parent[tmp2]:tmp2):
				(dec_lvl[tmp3] == curr_lvl ? least_parent[tmp3]:tmp3);
              int lstparent3 = (tmp4 == var_ded) ?  (dec_lvl[tmp3] == curr_lvl ? least_parent[tmp3]:tmp3) : (dec_lvl[tmp4] == curr_lvl ? least_parent[tmp4]:tmp4);
              int lvl1 = dec_lvl[lstparent1] == curr_lvl ? -1 : dec_lvl[lstparent1]; 
              int lvl2 = dec_lvl[lstparent2] == curr_lvl ? -1 : dec_lvl[lstparent2]; 
              int lvl3 = dec_lvl[lstparent3] == curr_lvl ? -1 : dec_lvl[lstparent3]; 
              if (tmp3 == 0){ // 2-lit cls
                //least_parent[var_ded] = (lvl1 == 0) ? curr_lvl - 1 : lvl1;
                least_parent[var_ded] = lstparent1; 
              }else if (tmp4 == 0){ //3-lit cls
                least_parent[var_ded] = lvl1 > lvl2 ? lstparent1 : lstparent2; 
              }else{ // 4-lit cls
                least_parent[var_ded] = ((lvl1 >= lvl2) && (lvl1 >= lvl3)) ? lstparent1 : (lvl2 > lvl3) ? lstparent2 : lstparent3;
              }
              //printf("Add ded var(%d) --- cls(%d) : %d(%d) %d(%d) %d(%d) %d(%d)(currlvl %d)\n", l_ded[x], cls_ded[x], tmp1, dec_lvl[abs(tmp1)], tmp2, dec_lvl[abs(tmp2)], tmp3, dec_lvl[abs(tmp3)], tmp4, dec_lvl[abs(tmp4)], curr_lvl);
              //printf("lstparent: l1-%d(%d), l2-%d(%d), l3-%d(%d) ,assignedparent(%d(%d) )\n", lstparent1, lvl1, lstparent2, lvl2, lstparent3, lvl3, least_parent[var_ded], dec_lvl[least_parent[var_ded]]);
              //For debug 
              if(least_parent[var_ded] == -1 || dec_lvl[least_parent[var_ded]] >  curr_lvl){state = EXIT;  printf("Error - ded\n");
                printf("Add ded var(%d) --- cls(%d) : %d(%d) %d(%d) %d(%d) %d(%d)(declvl %d lstparent %d)\n", l_ded[x], cls_ded[x], tmp1, dec_lvl[abs(tmp1)], tmp2, dec_lvl[abs(tmp2)], tmp3, dec_lvl[abs(tmp3)], tmp4, dec_lvl[abs(tmp4)], curr_lvl, least_parent[var_ded]);
    printf("lstparent: l1-%d, l2-%d, l3-%d assignedparent(%d)\n", lstparent1, lstparent2, lstparent3, least_parent[var_ded]);
                break;
              }
            }else if ((var_truth_table[var_ded] == T && l_ded[x] < 0) || (var_truth_table[var_ded] == F && l_ded[x] > 0) ){
                //Check whether conflict in same level deduction 
                conf_ded=1; 
                conf_var = var_ded;
                conf_cls = cls_ded[x];
                //printf("Found conflict Var(%d) due to cls(%d) with parentcls(%d)\n", conf_var, conf_cls, parent_cls[var_ded]);
            }else{
                //printf("Duplicate ded var(%d) ----- cls : %d %d %d\n", l_ded[x], local_clauses[cls_ded[x]][0], local_clauses[cls_ded[x]][1], local_clauses[cls_ded[x]][2]);
            }
          }
        }

        //printf("curr ptr: %d, end ptr: %d\n", buf_ded_curr, buf_ded_end);
        if (buf_ded_end > BUF_DED_SIZE){
            printf("Buf size is too short\n");
            state = EXIT;
            break; 
        }

        //For debug
        if (state == EXIT){
          break; 
        }

        if (conf_ded){
          //Found conflict 
          state = (conf_var == dec_var[curr_lvl]) ? BACKTRACK_DEC : ANALYSIS;
          buf_ded_curr = -1; 
          buf_ded_end = -1;
        }else if (buf_ded_end == buf_ded_curr){
          //No deducted variable in buf_ded
          state = DECISION;
          buf_ded_curr = -1;
          buf_ded_end = -1; 
        }else{
          //Move to next variable in buf_ded
          state = PROP;
          buf_ded_curr ++;  
        }
        break; 

      case ANALYSIS: 
        //printf("State = ANALYSIS; ");
        prev_state = ANALYSIS; 
        loc0 = abs(local_clauses[parent_cls[conf_var]][0]);
        loc1 = abs(local_clauses[parent_cls[conf_var]][1]);
        loc2 = abs(local_clauses[parent_cls[conf_var]][2]);
        loc3 = abs(local_clauses[parent_cls[conf_var]][3]);

        loc4 = abs(local_clauses[conf_cls][0]);
        loc5 = abs(local_clauses[conf_cls][1]);
	loc6 = abs(local_clauses[conf_cls][2]);
	loc7 = abs(local_clauses[conf_cls][3]);

 /*
 * parent_cls/conf_cls: 2-lit/2-lit (2-parents)
 * parent_cls/conf_cls: 3-lit/3-lit, 4-lit/2-lit, 2-lit/4-lit (4 parents)
 * parent_cls/conf_cls: 3-lit/4-lit, 4-lit/3-lit  (5 parents)
 * parent_cls/conf_cls: 4-lit/4-lit (6 parents)
 * */

        if((conf_cls >= NUM_ORG_CLAUSES) || (parent_cls[conf_var] >= NUM_ORG_CLAUSES)){ // Don't add conflict clauses if it is deducted by learning clauses
          state = BACKTRACK_DEC;
          //curr_lst = curr_lvl - 1;

	  int lst_lvl0 = ((loc0 == prop_var) || (dec_lvl[least_parent[loc0]] == curr_lvl)) ? -1 : dec_lvl[least_parent[loc0]];
	  int lst_lvl1 = ((loc1 == prop_var) || (dec_lvl[least_parent[loc1]] == curr_lvl)) ? -1 : dec_lvl[least_parent[loc1]];
	  int lst_lvl2 = ((loc2 == prop_var) || (dec_lvl[least_parent[loc2]] == curr_lvl)) ? -1 : dec_lvl[least_parent[loc2]];
	  int lst_lvl3 = ((loc3 == prop_var) || (dec_lvl[least_parent[loc3]] == curr_lvl)) ? -1 : dec_lvl[least_parent[loc3]];

	  int lst_lvl4 = ((loc4 == prop_var) || (dec_lvl[least_parent[loc4]] == curr_lvl)) ? -1 : dec_lvl[least_parent[loc4]];
	  int lst_lvl5 = ((loc5 == prop_var) || (dec_lvl[least_parent[loc5]] == curr_lvl)) ? -1 : dec_lvl[least_parent[loc5]];
	  int lst_lvl6 = ((loc6 == prop_var) || (dec_lvl[least_parent[loc6]] == curr_lvl)) ? -1 : dec_lvl[least_parent[loc6]];
	  int lst_lvl7 = ((loc7 == prop_var) || (dec_lvl[least_parent[loc7]] == curr_lvl)) ? -1 : dec_lvl[least_parent[loc7]];

	  int hi1 = ((lst_lvl0 >= lst_lvl1) && (lst_lvl0 >= lst_lvl2)) ? lst_lvl0 : lst_lvl1 >= lst_lvl2 ? lst_lvl1 : lst_lvl2;
	  int hi2 = ((lst_lvl3 >= lst_lvl4) && (lst_lvl3 >= lst_lvl5)) ? lst_lvl3 : lst_lvl4 >= lst_lvl5 ? lst_lvl4 : lst_lvl5;
          int hi3 = lst_lvl6 > lst_lvl7 ? lst_lvl6 : lst_lvl7;
          curr_lst = ((hi1 >= hi2) && (hi1 >= hi3)) ? hi1 : (hi2 >= hi3) ? hi2 : hi3;

          if (var_truth_table[dec_var[curr_lvl]] == TF || var_truth_table[dec_var[curr_lvl]] == FT){
            //back_lvl = dec_lst_lvl[curr_lvl] > curr_lst ? dec_lst_lvl[curr_lvl] : curr_lst; 
            back_lvl = curr_lst;
            //For debug
            if (curr_lst == curr_lvl){printf("Error: lst parent is current lvl\n"); state = EXIT;}
          }else{
            dec_lst_lvl[curr_lvl] = curr_lst;
            back_lvl = curr_lvl;
            //For debug
            if (curr_lst == curr_lvl){printf("Error: lst parent is current lvl\n"); state = EXIT;}
          }
	  break;
	}

	conf_parents_tmp[0] = abs(local_clauses[parent_cls[conf_var]][0]) == conf_var ? 
                          local_clauses[parent_cls[conf_var]][1] : local_clauses[parent_cls[conf_var]][0]; 
        conf_parents_tmp[1] = abs(local_clauses[parent_cls[conf_var]][2]) == conf_var ? 
                          local_clauses[parent_cls[conf_var]][1] : local_clauses[parent_cls[conf_var]][2]; 
        
        conf_parents_tmp[2] = abs(local_clauses[conf_cls][0]) == conf_var ? 
                          local_clauses[conf_cls][1] : local_clauses[conf_cls][0]; 
        conf_parents_tmp[3] = abs(local_clauses[conf_cls][2]) == conf_var ? 
                          local_clauses[conf_cls][1] : local_clauses[conf_cls][2]; 
	
        //Sort based on parent_lvl
        #pragma ACCEL parallel flatten
        for (int i = 0; i < 4; i++){
          parent_lvl[i] = dec_lvl[abs(conf_parents_tmp[i])];
        }

        //printf("Original Parents var(lvl) %d(%d) %d(%d) %d(%d) %d(%d) \n", conf_parents_tmp[0], parent_lvl[0], conf_parents_tmp[1], parent_lvl[1], 
        //        conf_parents_tmp[2], parent_lvl[2], conf_parents_tmp[3], parent_lvl[3]);

        int sorted_idx[4]; 
        sort4_idx(parent_lvl, sorted_idx); 
        #pragma ACCEL parallel flatten
        for (int i = 0; i < 4; i++){
          conf_parents[i] = conf_parents_tmp[sorted_idx[i]];
        }
	
	conf_parents[1] = (conf_parents[0] != conf_parents[1]) ? conf_parents[1] : conf_parents[2];
	conf_parents[2] = (conf_parents[1] != conf_parents[2]) ? conf_parents[2] : (conf_parents[1] != conf_parents[3]) ? conf_parents[3] : 0;
	conf_parents[3] = ((conf_parents[2] != conf_parents[3]) && (conf_parents[2] != 0)) ? conf_parents[3] : 0;

	parent_lvl[0] = dec_lvl[abs(conf_parents[0])];
	parent_lvl[1] = dec_lvl[abs(conf_parents[1])];
	parent_lvl[2] = (conf_parents[2] == 0) ? -1 : dec_lvl[abs(conf_parents[2])];
	parent_lvl[3] = (conf_parents[3] == 0) ? -1 : dec_lvl[abs(conf_parents[3])];

        conf_lst_lvl[0] = dec_lvl[least_parent[abs(conf_parents[0])]]; 
        conf_lst_lvl[1] = dec_lvl[least_parent[abs(conf_parents[1])]]; 
        conf_lst_lvl[2] = (conf_parents[2] == 0) ? -1 : dec_lvl[least_parent[abs(conf_parents[2])]]; 
        conf_lst_lvl[3] = (conf_parents[3] == 0) ? -1 : dec_lvl[least_parent[abs(conf_parents[3])]]; 
/*
        printf("Analysis Conflict var %d with dec_lvl(%d), conf_cls(%d) parent_cls(%d)\n", conf_var,dec_lvl[conf_var], conf_cls, parent_cls[conf_var]);
        printf("Parents var(lvl) %d(%d) %d(%d) %d(%d) %d(%d) \n", conf_parents[0], parent_lvl[0], conf_parents[1], parent_lvl[1], 
                conf_parents[2], parent_lvl[2], conf_parents[3], parent_lvl[3]);
        printf("Lst back var(lvl) %d(%d) %d(%d) %d(%d) %d(%d)\n ", least_parent[abs(conf_parents[0])], conf_lst_lvl[0],
            least_parent[abs(conf_parents[1])], conf_lst_lvl[1],
            least_parent[abs(conf_parents[2])], conf_lst_lvl[2],
            least_parent[abs(conf_parents[3])], conf_lst_lvl[3]);
*/
        //Learning 
        tot_conflict = 0;
        //check 1: whether learn table is full
        if (learn_cls_nxtidx > NUM_TOT_CLAUSES){
          //printf("learn table is not enough\n");
	  tot_conflict = 1;
        }else {
          //Check 2: whether this clause is already in local cls
          #pragma ACCEL parallel flatten reduction=tot_conflict
          for (int i = 0; i < learn_cls_nxtidx; i++){
            int loc_l1 = local_clauses[i][0];
            int loc_l2 = local_clauses[i][1];
            int loc_l3 = local_clauses[i][2];
            int loc_l4 = local_clauses[i][3];
            bool found1 = (conf_parents[0]== loc_l1) || (conf_parents[0]== loc_l2) || (conf_parents[0]== loc_l3) || (conf_parents[0]== loc_l4);
            bool found2 = (conf_parents[1]== loc_l1) || (conf_parents[1]== loc_l2) || (conf_parents[1]== loc_l3) || (conf_parents[1]== loc_l4) || (conf_parents[1] == 0);
            bool found3 = (conf_parents[2]== loc_l1) || (conf_parents[2]== loc_l2) || (conf_parents[2]== loc_l3) || (conf_parents[2]== loc_l4) || (conf_parents[2] == 0);
            bool found4 = (conf_parents[3]== loc_l1) || (conf_parents[3]== loc_l2) || (conf_parents[3]== loc_l3) || (conf_parents[3]== loc_l4) || (conf_parents[3] == 0);
            tot_conflict |= (found1 && found2 && found3 && found4); 
          }
          if (tot_conflict){
            printf("Duplicate cls \n");
          }
	  //Check 3 : whether there's space for pos/neg buffer for all variables
	  conflict[0] = ((conf_parents[0] > 0) && (pos_cls_end[conf_parents[0]] >= BUF_CLS_SIZE)) || ((conf_parents[0] < 0) && (neg_cls_end[-conf_parents[0]] >= BUF_CLS_SIZE));
	  conflict[1] = ((conf_parents[1] > 0) && (pos_cls_end[conf_parents[1]] >= BUF_CLS_SIZE)) || ((conf_parents[1] < 0) && (neg_cls_end[-conf_parents[1]] >= BUF_CLS_SIZE));
	  conflict[2] = ((conf_parents[2] > 0) && (pos_cls_end[conf_parents[2]] >= BUF_CLS_SIZE)) || ((conf_parents[2] < 0) && (neg_cls_end[-conf_parents[2]] >= BUF_CLS_SIZE));
	  conflict[3] = ((conf_parents[3] > 0) && (pos_cls_end[conf_parents[3]] >= BUF_CLS_SIZE)) || ((conf_parents[3] < 0) && (neg_cls_end[-conf_parents[3]] >= BUF_CLS_SIZE));
          if (conflict[0] || conflict[1] || conflict[2] || conflict[3]){
	    tot_conflict = 1;
	    //printf("No space for this learned clauses\n");
	  }
	}

	if (!tot_conflict){
          printf("Add learned clauses(%d): %d, %d, %d, %d\n", learn_cls_nxtidx, conf_parents[0], conf_parents[1], conf_parents[2], conf_parents[3]);
          local_clauses[learn_cls_nxtidx][0] = conf_parents[0];
          local_clauses[learn_cls_nxtidx][1] = conf_parents[1];
          local_clauses[learn_cls_nxtidx][2] = conf_parents[2];
          local_clauses[learn_cls_nxtidx][3] = conf_parents[3];

          //parent 0
          if (conf_parents[0] > 0){
            if (pos_cls_end[conf_parents[0]] < BUF_CLS_SIZE){
              pos_cls[conf_parents[0]][pos_cls_end[conf_parents[0]]] = learn_cls_nxtidx;
              pos_cls_end[conf_parents[0]] ++; 
            }else{
              printf("Not enough pos cls buffer\n"); state = FAILED; printf("Error\n"); break;
            } 
          }else { //conf_parents[0] cannot be 0
            if (neg_cls_end[-conf_parents[0]] < BUF_CLS_SIZE){
              neg_cls[-conf_parents[0]][neg_cls_end[-conf_parents[0]]] = learn_cls_nxtidx;
              neg_cls_end[-conf_parents[0]] ++; 
            }else{
              printf("Not enough neg cls buffer\n"); state = FAILED; printf("Error\n"); break;
            } 
          }

          //parent 1
          if (conf_parents[1] > 0){
            if (pos_cls_end[conf_parents[1]] < BUF_CLS_SIZE){
              pos_cls[conf_parents[1]][pos_cls_end[conf_parents[1]]] = learn_cls_nxtidx;
              pos_cls_end[conf_parents[1]] ++; 
            }else{
              printf("Not enough pos cls buffer\n"); state = FAILED; printf("Error\n"); break;
            }
          }else{ //conf_parent[1] cannot be 0
            if (neg_cls_end[-conf_parents[1]] < BUF_CLS_SIZE){
              neg_cls[-conf_parents[1]][neg_cls_end[-conf_parents[1]]] = learn_cls_nxtidx;
              neg_cls_end[-conf_parents[1]] ++; 
            }else{
              printf("Not enough neg cls buffer\n"); state = FAILED; printf("Error\n"); break;
            }
          }

          //parent 2 
          if (conf_parents[2] > 0){
            if (pos_cls_end[conf_parents[2]] < BUF_CLS_SIZE){
              pos_cls[conf_parents[2]][pos_cls_end[conf_parents[2]]] = learn_cls_nxtidx;
              pos_cls_end[conf_parents[2]] ++; 
            }else{
              printf("Not enough pos cls buffer\n"); state = FAILED; printf("Error\n"); break;
            } 
          }else if (conf_parents[2] < 0){
            if (neg_cls_end[-conf_parents[2]] < BUF_CLS_SIZE){
              neg_cls[-conf_parents[2]][neg_cls_end[-conf_parents[2]]] = learn_cls_nxtidx;
              neg_cls_end[-conf_parents[2]] ++; 
            }else{
              printf("Not enough neg cls buffer\n"); state = FAILED; printf("Error\n"); break;
            } 
          }

          //parent 3
          if (conf_parents[3] > 0){
            if (pos_cls_end[conf_parents[3]] < BUF_CLS_SIZE){
              pos_cls[conf_parents[3]][pos_cls_end[conf_parents[3]]] = learn_cls_nxtidx;
              pos_cls_end[conf_parents[3]] ++; 
            }else{
              printf("Not enough pos cls buffer\n"); state = FAILED; printf("Error\n"); break;
            } 
          }else if (conf_parents[3] < 0){
            if (neg_cls_end[-conf_parents[3]] < BUF_CLS_SIZE){
              neg_cls[-conf_parents[3]][neg_cls_end[-conf_parents[3]]] = learn_cls_nxtidx;
              neg_cls_end[-conf_parents[3]] ++; 
            }else{
              printf("Not enough neg cls buffer\n"); state = FAILED; printf("Error\n"); break;
            } 
          }
	}//ENd of adding learnning cls (tot_conflict)

        if (conf_parents[2] == 0 && dec_lvl[abs(conf_parents[0])] < curr_lvl && tot_conflict){ // 2 lit cls
	  back_lvl = dec_lvl[abs(conf_parents[0])]; 
	  learned_lit = conf_parents[1];
          state = BACKTRACK_DED; break; 
	}else if ((conf_parents[3] == 0) && (conf_parents[2] != 0) && (dec_lvl[abs(conf_parents[1])] < curr_lvl) && !tot_conflict){ //3 lit cls
	  back_lvl = dec_lvl[abs(conf_parents[1])]; 
	  learned_lit = conf_parents[2];
          state = BACKTRACK_DED; break; 
	}
        if (!tot_conflict){  
          learn_cls_nxtidx ++;
        }
        //End of Learning part
        
        sort4(conf_lst_lvl);
        curr_lst = (conf_lst_lvl[3] != curr_lvl) ? conf_lst_lvl[3]: 
		(conf_lst_lvl[2] != curr_lvl) ? conf_lst_lvl[2] : (conf_lst_lvl[1] != curr_lvl) ? conf_lst_lvl[1] : conf_lst_lvl[0]; 
	//For debug 
        if (curr_lst < 0 || curr_lst == curr_lvl){
	  printf("Error\n"); state = FAILED; break;
	}

        if (var_truth_table[dec_var[curr_lvl]] == TF || var_truth_table[dec_var[curr_lvl]] == FT){
          back_lvl = dec_lst_lvl[curr_lvl] > curr_lst ? dec_lst_lvl[curr_lvl] : curr_lst; 
          //For debug
          if (curr_lst == curr_lvl){printf("Error: lst parent is current lvl\n"); state = EXIT;}
        }else{
          dec_lst_lvl[curr_lvl] = curr_lst;
          back_lvl = curr_lvl;
          //For debug
          if (curr_lst == curr_lvl){printf("Error: lst parent is current lvl\n"); state = EXIT;}
        }
        state = BACKTRACK_DEC;
        break; 

      case BACKTRACK_DEC: 
        //printf("State = BACKTRACK_DEC; ");
        if (prev_state == DEDUCTION){
          back_lvl = curr_lvl; 
        }
        
        prev_state = BACKTRACK_DEC;

        while(var_truth_table[dec_var[back_lvl]] == TF || var_truth_table[dec_var[back_lvl]] == FT){
          back_lvl --; 
          if (back_lvl < 0){
            break; 
          }
        }

        if (back_lvl < 0){
          printf("Failed at lvl %d\n", back_lvl);
          state = FAILED; 
          break;
        }

if (back_lvl < 15){
        printf("Back to lvl %d - Var %d\n", back_lvl, dec_var[back_lvl]);
}

        prev_assigned_value = var_truth_table[dec_var[back_lvl]]; 
        //Undo all variable assignment after back_lvl
        #pragma ACCEL parallel flatten
        for (int i = 0; i < NUM_VARS; i ++){
          if (dec_lvl[i] >= back_lvl){
            var_truth_table[i] = U;
            dec_lvl[i] = -1; 
            parent_cls[i] = -1;
            least_parent[i] = 0;
          }
        }

        #pragma ACCEL parallel flatten
        for (int i = 0; i < BUF_DEC_LVL; i++){
          if (i > back_lvl){
            dec_var[i] = 0; 
            dec_lst_lvl[i] = -1; 
          }
        }

        new_var_idx = dec_var[back_lvl]; 
        var_truth_table[new_var_idx] = (prev_assigned_value == T) ? TF : FT;
        dec_lvl[new_var_idx] = back_lvl;
        least_parent[new_var_idx] = new_var_idx;
        //printf("Change VTT Var(%d) to %d\n", dec_var[back_lvl], var_truth_table[dec_var[back_lvl]]);
        curr_lvl = back_lvl; 

        state = PROP;
        break;

      case BACKTRACK_DED:
        prev_state = BACKTRACK_DED;
        //printf("Conflict var %d with dec_lvl(%d), conf_cls(%d) parent_cls(%d)\n", conf_var,dec_lvl[conf_var], conf_cls, parent_cls[conf_var]);
        #pragma ACCEL parallel flatten
        for (int i = 0; i < NUM_VARS; i ++){
          if (dec_lvl[i] > back_lvl){
            var_truth_table[i] = U;
            dec_lvl[i] = -1; 
            parent_cls[i] = -1;
            least_parent[i] = 0; 
          }
        }

        #pragma ACCEL parallel flatten
        for (int i = 0; i < BUF_DEC_LVL; i++){
          if (i > back_lvl){
            dec_var[i] = 0; 
          }
        }

        new_var_idx = dec_var[back_lvl]; 
        var_truth_table[abs(learned_lit)] = learned_lit > 0 ? T : F; 
        dec_lvl[abs(learned_lit)] = back_lvl;
        parent_cls[abs(learned_lit)] = learn_cls_nxtidx;
        learn_cls_nxtidx ++; 
        curr_lvl = back_lvl;
        if (conf_parents[2] == 0){
	  // 2-lit cls
	  least_parent[abs(learned_lit)] = least_parent[abs(conf_parents[0])];
	}else {
	  int lst1 = least_parent[abs(conf_parents[0])];
	  int lst2 = least_parent[abs(conf_parents[1])];
          int lv1 = dec_lvl[lst1] == curr_lvl ? -1 : dec_lvl[lst1]; 
          int lv2 = dec_lvl[lst2] == curr_lvl ? -1 : dec_lvl[lst2]; 
	  least_parent[abs(learned_lit)] = (dec_lvl[abs(conf_parents[0])] == back_lvl) ? (lv1 > lv2 ? lst1 : lst2) : abs(conf_parents[0]); 
	  if ((lv1== -1) && (lv2 == -1)){
	    least_parent[abs(learned_lit)] = lst1;
	     printf("Error\n"); state = FAILED; break; 
	  }
	}
        //printf("Change VTT Var(%d) to %d\n", dec_var[back_lvl], var_truth_table[dec_var[back_lvl]]);

if (back_lvl < 15){
        printf("Back to learn lvl %d - Var %d\n", back_lvl, dec_var[back_lvl]);
}

        state = PROP; 
        break; 

      case SOLVED:
        printf("Solved\n");
        tot_conflict = 0;
        #pragma ACCEL parallel flatten reduction=tot_conflict
        for (int x = 0; x < NUM_ORG_CLAUSES; x++){
          int l1_tmp = local_clauses[x][0];
          int l2_tmp = local_clauses[x][1];
          int l3_tmp = local_clauses[x][2];
          bool unsat1 = l1_tmp >0 ? (var_truth_table[l1_tmp] == F || var_truth_table[l1_tmp] == TF) : (var_truth_table[-l1_tmp] == T || var_truth_table[-l1_tmp] == FT);
          bool unsat2 = l2_tmp >0 ? (var_truth_table[l2_tmp] == F || var_truth_table[l2_tmp] == TF) : (var_truth_table[-l2_tmp] == T || var_truth_table[-l2_tmp] == FT);
          bool unsat3 = l3_tmp >0 ? (var_truth_table[l3_tmp] == F || var_truth_table[l3_tmp] == TF) : (var_truth_table[-l3_tmp] == T || var_truth_table[-l3_tmp] == FT);
          tot_conflict |= (unsat1 && unsat2 && unsat3);
        }

        for (int x = 1; x < NUM_VARS; x++){
          if (var_truth_table[x] == U){
            tot_conflict = 1;
            printf("Not assign value to var(%d)\n", x);
            //break;
           }
         }

        if (tot_conflict){
          printf("Error!! Solution is not correct\n");
        }else{
          printf("Solution is correct\n");
        }

        state = EXIT;
        break; 

      case FAILED:
        printf("Failed to solve the problem. \n");
        state = EXIT; 
        break;
    }//end of sw
  }//end of while



  satisfiable = unsatisfiable ? 0 : 1; 

  printf("SAT result: %d\n", satisfiable);
  printf("unSAT result: %d\n", unsatisfiable);

  result[0] = satisfiable;

}
