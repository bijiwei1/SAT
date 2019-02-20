#include <string.h>
#include <math.h>
#include <assert.h>
#include <stdlib.h>
#include <stdio.h>

#include <config.h>
//#include <string> 
//using namespace std; 


void collect_buffer(int pos_cls[NUM_VARS][BUF_CLS_SIZE], int neg_cls[NUM_VARS][BUF_CLS_SIZE], 
  int lit, int x, 
  int *extra_cls, int *extra_lit, 
  int* num_extra);

bool deduction(int l1, int l2, char *var_truth_table, int x, int *l_ded);

void sort (int array[4]); 

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
  int local_clauses[NUM_CLAUSES][3];
  char var_truth_table[NUM_VARS] = {U}; // T, F, U (Undef), TF(assigned to T first), FT(assigned to F first)
  int dec_lvl[NUM_VARS] = {-1};
  int dec_var[100]= {0}; // Variable idx at each decision lvl, we assume at most 100 decision level
  int parent_cls[NUM_VARS] = {0}; 
  int buf_ded[BUF_DED_SIZE] = {0};
  int buf_ded_cls[BUF_DED_SIZE] = {-1}; 

  int learn_cls_table[LEARN_TABLE_SIZE][3];
  int learn_cls_nxtidx= 0; 

  int l_ded[BUF_CLS_SIZE];
  int cls_ded[BUF_CLS_SIZE]; 
  bool conflict[BUF_CLS_SIZE];

  int l_ded_learn[LEARN_TABLE_SIZE];
  int cls_ded_learn[LEARN_TABLE_SIZE]; 
  bool conflict_learn[LEARN_TABLE_SIZE]; 
  
  int pos_cls[NUM_VARS][BUF_CLS_SIZE] = {-1}; 
  int neg_cls[NUM_VARS][BUF_CLS_SIZE] = {-1}; 
  int extra_cls[extra_buf_size] = {0}; 
  int extra_lit[extra_buf_size] = {0}; 


  //Idx and ptr 
  int new_var_idx = 1;
  int curr_lvl = -1; 
  int buf_ded_curr = -1;
  int buf_ded_end = -1;

  //Other global variables
  int state = DECISION; 
  int prev_state = DECISION; 
  int num_extra[1] = {0};
  int conf_var; 
  int conf_cls; 
  int conf_parents[4]; 
  int parent_lvl[4]; 
  int back_lvl = 0; 

  //Temporary variabels
  bool tot_conflict = 0; //PROP, DED
  bool conf_ded; //PROP
  int tmp_conf_cls; //BACKTRACK
  int prev_assigned_value; // BACKTRACK
  int prop_var; //PROP

/*************************** Initializing array ***************************/

//#pragma ACCEL parallel flatten
  for (int x = 1; x< NUM_VARS; x++){
    for (int y = 0; y< BUF_CLS_SIZE; y++){
      pos_cls[x][y] = EMPTY; 
      neg_cls[x][y] = EMPTY; 
    }
  }

/*************************** Loading Clauses ***************************/
  //Load data
  printf("Start to load data \n");
  for (int x = 0; x < NUM_CLAUSES; ++x) {
    local_clauses[x][0] = c1[x];
    local_clauses[x][1] = c2[x];
    local_clauses[x][2] = c3[x];

    collect_buffer(pos_cls, neg_cls, c1[x], x, extra_cls, extra_lit, num_extra);
    collect_buffer(pos_cls, neg_cls, c2[x], x, extra_cls, extra_lit, num_extra);
    collect_buffer(pos_cls, neg_cls, c3[x], x, extra_cls, extra_lit, num_extra);
  }
/*
for (int x = 0; x < NUM_CLAUSES; x++){
    printf("%d %d %d\n", local_clauses[x][0], local_clauses[x][1], local_clauses[x][2]);
  } 
  for (int x = 1; x < NUM_VARS; x++){
    printf("Pos var(%d): %d %d %d %d %d %d %d %d %d %d\n", x, 
      pos_cls[x][0], pos_cls[x][1], pos_cls[x][2], pos_cls[x][3], pos_cls[x][4], 
      pos_cls[x][5], pos_cls[x][6], pos_cls[x][7], pos_cls[x][8], pos_cls[x][9]); 
    printf("Neg var(%d): %d %d %d %d %d %d %d %d %d %d\n", x, 
      neg_cls[x][0], neg_cls[x][1], neg_cls[x][2], neg_cls[x][3], neg_cls[x][4], 
      neg_cls[x][5], neg_cls[x][6], neg_cls[x][7], neg_cls[x][8], neg_cls[x][9]);
  } 
  printf("Extra cls buffer size : %d < %d\n", num_extra[0], extra_buf_size);
  for (int x = 0; x < num_extra[0]; x++){
    printf("Extra var(%d) at cls(%d) \n", extra_lit[x], extra_cls[x]);
  }
  for (int x = 1; x < NUM_VARS; x++){
    printf("Pos var(%d): %d %d %d %d %d %d %d %d %d %d\n", x, 
      pos_cls[x][0], pos_cls[x][2], pos_cls[x][4], pos_cls[x][6], pos_cls[x][8], 
      pos_cls[x][10], pos_cls[x][12], pos_cls[x][14], pos_cls[x][16], pos_cls[x][20]); 
    printf("Neg var(%d): %d %d %d %d %d %d %d %d %d %d\n", x, 
      neg_cls[x][0], neg_cls[x][2], neg_cls[x][4], neg_cls[x][6], neg_cls[x][8], 
      neg_cls[x][10], neg_cls[x][12], neg_cls[x][14], neg_cls[x][16], neg_cls[x][20]);
  } 
  */
  printf("Extra cls buffer size : %d < %d\n", num_extra[0], extra_buf_size);
  for (int x = 0; x< NUM_VARS; x++){
     var_truth_table[x] = U; 
  }

/********************************* FSM **********************************/
  while (state != EXIT){
    switch(state){
      case DECISION: 
        printf("State = DECISION; ");

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
        if (curr_lvl < 15){
            printf("Decide Var(%d)\n", new_var_idx);
        }
          curr_lvl ++; 

          if (pos_cls[new_var_idx][5] != -1){
            var_truth_table[new_var_idx] = T;
          }else {
            var_truth_table[new_var_idx] = F;
          }

          dec_lvl[new_var_idx] = curr_lvl; 
          dec_var[curr_lvl] = new_var_idx; 
        }

        prev_state = DECISION; 
        break;

      case PROP:
        printf("State = PROP; ");
        if (prev_state == DECISION){
          prop_var = new_var_idx;
          printf("Prop dec Var(%d): %d\n", prop_var, var_truth_table[prop_var]);
        }else if (prev_state == DEDUCTION){
          prop_var = abs(buf_ded[buf_ded_curr]);
          printf("Prop ded Var(%d): %d\n", prop_var, var_truth_table[prop_var]);
        }else if (prev_state == BACKTRACK){
          prop_var = new_var_idx;
          printf("Prop dec_back Var(%d): %d\n", prop_var, var_truth_table[prop_var]);
        }

        /****************** pos_buf & neg_buf *****************/
        tot_conflict = 0; 
        #pragma ACCEL parallel flatten 
        for (int x = 0; x < BUF_CLS_SIZE; x++){
          int l1, l2; 
          if( (var_truth_table[prop_var] == T || var_truth_table[prop_var] == FT) && neg_cls[prop_var][x] != EMPTY){
            l1 = (local_clauses[neg_cls[prop_var][x]][0] == -prop_var)? 
              local_clauses[neg_cls[prop_var][x]][1] : local_clauses[neg_cls[prop_var][x]][0];
            l2 = (local_clauses[neg_cls[prop_var][x]][2] == -prop_var)? 
              local_clauses[neg_cls[prop_var][x]][1] : local_clauses[neg_cls[prop_var][x]][2];
            conflict[x] = deduction(l1, l2, var_truth_table, x, l_ded);
            cls_ded[x] = neg_cls[prop_var][x];
            //if (conflict[x]){ printf("Found conflict @cls(%d)\n", neg_cls[prop_var][x]);}
          }else if ((var_truth_table[prop_var] == F  || var_truth_table[prop_var] == TF) && pos_cls[prop_var][x] != EMPTY){
            l1 = (local_clauses[pos_cls[prop_var][x]][0] == prop_var)? 
              local_clauses[pos_cls[prop_var][x]][1] : local_clauses[pos_cls[prop_var][x]][0];
            l2 = (local_clauses[pos_cls[prop_var][x]][2] == prop_var)? 
              local_clauses[pos_cls[prop_var][x]][1] : local_clauses[pos_cls[prop_var][x]][2];
            conflict[x] = deduction(l1, l2, var_truth_table, x, l_ded);
            cls_ded[x] = pos_cls[prop_var][x];
            //if (conflict[x]){ printf("Found conflict @cls(%d)\n", pos_cls[prop_var][x]);}
          }else {
            conflict[x] = 0;
            l_ded[x] = 0;
            cls_ded[x] = 0;
          }
        }

        //For learning clauses
        /*
        #pragma ACCEL parallel flatten 
        for (int x = 0; x < learn_cls_nxtidx; x++){
          int l1, l2; 
          if (learn_cls_table[x][0] == prop_var){
            l1 = learn_cls_table[x][1]; 
            l2 = learn_cls_table[x][2];
            conflict_learn[x] = deduction(l1, l2, var_truth_table, x, l_ded_learn);
            cls_ded_learn[x] = x + BUF_CLS_SIZE;
          }else if (learn_cls_table[x][1] == prop_var){
            l1 = learn_cls_table[x][0]; 
            l2 = learn_cls_table[x][2];
            conflict_learn[x] = deduction(l1, l2, var_truth_table, x, l_ded_learn);
            cls_ded_learn[x] = x + BUF_CLS_SIZE;
          }else if (learn_cls_table[x][2] == prop_var){
            l1 = learn_cls_table[x][0]; 
            l2 = learn_cls_table[x][1];
            conflict_learn[x] = deduction(l1, l2, var_truth_table, x, l_ded_learn);
            cls_ded_learn[x] = x + BUF_CLS_SIZE;
            if (conflict_learn[x]){ printf("Found conflict at learn table @cls(%d)\n", x);}
          }else{
            conflict_learn[x] = 0;
            l_ded_learn[x] = 0;
            cls_ded_learn[x] = 0;
          }
        } */
        state = DEDUCTION;
        break;

      case DEDUCTION: 
        printf("State = DED; ");
        prev_state = DEDUCTION; 
        conf_ded = 0;  
        for (int x = 0; x < BUF_CLS_SIZE; x++){
          if (conflict[x]){
            conf_ded=1; 
            conf_var = prop_var;
            conf_cls = (var_truth_table[conf_var] == T || var_truth_table[conf_var] == FT)? neg_cls[conf_var][x] : pos_cls[conf_var][x];
            printf("Found conflict Var(%d) due to cls(%d) with parent_cls(%d)\n", conf_var, conf_cls,parent_cls[conf_var]);
          break; 
          }else if (l_ded[x] != 0){ 
            if (var_truth_table[abs(l_ded[x])] == U){
              buf_ded_end ++;
              buf_ded[buf_ded_end] = l_ded[x]; 
              buf_ded_cls[buf_ded_end] = cls_ded[x]; 
              printf("Add ded var(%d) to buf ----- cls : %d %d %d (declvl %d)\n", l_ded[x], local_clauses[cls_ded[x]][0], local_clauses[cls_ded[x]][1], local_clauses[cls_ded[x]][2], curr_lvl);
              //Change ded value here
              dec_lvl[abs(l_ded[x])] = curr_lvl;  
              parent_cls[abs(l_ded[x])] = cls_ded[x]; 
              var_truth_table[abs(l_ded[x])] = l_ded[x] > 0 ? T : F;
              var_truth_table[abs(l_ded[x])] = l_ded[x] > 0 ? T : F;
              //printf("Change VTT Var(%d) to %d\n", abs(l_ded[x]), var_truth_table[abs(l_ded[x])]);
            }else if ((var_truth_table[abs(l_ded[x])] == T && l_ded[x] < 0) || (var_truth_table[abs(l_ded[x])] == F && l_ded[x] > 0) ){
                //Check whether conflict in same level deduction 
                conf_ded=1; 
                conf_var = abs(l_ded[x]);
                conf_cls = cls_ded[x];
                //printf("Found conflict Var(%d) due to cls(%d) with parentcls(%d)\n", conf_var, conf_cls, parent_cls[abs(l_ded[x])]);
            }else{
                //printf("Duplicate ded var(%d) ----- cls : %d %d %d\n", l_ded[x], local_clauses[cls_ded[x]][0], local_clauses[cls_ded[x]][1], local_clauses[cls_ded[x]][2]);
            }
          }
        }
/*
        for (int x = 0; x < learn_cls_nxtidx; x++){
          if (conflict_learn[x]){
            conf_ded=1; 
            conf_var = prop_var;
            conf_cls = x;
            printf("Found conflict Var(%d) due to learnt cls(%d) with parent_cls(%d)\n", conf_var, conf_cls,parent_cls[conf_var]);
            break; 
          }else if (l_ded_learn[x] != 0){ 
            if (var_truth_table[abs(l_ded_learn[x])] == U){
              buf_ded_end ++;
              buf_ded[buf_ded_end] = l_ded_learn[x]; 
              buf_ded_cls[buf_ded_end] = cls_ded_learn[x]; 
              printf("Add ded var(%d) to buf ----- cls : %d %d %d (declvl %d)\n", l_ded_learn[x], learn_cls_table[cls_ded_learn[x]][0], learn_cls_table[cls_ded_learn[x]][1], learn_cls_table[cls_ded_learn[x]][2], curr_lvl);
              //Change ded value here
              dec_lvl[abs(l_ded_learn[x])] = curr_lvl;  
              parent_cls[abs(l_ded_learn[x])] = cls_ded_learn[x]; 
              var_truth_table[abs(l_ded_learn[x])] = l_ded[x] > 0 ? T : F;
              var_truth_table[abs(l_ded_learn[x])] = l_ded[x] > 0 ? T : F;
              //printf("Change VTT Var(%d) to %d\n", abs(l_ded_learn[x]), var_truth_table[abs(l_ded_learn[x])]);
            }else if ((var_truth_table[abs(l_ded_learn[x])] == T && l_ded_learn[x] < 0) || (var_truth_table[abs(l_ded_learn[x])] == F && l_ded_learn[x] > 0) ){
                //Check whether conflict in same level deduction 
                conf_ded=1; 
                conf_var = abs(l_ded_learn[x]);
                conf_cls = cls_ded_learn[x];
                printf("Found conflict Var(%d) due to cls(%d) with parentcls(%d)\n", conf_var, conf_cls, parent_cls[abs(l_ded_learn[x])]);
            }else{
                //printf("Duplicate ded var(%d) ----- cls : %d %d %d\n", l_ded[x], local_clauses[cls_ded[x]][0], local_clauses[cls_ded[x]][1], local_clauses[cls_ded[x]][2]);
            }
          }
        }
*/
        //printf("curr ptr: %d, end ptr: %d\n", buf_ded_curr, buf_ded_end);
        if (buf_ded_end > BUF_DED_SIZE){
            printf("Buf size is too short\n");
            state = EXIT;
            break; 
        }

        if (conf_ded){
        //Found conflict during deduction process
          state = BACKTRACK;
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

        //Precheck conflict
        /*
        #pragma ACCEL parallel flatten reduction=tot_conflict
        for (int x = 0; x < NUM_CLAUSES; x++){
          int l1_tmp = local_clauses[x][0];
          int l2_tmp = local_clauses[x][1];
          int l3_tmp = local_clauses[x][2];
          bool unsat1 = l1_tmp >0 ? (var_truth_table[l1_tmp] == F || var_truth_table[l1_tmp] == TF) : (var_truth_table[-l1_tmp] == T || var_truth_table[-l1_tmp] == FT);
          bool unsat2 = l2_tmp >0 ? (var_truth_table[l2_tmp] == F || var_truth_table[l2_tmp] == TF) : (var_truth_table[-l2_tmp] == T || var_truth_table[-l2_tmp] == FT);
          bool unsat3 = l3_tmp >0 ? (var_truth_table[l3_tmp] == F || var_truth_table[l3_tmp] == TF) : (var_truth_table[-l3_tmp] == T || var_truth_table[-l3_tmp] == FT);
          tot_conflict |= (unsat1 && unsat2 && unsat3);
        }

        if (tot_conflict){
          state = BACKTRACK2; 
        }else{
          state = DEDUCTION; 
        }*/

        break; 

      case BACKTRACK2: 
        printf("State = BACKTRACK2; ");
        var_truth_table[new_var_idx] = (var_truth_table[new_var_idx] == T) ? TF : FT; 
        prev_state = DECISION; 
        state = EXIT;
        break;

      case BACKTRACK:
        printf("State = BACKTRACK; ");
        prev_state = BACKTRACK;
        printf("Conflict var %d with dec_lvl(%d), conf_cls(%d) parent_cls(%d)\n", conf_var,dec_lvl[conf_var], conf_cls, parent_cls[conf_var]);
        //printf("Conflict var %d with dec_lvl(%d), conf_cls(%d) parent_vars(%d %d)\n", conf_var,dec_lvl[conf_var], conf_cls, parent_var1[conf_var], parent_var2[conf_var]);

        conf_parents[0] = abs(local_clauses[parent_cls[conf_var]][0]) == conf_var ? 
                          local_clauses[parent_cls[conf_var]][1] : local_clauses[parent_cls[conf_var]][0]; 
        conf_parents[1] = abs(local_clauses[parent_cls[conf_var]][2]) == conf_var ? 
                          local_clauses[parent_cls[conf_var]][1] : local_clauses[parent_cls[conf_var]][2]; 
        conf_parents[2] = abs(local_clauses[conf_cls][0]) == conf_var ? 
                          local_clauses[conf_cls][1] : local_clauses[conf_cls][0]; 
        conf_parents[3] = abs(local_clauses[conf_cls][2]) == conf_var ? 
                          local_clauses[conf_cls][1] : local_clauses[conf_cls][2]; 

        for (int i = 0; i < 4; i++){
          parent_lvl[i] = dec_lvl[abs(conf_parents[i])];
        }

        for (int i = 0; i < 4; i++){
          for (int j = 0; j < 4; j++){
            if (i < j && (abs(conf_parents[i]) == abs(conf_parents[j]))){
              conf_parents[j] = 0; 
              dec_lvl[j] = 0; 
            }
          }
        }

        // Learning process
        if (conf_parents[1] == 0){
          printf("Add learn cls %d %d %d\n", conf_parents[0], conf_parents[2], conf_parents[3]);
          learn_cls_table[learn_cls_nxtidx][0] =  -conf_parents[0]; 
          learn_cls_table[learn_cls_nxtidx][1] =  -conf_parents[2]; 
          learn_cls_table[learn_cls_nxtidx][2] =  -conf_parents[3];
          learn_cls_nxtidx ++; 
        }else if (conf_parents[2] == 0){
          printf("Add learn cls %d %d %d\n", conf_parents[0], conf_parents[1], conf_parents[3]);
          learn_cls_table[learn_cls_nxtidx][0] =  -conf_parents[0]; 
          learn_cls_table[learn_cls_nxtidx][1] =  -conf_parents[1]; 
          learn_cls_table[learn_cls_nxtidx][2] =  -conf_parents[3]; 
          learn_cls_nxtidx ++; 
        }else if (conf_parents[3] == 0){
          printf("Add learn cls %d %d %d\n", conf_parents[0], conf_parents[1], conf_parents[2]);
          learn_cls_table[learn_cls_nxtidx][0] =  -conf_parents[0]; 
          learn_cls_table[learn_cls_nxtidx][1] =  -conf_parents[1]; 
          learn_cls_table[learn_cls_nxtidx][2] =  -conf_parents[2]; 
          learn_cls_nxtidx ++; 
        }

	if (learn_cls_nxtidx > 50){
 	  state = EXIT;
	  printf("learn table is not enough\n")	;
	}

        //sort(parent_lvl);     
        printf("Parents lvl %d %d %d %d", parent_lvl[0], parent_lvl[1], parent_lvl[2], parent_lvl[3]);

       /*
        parent1 = parent_var1[conf_cls];
        parent2 = parent_var2[conf_cls];
        printf("Parents(lvl) %d(%d) %d(%d) %d(%d) %d(%d)", parent1, dec_lvl[parent1], parent2, dec_lvl[parent2], parent3, dec_lvl[parent3], parent4, dec_lvl[parent4]);
       parent_lvl[0] = dec_lvl[parent1];
       parent_lvl[1] = dec_lvl[parent2];
       parent_lvl[2] = dec_lvl[parent3];
       parent_lvl[3] = dec_lvl[parent4];
*/
//        printf("Parents lvl %d %d %d %d", parent_lvl[0], parent_lvl[1], parent_lvl[2], parent_lvl[3]);
        //sort(parent_lvl); 
    
//        printf("Parents lvl %d %d %d %d", parent_lvl[0], parent_lvl[1], parent_lvl[2], parent_lvl[3]);
        /*
        back_lvl = var_truth_table[dec_var[parent_lvl[3]]] <= F ? parent_lvl[3] : 
                      var_truth_table[dec_var[parent_lvl[2]]] <= F ? parent_lvl[2] : 
                      var_truth_table[dec_var[parent_lvl[1]]] <= F ? parent_lvl[1] : 
                      var_truth_table[dec_var[parent_lvl[0]]] <= F ? parent_lvl[0] : -1;  
        */

        back_lvl = curr_lvl; 
        while(var_truth_table[dec_var[back_lvl]] == TF || var_truth_table[dec_var[back_lvl]] == FT){
          back_lvl --; 
        }
  
        if (back_lvl < 0){
          printf("Failed at lvl %d\n", back_lvl);
          state = FAILED; 
          break; 
        }else{
          printf("Back to lvl %d\n", back_lvl);
        }
  

        prev_assigned_value = var_truth_table[dec_var[back_lvl]]; 
        //Undo all variable assignment after back_lvl
        #pragma ACCEL parallel flatten
        for (int i = 0; i < NUM_VARS; i ++){
          if (dec_lvl[i] >= back_lvl){
            var_truth_table[i] = U;
            dec_lvl[i] = -1; 
            parent_cls[i] = -1;
            //parent_var1[i] = 0;
            //parent_var2[i] = 0;
          }
        }

        var_truth_table[dec_var[back_lvl]] = (prev_assigned_value == T) ? TF : FT;
        printf("Change VTT Var(%d) to %d\n", dec_var[back_lvl], var_truth_table[dec_var[back_lvl]]);
        dec_lvl[dec_var[back_lvl]] = back_lvl;
        new_var_idx = dec_var[back_lvl]; 
        curr_lvl = back_lvl; 


        #pragma ACCEL parallel flatten
        for (int i = 0; i < 100; i++){
          if (i > back_lvl){
            dec_var[i] = 0; 
          }
        }

        state = PROP; 
        break; 

      case SOLVED:
        printf("Solved\n");
        tot_conflict = 0;
        #pragma ACCEL parallel flatten reduction=tot_conflict
        for (int x = 0; x < NUM_CLAUSES; x++){
          int l1_tmp = local_clauses[x][0];
          int l2_tmp = local_clauses[x][1];
          int l3_tmp = local_clauses[x][2];
          bool unsat1 = l1_tmp >0 ? (var_truth_table[l1_tmp] == F || var_truth_table[l1_tmp] == TF) : (var_truth_table[-l1_tmp] == T || var_truth_table[-l1_tmp] == FT);
          bool unsat2 = l2_tmp >0 ? (var_truth_table[l2_tmp] == F || var_truth_table[l2_tmp] == TF) : (var_truth_table[-l2_tmp] == T || var_truth_table[-l2_tmp] == FT);
          bool unsat3 = l3_tmp >0 ? (var_truth_table[l3_tmp] == F || var_truth_table[l3_tmp] == TF) : (var_truth_table[-l3_tmp] == T || var_truth_table[-l3_tmp] == FT);
          tot_conflict |= (unsat1 && unsat2 && unsat3);
        }

        for (int x = 0; x < NUM_VARS; x++){
	  if (var_truth_table[x] == U){
	    tot_conflict = 1;
	    break;
	  }
	}
        if (tot_conflict){
	  printf("Error!! Solution is not correct");
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
