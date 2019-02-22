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
  int local_clauses[NUM_CLAUSES][3];
  char var_truth_table[NUM_VARS] = {U}; // T, F, U (Undef), TF(assigned to T first), FT(assigned to F first)
  int dec_lvl[NUM_VARS] = {-1};
  int dec_var[BUF_DEC_LVL]= {0}; // Variable idx at each decision lvl, we assume at most 100 decision level
  int buf_ded[BUF_DED_SIZE] = {0};
  int buf_ded_cls[BUF_DED_SIZE] = {-1}; 
  int parent_cls[NUM_VARS] = {0}; 

  int least_parent[NUM_VARS] = {-1};
  int dec_lst_lvl[BUF_DEC_LVL] = {-1}; 


  int l_ded[BUF_CLS_SIZE];
  int cls_ded[BUF_CLS_SIZE]; 
  bool conflict[BUF_CLS_SIZE];
  
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
  int conf_lst_lvl[4]; 
  int back_lvl = 0; 

  //Temporary variabels
  bool tot_conflict = 0; //PROP, DED
  bool conf_ded; //PROP
  int tmp_conf_cls; //BACKTRACK
  int prev_assigned_value; // BACKTRACK
  int prop_var; //PROP
  int conf_parent_tmp[4], parent_lvl_tmp[4], lst_tmp[4];
  int curr_lst;

/* For learn clause
  int learn_cls_table[LEARN_TABLE_SIZE][3];
  int learn_cls_nxtidx= 0; 
  int l_ded_learn[LEARN_TABLE_SIZE];
  int cls_ded_learn[LEARN_TABLE_SIZE]; 
  bool conflict_learn[LEARN_TABLE_SIZE]; 
  bool isduplicate; 
  int poss_learn_cls[3]; 
  bool issameparent; 
  bool islearned; 
  int lit_learned; 
*/


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
  //      printf("State = DECISION; ");

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
//          printf("Decide Var(%d) - at lvl %d\n", new_var_idx, curr_lvl);

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
//        printf("State = PROP; ");
        if (prev_state == DECISION || prev_state == BACKTRACK_DEC){
          prop_var = new_var_idx;
        }else if (prev_state == DEDUCTION){
          prop_var = abs(buf_ded[buf_ded_curr]);
        }else if (prev_state == BACKTRACK){
          //prop_var = abs(lit_learned);
        }
        //printf("Prop ded Var(%d): %d\n", prop_var, var_truth_table[prop_var]);

        /****************** pos_buf & neg_buf *****************/
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
          if (abs(learn_cls_table[x][0]) == prop_var){
            if((learn_cls_table[x][0] < 0 && (var_truth_table[prop_var] == T || var_truth_table[prop_var] == FT)) 
		          || (learn_cls_table[x][0] > 0 && (var_truth_table[prop_var] == F || var_truth_table[prop_var] == TF))){
              l1 = learn_cls_table[x][1]; 
              l2 = learn_cls_table[x][2];
              conflict_learn[x] = deduction(l1, l2, var_truth_table, x, l_ded_learn);
              cls_ded_learn[x] = x;
              //if (conflict_learn[x]){ printf("Found conflict at learn table @cls(%d)\n", x);}
            }
          }else if (abs(learn_cls_table[x][1]) == prop_var){
            if((learn_cls_table[x][1] < 0 && (var_truth_table[prop_var] == T || var_truth_table[prop_var] == FT)) 
		          || (learn_cls_table[x][1] > 0 && (var_truth_table[prop_var] == F || var_truth_table[prop_var] == TF))){
              l1 = learn_cls_table[x][0]; 
              l2 = learn_cls_table[x][2];
              conflict_learn[x] = deduction(l1, l2, var_truth_table, x, l_ded_learn);
              cls_ded_learn[x] = x;
              //if (conflict_learn[x]){ printf("Found conflict at learn table @cls(%d)\n", x);}
            }
          }else if ((learn_cls_table[x][2]) == prop_var){
            if((learn_cls_table[x][2] < 0 && (var_truth_table[prop_var] == T || var_truth_table[prop_var] == FT)) 
		        || (learn_cls_table[x][2] > 0 && (var_truth_table[prop_var] == F || var_truth_table[prop_var] == TF))){
              l1 = learn_cls_table[x][0]; 
              l2 = learn_cls_table[x][1];
              conflict_learn[x] = deduction(l1, l2, var_truth_table, x, l_ded_learn);
              cls_ded_learn[x] = x;
              //if (conflict_learn[x]){ printf("Found conflict at learn table @cls(%d)\n", x);}
            }
          }else{
            conflict_learn[x] = 0;
            l_ded_learn[x] = 0;
            cls_ded_learn[x] = 0;
          }
        } 
*/

        state = DEDUCTION;
        break;

      case DEDUCTION: 
        //printf("State = DED; ");
        prev_state = DEDUCTION; 
        conf_ded = 0;  

        for (int x = 0; x < BUF_CLS_SIZE; x++){
          if (conflict[x]){
            conf_ded=1; 
            conf_var = prop_var;
            conf_cls = (var_truth_table[conf_var] == T || var_truth_table[conf_var] == FT)? neg_cls[conf_var][x] : pos_cls[conf_var][x];
            //printf("Found conflict Var(%d) due to cls(%d) with parent_cls(%d)\n", conf_var, conf_cls,parent_cls[conf_var]);
            break; 
          }else if (l_ded[x] != 0){ 
            if (var_truth_table[abs(l_ded[x])] == U){
              buf_ded_end ++;
              buf_ded[buf_ded_end] = l_ded[x]; 
              buf_ded_cls[buf_ded_end] = cls_ded[x]; 
		          int tmp1 = local_clauses[cls_ded[x]][0];
		          int tmp2 = local_clauses[cls_ded[x]][1];
		          int tmp3 = local_clauses[cls_ded[x]][2];
              //Change ded value here
              dec_lvl[abs(l_ded[x])] = curr_lvl;  
              parent_cls[abs(l_ded[x])] = cls_ded[x]; 
              var_truth_table[abs(l_ded[x])] = l_ded[x] > 0 ? T : F;
              int lstparent1 = (tmp1 == l_ded[x]) ? least_parent[abs(tmp2)] : least_parent[abs(tmp1)];
              int lstparent2 = (tmp3 == l_ded[x]) ? least_parent[abs(tmp2)] : least_parent[abs(tmp3)];
              int lvl1 = dec_lvl[lstparent1]; 
              int lvl2 = dec_lvl[lstparent2];
              least_parent[abs(l_ded[x])] = (lvl1 == curr_lvl) ? lstparent2 : (lvl2 == curr_lvl)? lstparent1 : (lvl1 > lvl2 ? lstparent1 : lstparent2); 
	//	printf("lstparent: l1-%d, l2-%d, %d\n", lstparent1, lstparent2, least_parent[abs(l_ded[x])]);
	//	printf("lstparent: %d\n", least_parent[abs(l_ded[x])]);
              //printf("Add ded var(%d) ----- cls : %d(%d) %d(%d) %d(%d) (declvl %d lstlvl %d)\n", l_ded[x],tmp1, dec_lvl[abs(tmp1)], tmp2, dec_lvl[abs(tmp2)], tmp3, dec_lvl[abs(tmp3)], curr_lvl, least_parent[abs(l_ded[x])]);
	      //For debug 
	      if(lvl1 == curr_lvl && lvl2 == curr_lvl){state = EXIT;  printf("Error \n");
              printf("Add ded var(%d) to buf ----- cls : %d(%d) %d(%d) %d(%d) (declvl %d)\n", l_ded[x],tmp1, dec_lvl[abs(tmp1)], tmp2, dec_lvl[abs(tmp2)], tmp3, dec_lvl[abs(tmp3)], curr_lvl);
		printf("lstparent: l1-%d, l2-%d, %d\n", lstparent1, lstparent2, least_parent[abs(l_ded[x])]);
		break;
		}
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
        if (conf_ded){
          //Found conflict 
          state = conf_var == dec_var[curr_lvl] ? BACKTRACK_DEC : ANALYSIS;
          buf_ded_curr = -1; 
          buf_ded_end = -1;
          break; 
        }

        for (int x = 0; x < learn_cls_nxtidx; x++){
          if (conflict_learn[x]){
            conf_ded=1; 
            conf_var = prop_var;
            conf_cls = x + NUM_CLAUSES;
            //printf("Found learn conflict Var(%d) due to learnt cls(%d) with parent_cls(%d)\n", conf_var, conf_cls,parent_cls[conf_var]);
            break; 
          }else if (l_ded_learn[x] != 0){ 
            if (var_truth_table[abs(l_ded_learn[x])] == U){
              buf_ded_end ++;
              buf_ded[buf_ded_end] = l_ded_learn[x]; 
              buf_ded_cls[buf_ded_end] = cls_ded_learn[x]; 
		          int tmp1 = learn_cls_table[cls_ded_learn[x]][0];
		          int tmp2 = learn_cls_table[cls_ded_learn[x]][1];
		          int tmp3 = learn_cls_table[cls_ded_learn[x]][2];
             printf("Add learned ded var(%d) to buf ----- cls : %d(%d) %d(%d) %d(%d) (declvl %d)\n", l_ded_learn[x],tmp1, dec_lvl[abs(tmp1)], tmp2, dec_lvl[abs(tmp2)], tmp3, dec_lvl[abs(tmp3)], curr_lvl);
              //Change ded value here
              dec_lvl[abs(l_ded_learn[x])] = curr_lvl;  
              parent_cls[abs(l_ded_learn[x])] = cls_ded_learn[x] + NUM_CLAUSES; 
              var_truth_table[abs(l_ded_learn[x])] = l_ded_learn[x] > 0 ? T : F;
              //printf("Change VTT Var(%d) to %d\n", abs(l_ded_learn[x]), var_truth_table[abs(l_ded_learn[x])]);
              int lstparent1 = abs(cls_ded_learn[x][0]) == abs(l_ded_learn[x]) ? least_back_parent[cls_ded_learn[x][1]] : least_back_parent[cls_ded_learn[x][0]];
              int lstparent2 = abs(cls_ded_learn[x][2]) == abs(l_ded_learn[x]) ? least_back_parent[cls_ded_learn[x][1]] : least_back_parent[cls_ded_learn[x][2]];
              int lvl1 = dec_lvl[lstparent1]; 
              int lvl2 = dec_lvl[lstparent2];
              least_back_parent[abs(l_ded_learn[x])] = lvl1 > lvl2 ? lstparent1 : lstparent2;
            }else if ((var_truth_table[abs(l_ded_learn[x])] == T && l_ded_learn[x] < 0) || (var_truth_table[abs(l_ded_learn[x])] == F && l_ded_learn[x] > 0) ){
                //Check whether conflict in same level deduction 
                conf_ded=1; 
                conf_var = abs(l_ded_learn[x]);
                conf_cls = cls_ded_learn[x] + NUM_CLAUSES;
                //printf("Found learn conflict Var(%d) due to cls(%d) with parentcls(%d)\n", conf_var, conf_cls, parent_cls[abs(l_ded_learn[x])]);
            }else{
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

        if (parent_cls[conf_var] < NUM_CLAUSES){
          conf_parents[0] = abs(local_clauses[parent_cls[conf_var]][0]) == conf_var ? 
                          local_clauses[parent_cls[conf_var]][1] : local_clauses[parent_cls[conf_var]][0]; 
          conf_parents[1] = abs(local_clauses[parent_cls[conf_var]][2]) == conf_var ? 
                          local_clauses[parent_cls[conf_var]][1] : local_clauses[parent_cls[conf_var]][2]; 
        }
        /*else{
          int cls_no = parent_cls[conf_var] - NUM_CLAUSES;
          conf_parents[0] = abs(learn_cls_table[cls_no][0]) == conf_var ? 
                          learn_cls_table[cls_no][1] :  learn_cls_table[cls_no][0]; 
          conf_parents[1] = abs(learn_cls_table[cls_no][2]) == conf_var ? 
                          learn_cls_table[cls_no][1] :  learn_cls_table[cls_no][2]; 
        }*/ 

        if (conf_cls < NUM_CLAUSES){
          conf_parents[2] = abs(local_clauses[conf_cls][0]) == conf_var ? 
                          local_clauses[conf_cls][1] : local_clauses[conf_cls][0]; 
          conf_parents[3] = abs(local_clauses[conf_cls][2]) == conf_var ? 
                          local_clauses[conf_cls][1] : local_clauses[conf_cls][2]; 
        }
        /*else{
          int cls_no = conf_cls - NUM_CLAUSES;
          conf_parents[2] = abs(learn_cls_table[cls_no][0]) == conf_var ? 
                          learn_cls_table[cls_no][1] :  learn_cls_table[cls_no][0]; 
          conf_parents[3] = abs(learn_cls_table[cls_no][2]) == conf_var ? 
                          learn_cls_table[cls_no][1] :  learn_cls_table[cls_no][2]; 
        }*/

        //Sort based on parent_lvl
        #pragma ACCEL parallel flatten
        for (int i = 0; i < 4; i++){
          //parent_lvl[i] = dec_lvl[abs(conf_parents[i])];
          //conf_lst_lvl[i] = dec_lvl[least_back_parent[abs(conf_parents[i])]]; 
          conf_parent_tmp[i] = conf_parents[i]; 
          parent_lvl_tmp[i] = dec_lvl[abs(conf_parents[i])];
          lst_tmp[i] = dec_lvl[least_parent[abs(conf_parents[i])]]; 
        }
        //printf("Original Parents var(lvl) %d(%d) %d(%d) %d(%d) %d(%d) \n", conf_parents[0], parent_lvl_tmp[0], conf_parents[1], parent_lvl_tmp[1], 
        //        conf_parents[2], parent_lvl_tmp[2], conf_parents[3], parent_lvl_tmp[3]);

        int sorted_idx[4]; 
        sort4_idx(parent_lvl_tmp, sorted_idx); 
        #pragma ACCEL parallel flatten
        for (int i = 0; i < 4; i++){
          conf_parents[i] = conf_parent_tmp[sorted_idx[i]];
          parent_lvl[i] = parent_lvl_tmp[sorted_idx[i]]; 
          conf_lst_lvl[i] = lst_tmp[sorted_idx[i]]; 
        }

	/*
        printf("Analysis Conflict var %d with dec_lvl(%d), conf_cls(%d) parent_cls(%d)\n", conf_var,dec_lvl[conf_var], conf_cls, parent_cls[conf_var]);
        printf("Parents var(lvl) %d(%d) %d(%d) %d(%d) %d(%d) \n", conf_parents[0], parent_lvl[0], conf_parents[1], parent_lvl[1], 
                conf_parents[2], parent_lvl[2], conf_parents[3], parent_lvl[3]);
        printf("Lst back var(lvl) %d(%d) %d(%d) %d(%d) %d(%d)\n ", least_parent[abs(conf_parents[0])], conf_lst_lvl[0],
		 least_parent[abs(conf_parents[1])], conf_lst_lvl[1],
		 least_parent[abs(conf_parents[2])], conf_lst_lvl[2],
		 least_parent[abs(conf_parents[3])], conf_lst_lvl[3]);
*/
        /*
        for (int i = 0; i < 4; i++){
          for (int j = 0; j < 4; j++){
            if (i < j && (abs(conf_parents[i]) == abs(conf_parents[j]))){
              conf_parents[j] = 0; 
              parent_lvl[j] = 0;
            }
          }
        }

        // Check whether there is the same variables in 4 parents 
        if (conf_parents[1] == 0 && (parent_lvl[2] < curr_lvl)){
          issameparent = 1;
          poss_learn_cls[0] =  conf_parents[0]; 
          poss_learn_cls[1] =  conf_parents[2]; 
          poss_learn_cls[2] =  conf_parents[3]; 
          lit_learned = ((parent_lvl[0] >= parent_lvl[2]) && (parent_lvl[0] >= parent_lvl[3]))? conf_parents[0] : 
                          (parent_lvl[2] >= parent_lvl[3]) ? conf_parents[2]: conf_parents[3] ;

          //printf("lit learned 1 is %d \n", lit_learned);
        }else if (conf_parents[2] == 0 && (parent_lvl[2] < curr_lvl)){
          issameparent = 1;
          poss_learn_cls[0] =  conf_parents[0]; 
          poss_learn_cls[1] =  conf_parents[1]; 
          poss_learn_cls[2] =  conf_parents[3]; 
          lit_learned = ((parent_lvl[0] >= parent_lvl[1]) && (parent_lvl[0] >= parent_lvl[3]))? conf_parents[0] : 
                         (parent_lvl[1] >= parent_lvl[3]) ? conf_parents[1]: conf_parents[3] ;
          //printf("lit learned 2 is %d \n", lit_learned);
        }else if (conf_parents[3] == 0 && (parent_lvl[2] < curr_lvl) ){
          issameparent = 1;
          poss_learn_cls[0] =  conf_parents[0]; 
          poss_learn_cls[1] =  conf_parents[1]; 
          poss_learn_cls[2] =  conf_parents[2]; 
          lit_learned = ((parent_lvl[0] >= parent_lvl[1]) && (parent_lvl[0] >= parent_lvl[2]))? conf_parents[0] : 
                         (parent_lvl[1] >= parent_lvl[2]) ? conf_parents[1]: conf_parents[2];
          //printf("lit learned is 3 %d \n", lit_learned);
        }else{
          issameparent = 0; 
        }

        if (learn_cls_nxtidx >= LEARN_TABLE_SIZE){
          printf("learn table is not enough\n") ;
          islearned = 0;
          state = FAILED; 
        }else if ((parent_lvl[2] < curr_lvl) && issameparent){
          islearned = 1; 
        }

        isduplicate = 0;
        if (islearned){
          #pragma ACCEL parallel reduction=isduplicate
          for (int x = 0; x < learn_cls_nxtidx; x++){
            bool tmp1 = poss_learn_cls[0] == learn_cls_table[x][0] || poss_learn_cls[0] == learn_cls_table[x][1] || poss_learn_cls[0] == learn_cls_table[x][2];
            bool tmp2 = poss_learn_cls[1] == learn_cls_table[x][0] || poss_learn_cls[1] == learn_cls_table[x][1] || poss_learn_cls[1] == learn_cls_table[x][2];
            bool tmp3 = poss_learn_cls[2] == learn_cls_table[x][0] || poss_learn_cls[2] == learn_cls_table[x][1] || poss_learn_cls[2] == learn_cls_table[x][2];
            bool tmp = (tmp1&&tmp2) || (tmp2&&tmp3) || (tmp1&&tmp3);
            isduplicate |= tmp; 
          }
        }

        if (isduplicate){
          islearned = 0;
          //printf("Found duplicate cls");
        }

        //For debug
        if (parent_cls[conf_var] < 0){
          //Check whether it is a decision variable
          printf("Error: find dec in analysis state\n");
          state = EXIT; 
          break; 
        }

        if (islearned){
          // Add learned clause to table
          //printf("Analysis Conflict var %d with dec_lvl(%d), conf_cls(%d) parent_cls(%d)\n", conf_var,dec_lvl[conf_var], conf_cls, parent_cls[conf_var]);
          printf("Add learn cls(%d) %d %d %d\n", learn_cls_nxtidx, poss_learn_cls[0], poss_learn_cls[1], poss_learn_cls[2]);
          learn_cls_table[learn_cls_nxtidx][0] =  poss_learn_cls[0]; 
          learn_cls_table[learn_cls_nxtidx][1] =  poss_learn_cls[1]; 
          learn_cls_table[learn_cls_nxtidx][2] =  poss_learn_cls[2]; 
          //For debug
          if (poss_learn_cls[0] == 0 || poss_learn_cls[1] == 0 || poss_learn_cls[2] == 0){
		        printf("Learned var is 0 \n");
		        state = FAILED; break;}

          learn_cls_nxtidx ++; 

          back_lvl = parent_lvl[2];
          state = BACKTRACK;
        }else{
          back_lvl = conf_lst_lvl[3];
          if (back_lvl == curr_lvl){
            state = EXIT;
            break; printf("Error, get back lvl to current lvl\n");
          } 
          state = BACKTRACK_DEC; 

        }*/

	sort4(conf_lst_lvl);
	curr_lst = (conf_lst_lvl[3] != curr_lvl) ? conf_lst_lvl[3]: (conf_lst_lvl[2] != curr_lvl) ? conf_lst_lvl[2] : conf_lst_lvl[1]; 
        if (var_truth_table[dec_var[curr_lvl]] == TF || var_truth_table[dec_var[curr_lvl]] == FT){
	  state = BACKTRACK_DEC;
          back_lvl = dec_lst_lvl[curr_lvl] > curr_lst ? dec_lst_lvl[curr_lvl] : curr_lst; 
          //For debug
          if (curr_lst == curr_lvl){printf("Error: lst parent is vurrent lvl\n"); state = EXIT;}
        }else{
	  state = BACKTRACK_DEC;
	  int curr_var = dec_var[curr_lvl];
          dec_lst_lvl[curr_lvl] = curr_lst;
	  back_lvl = curr_lvl;
          //For debug
          if (curr_lst == curr_lvl){printf("Error: lst parent is vurrent lvl\n"); state = EXIT;}
        }

        break; 

      case BACKTRACK_DEC: 
        //printf("State = BACKTRACK_DEC; ");
        prev_state = BACKTRACK_DEC;

        if (prev_state == DEDUCTION){
          back_lvl = curr_lvl; 
        }

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

	if (back_lvl < 10){
        printf("Back to lvl %d - Var %d\n", back_lvl, dec_var[back_lvl]);
	}
        prev_assigned_value = var_truth_table[dec_var[back_lvl]]; 
        //Undo all variable assignment after back_lvl
        #pragma ACCEL parallel flatten
        for (int i = 0; i < NUM_VARS; i ++){
          if (dec_lvl[i] >= back_lvl){
            //if (i == 25){printf("Get here with dec_lvl%d\n", dec_lvl[25]);}
            var_truth_table[i] = U;
            dec_lvl[i] = -1; 
            parent_cls[i] = -1;
            least_parent[i] = -1;
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
/*
      case BACKTRACK:
        //printf("State = BACKTRACK; ");
        prev_state = BACKTRACK;

        printf("Back learn to lvl %d\n", back_lvl);

        //printf("Conflict var %d with dec_lvl(%d), conf_cls(%d) parent_cls(%d)\n", conf_var,dec_lvl[conf_var], conf_cls, parent_cls[conf_var]);
        #pragma ACCEL parallel flatten
        for (int i = 0; i < NUM_VARS; i ++){
          if (dec_lvl[i] > back_lvl){
            var_truth_table[i] = U;
            dec_lvl[i] = -1; 
            parent_cls[i] = -1;
          }
        }

        #pragma ACCEL parallel flatten
        for (int i = 0; i < BUF_DEC_LVL; i++){
          if (i > back_lvl){
            dec_var[i] = 0; 
          }
        }

        var_truth_table[abs(lit_learned)] = lit_learned > 0 ? T : F; 
        dec_lvl[abs(lit_learned)] = back_lvl;
        parent_cls[abs(lit_learned)] = learn_cls_nxtidx + NUM_CLAUSES - 1;
        least_back_parent[abs(lit_learned)] = -1; //TO fix
        //printf("Change VTT Var(%d) to %d\n", abs(lit_learned), var_truth_table[abs(lit_learned)]);

        new_var_idx = dec_var[back_lvl]; 
        curr_lvl = back_lvl; 

        state = PROP; 
        break; 
*/
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
