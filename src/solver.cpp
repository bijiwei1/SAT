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
  bool isduplicate; 
  int poss_learn_cls[3]; 
  
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

  bool issameparent; 
  bool islearned; 
  int lit_learned; 

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
          curr_lvl ++; 
          printf("Decide Var(%d) - at lvl %d\n", new_var_idx, curr_lvl);

          if (pos_cls[new_var_idx][5] != -1){
            var_truth_table[new_var_idx] = T;
          }else {
            var_truth_table[new_var_idx] = F;
          }

          dec_lvl[new_var_idx] = curr_lvl; 
	  if (new_var_idx == 25){   printf("Get here4\n");}
          dec_var[curr_lvl] = new_var_idx; 
        }

        prev_state = DECISION; 
        break;

      case PROP:
//        printf("State = PROP; ");
        if (prev_state == DECISION){
          prop_var = new_var_idx;
          printf("Prop dec Var(%d): %d\n", prop_var, var_truth_table[prop_var]);
        }else if (prev_state == DEDUCTION){
          prop_var = abs(buf_ded[buf_ded_curr]);
          printf("Prop ded Var(%d): %d\n", prop_var, var_truth_table[prop_var]);
        }else if (prev_state == BACKTRACK){
          prop_var = islearned ? abs(lit_learned) : new_var_idx;
          printf("Prop dec_back Var(%d): %d\n", prop_var, var_truth_table[prop_var]);
        }

        /****************** pos_buf & neg_buf *****************/

        //#pragma ACCEL parallel flatten
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
        #pragma ACCEL parallel flatten 
        for (int x = 0; x < learn_cls_nxtidx; x++){
          int l1, l2; 
          if (abs(learn_cls_table[x][0]) == prop_var){
            if((learn_cls_table[x][0] < 0 && (var_truth_table[prop_var] == T || var_truth_table[prop_var] == FT)) 
		          || (learn_cls_table[x][0] > 0 && (var_truth_table[prop_var] == F || var_truth_table[prop_var] == TF))){
              l1 = learn_cls_table[x][1]; 
              l2 = learn_cls_table[x][2];
              conflict_learn[x] = deduction(l1, l2, var_truth_table, x, l_ded_learn);
              cls_ded_learn[x] = x + NUM_CLAUSES;
              //if (conflict_learn[x]){ printf("Found conflict at learn table @cls(%d)\n", x);}
            }
          }else if (abs(learn_cls_table[x][1]) == prop_var){
            if((learn_cls_table[x][1] < 0 && (var_truth_table[prop_var] == T || var_truth_table[prop_var] == FT)) 
		          || (learn_cls_table[x][1] > 0 && (var_truth_table[prop_var] == F || var_truth_table[prop_var] == TF))){
              l1 = learn_cls_table[x][0]; 
              l2 = learn_cls_table[x][2];
              conflict_learn[x] = deduction(l1, l2, var_truth_table, x, l_ded_learn);
              cls_ded_learn[x] = x + NUM_CLAUSES;
              //if (conflict_learn[x]){ printf("Found conflict at learn table @cls(%d)\n", x);}
            }
          }else if ((learn_cls_table[x][2]) == prop_var){
            if((learn_cls_table[x][2] < 0 && (var_truth_table[prop_var] == T || var_truth_table[prop_var] == FT)) 
		        || (learn_cls_table[x][2] > 0 && (var_truth_table[prop_var] == F || var_truth_table[prop_var] == TF))){
              l1 = learn_cls_table[x][0]; 
              l2 = learn_cls_table[x][1];
              conflict_learn[x] = deduction(l1, l2, var_truth_table, x, l_ded_learn);
              cls_ded_learn[x] = x + NUM_CLAUSES;
              //if (conflict_learn[x]){ printf("Found conflict at learn table @cls(%d)\n", x);}
            }
          }else{
            conflict_learn[x] = 0;
            l_ded_learn[x] = 0;
            cls_ded_learn[x] = 0;
          }
        } 

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
              printf("Add ded var(%d) to buf ----- cls : %d %d %d (declvl %d)\n", l_ded[x], local_clauses[cls_ded[x]][0], local_clauses[cls_ded[x]][1], local_clauses[cls_ded[x]][2], curr_lvl);
              //Change ded value here
              dec_lvl[abs(l_ded[x])] = curr_lvl;  
              if (abs(l_ded[x]) == 25){   printf("Get here5\n");}
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

	printf("Check point DED2 dec lvl %d\n", dec_lvl[25]);

        for (int x = 0; x < learn_cls_nxtidx; x++){
          if (conflict_learn[x]){
            conf_ded=1; 
            conf_var = prop_var;
            conf_cls = x;
            //printf("Found learn conflict Var(%d) due to learnt cls(%d) with parent_cls(%d)\n", conf_var, conf_cls,parent_cls[conf_var]);
            break; 
          }else if (l_ded_learn[x] != 0){ 
            if (var_truth_table[abs(l_ded_learn[x])] == U){
              buf_ded_end ++;
              buf_ded[buf_ded_end] = l_ded_learn[x]; 
              buf_ded_cls[buf_ded_end] = cls_ded_learn[x]; 
              printf("Add ded var(%d) to buf ----- cls : %d %d %d (declvl %d)\n", l_ded_learn[x], learn_cls_table[cls_ded_learn[x]][0], learn_cls_table[cls_ded_learn[x]][1], learn_cls_table[cls_ded_learn[x]][2], curr_lvl);
              //Change ded value here
              dec_lvl[abs(l_ded_learn[x])] = curr_lvl;  
              if (abs(l_ded_learn[x]) == 25){   printf("Get here6\n");}
              parent_cls[abs(l_ded_learn[x])] = cls_ded_learn[x]; 
              var_truth_table[abs(l_ded_learn[x])] = l_ded[x] > 0 ? T : F;
              var_truth_table[abs(l_ded_learn[x])] = l_ded[x] > 0 ? T : F;
              //printf("Change VTT Var(%d) to %d\n", abs(l_ded_learn[x]), var_truth_table[abs(l_ded_learn[x])]);
            }else if ((var_truth_table[abs(l_ded_learn[x])] == T && l_ded_learn[x] < 0) || (var_truth_table[abs(l_ded_learn[x])] == F && l_ded_learn[x] > 0) ){
                //Check whether conflict in same level deduction 
                conf_ded=1; 
                conf_var = abs(l_ded_learn[x]);
                conf_cls = cls_ded_learn[x];
                //printf("Found learn conflict Var(%d) due to cls(%d) with parentcls(%d)\n", conf_var, conf_cls, parent_cls[abs(l_ded_learn[x])]);
            }else{
                //printf("Duplicate ded var(%d) ----- cls : %d %d %d\n", l_ded[x], local_clauses[cls_ded[x]][0], local_clauses[cls_ded[x]][1], local_clauses[cls_ded[x]][2]);
            }
          }
        }

        //printf("curr ptr: %d, end ptr: %d\n", buf_ded_curr, buf_ded_end);
        if (buf_ded_end > BUF_DED_SIZE){
            //printf("Buf size is too short\n");
            state = EXIT;
            break; 
        }

        if (conf_ded){
          //Found conflict 
          state = conf_var == dec_var[curr_lvl] ? BACKTRACK_DEC : ANALYSIS;
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
        printf("State = ANALYSIS; ");
        printf("Analysis Conflict var %d with dec_lvl(%d), conf_cls(%d) parent_cls(%d)\n", conf_var,dec_lvl[conf_var], conf_cls, parent_cls[conf_var]);
        
        if (parent_cls[conf_var] < NUM_CLAUSES){
          conf_parents[0] = abs(local_clauses[parent_cls[conf_var]][0]) == conf_var ? 
                          local_clauses[parent_cls[conf_var]][1] : local_clauses[parent_cls[conf_var]][0]; 
          conf_parents[1] = abs(local_clauses[parent_cls[conf_var]][2]) == conf_var ? 
                          local_clauses[parent_cls[conf_var]][1] : local_clauses[parent_cls[conf_var]][2]; 
        }else{
          int cls_no = parent_cls[conf_var] - NUM_CLAUSES;
          conf_parents[0] = abs(learn_cls_table[cls_no][0]) == conf_var ? 
                          learn_cls_table[cls_no][1] :  learn_cls_table[cls_no][0]; 
          conf_parents[1] = abs(learn_cls_table[cls_no][2]) == conf_var ? 
                          learn_cls_table[cls_no][1] :  learn_cls_table[cls_no][2]; 
        }

        if (conf_cls < NUM_CLAUSES){
          conf_parents[2] = abs(local_clauses[conf_cls][0]) == conf_var ? 
                          local_clauses[conf_cls][1] : local_clauses[conf_cls][0]; 
          conf_parents[3] = abs(local_clauses[conf_cls][2]) == conf_var ? 
                          local_clauses[conf_cls][1] : local_clauses[conf_cls][2]; 
        }else{
          int cls_no = conf_cls - NUM_CLAUSES;
          conf_parents[2] = abs(learn_cls_table[cls_no][0]) == conf_var ? 
                          learn_cls_table[cls_no][1] :  learn_cls_table[cls_no][0]; 
          conf_parents[3] = abs(learn_cls_table[cls_no][2]) == conf_var ? 
                          learn_cls_table[cls_no][1] :  learn_cls_table[cls_no][2]; 
        }

        for (int i = 0; i < 4; i++){
          parent_lvl[i] = dec_lvl[abs(conf_parents[i])];
        }

        printf("Parents var(lvl) %d(%d) %d(%d) %d(%d) %d(%d) \n", conf_parents[0], parent_lvl[0], conf_parents[1], parent_lvl[1], 
                conf_parents[2], parent_lvl[2], conf_parents[3], parent_lvl[3]);
        printf("Current lvl %d\n", curr_lvl);

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
          z//printf("lit learned is 3 %d \n", lit_learned);
        }else{
          issameparent = 0; 
        }

        //Must after previous if-else statement
        sort4(parent_lvl); 

        if (learn_cls_nxtidx >= LEARN_TABLE_SIZE){
          printf("learn table is not enough\n") ;
          islearned = 0;
        }else if (parent_lvl[2] < curr_lvl){
          islearned = 1; 
        }

        isduplicate = 0;
        if (islearned){
          #pragma ACCEL parallel reduction=isduplicate
          for (int x = 0; x < learn_cls_nxtidx; x++){
            int tmp= (poss_learn_cls[0] == learn_cls_table[x][0] || poss_learn_cls[0] == learn_cls_table[x][1] || poss_learn_cls[0] == learn_cls_table[x][2])
                && (poss_learn_cls[1] == learn_cls_table[x][0] || poss_learn_cls[1] == learn_cls_table[x][1] || poss_learn_cls[1] == learn_cls_table[x][2])
                && (poss_learn_cls[2] == learn_cls_table[x][0] || poss_learn_cls[2] == learn_cls_table[x][1] || poss_learn_cls[2] == learn_cls_table[x][2]);
                isduplicate |= tmp; 
          }
        }

        if (isduplicate){
          islearned = 0;
          printf("Found duplicate cls");
        }

        //For debug
        if (parent_cls[conf_var] <= 0){
          //Check whether it is a decision variable
          printf("Error: find dec in analysis state\n");
          state = EXIT; 
          break; 
        }

        if (islearned){
          // Add learned clause to table
          printf("Add learn cls(%d) %d %d %d\n", learn_cls_nxtidx, poss_learn_cls[0], poss_learn_cls[1], poss_learn_cls[2]);
          learn_cls_table[learn_cls_nxtidx][0] =  poss_learn_cls[0]; 
          learn_cls_table[learn_cls_nxtidx][1] =  poss_learn_cls[1]; 
          learn_cls_table[learn_cls_nxtidx][2] =  poss_learn_cls[2]; 
          learn_cls_nxtidx ++; 

          back_lvl = parent_lvl[2];
          state = BACKTRACK;
        }else{
          state = BACKTRACK2; 
        }

        state = BACKTRACK; 
        break; 

      case BACKTRACK_DEC: 
        printf("State = BACKTRACK2; ");
        back_lvl = curr_lvl; 
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
        }else{
          printf("Back to lvl %d\n", back_lvl);
        }

        prev_assigned_value = var_truth_table[dec_var[back_lvl]]; 
        //Undo all variable assignment after back_lvl
        #pragma ACCEL parallel flatten
        for (int i = 0; i < NUM_VARS; i ++){
          if (dec_lvl[i] >= back_lvl){
            if (i == 25){printf("Get here with dec_lvl%d\n", dec_lvl[25]);}
            var_truth_table[i] = U;
            dec_lvl[i] = -1; 
            parent_cls[i] = -1;
          }
        }

        var_truth_table[dec_var[back_lvl]] = (prev_assigned_value == T) ? TF : FT;
        dec_lvl[dec_var[back_lvl]] = back_lvl;
        //printf("Change VTT Var(%d) to %d\n", dec_var[back_lvl], var_truth_table[dec_var[back_lvl]]);

        #pragma ACCEL parallel flatten
        for (int i = 0; i < BUF_DEC_LVL; i++){
          if (i > back_lvl){
            dec_var[i] = 0; 
          }
        }

        printf("Check point dec lvl %d\n", dec_lvl[25]);

        state = PROP;
        break;

      case BACKTRACK:
        printf("State = BACKTRACK; ");
        prev_state = BACKTRACK;

        printf("Back to lvl %d\n", back_lvl);

        //printf("Conflict var %d with dec_lvl(%d), conf_cls(%d) parent_cls(%d)\n", conf_var,dec_lvl[conf_var], conf_cls, parent_cls[conf_var]);
        printf("Check point B1 dec lvl %d\n", dec_lvl[25]);

        var_truth_table[abs(lit_learned)] = lit_learned > 0 ? T : F; 
        dec_lvl[abs(lit_learned)] = back_lvl;
        parent_cls[abs(lit_learned)] = learn_cls_nxtidx + NUM_CLAUSES - 1;
        printf("Change VTT Var(%d) to %d\n", abs(lit_learned), var_truth_table[abs(lit_learned)]);

        if (abs(lit_learned)== 25){printf("Get here 2 with dec_lvl%d\n", dec_lvl[25]);}

        new_var_idx = dec_var[back_lvl]; 
        curr_lvl = back_lvl; 

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
