#include <string.h>
#include <math.h>
#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
//#include <string> 
//using namespace std; 

#define NUM_CLAUSES 1024
#define NUM_VARS 251

#define BUF_CLS_SIZE 10
#define extra_buf_size 30
#define BUF_DED_SIZE 50

#define TF 4
#define FT 3
#define F 2
#define T 1
#define U 0

#define SOLVED 0
#define DECISION 1
#define PROP 2
#define DEDUCTION 3
#define BACKTRACK 4 
#define FAILED 5
#define EXIT 6
#define BACKTRACK2 7

#define EMPTY -1

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
  char var_truth_table[NUM_VARS] = {U}; 
  // T, F, U (Undef), f(assigned to T first), t(assigned to F first)
  int dec_lvl[NUM_VARS] = {-1};
  int dec_var[100]= {0}; // Variable idx at each decision lvl, we assume at most 100 decision level
  int parent_cls[NUM_VARS] = {0};
  int buf_ded[BUF_DED_SIZE] = {0};
  int buf_ded_cls[BUF_DED_SIZE] = {-1}; 


  int l_ded[BUF_CLS_SIZE];
  int cls_ded[BUF_CLS_SIZE]; 
  
  int pos_cls[NUM_VARS][BUF_CLS_SIZE] = {-1}; 
  int neg_cls[NUM_VARS][BUF_CLS_SIZE] = {-1}; 
  int extra_cls[extra_buf_size] = {0}; 
  int extra_lit[extra_buf_size] = {0}; 


  //Idx and ptr 
  int new_var_idx = 1;
  int curr_lvl = -1; 
  int buf_ded_curr = -1;
  int buf_ded_end = -1;
  //Other variables
  int state = DECISION; 
  int prev_state = DECISION; 
  int num_extra[1] = {0};
  int conf_var; 
  int conf_cls; 
  int parent1, parent2, parent3, parent4;
  int parent_lvl[4]; 
  int back_lvl = 0; 

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
  printf("Extra cls buffer size : %d = %d\n", num_extra[0], extra_buf_size);
  for (int x = 0; x < num_extra[0]; x++){
    printf("Extra var(%d) at cls(%d) \n", extra_lit[x], extra_cls[x]);
  }
*/
  
  for (int x = 0; x< NUM_VARS; x++){
     var_truth_table[x] = U; 
  }
/********************************* FSM **********************************/
  int test = 0; 
  while (state != EXIT){
    if (test > 4){
      break;
    }
    switch(state){
      case DECISION: 
        printf("State = DECISION; ");

        while (new_var_idx < NUM_VARS){
          if (var_truth_table[new_var_idx] != U){
            printf("Skip var %d(Value - %d)\n", new_var_idx, var_truth_table[new_var_idx]); 
            new_var_idx ++; 
          }else{
            break; 
          }
        } 
        
        if (new_var_idx == NUM_VARS){
          state = SOLVED; 
        }else {
          state = PROP;
          printf("Decide Var(%d)\n", new_var_idx);
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
        int prop_var; 
        if (prev_state == DECISION || prev_state == BACKTRACK){
          prop_var = new_var_idx;
          printf("Prop dec Var(%d): %d\n", prop_var, var_truth_table[prop_var]);
        }else if (prev_state == DEDUCTION){
          prop_var = abs(buf_ded[buf_ded_curr]);
          printf("Prop ded Var(%d): %d\n", prop_var, var_truth_table[prop_var]);
        }

        /****************** pos_buf & neg_buf *****************/
        bool conflict[BUF_CLS_SIZE]; 
        bool tot_conflict; 
        #pragma ACCEL parallel flatten 
        for (int x = 0; x < BUF_CLS_SIZE; x++){
          int l1, l2; 
          if(var_truth_table[prop_var] == T && neg_cls[prop_var][x] != EMPTY){
            l1 = (local_clauses[neg_cls[prop_var][x]][0] == -prop_var)? 
              local_clauses[neg_cls[prop_var][x]][1] : local_clauses[neg_cls[prop_var][x]][0];
            l2 = (local_clauses[neg_cls[prop_var][x]][2] == -prop_var)? 
              local_clauses[neg_cls[prop_var][x]][1] : local_clauses[neg_cls[prop_var][x]][2];
            conflict[x] = deduction(l1, l2, var_truth_table, x, l_ded);
            cls_ded[x] = neg_cls[prop_var][x];
            if (conflict[x]){
	           printf("Found conflict @cls(%d)\n", neg_cls[prop_var][x]);
		        }
          }else if (var_truth_table[prop_var] == F && pos_cls[prop_var][x] != EMPTY){
            l1 = (local_clauses[pos_cls[prop_var][x]][0] == prop_var)? 
              local_clauses[pos_cls[prop_var][x]][1] : local_clauses[pos_cls[prop_var][x]][0];
            l2 = (local_clauses[pos_cls[prop_var][x]][2] == prop_var)? 
              local_clauses[pos_cls[prop_var][x]][1] : local_clauses[pos_cls[prop_var][x]][2];
            conflict[x] = deduction(l1, l2, var_truth_table, x, l_ded);
            cls_ded[x] = pos_cls[prop_var][x];
            if (conflict[x]){
	           printf("Found conflict @cls(%d)\n", pos_cls[prop_var][x]);
            }
          }
        }

        #pragma ACCEL parallel flatten reduction=tot_conflict
        for (int x = 0; x < BUF_CLS_SIZE; x++){
          tot_conflict |= conflict[x]; 
        }
        
        state = DEDUCTION; 
        break; 

      case DEDUCTION: 
        printf("State = DED; ");
        if (tot_conflict){
          state = (prev_state == DECISION) ? BACKTRACK2: BACKTRACK;
          break; // jump out of this case 
        }

        prev_state = DEDUCTION; 
        bool conf_ded = 0;  
        for (int x = 0; x < BUF_CLS_SIZE; x++){
          if (l_ded[x] != 0){ 
            buf_ded_end ++;
            buf_ded[buf_ded_end] = l_ded[x]; 
            buf_ded_cls[buf_ded_end] = cls_ded[x]; 
            printf("Add ded var(%d) to buf ----- cls : %d %d %d\n", l_ded[x], local_clauses[cls_ded[x]][0], local_clauses[cls_ded[x]][1], local_clauses[cls_ded[x]][2]);
            //Change ded value here
            if (var_truth_table[abs(l_ded[x])] == U){
              dec_lvl[abs(l_ded[x])] = curr_lvl;  
              parent_cls[abs(l_ded[x])] = cls_ded[x]; 
              var_truth_table[abs(l_ded[x])] = l_ded[x] > 0 ? T : F;
              printf("Change VTT Var(%d) to %d\n", abs(l_ded[x]), var_truth_table[abs(l_ded[x])]);
            }else if ((var_truth_table[abs(l_ded[x])] == T && l_ded[x] < 0) || (var_truth_table[abs(l_ded[x])] == F && l_ded[x] < 0) ){
                //Check whether conflict in same level deduction 
                conf_ded=1; 
                conf_var = abs(l_ded[x]);
                conf_cls = cls_ded[x];
            }
          }
        }

        printf("curr ptr: %d, end ptr: %d\n", buf_ded_curr, buf_ded_end);

        if (buf_ded_end > BUF_DED_SIZE){
            printf("Buf size is too short\n");
            state = EXIT;
            break; 
        }

        if (buf_ded_end == buf_ded_curr){
          //No deducted variable in buf_ded
          state = DECISION;
          buf_ded_curr = -1;
          buf_ded_end = -1; 

        }else{
          //Move to next variable in buf_ded
          buf_ded_curr ++;  
          int prop_lit = buf_ded[buf_ded_curr]; 

          //Check whether conflict in same level deduction 
          //bool conf_ded = prop_lit > 0 ? (var_truth_table[prop_lit] == F) : 
          //                            (var_truth_table[-prop_lit] == T); 

          if (conf_ded){
            state = BACKTRACK; 
            //conf_var = abs(prop_lit);
            //conf_cls = buf_ded_cls[buf_ded_curr];
            buf_ded_curr = -1; 
            buf_ded_end = -1;
            //printf("Found conflict %d\n", conf_var);
          }else{
            state = PROP;
            //dec_lvl[abs(prop_lit)] = curr_lvl; 
            //parent_cls[abs(prop_lit)] = buf_ded_cls[buf_ded_curr]; 
            //var_truth_table[abs(prop_lit)] = prop_lit > 0 ? T : F;
            //printf("Change VTT Var(%d) to %d\n", abs(prop_lit), var_truth_table[abs(prop_lit)]);
          } 
        }

        break; 


      case BACKTRACK2: 
        printf("State = BACKTRACK2; ");
        var_truth_table[new_var_idx] = (var_truth_table[new_var_idx] == T) ? TF : FT; 
        prev_state = DECISION; 
        break;

      case BACKTRACK:
        printf("State = BACKTRACK; ");
        prev_state = BACKTRACK;
        printf("Conflict var %d with dec_lvl(%d), cls_no(%d)  \n", conf_var,dec_lvl[conf_var], conf_cls);
	//int l1 = local_clauses[parent_cls[conf_var]][0];
	//int l2 = local_clauses[parent_cls[conf_var]][1];
	//int l3 = local_clauses[parent_cls[conf_var]][2];
        parent1 = abs(local_clauses[parent_cls[conf_var]][0]) == conf_var ? abs(local_clauses[parent_cls[conf_var]][1]) : abs(local_clauses[parent_cls[conf_var]][0]); 
        parent2 = abs(local_clauses[parent_cls[conf_var]][2]) == conf_var ? abs(local_clauses[parent_cls[conf_var]][2]) : abs(local_clauses[parent_cls[conf_var]][1]); 

        parent3 = abs(local_clauses[parent_cls[conf_var]][0]) == conf_var ? abs(local_clauses[parent_cls[conf_var]][1]) : abs(local_clauses[parent_cls[conf_var]][0]); 
        parent4 = abs(local_clauses[parent_cls[conf_var]][2]) == conf_var ? abs(local_clauses[parent_cls[conf_var]][2]) : abs(local_clauses[parent_cls[conf_var]][1]); 

	     parent_lvl[0] = dec_lvl[parent1];
	     parent_lvl[1] = dec_lvl[parent2];
	     parent_lvl[2] = dec_lvl[parent3];
	     parent_lvl[3] = dec_lvl[parent4];

        sort(parent_lvl); 

        back_lvl = var_truth_table[dec_var[parent_lvl[3]]] <= F ? parent_lvl[3] : 
                      var_truth_table[dec_var[parent_lvl[2]]] <= F ? parent_lvl[2] : 
                      var_truth_table[dec_var[parent_lvl[1]]] <= F ? parent_lvl[1] : 
                      var_truth_table[dec_var[parent_lvl[0]]] <= F ? parent_lvl[0] : -1; 

	       printf("Back_lvl %d", back_lvl);
        if (back_lvl == -1){
          state = FAILED; 
          break; 
        }

        //Undo all variable assignment after back_lvl
        #pragma ACCEL parallel flatten
        for (int i = 0; i < NUM_VARS; i ++){
          if (dec_lvl[i] >= back_lvl){
            var_truth_table[i] = U;
            dec_lvl[i] = -1; 
            parent_cls[i] = -1;
          }
        }

        var_truth_table[dec_var[back_lvl]] = (var_truth_table[dec_var[back_lvl]] == T) ? TF : FT;
        dec_lvl[dec_var[back_lvl]] = back_lvl;


	   #pragma ACCEL parallel flatten
        for (int i = 0; i < 100; i++){
          if (i > back_lvl){
            dec_var[i] = 0; 
          }
        }

        test ++; 
        state = PROP; 
        break; 

      case SOLVED:
        printf("Solved\n");
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
