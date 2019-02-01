#include <string.h>
#include <math.h>
#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
//#include <string> 
//using namespace std; 

#define NUM_CLAUSES 1024
#define NUM_VARS 251

#define BUF_CLS_SIZE 20
#define BUF_DED_SIZE 10

void collect_buffer(int pos_cls[NUM_VARS][BUF_CLS_SIZE], int neg_cls[NUM_VARS][BUF_CLS_SIZE], 


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
  char var_truth_table[NUM_VARS] = {'U'}; 
  // T, F, U (Undef), f(assigned to T first), t(assigned to F first)
  bool dec_ded_type[NUM_VARS] = {0}; // 0 - DEC, 1 - DED
  int dec_lvl[NUM_VARS] = {0}
  int buf_ded[BUF_DED_SIZE] = {-1};
  
  int pos_cls[BUF_CLS_SIZE] = {-1}; 
  int neg_cls[BUF_CLS_SIZE] = {-1}; 
  int extra_cls[extra_buf_size] = {0}; 
  int extra_lit[extra_buf_size] = {0}; 

  //Idx and ptr 
  int new_var_idx = 1;
  int curr_lvl = -1; 
  int buf_ded_curr = -1;
  int buf_ded_end = -1;
  //Other variables
  int state = DECISION; 


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

/********************************* FSM **********************************/
  while (state != EXIT){
    switch(state){
      case DECISION: 
        printf("State = DECISION; ");

        while (new_var_idx < NUM_VARS){
          //printf("Skip var %d\n", new_var_idx); 
          if (var_truth_table[new_var_idx] != 'U'){
            new_var_idx ++; 
          }else{
            break; 
          }
        } 
        
        if (new_var_idx == NUM_VARS){
          state = SOLVED; 
        }else {
          state = PROP;
          //printf("Decide Var(%d)\n", new_var_idx);
          curr_lvl ++; 

          if (pos_cls[new_var_idx][8] != -1){
            var_truth_table[new_var_idx] = T;
          }else {
            var_truth_table[new_var_idx] = F;
          }
 
          dec_ded_type[new_var_idx] = 0; // DEC
          dec_lvl[new_var_idx] = curr_lvl; 
        }

        prev_state = DECISION; 
        break;
      case PROP:
        if (prev_state == DECISION || prev_state == BACKTRACK){
          prop_var = new_var_idx;
          //printf("Decision Var(%d): %d\n", prop_var, var_truth_table[prop_var]);
        }else if (prev_state == DEDUCTION){
          prop_var = abs(buf_ded[buf_ded_curr]);
          buf_ded_curr ++; 
          //printf("deduction Var(%d): %d\n", prop_var, var_truth_table[prop_var]);
        }

        /****************** Regular buffer *****************/
        int l1[BUF_CLS_SIZE], l2[BUF_CLS_SIZE];

/*
        #pragma ACCEL parallel flatten 
        for (int x = 0; x < BUF_CLS_SIZE; x++){
          if ()
        }
        */ 
        break; 

    }//end of sw
  }//end of while



  satisfiable = unsatisfiable ? 0 : 1; 

  printf("SAT result: %d\n", satisfiable);
  printf("unSAT result: %d\n", unsatisfiable);

  result[0] = satisfiable;

}
