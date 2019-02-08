#include <string.h>
#include <math.h>
#include <assert.h>
#include <stdlib.h>
#include <stdio.h>

#define NUM_VARS 251
#define BUF_CLS_SIZE 10
#define EMPTY -1

#define TF 4
#define FT 3
#define F 2
#define T 1
#define U 0

void collect_buffer(int pos_cls[NUM_VARS][BUF_CLS_SIZE], int neg_cls[NUM_VARS][BUF_CLS_SIZE], 
  int lit, int x, 
  int *extra_cls, int *extra_lit, 
  int* num_extra){
    if (lit> 0){
      if (pos_cls[lit][0] == EMPTY){
        pos_cls[lit][0] = x; 
      }else if (pos_cls[lit][1] == EMPTY){
        pos_cls[lit][1] = x;
      }else if (pos_cls[lit][2] == EMPTY){
        pos_cls[lit][2] = x;
      }else if (pos_cls[lit][3] == EMPTY){
        pos_cls[lit][3] = x; 
      }else if (pos_cls[lit][4] == EMPTY){
        pos_cls[lit][4] = x; 
      }else if (pos_cls[lit][5] == EMPTY){
        pos_cls[lit][5] = x; 
      }else if (pos_cls[lit][6] == EMPTY){
        pos_cls[lit][6] = x; 
      }else if (pos_cls[lit][7] == EMPTY){
        pos_cls[lit][7] = x;
      }else if (pos_cls[lit][8] == EMPTY){
        pos_cls[lit][8] = x; 
      }else if (pos_cls[lit][9] == EMPTY){
        pos_cls[lit][9] = x; 
      }else {
        extra_cls[num_extra[0]]= x; 
        extra_lit[num_extra[0]] = lit;
        num_extra[0] ++; 
      }
    }else{
      //assert(neg_cls[var][4]>0);
      if (neg_cls[-lit][0] == EMPTY){
        neg_cls[-lit][0] = x; 
      }else if (neg_cls[-lit][1] == EMPTY){
        neg_cls[-lit][1] = x; 
      }else if (neg_cls[-lit][2] == EMPTY){
        neg_cls[-lit][2] = x; 
      }else if (neg_cls[-lit][3] == EMPTY){
        neg_cls[-lit][3] = x; 
      }else if (neg_cls[-lit][4] == EMPTY){
        neg_cls[-lit][4] = x; 
      }else if (neg_cls[-lit][5] == EMPTY){
        neg_cls[-lit][5] = x; 
      }else if (neg_cls[-lit][6] == EMPTY){
        neg_cls[-lit][6] = x; 
      }else if (neg_cls[-lit][7] == EMPTY){
        neg_cls[-lit][7] = x;
      }else if (neg_cls[-lit][8] == EMPTY){
        neg_cls[-lit][8] = x; 
      }else if (neg_cls[-lit][9] == EMPTY){
        neg_cls[-lit][9] = x; 
      }else {
        extra_cls[num_extra[0]]= x; 
        extra_lit[num_extra[0]] = lit;
        num_extra[0] ++; 
    }

  }
}

/*
bool deduction(int l1, int l2, int *var_truth_table, int x, int *l_ded){
  //printf("Deduction: l1 - %d, l2 - %d\n", l1, l2); 
  int conflict = 0; 
  if (l1>0 && l2>0){ 
    if (var_truth_table[l1] == F && var_truth_table[l2] == F){ // F & F
      conflict = 1;
    }else if (var_truth_table[l1] == F && var_truth_table[l2] == Undef){ 
      l_ded[x] = l2; 
    }else if (var_truth_table[l1] == Undef && var_truth_table[l2] == F){
      l_ded[x] = l1; 
    }

  }else if (l1>0 && l2<0){ 
    if (var_truth_table[l1] == F && var_truth_table[-l2] == T){ // F | ~T
      conflict = 1;
    }else if (var_truth_table[l1] == F && var_truth_table[-l2] == Undef){ 
      l_ded[x] = l2; 
    }else if (var_truth_table[l1] == Undef && var_truth_table[-l2] == T){
      l_ded[x] = l1; 
    }
     
  }else if (l1<0 && l2>0){
    if (var_truth_table[-l1] == T && var_truth_table[l2] == F){ // ~T & F
      conflict = 1;
    }else if (var_truth_table[-l1] == T && var_truth_table[l2] == Undef){ 
      l_ded[x] = l2; 
    }else if (var_truth_table[-l1] == Undef && var_truth_table[l2] == F){
      l_ded[x] = l1; 
    }

  }else{
    if (var_truth_table[-l1] == T && var_truth_table[-l2] == T){ // ~T & ~T
      conflict = 1;
    }else if (var_truth_table[-l1] == T && var_truth_table[-l2] == Undef){ 
      l_ded[x] = l2; 
    }else if (var_truth_table[-l1] == Undef && var_truth_table[-l2] == T){
      l_ded[x] = l1; 
    }

  }
  return conflict; 
}*/

bool deduction(int l1, int l2, int *var_truth_table, int x, int *l_ded){
  //printf("Deduction: l1 - %d, l2 - %d\n", l1, l2); 
  bool conflict = 0; 
  bool unsat1 = (l1 > 0) ? (var_truth_table[l1]==F || var_truth_table[l1]==TF) :
                           (var_truth_table[-l1]==T || var_truth_table[-l1]==FT);
  bool unsat2 = (l2 > 0) ? (var_truth_table[l2]==F || var_truth_table[l2]==TF) : 
                           (var_truth_table[-l2]==T || var_truth_table[-l2]==FT);

  conflict = unsat1 & unsat2; 
  

  l_ded[x] = conflict ? 0 : unsat1 ? l2 : l1; 

  return conflict; 
}
