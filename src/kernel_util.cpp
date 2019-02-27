#include <string.h>
#include <math.h>
#include <assert.h>
#include <stdlib.h>
#include <stdio.h>

#include <config.h>
int collect_buffer(int pos_cls[NUM_VARS][BUF_CLS_SIZE], int neg_cls[NUM_VARS][BUF_CLS_SIZE], 
  int lit, int x, 
  int *extra_cls, 
  int num_extra){
   
  int i = 0; 
  if (lit > 0){
    while (i<BUF_CLS_SIZE){
      if (pos_cls[lit][i] == EMPTY){
        break;
      }else {
        i ++; 
      }
    }
    if (i>=BUF_CLS_SIZE){
      extra_cls[num_extra]= x; 
      num_extra ++; 
    }else {
      pos_cls[lit][i] = x; 
    }
  }else {
    while (i<BUF_CLS_SIZE){
      if (neg_cls[-lit][i] == EMPTY){
        break;
      }else {
        i ++; 
      }
    }
    if (i>=BUF_CLS_SIZE){
      extra_cls[num_extra]= x; 
      num_extra ++; 
    }else {
      neg_cls[-lit][i] = x; 
    }
  }
  return num_extra;
}

bool deduction(int l1, int l2, int var1, int var2, int x, int *l_ded){
  //printf("Deduction: l1 - %d, l2 - %d\n", l1, l2); 
  bool conflict = 0; 
  bool unsat1 = (l1 > 0) ? (var1 == F || var1 ==TF) : (var1 == T || var1 ==FT);
  bool unsat2 = (l2 > 0) ? (var2 == F || var2 ==TF) : (var2 == T || var2 ==FT);

  conflict = unsat1 & unsat2; 

  l_ded[x] = (unsat1 && (var2 == U))? l2 : (unsat2 && (var1 == U))? l1 : 0; 

  return conflict; 
}

bool deduction4(int l1, int l2, int l3, int var1, int var2, int var3, int x, int *l_ded){
  //printf("Deduction: l1 - %d, l2 - %d\n", l1, l2); 
  bool conflict = 0; 
  bool unsat1 = (l1 > 0) ? (var1 == F || var1 ==TF) : (var1 == T || var1 ==FT);
  bool unsat2 = (l2 > 0) ? (var2 == F || var2 ==TF) : (var2 == T || var2 ==FT);
  bool unsat3 = (l3 > 0) ? (var3 == F || var3 ==TF) : (var3 == T || var3 ==FT);

  conflict = unsat1 & unsat2 & unsat3; 

  l_ded[x] = (unsat1 && unsat2 && (var3==U))? l3 : (unsat1 && unsat3 && (var2==U))? l2 : (unsat2 && unsat3 && (var1==U))? l1 : 0; 

  return conflict; 
}

void sort4 (int array[4]){
  int hi1 = (array[0] > array[1]) ? array[0] : array[1]; 
  int hi2 = (array[2] > array[3]) ? array[2] : array[3];  
  int lo1 = (array[0] <= array[1]) ? array[0] : array[1];
  int lo2 = (array[2] <= array[3]) ? array[2] : array[3]; 

  array[0] = lo1 <= lo2 ? lo1 : lo2; 
  array[3] = hi1 > hi2 ? hi1 : hi2; 

  array[1] = lo1 <= lo2 ? (lo2 <= hi1 ? lo2 : hi1) : (lo1 <= hi2 ? lo1 : hi2);
  array[2] = hi1 > hi2 ? (hi2 >= lo1 ? hi2 : lo1) : (hi1 >= lo2 ? hi1 : lo2); 
}

void sort4_idx (int array[4], int idx[4]){

  int hi1 = (array[0] > array[1]) ? 0 : 1; 
  int hi2 = (array[2] > array[3]) ? 2 : 3;  
  int lo1 = (array[0] <= array[1]) ? 0 : 1;
  int lo2 = (array[2] <= array[3]) ? 2 : 3; 

  idx[0] = array[lo1] <= array[lo2] ? lo1 : lo2; 
  idx[3] = array[hi1] > array[hi2] ? hi1 : hi2; 

  idx[1] = array[lo1] <= array[lo2] ? (array[lo2] <= array[hi1] ? lo2 : hi1) : (array[lo1] <= array[hi2] ? lo1 : hi2);
  idx[2] = array[hi1] > array[hi2] ? (array[hi2] >= array[lo1] ? hi2 : lo1) : (array[hi1] >= array[lo2] ? hi1 : lo2); 

}


/*
void sort3 (int array[3]){
  int lowest = ((array[0] < array[1]) && (array[0] < array[2]))? array[0] ? (array[1] < array[2]) ? array[1] : array[2]; 
  int highest = ((array[0] > array[1]) && (array[0] > array[2]))? array[0] ? (array[1] > array[2]) ? array[1] : array[2]; 
  int middle = (array[0] != highest && array[0] != lowest)? array[0] : (array[1] != highest && array[1] != lowest)? array[1] : array[2];
  array[0] = lowest; 
  array[1] = middle; 
  array[2] = highest; 
}*/


