#include <string.h>
#include <math.h>
#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>

#include <config.h>

int priority_encoder_8(int in){
  int pos = ((in & 0x80) != 0) ? 7 : 
    ((in & 0x40) != 0) ? 6 : 
    ((in & 0x20) != 0) ? 5 :
    ((in & 0x10) != 0) ? 4 : 
    ((in & 0x08) != 0) ? 3 : 
    ((in & 0x04) != 0) ? 2 : 
    ((in & 0x02) != 0) ? 1 :
    ((in & 0x01) != 0) ? 0 : -1;

    return pos; 
}

int priority_encoder_16(int in){
    int pos = (in & 0x8000) != 0 ? 15 : 
        (in & 0x4000) != 0 ? 14 : 
        (in & 0x2000) != 0 ? 13 : 
        (in & 0x1000) != 0 ? 12 : 
        (in & 0x0800) != 0 ? 11 : 
        (in & 0x0400) != 0 ? 10 : 
        (in & 0x0200) != 0 ? 9 : 
        (in & 0x0100) != 0 ? 8 : 
        (in & 0x0080) != 0 ? 7 : 
        (in & 0x0040) != 0 ? 6 : 
        (in & 0x0020) != 0 ? 5 : 
        (in & 0x0010) != 0 ? 4 : 
        (in & 0x0008) != 0 ? 3 : 
        (in & 0x0004) != 0 ? 2 : 
        (in & 0x0002) != 0 ? 1 : 
        (in & 0x0001) != 0 ? 0 : -1;
    return pos;
}

int priority_encoder_64(uint64_t in){

    int pos_1  = priority_encoder_16(in&0xffff);
    int pos_2  = priority_encoder_16(in >> 16 &0xffff);
    int pos_3  = priority_encoder_16(in >> 32 &0xffff);
    int pos_4  = priority_encoder_16(in >> 48 &0xffff);

    int pos = (pos_4 != -1)? pos_4 : 
            (pos_3 != -1)? pos_3 :
            (pos_2 != -1)? pos_2 :
            (pos_1 != -1)? pos_1 : -1;

    return pos;
}

/*
bool collect_buffer(int pos_cls[NUM_VARS][BUF_CLS_SIZE], int neg_cls[NUM_VARS][BUF_CLS_SIZE], 
  int lit, int x){
   
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
      return 1; 
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
      return 1; 
    }else {
      neg_cls[-lit][i] = x; 
    }
  }
  return 0; 
}


bool deduction3(int l1, int l2, int var1, int var2, int x, int pe_no, int l_ded[NUM_PE][BUF_CLS_SIZE]){
  //printf("Deduction: l1 - %d, l2 - %d\n", l1, l2); 
  bool conflict = 0; 
  bool unsat1 = (l1 > 0) ? (var1 == F || var1 ==TF) : (var1 == T || var1 ==FT);
  bool unsat2 = (l2 > 0) ? (var2 == F || var2 ==TF) : (var2 == T || var2 ==FT);

  conflict = unsat1 & unsat2; 

  l_ded[pe_no][x] = (unsat1 && (var2 == U))? l2 : (unsat2 && (var1 == U))? l1 : 0; 

  return conflict; 
}

bool deduction4(int l1, int l2, int l3, int var1, int var2, int var3, int x, int pe_no, int l_ded[NUM_PE][BUF_CLS_SIZE]){ 
  //printf("Deduction: l1 - %d, l2 - %d\n", l1, l2); 
  bool conflict = 0; 
  bool unsat1 = (l1 > 0) ? (var1 == F || var1 ==TF) : (var1 == T || var1 ==FT);
  bool unsat2 = (l2 > 0) ? (var2 == F || var2 ==TF) : (var2 == T || var2 ==FT);
  bool unsat3 = (l3 > 0) ? (var3 == F || var3 ==TF) : (var3 == T || var3 ==FT);

  conflict = unsat1 & unsat2 & unsat3; 

  l_ded[pe_no][x] = (unsat1 && unsat2 && (var3==U))? l3 : (unsat1 && unsat3 && (var2==U))? l2 : (unsat2 && unsat3 && (var1==U))? l1 : 0; 

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


