#include <string.h>
#include <math.h>
#include <assert.h>
#include <stdlib.h>
#include <stdio.h>

#define NUM_VARS 251
#define BUF_CLS_SIZE 10
#define EMPTY -1

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
