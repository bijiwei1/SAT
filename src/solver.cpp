#include <string.h>
#include <math.h>
#include <assert.h>
#include <stdlib.h>
#include <stdio.h>

#include <config.h>
#include <stdint.h>

//using namespace std; 


/*
*  data_in1(32), data_in2(32), 
*  data_out1(64)
*  INIT: initial kernel
*  LOAD: data_in1 = {c3, c2, c1} // each 8 bit var idx, 
*        data_in2 = {s3, s2, s1} // each 1 bit sign
*        data_out1 = {cls_no, pe_no} // cls_no(10), pe_no(6)
*        
*  DEC : data_in1 = {curr_lvl, var_idx, s} // var_idx(8), sign(1), T/F
*        data_out1[0] = {conf_cls_no, conf_cls_pe, conf_var, conf} // conf_cls_no(10), conf_cls_pe(6), conf_var(8), conf(1)
*        data_out1[1] =  {num of ded, xxxx xxxx xxxx xxxx} //assigned value for the above data , num of ded variable
*        data_out2[0/1] = {var_idx*8} //Each 8 bits - total 8*2 variables
*        data_out3[0/1] = {parent_cls1*4} //Each parent_cls has cls_no(10) & pe_no(6)
*        data_out4[0/1] = {parent_cls1*4} //Each parent_cls has cls_no(10) & pe_no(6)
*  BACK: Same as above   
*        data_in2 = {back_lvl}       
*/


int priority_encoder_16(int in);
int priority_encoder_64(uint64_t in);

#pragma ACCEL kernel
void solver_kernel(int mode, int* data_in1, int* data_in2, 
            uint64_t* data_out1, uint64_t* data_out2, uint64_t* data_out3, uint64_t* data_out4){

#pragma ACCEL interface variable=mode depth = 1
#pragma ACCEL interface variable=data_in1 depth = 1
#pragma ACCEL interface variable=data_in2 depth = 1
#pragma ACCEL interface variable=data_out1 depth = 2
#pragma ACCEL interface variable=data_out2 depth = 2
#pragma ACCEL interface variable=data_out3 depth = 2
#pragma ACCEL interface variable=data_out4 depth = 2
#pragma ACCEL interface variable=data_out5 depth = 2
/************************ Variable Declaration **************************/

  int local_mode = mode; 

  //Table and buffers
  /*
   * Var: 256 (8 bits), Clause: 2^32 (32 bits)
   */
  uint8_t clauses[NUM_PE][NUM_CLAUSES_PE][MAX_NUM_LIT]; //Only variable idx, If no var, => 255 
  uint16_t clauses_sign[NUM_PE][NUM_CLAUSES_PE]; // 
  uint16_t clauses_cls_size[NUM_PE]; 
  uint16_t watch_var_info[NUM_PE][NUM_CLAUSES_PE][2]; //bit 0 - 7 : var_idx, 8 - 11 : pid
  uint16_t pid_cls_info[NUM_PE][NUM_VARS][NUM_P] = {EMPTY}; //bit 0 - 4: pid pos, > 5 : cls


  /* Variable Information */
  uint8_t var_truth_table[NUM_VARS]; // T, F, U (Undef)
  int var_dec_lvl[NUM_VARS]; 

  int buf_ded_lit[BUF_DED_SIZE];
  uint64_t buf_ded_parent_cls[BUF_DED_SIZE]; //pe: 0-5, cls: >6 (10bit)
  int buf_ded_curr = -1;
  int buf_ded_end = -1;

  /* Used for each PE*/
  int l_ded[NUM_PE][NUM_P];
  int cls_ded[NUM_PE][NUM_P]; // 0 -16: cls, > 17: pe_no, -1 : if not assigned
  bool conflict[NUM_PE][NUM_P];

  /* Used for collecting all PE*/
  uint64_t tot_conflict[NUM_P], is_ded[NUM_P]; // num of bits = num_pe 
  int conf_pe, ded_pe;
  uint8_t conf_p, ded_p;
  int conf_cls; // pe: 0 - 5, cls: > 6 (10 bit)
  uint8_t conf_var;

  //Idx and ptr  

  //Other global variables
  uint8_t prop_var;
  int curr_lvl; 

  int ii;
  if (local_mode == INIT){
    /*************************** Initializing array ***************************/
    for (int i = 0; i < NUM_PE; i++){
      clauses_cls_size[i] = 0;
      for (int j = 0; j < NUM_VARS; j++){
        for (int k = 0; k < NUM_P; k++){
          pid_cls_info[i][j][k] = EMPTY;
        }
      }
    }

    for (int x = 0; x< NUM_VARS; x++){
     var_truth_table[x] = U; 
    }

  }else if (local_mode == LOAD){
    /*************************** Loading Clauses ***************************/
    //Load data
    printf("Start to load data \n");
    //Load original clauses 
    
    int var1 = data_in1[0] & 0xff;
    int var2 = data_in1[0] >> 8 & 0xff;
    int var3 = data_in1[0] >> 16 & 0xff;
    int s1 = data_in2[0] & 0x1; 
    int s2 = data_in2[0]>>1 & 0x1; 
    int s3 = data_in2[0]>>2 & 0x1; 
    int avail_pe;
    int avail_idx1, avail_idx2;
   
    for (avail_pe = 0; avail_pe < NUM_PE; avail_pe ++){
      avail_idx1 = (pid_cls_info[avail_pe][var1][0] == EMPTY) ? 0 : 
                (pid_cls_info[avail_pe][var1][1] == EMPTY) ? 1 : 
                (pid_cls_info[avail_pe][var1][2] == EMPTY) ? 2 :
                (pid_cls_info[avail_pe][var1][3] == EMPTY) ? 3 : -1;
      avail_idx2 = (pid_cls_info[avail_pe][var2][0] == EMPTY) ? 0 : 
                (pid_cls_info[avail_pe][var2][1] == EMPTY) ? 1 : 
                (pid_cls_info[avail_pe][var2][2] == EMPTY) ? 2 :
                (pid_cls_info[avail_pe][var2][3] == EMPTY) ? 3 : -1;      
      if (avail_idx1 == -1 && avail_idx2 == -1)
        goto end;
    }
    end:;
    assert(avail_pe < NUM_PE);

    int cls_idx = clauses_cls_size[avail_pe]; 
    //Write clause info
    clauses[avail_pe][clauses_cls_size[avail_pe]][0] = var1;
    clauses[avail_pe][clauses_cls_size[avail_pe]][1] = var2;
    clauses[avail_pe][clauses_cls_size[avail_pe]][2] = var3;
    clauses_sign[avail_pe][cls_idx] = data_in2[0];

    //Write variable info
    watch_var_info[avail_pe][cls_idx][0] = (var1 << 5);
    watch_var_info[avail_pe][cls_idx][1] = 1 | (var2 << 5);
    pid_cls_info[avail_pe][var1][avail_idx1] = clauses_cls_size[avail_pe];
    pid_cls_info[avail_pe][var2][avail_idx2] = clauses_cls_size[avail_pe];
    clauses_cls_size[avail_pe] ++; 

    data_out1[0] = avail_pe | cls_idx << 6;
    printf("Add cls %d %d %d to pe %d idx %d\n", var1, var2, var3, avail_pe, clauses_cls_size[avail_pe]);

    /*
  for (int i = 0; i < NUM_PE; i++){
    for (int j = 0; j < clauses_cls_size[i]; j++){
      printf("PE %d(cls_no %d): clause %d %d %d, sign %d\n", i, j, clauses[i][j][0], clauses[i][j][1], clauses[i][j][2], clauses_sign[i][j]);
    }
  } */

  }else if (mode == DECISION || mode == BACKTRACK){

    prop_var = data_in1[0] >> 1 & 0xff;
    var_truth_table[prop_var] = data_in1[0] & 0x1; 
    curr_lvl = data_in1[0] >> 9;

    if (mode == BACKTRACK){
      for (int i = 0; i < NUM_VARS; i++){
        if(var_dec_lvl[i] >= curr_lvl){
          var_truth_table[i] = U;
          var_dec_lvl[i] = -1;
        }
      }
    }

    bool isdone = 0;
    while (~isdone){
    printf("Prop var %d\n", prop_var);
    #pragma ACCEL parallel flatten
    for (int pe_no = 0; pe_no < NUM_PE; pe_no++){
      for (int i = 0; i < NUM_P; i++){
        conflict[pe_no][i] = 0;
        cls_ded[pe_no][i] = -1;
        int cls_info = pid_cls_info[pe_no][prop_var][i];
        int cls_no = cls_info >> 5; 
        int other_watch_info = watch_var_info[pe_no][cls_no][0] == cls_no ? watch_var_info[pe_no][cls_no][1] : watch_var_info[pe_no][cls_no][0];
        int prop_var_sign = clauses_sign[pe_no][cls_no] >> (cls_info & 0x1f);
        int other_watch_sign = clauses_sign[pe_no][cls_no] >> (other_watch_info & 0x1f);
        int other_watch_var = other_watch_info >>5;
        if (var_truth_table[prop_var] != prop_var_sign || var_truth_table[other_watch_var] != other_watch_sign){
            //Do nothing since either one  is true
        }else if (var_truth_table[other_watch_var] == other_watch_sign){
            //The other var_truth table is false
          conflict[pe_no][i] = 1; 
          printf("Found conflict - pe_no %d, cls_no%d\n", pe_no, i);
        }else{
          // var_truth_table[other_watch_info] == U
          int nxt_unassign_pid = (var_truth_table[clauses[pe_no][cls_no][0]] == U && clauses[pe_no][cls_no][0] != other_watch_var) ? 0 : 
                  (var_truth_table[clauses[pe_no][cls_no][1]] == U && clauses[pe_no][cls_no][1] != other_watch_var) ? 1 :
                  (var_truth_table[clauses[pe_no][cls_no][2]] == U && clauses[pe_no][cls_no][2] != other_watch_var) ? 2 :
                  (var_truth_table[clauses[pe_no][cls_no][3]] == U && clauses[pe_no][cls_no][3] != other_watch_var) ? 3 :
                  (var_truth_table[clauses[pe_no][cls_no][4]] == U && clauses[pe_no][cls_no][4] != other_watch_var) ? 4 :
                  (var_truth_table[clauses[pe_no][cls_no][5]] == U && clauses[pe_no][cls_no][5] != other_watch_var) ? 5 :
                  (var_truth_table[clauses[pe_no][cls_no][6]] == U && clauses[pe_no][cls_no][6] != other_watch_var) ? 6 :
                  (var_truth_table[clauses[pe_no][cls_no][7]] == U && clauses[pe_no][cls_no][7] != other_watch_var) ? 7 :
                  (var_truth_table[clauses[pe_no][cls_no][8]] == U && clauses[pe_no][cls_no][8] != other_watch_var) ? 8 :
                  (var_truth_table[clauses[pe_no][cls_no][9]] == U && clauses[pe_no][cls_no][9] != other_watch_var) ? 9 : -1;
          int nxt_unassign_var = clauses[pe_no][cls_no][nxt_unassign_pid];
          if (nxt_unassign_pid == -1){
            //This is the last unassigned variable 
            cls_ded[pe_no][i] = cls_no;
            l_ded[pe_no][i]= (other_watch_sign == POS) ? other_watch_var : -other_watch_var;
            printf("Found ded var %d, - pe_no %d, cls_no %d\n", pe_no, i);
          }else{
            watch_var_info[pe_no][cls_no][0] = other_watch_info;
            int new_watch_info = nxt_unassign_pid | (clauses[pe_no][cls_no][nxt_unassign_pid] >> 5);
            watch_var_info[pe_no][cls_no][1] = (nxt_unassign_pid == -1) ?  watch_var_info[pe_no][cls_no][1] : new_watch_info; //Not changing 
            int avail_idx = (pid_cls_info[pe_no][nxt_unassign_var][0] == EMPTY) ? 0 : 
                (pid_cls_info[pe_no][nxt_unassign_var][1] == EMPTY) ? 1 : 
                (pid_cls_info[pe_no][nxt_unassign_var][2] == EMPTY) ? 2 :
                (pid_cls_info[pe_no][nxt_unassign_var][3] == EMPTY) ? 3 : -1;
            assert(avail_idx != -1);
            pid_cls_info[pe_no][nxt_unassign_var][avail_idx] = nxt_unassign_pid | (cls_no << 5);
          } 
        }

      }//End of p
    }//End of pe

    //Inference collection
    tot_conflict[0] = 0; 
    tot_conflict[1] = 0; 
    tot_conflict[2] = 0; 
    tot_conflict[3] = 0; 
    #pragma ACCEL parallel flatten reduction=tot_conflict
    for (int i = 0; i < NUM_PE ; i++){
      for (int j = 0; j < NUM_P; j++){
        tot_conflict[j] |= (cls_ded[i][j] == -1 ? 0 : 1<<i); 
      }
    }
      
    is_ded[0] = 0;
    is_ded[1] = 1;
    is_ded[2] = 2;
    is_ded[3] = 3;
    #pragma ACCEL parallel flatten reduction=is_ded
    for (int i = 0; i < NUM_PE ; i++){
      for (int j = 0; j < NUM_P; j++){
        is_ded[j] |= (cls_ded[i][j] == -1 ? 0 : 1<<i); 
      }
    }

    conf_p = tot_conflict[0] != 0 ? 0 : 
            tot_conflict[1] != 0 ? 1 :
            tot_conflict[2] != 0 ? 2 :
            tot_conflict[3] != 0 ? 3 : -1;

    if (conf_p != -1){
        conf_pe = priority_encoder_16(tot_conflict[conf_p]); 
        conf_var = prop_var;
        conf_cls = (pid_cls_info[conf_pe][prop_var][conf_p] >> 6) & conf_pe;
        break; 
    }

    for (int x = 0; x < NUM_P; x++){
      ded_pe = priority_encoder_64(is_ded[x]);
      while (ded_pe != -1){
        int var_ded = abs(l_ded[ded_pe][x]);
        int var_ded_value = (l_ded[ded_pe][x] == POS) ? T : F; 
        if (var_truth_table[var_ded] == U){
          buf_ded_end ++;
          buf_ded_lit[buf_ded_end] = l_ded[ded_pe][x]; 
          buf_ded_parent_cls[buf_ded_end] =  (cls_ded[ded_pe][x] >> 6 )& ded_pe; 
          printf("Add ded var %d due to cls %d\n", buf_ded_lit[buf_ded_end], buf_ded_parent_cls[buf_ded_end]);
          //Change ded value here
          var_truth_table[var_ded] = l_ded[ded_pe][x] > 0 ? T : F;
        }else if (var_truth_table[var_ded] != var_ded_value){
          //Found conflict in same level
          conf_p=1; 
          conf_var = var_ded;
          conf_cls = cls_ded[ded_pe][x] & (ded_pe >> 16);
          printf("Found inner conflict Var(%d) due to cls(%d)\n", conf_var, conf_cls);
        }
      }
      is_ded[x] ^= (1 << ded_pe);
    }

    assert (buf_ded_end < BUF_DED_SIZE);

    if (conf_p){
      //Found conflict 
      isdone = 1;
    }else if (buf_ded_curr == buf_ded_end){
      //No deducted variable in buf_ded
      isdone = 1;
    }else{
      //Move to next variable in buf_ded
      buf_ded_curr++;
      prop_var = buf_ded_lit[buf_ded_curr];
    }

    }//End of isdone while loop


    int conf_info_out = conf_p | conf_var << 1 |  conf_cls << 9;
    int assigned_value = 0; 
    int var_idx_out1 = 0; 
    int var_idx_out2 = 0; 

    #pragma ACCEL parallel flatten reduction=assigned_value
    for (int i = 0; i < BUF_DED_SIZE; i++){
      if (i <= buf_ded_end){
        assigned_value |= (var_truth_table[abs(buf_ded_lit[i])] << i); 
      }
    }


    for (int i = 0; i < BUF_DED_SIZE; i++){
      if (i <= buf_ded_end){
        if (i < 8){
          var_idx_out1 |= (abs(buf_ded_lit[i])) << (8*i);  
        }else {
          var_idx_out2 |= (abs(buf_ded_lit[i])) << (8*(i-1));  
        }
      }
    }

    data_out1[0] = conf_info_out;
    data_out1[1] = assigned_value | (buf_ded_end << 16); 
    data_out2[0] = var_idx_out1;
    data_out2[1] = var_idx_out2;

    data_out3[0] = ((buf_ded_end >= 0) ? buf_ded_parent_cls[0] : 0) | 
                  ((buf_ded_end >= 1) ? buf_ded_parent_cls[1] << 16: 0) |
                  ((buf_ded_end >= 2) ? buf_ded_parent_cls[2] << 32: 0) |
                  ((buf_ded_end >= 3) ? buf_ded_parent_cls[1] << 48: 0) ; 

    data_out3[1] =  ((buf_ded_end >= 4) ? buf_ded_parent_cls[4] : 0) | 
                  ((buf_ded_end >= 5) ? buf_ded_parent_cls[5] << 16: 0) |
                  ((buf_ded_end >= 6) ? buf_ded_parent_cls[6] << 32: 0) |
                  ((buf_ded_end >= 7) ? buf_ded_parent_cls[7] << 48: 0) ; 

    data_out4[0] =  ((buf_ded_end >= 8) ? buf_ded_parent_cls[8] : 0) | 
                  ((buf_ded_end >= 9) ? buf_ded_parent_cls[9] << 16: 0) |
                  ((buf_ded_end >= 10) ? buf_ded_parent_cls[10] << 32: 0) |
                  ((buf_ded_end >= 11) ? buf_ded_parent_cls[11] << 48: 0) ; 

    data_out4[0] =  ((buf_ded_end >= 12) ? buf_ded_parent_cls[12] : 0) | 
                  ((buf_ded_end >= 13) ? buf_ded_parent_cls[13] << 16: 0) |
                  ((buf_ded_end >= 14) ? buf_ded_parent_cls[14] << 32: 0) |
                  ((buf_ded_end >= 15) ? buf_ded_parent_cls[15] << 48: 0) ;              

  }//End of mode DEC

  /*
       *        data_out1[0] = {conf_cls_no, conf_cls_pe, conf_var, conf} // conf_cls_no(10), conf_cls_pe(6), conf_var(8), conf(1)
       *        data_out1[1] =  {num of ded, xxxx xxxx xxxx xxxx} //assigned value for the above data , num of ded variable
       *        data_out2[0/1] = {var_idx*8} //Each 8 bits - total 8*2 variables
       *        data_out3[0/1] = {parent_cls1*4} //Each parent_cls has cls_no(10) & pe_no(6)
       *        data_out4[0/1] = {parent_cls1*4} //Each parent_cls has cls_no(10) & pe_no(6)
       *  BACK: Same as above   
       *        data_in2 = {back_lvl}   
     */

  

  

      ii++;
    printf("Check %d\n", ii);

      

}
