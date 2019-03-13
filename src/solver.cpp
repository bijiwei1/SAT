#include <string.h>
#include <math.h>
#include <assert.h>
#include <stdlib.h>
#include <stdio.h>

#include <config.h>
#include <stdint.h>

//using namespace std; 


bool collect_buffer(int pos_cls[NUM_VARS][BUF_CLS_SIZE], int neg_cls[NUM_VARS][BUF_CLS_SIZE], 
  int lit, int x);

bool deduction3(int l1, int l2, int var1, int var2, int x, int pe_no, int l_ded[NUM_PE][BUF_CLS_SIZE]);
bool deduction4(int l1, int l2, int l3, int var1, int var2, int var3, int x, int pe_no, int l_ded[NUM_PE][BUF_CLS_SIZE]);

void sort4 (int array[4]); 

void sort4_idx (int array[4], int idx[4]);



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



#pragma ACCEL kernel
void solver_kernel(
        int* c1, int* c2, int* c3, int* result){

#pragma ACCEL interface variable=c1 depth = 218
#pragma ACCEL interface variable=c2 depth = 218
#pragma ACCEL interface variable=c3 depth = 218
#pragma ACCEL interface variable=result depth=1
/************************ Variable Declaration **************************/
  int satisfiable; 
  int unsatisfiable = 0; 

  //Table and buffers
  /*
   * Var: 256 (8 bits), Clause: 2^32 (32 bits)
   */
  uint8_t clauses[NUM_PE][NUM_CLAUSES_PE][MAX_NUM_LIT]; //Only variable idx, If no var, => 255 
  uint16_t clauses_sign[NUM_PE][NUM_CLAUSES_PE]; // 
  uint16_t clauses_cls_size[NUM_PE] = {0}; 
  uint16_t watch_var_info[NUM_PE][NUM_CLAUSES_PE][2]; //bit 0 - 7 : var_idx, 8 - 11 : pid
  uint16_t pid_cls_info[NUM_PE][NUM_VARS][NUM_P] = {EMPTY}; //bit 0 - 4: pid pos, > 5 : cls


  /* Variable Information */
  uint8_t var_truth_table[NUM_VARS] = {U}; // T, F, U (Undef)
  //bool var_ischecked[NUM_VARS] = {0};
  uint32_t var_ischecked[NUM_VARS] = 0;
  bool var_ismarked[NUM_VARS] ={0};
  int dec_lvl[NUM_VARS] = {-1};
  int dec_var[BUF_DEC_LVL]= {0}; // Variable idx at each decision lvl, we assume at most 100 decision level
  uint8_t assigned_stack[NUM_VARS] = {IDLE_VAR}; 
  int num_assigned = 0; 
  int buf_ded[BUF_DED_SIZE] = {0};
  int buf_ded_cls[BUF_DED_SIZE] = {-1}; 
  int parent_cls[NUM_VARS] = {0}; // 0 - 16: cls, > 17 : pe_no

  //int least_parent[NUM_VARS] = {0};
  //int dec_lst_lvl[BUF_DEC_LVL] = {-1}; 

  /* Used for each PE*/
  int l_ded[NUM_PE][NUM_P];
  int cls_ded[NUM_PE][NUM_P]; // 0 -16: cls, > 17: pe_no, -1 : if not assigned
  bool conflict[NUM_PE][NUM_P];

  /* Used for collecting all PE*/
  int tot_conflict[NUM_P], is_ded[NUM_P]; // num of bits = num_pe 
  int conf_pe, ded_pe;
  uint8_t conf_p, ded_p;
  int conf_cls; // 0 -16:cls, > 17 -pe
  uint8_t conf_var;

  //Idx and ptr 
  int new_var_idx = 1;
  int curr_lvl = -1; 
  int buf_ded_curr = -1;
  int buf_ded_end = -1;

  //Other global variables
  int state = DECISION; 
  int prev_state = DECISION; 
  uint8_t prop_var; 
  int back_lvl = 0; 

  //Temporary variabels
  bool conf_ded; //PROP
  int prev_assigned_value; // BACKTRACK
  int curr_lst;

/*************************** Initializing array ***************************/
    for (int i = 0; i < NUM_PE; i++){
        for (int j = 0; j < NUM_VARS; j++){
            for (int k = 0; k < NUM_P; k++){
                pid_cls_info[i][j][k] = EMPTY;
            }
        }
    }
  for (int x = 0; x< NUM_VARS; x++){
     var_truth_table[x] = U; 
  }

/*************************** Loading Clauses ***************************/
  //Load data
  printf("Start to load data \n");
  //Load original clauses 
  for (int x = 0; x < NUM_ORG_CLAUSES; ++x) {
    int var1 = abs(c1[x]);
    int var2 = abs(c2[x]);
    int var3 = abs(c3[x]); 
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
      if (avail_idx1 != -1 && avail_idx2 != -2)
          goto end;
    }
end:;

    assert(avail_pe < NUM_PE);

    //Write clause info
    clauses[avail_pe][clauses_cls_size[avail_pe]][0] = var1;
    clauses[avail_pe][clauses_cls_size[avail_pe]][1] = var2;
    clauses[avail_pe][clauses_cls_size[avail_pe]][2] = var3;
    clauses_sign[avail_pe][clauses_cls_size[avail_pe]] = (c1[x] > 0 ? POS : NEG) | ((c2[x] > 0 ? POS : NEG) << 1) | ((c3[x] > 0 ? POS : NEG) << 2);
    //printf("Add cls %d %d %d to pe %d idx %d\n", var1, var2, var3, avail_pe, clauses_cls_size[avail_pe]);

    //Write variable info
    watch_var_info[0][x][0] = (var1 << 5);
    watch_var_info[0][x][1] = 1 | (var2 << 5);
    pid_cls_info[avail_pe][var1][avail_idx1] = clauses_cls_size[avail_pe];
    pid_cls_info[avail_pe][var2][avail_idx2] = clauses_cls_size[avail_pe];

    clauses_cls_size[avail_pe] += 1; 
  }

  /*
  for (int i = 0; i < NUM_PE; i++){
    for (int j = 0; j < clauses_cls_size[i]; j++){
      printf("PE %d(cls_no %d): clause %d %d %d, sign %d\n", i, j, clauses[i][j][0], clauses[i][j][1], clauses[i][j][2], clauses_sign[i][j]);
    }
  } */


/********************************* FSM **********************************/
  while (state != EXIT){
  switch(state){
    case DECISION: 

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

        var_truth_table[new_var_idx] = T;
        dec_lvl[new_var_idx] = curr_lvl; 
        dec_var[curr_lvl] = new_var_idx; 
        assigned_stack[num_assigned] = new_var_idx;
        num_assigned ++;
      }

      prev_state = DECISION; 
      break;

    case PROP:
      if (prev_state == DECISION || prev_state == BACKTRACK_DEC){
        prop_var = new_var_idx;
      }else if (prev_state == DEDUCTION){
        prop_var = abs(buf_ded[buf_ded_curr]); 
      }else if (prev_state == BACKTRACK_DED){
        //prop_var = abs(learned_lit);
        assert(0);
      }

      printf("Prop var %d\n", prop_var);
      /****************** pos_buf & neg_buf *****************/
      #pragma ACCEL parallel flatten
      for (int pe_no = 0; pe_no < NUM_PE; pe_no++){

        for (int i = 0; i < NUM_P; i++){
          //Reset 
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
        //conflict[0][pe_no] = conflict[0] | (conflict[1] >>1) | (conflict[2]>>2) | (conflict[3]>>3);
        //is_ded[0][pe_no] = (cls_ded[0] != -1) | ((cls_ded[0] != -1) ? 0 : 2) | ((cls_ded[0] != -1) ? 0 : 4) | ((cls_ded[0] != -1) ? 0 : 8); 
      } // End of PE

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
      #pragma ACCEL parallel flatten reduction=tot_conflict
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
        conf_cls = pid_cls_info[conf_pe][prop_var][conf_p] & (conf_pe >> 16);
        state = BACKTRACK_DEC; 
        break; 
      }


      for (int x = 0; x < NUM_P; x++){
        ded_pe = priority_encoder_16(is_ded[x]);
        while (ded_pe != -1){
          int var_ded = abs(l_ded[ded_pe][x]);
          int var_ded_value = (l_ded[ded_pe][x] == POS) ? T : F; 
          if (var_truth_table[var_ded] == U){
            buf_ded_end ++;
            buf_ded[buf_ded_end] = l_ded[ded_pe][x]; 
            buf_ded_cls[buf_ded_end] = cls_ded[ded_pe][x]; 
            //Change ded value here
            dec_lvl[var_ded] = curr_lvl;  
            parent_cls[var_ded] = cls_ded[ded_pe][x] & (ded_pe >> 16); 
            var_truth_table[var_ded] = l_ded[ded_pe][x] > 0 ? T : F;
            assigned_stack[num_assigned] = var_ded;
            num_assigned++;
          }else if (var_truth_table[var_ded] != var_ded_value){
            //Found conflict in same level
            conf_ded=1; 
            conf_var = var_ded;
            conf_cls = cls_ded[ded_pe][x] & (ded_pe >> 16);
            //printf("Found inner conflict Var(%d) due to cls(%d) with parentcls(%d)\n", conf_var, conf_cls, parent_cls[var_ded]);
          }
        }
        
      }

      assert (buf_ded_end < BUF_DED_SIZE);
        
      if (conf_ded){
        //Found conflict 
        state = (conf_var == dec_var[curr_lvl]) ? BACKTRACK_DEC : ANALYSIS;
        buf_ded_curr = -1; buf_ded_end = -1;
      }else if (buf_ded_curr == buf_ded_end){
        //No deducted variable in buf_ded
        state = DECISION;
        buf_ded_curr = -1; buf_ded_end = -1;
      }else{
        //Move to next variable in buf_ded
        state = PROP;
        buf_ded_curr++;
      }
      break; 

      case ANALYSIS: 
        //printf("State = ANALYSIS; "
        /*
        for (int i = 0; i < MAX_NUM_LIT; i++){
            int conf_pe = ; 
            clauses
        }
        for (i = num_assigned; i >=0; i--){
         
        } */
        
        state = BACKTRACK_DEC;
        break; 

      case BACKTRACK_DEC: 
        //printf("State = BACKTRACK_DEC; ");
        back_lvl = curr_lvl; 
        prev_state = BACKTRACK_DEC;

        /*
        while(var_ischecked[dec_var[back_lvl]] && back_lvl >= 0){
          back_lvl --; 
        }*/

        if (back_lvl < 0){
          printf("Failed at lvl %d\n", back_lvl);
          state = FAILED; 
          break;
        }

        printf("Back to lvl %d - Var %d\n", back_lvl, dec_var[back_lvl]);

        prev_assigned_value = var_truth_table[dec_var[back_lvl]]; 
        //Undo all variable assignment after back_lvl
        #pragma ACCEL parallel flatten
        for (int i = 0; i < NUM_VARS; i ++){
          if (dec_lvl[i] >= back_lvl){
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

        new_var_idx = dec_var[back_lvl]; 
        var_truth_table[new_var_idx] = (prev_assigned_value == T) ? F : T;
        dec_lvl[new_var_idx] = back_lvl;
        //least_parent[new_var_idx] = new_var_idx;
        //printf("Change VTT Var(%d) to %d\n", dec_var[back_lvl], var_truth_table[dec_var[back_lvl]]);
        curr_lvl = back_lvl; 

        state = PROP;
        break;

        /*
      case BACKTRACK_DED:
        prev_state = BACKTRACK_DED;
        //printf("Conflict var %d with dec_lvl(%d), conf_cls(%d) parent_cls(%d)\n", conf_var,dec_lvl[conf_var], conf_cls, parent_cls[conf_var]);
        #pragma ACCEL parallel flatten
        for (int i = 0; i < NUM_VARS; i ++){
          if (dec_lvl[i] > back_lvl){
            var_truth_table[i] = U;
            dec_lvl[i] = -1; 
            parent_cls[i] = -1;
            least_parent[i] = 0; 
          }
        }

        #pragma ACCEL parallel flatten
        for (int i = 0; i < BUF_DEC_LVL; i++){
          if (i > back_lvl){
            dec_var[i] = 0; 
          }
        }

        new_var_idx = dec_var[back_lvl]; 
        var_truth_table[abs(learned_lit)] = learned_lit > 0 ? T : F; 
        dec_lvl[abs(learned_lit)] = back_lvl;
        parent_cls[abs(learned_lit)] = learn_cls_nxtidx;
        learn_cls_nxtidx ++; 
        curr_lvl = back_lvl;
  
        //printf("Change VTT Var(%d) to %d\n", dec_var[back_lvl], var_truth_table[dec_var[back_lvl]]);
        printf("Back to learn lvl %d - Var %d\n", back_lvl, dec_var[back_lvl]);
        state = PROP; 
        break; 
        */

      case SOLVED:
        printf("Solved\n");
        /*
        for (int i = 0; i < NUM_VARS; i++){
            result[i] = var_truth_table[i];
        }*/
        result[0] = 1;
        state = EXIT;
        break; 

      case FAILED:
        printf("Failed to solve the problem. \n");
        result[0] = 0;
        state = EXIT; 
        break;
    }//end of sw
  }//end of while



  satisfiable = unsatisfiable ? 0 : 1; 

  printf("SAT result: %d\n", satisfiable);
  printf("unSAT result: %d\n", unsatisfiable);

  result[0] = satisfiable;

}
