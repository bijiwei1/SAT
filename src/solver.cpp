#include <string.h>
#include <math.h>
#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
//#include <string> 
//using namespace std; 

#define NUM_CLAUSES 218  
#define NUM_VARS 51

<<<<<<< HEAD
=======
#define BUF_SIZE 20
#define BUF_LEARN 40
#define extra_buf_size 50

#define F 2
#define T 1
#define Undef 0

#define SOLVED 0
#define DECISION 1
#define PROP 2
#define DEDUCTION 3
#define BACKTRACK 4 
#define FAILED 5
#define EXIT 6

#define DEC 1
#define DED 0

#define EMPTY -1

void collect_buffer(int pos_cls[NUM_VARS][BUF_SIZE], int neg_cls[NUM_VARS][BUF_SIZE], 
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
}

>>>>>>> a7e71934e3db5489ccd38b120377f844d9267e31
#pragma ACCEL kernel
void solver_kernel(
        int* c1, int* c2, int* c3, int* result){

<<<<<<< HEAD

#pragma ACCEL interface variable=c1 bus_bitwidth=512 depth = 1065
#pragma ACCEL interface variable=c2 bus_bitwidth=512 depth = 1065
#pragma ACCEL interface variable=c3 bus_bitwidth=512 depth = 1065
=======
#pragma ACCEL interface variable=c1 bus_bitwidth=512 depth = 1065
#pragma ACCEL interface variable=c2 bus_bitwidth=512 depth = 1065
#pragma ACCEL interface variable=c3 bus_bitwidth=512 depth = 1065


/*
#pragma ACCEL interface variable=c1 depth = 70
#pragma ACCEL interface variable=c2 depth = 70
#pragma ACCEL interface variable=c3 depth = 70
*/

//#pragma ACCEL interface variable=num_pos_cls bus_bitwidth=512 depth = 1065
//#pragma ACCEL interface variable=num_neg_cls bus_bitwidth=512 depth = 1065  

#pragma ACCEL interface variable=result depth=1 
>>>>>>> a7e71934e3db5489ccd38b120377f844d9267e31

  int satisfiable; 
  int unsatisfiable = 0; 
  const int local_clauses[NUM_CLAUSES][3];

<<<<<<< HEAD
  char var_truth_table[NUM_VARS]; // T, F, U (Undef) 

  //initialize buffer  
  #pragma ACCEL parallel
  for (int x = 1; x < NUM_VARS; x++){
    var_truth_table[x] = 'U';
  }

  //Load data
  printf("Start to load data \n");
=======
  int var_truth_table[NUM_VARS] = {0};
 
  int extra_cls[extra_buf_size] = {0}; 
  int extra_lit[extra_buf_size] = {0}; 
  int num_extra[1] = {0}; 

  bool conflict[BUF_SIZE];
  bool extra_conflict[extra_buf_size] = {0}; 
  bool total_conflict = 0; 

  int state = DECISION; 
 
  int assigned_stack[NUM_VARS] = {0};  //default to be 0 
  bool dec_ded_type[NUM_VARS] = {0}; 
  bool TFchecked[NUM_VARS] = {0}; //1: if we assigned both True and False to variables
  int stack_endptr = -1 ; 
  int ded_currptr = -1; 
  int dec_currptr = -1;

  int new_var_idx = 1; // We make decision (T/F) on this var idx 

  int l_ded[BUF_SIZE]; // > 0, assigned to T, < 0 assigned to F
  int extra_l_ded[extra_buf_size]; 

  int prev_state= DECISION;

  int learnt_clauses[BUF_LEARN][3]; 

  //initialize buffer  
  
  #pragma ACCEL parallel 
  for (int x = 1; x< NUM_VARS; x++){
    for (int y = 0; y< BUF_SIZE; y++){
      pos_cls[x][y] = EMPTY; 
      neg_cls[x][y] = EMPTY; 
    }
  }

  for (int x = 0; x < BUF_LEARN; x ++){
    learnt_clauses[x][0] = 0;
    learnt_clauses[x][1] = 0;
    learnt_clauses[x][2] = 0;
  }
  //#pragma ACCEL parallel 
>>>>>>> a7e71934e3db5489ccd38b120377f844d9267e31
  for (int x = 0; x < NUM_CLAUSES; ++x) {
    local_clauses[x][0] = c1[x];
    local_clauses[x][1] = c2[x];
    local_clauses[x][2] = c3[x];
<<<<<<< HEAD
=======


    collect_buffer(pos_cls, neg_cls, c1[x], x, extra_cls, extra_lit, num_extra);
    collect_buffer(pos_cls, neg_cls, c2[x], x, extra_cls, extra_lit, num_extra);
    collect_buffer(pos_cls, neg_cls, c3[x], x, extra_cls, extra_lit, num_extra);
>>>>>>> a7e71934e3db5489ccd38b120377f844d9267e31
  }

<<<<<<< HEAD
  #pragma ACCEL parallel flatten 
  for (int x = 0; x < NUM_CLAUSES; x++){ 
    int l0_unsat =  (local_clauses[x][0] > 0) ? var_truth_table[local_clauses[x][0]] == 'F' :   var_truth_table[-local_clauses[x][0]] == 'T';
    int l1_unsat =  (local_clauses[x][1] > 0) ? var_truth_table[local_clauses[x][1]] == 'F' :   var_truth_table[-local_clauses[x][1]] == 'T';
    int l2_unsat =  (local_clauses[x][2] > 0) ? var_truth_table[local_clauses[x][2]] == 'F' :   var_truth_table[-local_clauses[x][2]] == 'T';
    unsatisfiable |= l0_unsat & l1_unsat & l2_unsat; 
  }

  satisfiable = ~not_satisfiable; 

  printf("SAT result: %d\n", satisfiable);


=======
  printf("Finish loading data \n");

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
  }*/
  //assert(0);  

  while (state != EXIT){

    switch(state){
      case DECISION:
        //printf("State = DECISION; ");
        prev_state = DECISION; 

        if (new_var_idx == NUM_VARS){
          state = SOLVED;
        }else {
          while (var_truth_table[new_var_idx] != Undef){
            //printf("Skip var %d\n", new_var_idx); 
            new_var_idx ++; 
            if (new_var_idx == NUM_VARS)
              break;
          }
        }

        if (new_var_idx == NUM_VARS){
          state = SOLVED; 
        }else {
          state = PROP;
          //printf("Decide Var(%d)\n", new_var_idx);
          if (pos_cls[new_var_idx][8] != -1){
            var_truth_table[new_var_idx] = T;
          }else {
            var_truth_table[new_var_idx] = F;
          }

          stack_endptr ++;   
          assigned_stack[stack_endptr] = new_var_idx;
          dec_ded_type[stack_endptr] = DEC;
          TFchecked[stack_endptr] = 0;

          dec_currptr = stack_endptr; 
          ded_currptr = stack_endptr;
        }
        break; 

      case PROP:
      //printf("State = PROP; ");
        total_conflict = 0; 

        int prop_var;
        if (prev_state == DECISION || prev_state == BACKTRACK){
          prop_var = new_var_idx;
          //printf("Decision Var(%d): %d\n", prop_var, var_truth_table[prop_var]);
        }else if (prev_state == DEDUCTION){
          prop_var = abs(assigned_stack[ded_currptr]);
          //printf("deduction Var(%d): %d\n", prop_var, var_truth_table[prop_var]);
        }

        /****************** Regular buffer *****************/
        #pragma ACCEL parallel 
        for (int x = 0; x < BUF_SIZE; x++){
          int l1, l2;
          conflict[x] = 0; 
          l_ded[x] = 0; 
          if(var_truth_table[prop_var] == T){
            if (neg_cls[prop_var][x] != EMPTY){
              if (local_clauses[neg_cls[prop_var][x]][0] == -prop_var){
                l1 = local_clauses[neg_cls[prop_var][x]][1];
                l2 = local_clauses[neg_cls[prop_var][x]][2];
              }else if (local_clauses[neg_cls[prop_var][x]][1] == -prop_var){
                l1 = local_clauses[neg_cls[prop_var][x]][0];
                l2 = local_clauses[neg_cls[prop_var][x]][2];
              }else{
                l1 = local_clauses[neg_cls[prop_var][x]][0];
                l2 = local_clauses[neg_cls[prop_var][x]][1];
              }
              conflict[x] = deduction(l1, l2, var_truth_table, x, l_ded);
              if (conflict[x]){
                //printf("Conflict - Cls(%d) - (%d) (%d) (-%d)\n", neg_cls[prop_var][x], l1, l2, prop_var);
              }
              if (l_ded[x]!=0){
                //printf("Found ded Var(%d)\n", l_ded[x]);
              }
            }
          }else{
            if (pos_cls[prop_var][x] != EMPTY){
              if (local_clauses[pos_cls[prop_var][x]][0] == prop_var){
                l1 = local_clauses[pos_cls[prop_var][x]][1];
                l2 = local_clauses[pos_cls[prop_var][x]][2];
              }else if (local_clauses[pos_cls[prop_var][x]][1] == prop_var){
                l1 = local_clauses[pos_cls[prop_var][x]][0];
                l2 = local_clauses[pos_cls[prop_var][x]][2];
              }else{
                l1 = local_clauses[pos_cls[prop_var][x]][0];
                l2 = local_clauses[pos_cls[prop_var][x]][1];
              } 
              conflict[x] = deduction(l1, l2, var_truth_table, x, l_ded);
               if (conflict[x]){
                //printf("Conflict - Cls(%d) - (%d) (%d) (-%d)\n", pos_cls[prop_var][x], l1, l2, prop_var);
              }
              if (l_ded[x]!=0){
                //printf("Found ded Var(%d)\n", l_ded[x]);
              }
            }
          }
        }

        //put int deduction buff
        //bool sub_conf[BUF_SIZE]; 
        #pragma ACCEL parallel flatten
        for (int x = 0; x < BUF_SIZE; x++){
          bool sub_conf[BUF_SIZE];  
          bool conf = 0; 

          
          for(int y = 0; y < BUF_SIZE; y++){
            sub_conf[y] = 0; 
            
            if (l_ded[x] != 0){
              if (l_ded[x] == -l_ded[y]){
                sub_conf[y] = 1; 
                total_conflict = 1; 
                //printf("Found conflict dedction Var(%d)\n", l_ded[x]);
              }else if(l_ded[x]==l_ded[y] && y<x){
                sub_conf[y]=1; 
                //printf("Found same dedction Var(%d)\n", l_ded[x]);
              } 
            } 
          } 

          #pragma ACCEL parallel reduction = conf
          for(int y = 0; y < BUF_SIZE; y++){
            conf |= sub_conf[y]; 
          }

          if ((conf == 0) && (l_ded[x] != 0)){
            stack_endptr ++;
            assigned_stack[stack_endptr] = l_ded[x]; 
            dec_ded_type[stack_endptr] = DED; 
            //printf("Add ded var(%d)\n", l_ded[x]);
          }
        }

        #pragma ACCEL parallel reduction = total_conflict 
        for (int x = 0; x < BUF_SIZE; x++){
          total_conflict |= conflict[x]; 
        }

        state = DEDUCTION; 
        break;

      case DEDUCTION:
        //printf("State = DEDUCTION\n"); 
        prev_state = DEDUCTION; 
        if (total_conflict){
          state = BACKTRACK; 
          //printf("Reason 1\n");
        }else if (ded_currptr == stack_endptr){
          state = DECISION; 
        }else{
          state = PROP; 
          // Check whether this is conflict with current assigned value
          #pragma ACCEL parallel flatten
          for (int i = 0; i <= NUM_VARS; i++){
            if ((i > dec_currptr) && (i <= stack_endptr)){
              if (assigned_stack[i] < 0){
                if (var_truth_table[abs(assigned_stack[i])] == T){
                  state = BACKTRACK; 
                  //printf("Reason 2\n");
                  break; 
                }else{
                  var_truth_table[abs(assigned_stack[i])] = F; 
                  //printf("Change ded Var(%d) - F\n", abs(assigned_stack[i]) );
                }
              }else {
                if (var_truth_table[abs(assigned_stack[i])] == F){
                  state = BACKTRACK; 
                  //printf("Reason 3\n");
                }else {
                  var_truth_table[abs(assigned_stack[i])] = T;  
                  //printf("Change ded Var(%d) - T\n", abs(assigned_stack[i]) );
                }
              }
            }
          }
        }

        if (state == BACKTRACK){
          //Only pop deducted variables
          #pragma ACCEL parallel flatten
          for (int i = 0; i <= NUM_VARS; i++){
            if (i > dec_currptr && i <= stack_endptr){
              var_truth_table[abs(assigned_stack[i])] = Undef; 
              //printf("Pop %d\n",assigned_stack[i]);
            }
          }
          ded_currptr = dec_currptr;
          stack_endptr = dec_currptr; 
          //printf("-> BACKTRACK\n");
        }else if(state == DECISION){
          new_var_idx ++; 
          //printf("-> Decision\n");
        }else { 
          ded_currptr ++; 
          //printf("-> PROP\n");
        }
        break;

      case BACKTRACK:
        //printf("State = BACKTRACK; ");
        prev_state = BACKTRACK; 

        while(TFchecked[stack_endptr] || dec_ded_type[stack_endptr] == DED){
          //We checked both True and False cases, we need to go back 
          var_truth_table[abs(assigned_stack[stack_endptr])] = Undef; 
          //printf("Unpop and clear var(%d)\n", abs(assigned_stack[stack_endptr]) ); 
          stack_endptr--;  
          if (stack_endptr < 0){ 
            state = FAILED; 
            break; 
          }
        }; 

        if (state != FAILED){
          state = PROP;
          new_var_idx = abs(assigned_stack[stack_endptr]); 
          dec_currptr = stack_endptr; 
          ded_currptr = stack_endptr;

          
          if (var_truth_table[new_var_idx] == T){
            var_truth_table[new_var_idx] = F;
          }else{
            var_truth_table[new_var_idx] = T;
          }
          //var_truth_table[new_var_idx] = F;
          TFchecked[stack_endptr] = 1; 
          //printf("Reassigned var(%d) -> %d\n", new_var_idx, var_truth_table[new_var_idx]); 
        } 
        break;

      case SOLVED:
        prev_state = SOLVED;
        satisfiable = 1;
        state = EXIT; 
        printf("Finish kernel - Solved\n");
        break;

      case FAILED: 
        prev_state = FAILED;
        satisfiable = 0; 
        state = EXIT; 
        printf("Finish kernel - Failed\n");
        break;
    }  

    //propogate
  }

  result[0] = satisfiable; 

>>>>>>> a7e71934e3db5489ccd38b120377f844d9267e31
}