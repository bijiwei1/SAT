#include <string.h>
#include <math.h>
#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
//#include <string> 
//using namespace std; 

#define NUM_CLAUSES 1065  
#define NUM_VARS 250

#pragma ACCEL kernel
void solver_kernel(
        int* c1, int* c2, int* c3, int* result){

#pragma ACCEL interface variable=c1 bus_bitwidth=512 depth = 1065
#pragma ACCEL interface variable=c2 bus_bitwidth=512 depth = 1065
#pragma ACCEL interface variable=c3 bus_bitwidth=512 depth = 1065
#pragma ACCEL interface variable=result depth=1 

  int satisfiable; 
  int unsatisfiable = 0; 
  int local_clauses[NUM_CLAUSES][3];
  char var_truth_table[NUM_VARS]; // T, F, U (Undef) 

  //initialize buffer  
  #pragma ACCEL parallel
  for (int x = 1; x < NUM_VARS; x++){
    var_truth_table[x] = 'U';
  }
  var_truth_table[3] = 'F';
  var_truth_table[42] = 'T';
  var_truth_table[48] = 'T';


  //Load data
  printf("Start to load data \n");
  for (int x = 0; x < NUM_CLAUSES; ++x) {
    local_clauses[x][0] = c1[x];
    local_clauses[x][1] = c2[x];
    local_clauses[x][2] = c3[x];
  }

  #pragma ACCEL parallel flatten 
  for (int x = 0; x < NUM_CLAUSES; x++){ 
    int l0_unsat =  (local_clauses[x][0] > 0) ? var_truth_table[local_clauses[x][0]] == 'F' :   var_truth_table[-local_clauses[x][0]] == 'T';
    int l1_unsat =  (local_clauses[x][1] > 0) ? var_truth_table[local_clauses[x][1]] == 'F' :   var_truth_table[-local_clauses[x][1]] == 'T';
    int l2_unsat =  (local_clauses[x][2] > 0) ? var_truth_table[local_clauses[x][2]] == 'F' :   var_truth_table[-local_clauses[x][2]] == 'T';
    unsatisfiable |= l0_unsat & l1_unsat & l2_unsat; 
  }

  satisfiable = ~unsatisfiable; 

  printf("SAT result: %d\n", satisfiable);
  printf("unSAT result: %d\n", unsatisfiable);


  result[0] = satisfiable;

}
