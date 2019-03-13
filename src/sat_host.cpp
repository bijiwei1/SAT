#include <iostream>
#include <string>
#include <chrono>
#include <fstream>
#include <assert.h>

#include <config.h>

using std::cout;
using std::endl;
using std::string;
using std::to_string;

#ifdef MCC_ACC
#include MCC_ACC_H_FILE
#else
void solver_kernel(int* c1, int* c2, int* c3, int* result);
#endif

// Util functions for host
void read_clause_file(string filename, int *c1, int *c2, int *c3,  int *max_size, 
  const int num_var, const int num_clauses); 


int main(int argc, char **argv) {

  //initialize timer
  auto start = std::chrono::high_resolution_clock::now();
  std::ofstream wf;
  wf.open("time.txt");
  int *c1 = (int *)malloc(sizeof(int) * NUM_ORG_CLAUSES);
  int *c2 = (int *)malloc(sizeof(int) * NUM_ORG_CLAUSES);
  int *c3 = (int *)malloc(sizeof(int) * NUM_ORG_CLAUSES);

  int *data_in1 = (int *)malloc(sizeof(int));
  int *data_in2 = (int *)malloc(sizeof(int));
  int *data_in3 = (int *)malloc(sizeof(int));

  uint64_t *data_out1 = (int *)malloc(sizeof(int)*2);
  uint64_t *data_out2 = (int *)malloc(sizeof(int)*2);
  uint64_t *data_out3 = (int *)malloc(sizeof(int)*2);
  uint64_t *data_out4 = (int *)malloc(sizeof(int)*2);
  uint64_t *data_out5 = (int *)malloc(sizeof(int)*2);



  int *max_size = (int *)malloc(sizeof(int) * 1); 
 
  int *result = (int *)malloc(sizeof(int)*NUM_VARS);

  if (argc < 2) {
    cout << "Usage: ./a.out <data path>" << endl;
    return 0;
  }

  //string path(argv[1]);

  // Prepare data
  //std::string test_file="test"+to_string(test_idx);
  //for (int i = 1; i <= NUM_TEST; ++i) { 
  //for (int i = 1; i <= 5; ++i) { 
    int i = 5;
    auto ts1=std::chrono::high_resolution_clock::now(); 
    std::string first("../benchmark/uf50-218/uf50-0");
    //std::string first("./data/uuf250/tests/uuf250-0");
    std::string f_end(".cnf");
    //istd::string fileName=first+test_file+end;
    std::string fileName=first+std::to_string(i)+f_end;
    read_clause_file(fileName, c1, c2, c3, max_size, NUM_VARS, NUM_ORG_CLAUSES);
    //for (int i = 0; i < NUM_ORG_CLAUSES; i++){cout << "Clause :"<< c1[i] << " " << c2[i]<< " " <<c3[i] << endl; }
    auto ts2 = std::chrono::high_resolution_clock::now();
    std::chrono::duration<double> readtime = ts2 -ts1; 
    wf<<"TestCase: " << fileName <<endl;  
    wf << "Time (Read file) : " << readtime.count() <<endl;

    vector<int> clauses[10000]; 
    int clauses_idx[NUM_PE *NUM_CLAUSES_PE]; //Only variable idx, If no var, => 255 

    bool var_ismarked[NUM_VARS] ={0};
    bool var_ischecked[NUM_VARS] = {0}; 
    int var_parents_cls[NUM_VARS] = {-1}; 
    //vector<int> var_parents[NUM_VARS];
    //int dec_lvl[NUM_VARS] = {-1};
    //int dec_var[BUF_DEC_LVL]= {0}; // Variable idx at each decision lvl, we assume at most 100 decision level
    //uint8_t assigned_stack[NUM_VARS] = {IDLE_VAR}; 
    vector<int> assigned_stack; // {var_idx, is_dec} 


    int state = DECISION; 
    int prev_state = DECISION; 
    int new_var_idx = 1;
    int mode = 0; 
    int load_cls_num = 0;

    //Temporary variabels
    bool conf_ded; //PROP
    int prev_assigned_value; // BACKTRACK

    for (int i = 0; i < NUM_ORG_CLAUSES; i++){
      clauses[i].push_back(c1[i]);
      clauses[i].push_back(c2[i]);
      clauses[i].push_back(c3[i]);
    }

    while (state != EXIT){
    switch(state){

      case INIT_Kernel: 
        mode = INIT;
        state = PROP; 
        break; 

      case LOAD: 
        mode = LOAD; 
        if (load_cls_num >= NUM_ORG_CLAUSES){
          state = DECISION; 
        }else{
          state = PROP;
          data_in1[0] = (abs(c1[load_cls_num])) | (abs(c2[load_cls_num]) << 8) | (abs(c3[load_cls_num]) << 16);
          data_in2[0] = (c1[load_cls_num] > 0 ? POS : NEG) |
                       ((c2[load_cls_num] > 0 ? POS : NEG) << 1) | ((c3[load_cls_num] > 0 ? POS : NEG) << 2);
        }

      case DECISION: 
        mode = DECISION; 
        while (var_truth_table[new_var_idx] != U && new_var_idx < NUM_VARS){
          //printf("Skip var %d(Value - %d)\n", new_var_idx, var_truth_table[new_var_idx]); 
          new_var_idx ++; 
        } 
        
        if (new_var_idx == NUM_VARS){
          state = SOLVED; 
        }else {
          state = PROP;
          curr_lvl ++; 
          printf("Decide Var(%d) - at lvl %d\n", new_var_idx, curr_lvl);

          var_truth_table[new_var_idx] = T; //assigne to T
          //dec_lvl[new_var_idx] = curr_lvl; 
          //dec_var[curr_lvl] = new_var_idx; 
          //assigned_stack[num_assigned] = new_var_idx;
          assigned_stack.push_back( new_var_idx<<1 & 1);
          data_in1[0] = T | (new_var_idx << 1) | (curr_lvl << 9);
        }
        state = PROP;
        break;

      case PROP: 
      /*
       *  data_in1(32), data_in2(32), 
       *  data_out1(64)
       *  INIT: data_in1 = {c3, c2, c1} // each 8 bit var idx, 
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
        solver_kernel(mode, data_in1, data_in2, 
            data_out1, data_out2, data_out3, data_out4);

        if (mode == INIT){

        }else if (mode == LOAD){
          state = LOAD; 
          clauses_idx[data_out1] = load_cls_num;
          load_cls_num ++; 
        }else if ((data_out1[0] & 1) == 1){
          //Conflict
          state = BACKTRACK;
        }else{
          //Not found conflict 
          int var, parent_cls, global_cls;

          for (int i = 0; i <= size; i ++){
            if (i < 8){
              var = (data_out2[0] >> i*8) & 0xff;
            }else{
              var = (data_out2[1] >> i*8) & 0xff;
            }
            parent_cls = find_parent_cls(data_out4[2], data_out5[2], i);

            var_truth_table[var] = (data_out1[1] >> i) & 0x1;
            var_parents_cls[var] = parent_cls; 
            global_cls = clauses_idx[parent_cls]; 
          }
         

          state = DECISION; 
          
        }
        break;

      case BACKTRACK: 
        //printf("State = BACKTRACK_DEC; ");
        back_lvl = curr_lvl; 
        prev_state = BACKTRACK_DEC;

        int curr_var_info = assigned_stack.back(); 
        assigned_stack.pop_back();
        int curr_var = curr_var_info >> 1; 
        while(curr_var_info&0x1 == 0 || var_ischecked[curr_var]){
          if (assigned_stack.empty()){
            back_lvl = -1;
            break;
          }
          //Undo assignment
          var_truth_table[curr_var] = U;
          var_ischecked[curr_var] = 0; 
          curr_var_info = assigned_stack.back(); 
          assigned_stack.pop_back();
          curr_var = curr_var_info >> 1; 
        }

        if (back_lvl < 0){
          printf("Failed at lvl %d\n", back_lvl);
          state = FAILED; 
          break;
        }

        printf("Back to lvl %d - Var %d\n", back_lvl, dec_var[back_lvl]);
        new_var_idx = curr_var; 
        var_truth_table[new_var_idx] = (var_truth_table[new_var_idx] == T) ? F : T;
        var_ischecked[new_var_idx] = 1; 
        int tmp = var_truth_table[new_var_idx] | (new_var_idx << 1);
        assigned_stack.push_back(tmp);
        printf("Change VTT Var(%d) to %d\n", dec_var[back_lvl], var_truth_table[dec_var[back_lvl]]);
        curr_lvl = back_lvl; 

        state = PROP;
        data_in1[0] = tmp;
        data_in2[0] = curr_lvl; 
        break;

      case SOLVED:
        printf("Solved\n");
        /*
        for (int i = 0; i < NUM_VARS; i++){
            result[i] = var_truth_table[i];
        }*/
        state = EXIT;
        break; 

      case FAILED:
        printf("Failed to solve the problem. \n");
        state = EXIT; 
        break;
    }//end of sw


  }

    auto ts3 = std::chrono::high_resolution_clock::now();
    std::chrono::duration<double> readtime2 = ts3 -ts2; 
    wf << "Time(Kernel) : " << readtime2.count() << endl; 
    if (result[0] == 0){
        cout<< "Failed"<<endl;
        assert(0);
    }else{
        cout << "Succeed" << endl; 
    }
//}//Comment this out for testing

#ifdef MCC_ACC
    __merlin_release();
#endif
  auto end=std::chrono::high_resolution_clock::now();
  std::chrono::duration<double> total=end-start;
  cout<< "Time(total) : "<<total.count() <<endl;
  free(c1);
  free(c2);
  free(c3);
  return 0;
}
