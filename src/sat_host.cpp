#include <iostream>
#include <string>
#include <chrono>
#include <fstream>
#include <assert.h>

#define NUM_TEST 10
#define NUM_CLAUSES 1065
#define NUM_VARS 250
#define BUF_SIZE 20

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
  int *c1 = (int *)malloc(sizeof(int) * NUM_CLAUSES);
  int *c2 = (int *)malloc(sizeof(int) * NUM_CLAUSES);
  int *c3 = (int *)malloc(sizeof(int) * NUM_CLAUSES);
  int *max_size = (int *)malloc(sizeof(int) * 1); 
 
  int *result = (int *)malloc(sizeof(int));

  if (argc < 2) {
    cout << "Usage: ./a.out <data path>" << endl;
    return 0;
  }

#ifdef MCC_ACC
  __merlin_init(argv[argc-1]);
#endif

  //string path(argv[1]);

  // Prepare data
  //std::string test_file="test"+to_string(test_idx);
//  for (int i = 1; i <= NUM_TEST; ++i) { 
    int i = 1; 
    auto ts1=std::chrono::high_resolution_clock::now(); 
    std::string first("./data/uf250/tests/uf50-0");
//    std::string first("./data/UUF50.218.1000/uuf50-0");
    std::string f_end(".cnf");
    //istd::string fileName=first+test_file+end;
    std::string fileName=first+std::to_string(i)+f_end;
    read_clause_file(fileName, c1, c2, c3, max_size, NUM_VARS, NUM_CLAUSES);
    int extra_buf_size = max_size[0] - BUF_SIZE;
    // cout << "Clause :"<< c1[0] << " " << c2[0]<< " " <<c3[0] << endl; 
    auto ts2 = std::chrono::high_resolution_clock::now();
    std::chrono::duration<double> readtime = ts2 -ts1; 
    wf<<"TestCase: " << fileName <<endl;  
    wf << "Time (Read file) : " << readtime.count() <<endl;

#ifdef MCC_ACC
    __merlin_solver_kernel(c1, c2, c3, result); 
#else
    solver_kernel(c1, c2, c3, result);
#endif

    auto ts3 = std::chrono::high_resolution_clock::now();
    std::chrono::duration<double> readtime2 = ts3 -ts2; 
    wf << "Time(Kernel) : " << readtime2.count() << endl; 
    if (result[0] == 0){
        cout<< "Failed"<<endl;
        assert(0);
    }else{
        cout << "Succeed" << endl; 
    }
//}    

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
