#include <stdio.h>
#include <stdlib.h>
#include <limits.h>
#include <iostream>
#include <vector>
#include <fstream>
#include <algorithm>
#include <sstream>

#include <bits/stdc++.h> 
using namespace std; 

using std::vector;
using std::cout;
using std::endl;
using std::ifstream;
using std::ios;
using std::string;
using std::sort;
using std::istringstream;


void read_clause_file(string filename, int *c1, int *c2, int *c3, int *max_size, 
  const int num_var, const int num_clauses){

  ifstream f;
  int l1, l2, l3; 
  int max_cls_size[num_var]; 
  int *c1_local = (int *)malloc(sizeof(int) * num_clauses);
  int *c2_local = (int *)malloc(sizeof(int) * num_clauses);
  int *c3_local = (int *)malloc(sizeof(int) * num_clauses); 

  for (int i = 0; i < num_var; i ++)
    max_cls_size[i] = 0; 

 
  f.open(filename.c_str(), ios::in);
  if (!f.is_open()) {
    cout << "Open " << filename << " failed" << endl;
    exit(1);
  }

  int cnt = 0;
  cout << "Start to read file" <<endl; 
  string line;
  while (std::getline(f, line)) {
    if (line == "")
      continue;
    if (cnt == num_clauses)
      break;
    
    if (line.at(0) != 'p' and line.at(0) != 'c') {
      vector<string> substrs;
      istringstream iss(line);
      for(string s; iss >> s;)
        substrs.push_back(s);

      if (substrs.size() < 2)
        continue;

      l1 = stoi(substrs.at(0));
      l2 = stoi(substrs.at(1));
      l3 = stoi(substrs.at(2));
      c1_local[cnt] = l1;
      c2_local[cnt] = l2;
      c3_local[cnt] = l3;

      c1[cnt] = l1;
      c2[cnt] = l2;
      c3[cnt] = l3;

      max_cls_size[abs(l1)] ++; 
      max_cls_size[abs(l2)] ++; 
      max_cls_size[abs(l3)] ++; 
      //cout << "Clause :"<< c1_local[cnt] << " " << c2_local[cnt]<< " " <<c3_local[cnt] << "\n"; 
      cnt ++; 
    }
  }

  int max = 0;
  for (int x = 1; x < num_var; x++){
    max = (max_cls_size[x] > max) ? max_cls_size[x] : max; 
  }
  max_size[0] = max; 
  cout << "Max size " << max << endl; 

  cout << "Number of clauses : " << cnt << endl << "Finish reading file" << endl;

  f.close();
  return ;
}


int find_parent_cls( uint64_t data_out4[2], uint64_t data_out5[2], int i){
  int par_cls ;
  switch(i){
    case 0: 
      par_cls = data_out4[0] & 0xffff; break;
    case 1:  
      par_cls = data_out4[0] >> 16 & 0xffff; break;
    case 2:  
      par_cls = data_out4[0] >> 32 & 0xffff; break;
    case 3:  
      par_cls = data_out4[0] >> 46 & 0xffff; break;
    case 4: 
      par_cls = data_out4[1] & 0xffff; break;
    case 5:  
      par_cls = data_out4[1] >> 16 & 0xffff; break;
    case 6:  
      par_cls = data_out4[1] >> 32 & 0xffff; break;
    case 7:  
      par_cls = data_out4[1] >> 46 & 0xffff; break;

    case 8: 
      par_cls = data_out5[0] & 0xffff; break;
    case 9:  
      par_cls = data_out5[0] >> 16 & 0xffff; break;
    case 10:  
      par_cls = data_out5[0] >> 32 & 0xffff; break;
    case 11:  
      par_cls = data_out5[0] >> 46 & 0xffff; break;
    case 12: 
      par_cls = data_out5[1] & 0xffff; break;
    case 13:  
      par_cls = data_out5[1] >> 16 & 0xffff; break;
    case 14:  
      par_cls = data_out5[1] >> 32 & 0xffff; break;
    case 15:  
      par_cls = data_out5[1] >> 46 & 0xffff; break;
    default:
        assert(0);
  }
  return par_cls; 

}