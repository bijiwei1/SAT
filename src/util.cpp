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

/*
  int bound1 = 14;
  int bound2 = 11; 
  std::vector<int> v1, v2, v3;
  for (int i = 1; i < num_var; i++){
    if (max_cls_size[i] > bound1){
      v1.push_back(i);
    }else if (max_cls_size[3] >= bound2){
      v2.push_back(i); 
    }else{
      v3.push_back(i);
    }
  }

  int new_idx = 1; 
  printf("Vector Size: %d, %d, %d\n", v1.size(), v2.size(), v3.size());
  for (int i = 0; i < v1.size(); i++){
    int curr_idx = v1.at(i); 
    for (int j = 1; j < num_clauses; j++){
      if (c1_local[j] == curr_idx){
        c1[j] = new_idx; 
      }else if (c1_local[j] == -curr_idx){
        c1[j] = -new_idx;
      }

      if (c2_local[j] == curr_idx){
        c2[j] = new_idx; 
      }else if (c2_local[j] == -curr_idx){
        c2[j] = -new_idx;
      }

      if (c3_local[j] == curr_idx){
        c3[j] = new_idx; 
      }else if (c3_local[j] == -curr_idx){
        c3[j] = -new_idx;
      }
    }
    new_idx ++; 
  }

  for (int i = 0; i < v2.size(); i++){
    int curr_idx = v2.at(i); 
    for (int j = 1; j < num_clauses; j++){
      if (c1_local[j] == curr_idx){
        c1[j] = new_idx; 
      }else if (c1_local[j] == -curr_idx){
        c1[j] = -new_idx;
      }

      if (c2_local[j] == curr_idx){
        c2[j] = new_idx; 
      }else if (c2_local[j] == -curr_idx){
        c2[j] = -new_idx;
      }

      if (c3_local[j] == curr_idx){
        c3[j] = new_idx; 
      }else if (c3_local[j] == -curr_idx){
        c3[j] = -new_idx;
      }
    }
    new_idx ++; 
  }

  for (int i = 0; i < v3.size(); i++){
    int curr_idx = v3.at(i); 
    for (int j = 1; j < num_clauses; j++){
      if (c1_local[j] == curr_idx){
        c1[j] = new_idx; 
      }else if (c1_local[j] == -curr_idx){
        c1[j] = -new_idx;
      }

      if (c2_local[j] == curr_idx){
        c2[j] = new_idx; 
      }else if (c2_local[j] == -curr_idx){
        c2[j] = -new_idx;
      }

      if (c3_local[j] == curr_idx){
        c3[j] = new_idx; 
      }else if (c3_local[j] == -curr_idx){
        c3[j] = -new_idx;
      }
    }
    new_idx ++; 
  }*/

  cout << "Number of clauses : " << cnt << endl << "Finish reading file" << endl;

  f.close();
  return ;
}
