#!/usr/bin/env python
import os

f = open("run_all", "w")
exe = './minisat'

i = 0;
for file in os.listdir("."):
	if ".cnf" in file: 
		i = i+1
		f.write(exe + " " + file+" > ./rpt/console_"+str(i)+".rpt\n")
