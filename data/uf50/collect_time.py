#!/usr/bin/env python
import os

f = open("time.rpt", "w")
exe = './minisat'

total_time = 0.0;
for file in os.listdir("./rpt"):
	f_rpt = open("./rpt/"+ file, "r" )
	lines = f_rpt.readlines()

	for line in lines:
		if "CPU time " in line:
			time=line.split(":")[1].split("s")[0]
			time_str = ''.join(time)
			time_str.replace(" ", "")
			time_str.replace("\n", "")
			f.write(time_str+"\n")
			total_time += float(time_str)

f.write("Total Time is " + str(total_time))
	