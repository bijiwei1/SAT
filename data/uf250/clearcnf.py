#!/usr/bin/env python
import os

for file in os.listdir("."):
	if ".cnf" in file: 
		f = open( file, "r" )
		lines = f.readlines()
		f.close()
		f = open( file, "w" )

		found = False
		for line in lines:
			if "%" in line:
				found = True
			elif not found:
				f.write(line) 
					
		f.close()
