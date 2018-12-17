import csv
import pdb

with open('./data/motivation2.csv') as readfile: 
     reader = csv.reader(readfile, delimiter=',')
     #     data = []
     #for row in reader:
     #    pdb.set_trace()
     #    data += row     

     print(list(reader))
