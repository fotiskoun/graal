import csv
import datetime
import pandas

def to_integer(dt_time):
    return 10000*dt_time.year + 100*dt_time.month + dt_time.day

table = pandas.read_table('lineitem.tbl', delimiter="|", header = None)
table = table.sort_values([6, 4, 10, 5], ascending=True)
table.drop([16], axis = 'columns', inplace=True)
# print(table.head())

listoflists = table.values.tolist()

with open("tpch6SortedLineitemDQSE140MB.tbl", "w") as ef:
    for innerList in listoflists:
    	ef.write("|".join(str(x) for x in innerList))
    	ef.write("\n")

