'''
Author: Eunice Jun (@emjun)
Date created: November, 4, 2019 
Purpose: Transform a wide format dataset into long format
Use: python3 longify.py <data_in_wide_format.csv>
'''
import sys
import csv
import pandas as pd 

if __name__ == "__main__":
    if len(sys.argv) != 2: 
        print("Misusing script. Must include EXACTLY ONE parameter: python3 longify.py <data_in_wide_format.csv>")
    elif not sys.argv[1].endswith('.csv'): 
        print("Data file must be a CSV file!")
    else:
        wide_csv = sys.argv[1]
        wide_df = pd.read_csv(wide_csv)
        # long_df = pd.wide_to_long(wide_df, stubnames='Score', i=None, j='ID')
        cols_to_collapse = ['AR', 'TV']
        result_col = 'Score'
        
        import pdb; pdb.set_trace()
        long_df.to_csv()


