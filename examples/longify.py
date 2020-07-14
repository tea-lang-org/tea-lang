"""
Author: Eunice Jun (@emjun)
Last updated: Feb 4, 2020
Purpose: Transform a wide format dataset into long format for AR_TV/ar_tv.csv; Could be adapted for future datasets
Use: python3 longify.py <data_in_wide_format.csv>
"""
import sys
import csv
import pandas as pd

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Misusing script. Must include EXACTLY ONE parameter: python3 longify.py <data_in_wide_format.csv>")
    elif not sys.argv[1].endswith(".csv"):
        print("Data file must be a CSV file!")
    else:
        wide_csv = sys.argv[1]
        wide_df = pd.read_csv(wide_csv, header=0)
        long_df = pd.DataFrame(columns=["ID", "Condition", "Score"])

        for label, val in wide_df.iterrows():
            long_df = long_df.append({"ID": val["ID"], "Condition": "AR", "Score": val["AR"]}, ignore_index=True)
            long_df = long_df.append({"ID": val["ID"], "Condition": "TV", "Score": val["TV"]}, ignore_index=True)

        long_df.to_csv("ar_tv_long.csv")
