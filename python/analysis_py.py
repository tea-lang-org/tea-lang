import pdb 
import os 
import sys
import csv
import numpy as np
import statsmodels.api as sm
import statsmodels.formula.api as smf

# There are sooo many libraries that do similar tests. 
# They just have slightly different implementations/defaults/needs for data layout

# GLOBALS
MAIN_CSV = ''
COLUMN_NAMES = [] # store column_names in an array that can access later
data_store = [] # store data as a 1 

# NAIVE way is to read the csv each time. 
# SMARTER way is to store the data and then access as/when needed

def omit_data():
    pass

def read_data(): 
    global COLUMN_NAMES, data_store

    with open(MAIN_CSV) as readfile:
        reader = csv.reader(readfile, delimiter=",")
        COLUMN_NAMES = next(reader) 

        for row in reader:
            data_store += row


def participant_summary():
    sn_id = COLUMN_NAMES.index('study_name')
    age_id = COLUMN_NAMES.index('age')
    gender_id = COLUMN_NAMES.index('gender')
    indices = [sn_id, age_id, gender_id]

    studies = []
    age = []
    gender = []
    demographics = [studies, age, gender]
    i = 0
    while i < (len(data_store)/len(COLUMN_NAMES)):

        for id in range(len(indices)):
            index  = i*len(COLUMN_NAMES) + (indices[id])
            try:
                demographics[id].append(int(data_store[index]))
            except:
                demographics[id].append(data_store[index])
        i+=1

    print('Visual Preferences count: ' + str(demographics[0].count('aesthetics')))
    print('Thinking Style count: ' + str(demographics[0].count('analytic_test_2')))
    print('Color Perception count: ' + str(demographics[0].count('color-age')))

    # pdb.set_trace()
    # print('Average age: ' + str(np.mean(demographics[1])))
    print('Male: ' + str(demographics[2].count(0)))
    print('Female: ' + str(demographics[2].count(1)))
        # pdb.set_trace()




    # with open(MAIN_CSV) as readfile:
    #     reader = csv.DictReader(readfile, delimiter=",")
    #     COLUMN_NAMES = reader.fieldnames

    #     study_name = []
    #     age = []
    #     gender = []
    #     for row in reader:
    #         study_name.append(row['study_name'])
    #         age.append(row['age'])
    #         gender.append(row['gender'])

    #     print('Visual Preferences count: ' + str(study_name.count('aesthetics')))
    #     print('Thinking Style count: ' + str(study_name.count('analytic_test_2')))
    #     print('Color Perception count: ' + str(study_name.count('color-age')))

    #     print('Average age: ')
    #     pdb.set_trace()

def get_data(col_name):
    id = COLUMN_NAMES.index(col_name)

    data = []
    i = 0
    while i < (len(data_store)/len(COLUMN_NAMES)):

        index  = i*len(COLUMN_NAMES) + id
        try:
            data.append(int(data_store[index]))
        except:
            if (data_store[index]):
                data.append(data_store[index])
        i+=1
    
    return data


# RQ 1
def motivation_corr():
    bored = get_data('data_bored')
    compare = get_data('data_compare')
    fun = get_data('data_fun')
    science = get_data('data_science')
    selfLearn = get_data('data_selfLearn')
    age = get_data('age')
    #somehow exclude data

    # OMITTING DATA/MISSING DATA IS HARD TO DEAL WITH 
    # TOOLS RELY ON INPUT DATA BEING CLEAN, if not, omitting data is hard to deal with
    np.corrcoef([[]] + bored + compare + fun + science + selfLearn + age, rowvar=True)

# RQ 2
def self_selection():
    bored = get_data('data_bored')
    compare = get_data('data_compare')
    fun = get_data('data_fun')
    science = get_data('data_science')
    selfLearn = get_data('data_selfLearn')
    age = get_data('age')
    aesthetics = get_data('aesthetics')
    thinking = get_data('thinking')
    color = get_data('colorage')
    pdb.set_trace()
    data = [[]] + bored + compare + fun + science + selfLearn + age + aesthetics + thinking + color
    #patsy.PatsyError: Error evaluating factor: TypeError: list indices must be integers or slices, not str
    # aesthetics ~ bored + compare + fun  + science + selfLearn + age
    # Types but not really data types! (problem with missing data)

    results = smf.ols('aesthetics ~ bored + compare + fun  + science + selfLearn + age', data=data).fit()
    # There are so many regression models to choose from!!!
    print(results.summary())

def main():
    read_data()
    participant_summary()
    # motivation_corr()
    self_selection()


if __name__ == '__main__':
    args = sys.argv
    MAIN_CSV = args[1] # CSV file
    main()



### MAIN OBSERVATIONS
# - How to run the analyses/script -- from terminal as program
#      - R:Python::R Studio: jupyter notebook
# - Difficult to delete/omit data from the dataset with discretion
####