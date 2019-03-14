import tea
import os

base_url = 'https://homes.cs.washington.edu/~emjun/tea-lang/datasets/'
uscrime_data_path = None

def test_load_data():
    global base_url, uscrime_data_path

    csv_name = 'UScrime.csv'
    csv_url = os.path.join(base_url, csv_name)
    uscrime_data_path = tea.download_data(csv_url, 'UScrime')

def test_indep_t_test():
    global uscrime_data_path
    # uscrime_data_path = "/Users/emjun/.tea/data/UScrime.csv"

    # Declare and annotate the variables of interest
    variables = [
        {
            'name' : 'So',
            'data type' : 'nominal',
            'categories' : ['0', '1']
        },
        {
            'name' : 'Prob',
            'data type' : 'ratio',
            'range' : [0,1]
        }
    ]
    experimental_design = {
                            'study type': 'observational study',
                            'contributor variables': 'So',
                            'outcome variables': 'Prob',
                        }
    assumptions = {
        'Type I (False Positive) Error Rate': 0.05
    }

    tea.data(uscrime_data_path)
    tea.define_variables(variables)
    tea.define_study_design(experimental_design) # Allows for using multiple study designs for the same dataset (could lead to phishing but also practical for saving analyses and reusing as many parts of analyses as possible)
    tea.assume(assumptions)

    tea.hypothesize(['So', 'Prob'])
    import pdb; pdb.set_trace()

def test_get_props():
    variables = [
        {
            'name' : 'So',
            'data type' : 'nominal',
            'categories' : ['0', '1']
        },
        {
            'name' : 'Prob',
            'data type' : 'ratio',
            'range' : [0,1]
        }
    ]
    experimental_design = {
                            'study type': 'observational study',
                            'contributor variables': 'So',
                            'outcome variables': 'Prob',
                        }
    assumptions = {
        'Type I (False Positive) Error Rate': 0.05
    }

    tea.define_variables(variables)
    tea.define_study_design(experimental_design) # Allows for using multiple study designs for the same dataset (could lead to phishing but also practical for saving analyses and reusing as many parts of analyses as possible)
    tea.assume(assumptions)

    tea.divine_properties(vars=['So', 'Prob'], tests=['students_t', 'chi_square'])
    
    import pdb; pdb.set_trace()
    









    ## IMPORTANT:
    # The above example from the tutorial does not explicate all the assumptions. 
    # We find that t-test is not appropriate because both groups are not normally distributed, 
    # but this is not discussed in the tutorial. This shows us potential for Tea to be used as 
    # a validation and learning tool.

    ## TODO: What happens if we had the assumptions?
    # --> May need to query the solver twice:
    # 1. With only data computed propertie
    # 2. With assumptions


    # Can always redefine experimental design 
    # tea.define_study_design(experimental_design)


# def test_dep_t_test():
#     global uscrime_data_path
#     variables = [
#         {
#             'name' : 'So',
#             'data type' : 'nominal',
#             'categories' : ['0', '1']
#         },
#         {
#             'name' : 'Prob',
#             'data type' : 'ratio',
#             'range' : [0,1]
#         },
#         {
#             'name' : 'U1',
#             'data type' : 'ratio'
#         },
#         {
#             'name': 'U2',
#             'data type' : 'ratio'
#         }
#     ]
#     experimental_design = {
#                             'study type': 'observational study',
#                             'contributor variables': ['So', 'U1', 'U2'],
#                             'outcome variables': 'Prob',
#                         }
#     assumptions = {
#         'Type I (False Positive) Error Rate': 0.05
#     }

#     tea.data(uscrime_data_path)
#     tea.define_variables(variables)
#     tea.define_study_design(experimental_design) # Allows for using multiple study designs for the same dataset (could lead to phishing but also practical for saving analyses and reusing as many parts of analyses as possible)
#     tea.assume(assumptions)
#     tea.hypothesize(['U1', 'U2']) # true hypothesis, false hypo.
#     # tea.hypothesize(['U1', 'U2'], alternative='U1 > 1.2*U2', null='U1 <= 1.2*U2') # true hypothesis, false hypo.
#     # output: P(D |H0), what is null hypothesis that we tested

#     # Test sample size
#     # Test values of tests

# # Wilcoxon rank sum test AKA Mann Whitney U
# # def 




# ## ADD TO PAPER
# # What happens when have no participant_id?
# # --> ask for key
# # ---> if there is no key, assume that each row is a separate/unique participant/observation 
# # --> May want to surface this assumption to the user....
