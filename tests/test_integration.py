import pandas as pd

import tea
import os

base_url = 'https://homes.cs.washington.edu/~emjun/tea-lang/datasets/'
file_names = ['UScrime.csv', 'statex77.csv', 'catsData.csv', 'cholesterol.csv', 'soya.csv', 'co2.csv', 'exam.csv', 'liar.csv',
              'pbcorr.csv', 'spiderLong_within.csv', 'drug.csv', 'alcohol.csv', 'ecstasy.csv', 'gogglesData.csv', 'gogglesData_dummy.csv']
data_paths = [None] * len(file_names)


def load_data():
    global base_url, data_paths, file_names
    global drug_path

    for i in range(len(data_paths)):
        csv_name = file_names[i]

        csv_url = os.path.join(base_url, csv_name)
        data_paths[i] = tea.download_data(csv_url, csv_name)


def get_data_path(filename):
    load_data()
    try:
        data_idx = file_names.index(filename)
    except:
        raise ValueError(f"File is not found!:{filename}")
    data_path = data_paths[data_idx]

    return data_path

# Example from Kabacoff
# Expected outcome: Pearson correlation
def test_pearson_corr():
    data_path = get_data_path('statex77.csv')
    # data_path2 = get_data_path('statex87.csv')

    # Declare and annotate the variables of interest
    variables = [
        {
            'name': 'Illiteracy',
            'data type': 'interval',
            'categories': [0, 100]
        },
        {
            'name': 'Life Exp',
            'data type': 'ratio',
        }
    ]
    # experimental_design = {
    #     'study type': 'observational study',
    #     'contributor variables': ['Illiteracy', 'Life Exp'],
    #     'outcome variables': ''
    # }
    # assumptions = {
    #     'Type I (False Positive) Error Rate': 0.05,
    #     'normal distribution': ['Illiteracy']
    # }

    # tea.data(data_path)
    # # tea.data(data_path2)
    
    # # Allows for using multiple study designs for the same dataset (could lead to phishing but also practical for saving analyses and reusing as many parts of analyses as possible)
    # tea.define_study_design(experimental_design)
    # tea.assume(assumptions, 'strict')

    # results = tea.hypothesize(['Illiteracy', 'Life Exp'], [
    #                           'Illiteracy ~ Life Exp'])
    # print("\nfrom Kabacoff")
    # print("Expected outcome: Pearson")

    state = tea.Unit("")
    illiteracy = state.interval('Illiteracy', [0, 100])
    life_exp = state.ratio('Life Exp')

    # tea.define_variables(variables)

    tea.data(data_path, key=state)
    tea.define_observational_study([illiteracy, life_exp], [])
    tea.assume(groups_normally_distributed=[], false_positive_error_rate=0.05)
    results = tea.hypothesize([illiteracy, life_exp], [illiteracy.linearRelationship(life_exp)])

    print('++++++++++++')


def test_pearson_corr_2():
    data_path = get_data_path('exam.csv')

    # Declare and annotate the variables of interest
    # variables = [
    #     {
    #         'name': 'Exam',
    #         'data type': 'ratio',
    #         'range': [0, 100]
    #     },
    #     {
    #         'name': 'Anxiety',
    #         'data type': 'interval',
    #         'range': [0, 100]
    #     },
    #     {
    #         'name': 'Gender',
    #         'data type': 'nominal',
    #         'categories': ['Male', 'Female']
    #     },
    #     {
    #         'name': 'Revise',
    #         'data type': 'ratio'
    #     }
    # ]
    # experimental_design = {
    #     'study type': 'observational study',
    #     'contributor variables': ['Anxiety', 'Gender', 'Revise'],
    #     'outcome variables': 'Exam'
    # }
    # assumptions = {
    #     'Type I (False Positive) Error Rate': 0.05,
    # }

    s_no = tea.Unit("")
    exam = s_no.ratio('Exam', range=[0, 100])
    anxiety = s_no.interval('Anxiety', range=[0, 100])
    gender = s_no.nominal('Gender', categories=['Male', 'Female'])
    revise = s_no.ratio('Revise')

    tea.data(data_path, key=s_no)
    tea.define_observational_study([anxiety, gender, revise], [exam])
    tea.assume(false_positive_error_rate=0.05)

    results = tea.hypothesize([anxiety, exam])
    results = tea.hypothesize([revise, exam])
    results = tea.hypothesize([anxiety, revise])
    # print("\nfrom Field et al.")
    # print("Expected outcome: Pearson")
    print('++++++++++++')


def test_spearman_corr():
    data_path = get_data_path('liar.csv')

    # Declare and annotate the variables of interest
    # variables = [
    #     {
    #         'name': 'Creativity',
    #         'data type': 'interval'
    #     },
    #     {
    #         'name': 'Position',
    #         'data type': 'ordinal',
    #         'categories': [6, 5, 4, 3, 2, 1]  # ordered from lowest to highest
    #     },
    #     {
    #         'name': 'Novice',
    #         'data type': 'nominal',
    #         'categories': [0, 1]
    #     }
    # ]
    # experimental_design = {
    #     'study type': 'observational study',
    #     'contributor variables': ['Novice', 'Creativity'],
    #     'outcome variables': 'Position'
    # }
    # assumptions = {
    #     'Type I (False Positive) Error Rate': 0.05,
    # }

    # tea.data(data_path)
    # tea.define_variables(variables)
    # tea.define_study_design(experimental_design)
    # tea.assume(assumptions)

    sno = tea.Unit("")
    creativity = sno.interval('Creativity')
    position = sno.ordinal('Position', ordered_categories=[6,5,4,3,2,1])
    novice = sno.nominal('Novice', [0, 1])

    tea.data(data_path, key=sno)
    tea.define_observational_study([novice, creativity], [position])
    tea.assume(false_positive_error_rate=0.05)

    # TODO: allow for partial orders?
    results = tea.hypothesize([position, creativity], [position[1].greaterThan(position[6])])
    # print("\nfrom Field et al.")
    # print("Expected outcome: Spearman")
    print('++++++++++++')

# Same as test for Spearman rho


def test_kendall_tau_corr():
    data_path = get_data_path('liar.csv')

    # Declare and annotate the variables of interest
    # variables = [
    #     {
    #         'name': 'Creativity',
    #         'data type': 'interval'
    #     },
    #     {
    #         'name': 'Position',
    #         'data type': 'ordinal',
    #         'categories': [6, 5, 4, 3, 2, 1]  # ordered from lowest to highest
    #     },
    #     {
    #         'name': 'Novice',
    #         'data type': 'nominal',
    #         'categories': [0, 1]
    #     }
    # ]
    # experimental_design = {
    #     'study type': 'observational study',
    #     'contributor variables': ['Novice', 'Creativity'],
    #     'outcome variables': 'Position'
    # }
    # assumptions = {
    #     'Type I (False Positive) Error Rate': 0.05,
    # }

    # tea.data(data_path)
    # tea.define_variables(variables)
    # tea.define_study_design(experimental_design)
    # tea.assume(assumptions)

    # results = tea.hypothesize(['Position', 'Creativity'], [
    #                           'Position:1 > 6', 'Position:1 > 2'])  # I think this works!?

    sno = tea.Unit("")
    creativity = sno.interval('Creativity')
    position = sno.ordinal('Position', ordered_categories=[6,5,4,3,2,1])
    novice = sno.nominal('Novice', [0, 1])

    tea.data(data_path, key=sno)
    tea.define_observational_study([novice, creativity], [position])
    tea.assume(false_positive_error_rate=0.05)

    results = tea.hypothesize([position, creativity], [position[1].greaterThan(position[6]), position[1].greaterThan(position[2])])

    # print("\nfrom Field et al.")
    # print("Expected outcome: Kendall Tau")
    print('++++++++++++')


def test_pointbiserial_corr():
    data_path = get_data_path('pbcorr.csv')

    # Declare and annotate the variables of interest
    # variables = [
    #     {
    #         'name': 'time',
    #         'data type': 'ratio'
    #     },
    #     {
    #         'name': 'gender',
    #         'data type': 'nominal',
    #         'categories': [0, 1]  # ordered from lowest to highest
    #     },
    #     {
    #         'name': 'recode',
    #         'data type': 'nominal',
    #         'categories': [0, 1]
    #     }
    # ]
    # experimental_design = {
    #     'study type': 'observational study',
    #     'contributor variables': ['gender', 'recode'],
    #     'outcome variables': 'time'
    # }
    # assumptions = {
    #     'Type I (False Positive) Error Rate': 0.05,
    # }

    # tea.data(data_path)
    # tea.define_variables(variables)
    # tea.define_study_design(experimental_design)
    # tea.assume(assumptions)

    time = tea.Ratio('time')
    gender = tea.Nominal('gender', categories=[0, 1])
    recode = tea.Nominal('recode', categories=[0,1])

    tea.data(data_path)
    tea.define_observational_study([gender, recode], [time])
    tea.assume()

    # I think this works!?
    # tea.hypothesize(['time', 'gender'], ['gender:1 > 0'])
    results = tea.hypothesize([time, gender], [gender[1].greaterThan(gender[0])])
    # print("\nfrom Field et al.")
    # print("Expected outcome: Pointbiserial")
    print('++++++++++++')


def test_indep_t_test():
    data_path = get_data_path('UScrime.csv')

    # Declare and annotate the variables of interest
    # variables = [
    #     {
    #         'name': 'So',
    #         'data type': 'nominal',
    #         'categories': [0, 1]
    #     },
    #     {
    #         'name': 'Prob',
    #         'data type': 'ratio',
    #         'range': [0, 1]
    #     }
    # ]
    # experimental_design = {
    #     'study type': 'observational study',
    #     'contributor variables': 'So',
    #     'outcome variables': 'Prob',
    # }
    # assumptions = {
    #     'Type I (False Positive) Error Rate': 0.05,
    #     'groups normally distributed': [['Prob', 'So']]
    # }

    # transformations = {
    #     'log': ['Prob']
    # }

    so = tea.Nominal('So', [0,1])
    prob = tea.Ratio('Prob', range=[0,1])
    
    tea.define_observational_study([so], [prob])
    tea.assume(groups_normally_distributed=[[prob, so]], false_positive_error_rate=0.05)

    tea.data(data_path)
    # tea.define_variables(variables)
    # # Allows for using multiple study designs for the same dataset (could lead to phishing but also practical for saving analyses and reusing as many parts of analyses as possible)
    # tea.define_study_design(experimental_design)
    # tea.assume(assumptions)

    tea.hypothesize([so, prob], [so[1].greaterThan(so[0])])  # Southern is greater
    # print("\nfrom Kabacoff")
    # print("Expected outcome: Student's t-test")
    print('++++++++++++')


def test_paired_t_test():
    data_path = get_data_path('spiderLong_within.csv')

    # Declare and annotate the variables of interest
    # variables = [
    #     {
    #         'name': 'Group',
    #         'data type': 'nominal',
    #         'categories': ['Picture', 'Real Spider']
    #     },
    #     {
    #         'name': 'Anxiety',
    #         'data type': 'ratio'
    #     }
    # ]
    # experimental_design = {
    #     'study type': 'experiment',
    #     'independent variables': 'Group',
    #     'dependent variables': 'Anxiety',
    #     'within subjects': 'Group'

    # }
    # assumptions = {
    #     'Type I (False Positive) Error Rate': 0.05
    # }

    # tea.data(data_path, key="id")
    # tea.define_variables(variables)
    # # Allows for using multiple study designs for the same dataset (could lead to phishing but also practical for saving analyses and reusing as many parts of analyses as possible)
    # tea.define_study_design(experimental_design)
    # tea.assume(assumptions)

    # tea.hypothesize(['Group', 'Anxiety'], ['Group:Real Spider > Picture'])

    group = tea.Nominal('Group', categories=['Picture', 'Real Spider'])
    anxiety = tea.Ratio('Anxiety')
    tea.define_experiment([group], [anxiety], within_subjects=[group])
    
    tea.data(data_path)
    tea.assume(false_positive_error_rate=0.05)
    tea.hypothesize([group, anxiety], [group['Real Spider'].greaterThan(group['Picture'])])

    # print("\nfrom Field et al.")
    # print("Expected outcome: Paired/Dependent t-test")
    print('++++++++++++')


def test_wilcoxon_signed_rank():
    data_path = get_data_path('alcohol.csv')

    # Declare and annotate the variables of interest
    # variables = [
    #     {
    #         'name': 'drug',
    #         'data type': 'nominal',
    #         'categories': ['Alcohol']
    #     },
    #     {
    #         'name': 'day',
    #         'data type': 'nominal',
    #         'categories': ['sundayBDI', 'wedsBDI']
    #     },
    #     {
    #         'name': 'value',
    #         'data type': 'ratio'
    #     }
    # ]
    # experimental_design = {
    #     'study type': 'experiment',
    #     'independent variables': 'day',
    #     'dependent variables': 'value',
    #     'within subjects': 'day'

    # }
    # assumptions = {
    #     'Type I (False Positive) Error Rate': 0.05
    # }

    tea.data(data_path)
    # tea.define_variables(variables)
    # Allows for using multiple study designs for the same dataset (could lead to phishing but also practical for saving analyses and reusing as many parts of analyses as possible)
    # tea.define_study_design(experimental_design)
    # tea.assume(assumptions)

    drug = tea.Nominal('drug', ['Alcohol'])
    day = tea.Nominal('day', ['sundayBDI', 'wedsBDI'])
    value = tea.Ratio('value')

    tea.define_experiment(independent_variables=[day], dependent_variables=[value], within_subjects=[day])
    tea.assume(false_positive_error_rate=0.05)

    tea.hypothesize([day, value], [day['sundayBDI'].notEquals(day['wedsBDI'])])

    # tea.hypothesize(['day', 'value'], ['day:sundayBDI != wedsBDI'])
    
    # print("\nfrom Field et al.")
    # print("Expected outcome: Wilcoxon signed rank test")
    print('++++++++++++')


def test_f_test():
    data_path = get_data_path('cholesterol.csv')

    # Declare and annotate the variables of interest
    # variables = [
    #     {
    #         'name': 'trt',
    #         'data type': 'nominal',
    #         'categories': ['1time', '2times', '4times', 'drugD', 'drugE']
    #     },
    #     {
    #         'name': 'response',
    #         'data type': 'ratio'
    #     }
    # ]
    # experimental_design = {
    #     'study type': 'experiment',
    #     'independent variables': 'trt',
    #     'dependent variables': 'response',
    #     'between subjects': 'trt'

    # }
    # assumptions = {
    #     'Type I (False Positive) Error Rate': 0.05,
    # }

    # Declare Variables
    trt = tea.Nominal('trt', ['1time', '2times', '4times', 'drugD', 'drugE'])
    response = tea.Ratio('response')

    tea.define_experiment([trt], [response], [trt])
    tea.assume(false_positive_error_rate=0.05)

    tea.data(data_path)
    # tea.define_variables(variables)
    # Allows for using multiple study designs for the same dataset (could lead to phishing but also practical for saving analyses and reusing as many parts of analyses as possible)
    # tea.define_study_design(experimental_design)
    # tea.assume(assumptions)

    tea.hypothesize([trt, response])
    # print("\nFrom Field et al.")
    # print("Expected outcome: Oneway ANOVA (F) test")
    print('++++++++++++')


def test_kruskall_wallis():
    data_path = get_data_path('soya.csv')

    # Declare and annotate the variables of interest
    # variables = [
    #     {
    #         'name': 'Sperm',
    #         'data type': 'interval'
    #     },
    #     {
    #         'name': 'Soya',
    #         'data type': 'ordinal',
    #         'categories': ['No Soya', '1 Soya Meal', '4 Soya Meals', '7 Soya Meals']
    #     }
    # ]
    # experimental_design = {
    #     'study type': 'experiment',
    #     'independent variables': 'Soya',
    #     'dependent variables': 'Sperm',
    #     'between subjects': 'Soya'
    # }
    # assumptions = {
    #     'Type I (False Positive) Error Rate': 0.05,
    # }

    # Declare variables
    sperm = tea.Interval('Sperm')
    soya = tea.Ordinal('Soya',['No Soya', '1 Soya Meal', '4 Soya Meals', '7 Soya Meals'])
    tea.define_experiment([soya], [sperm], [soya])

    tea.data(data_path)
    # tea.define_variables(variables)
    # Allows for using multiple study designs for the same dataset (could lead to phishing but also practical for saving analyses and reusing as many parts of analyses as possible)
    # tea.define_study_design(experimental_design)
    # tea.assume(assumptions)
    tea.assume(false_positive_error_rate=0.05)

    # tea.hypothesize(['Soya', 'Sperm'])
    tea.hypothesize([soya, sperm])

    # print("\nFrom Field et al.")
    # print("Expected outcome: Kruskall Wallis")
    print('++++++++++++')


def test_rm_one_way_anova():
    data_path = get_data_path('co2.csv')

    # Declare and annotate the variables of interest
    # variables = [
    #     {
    #         'name': 'uptake',
    #         'data type': 'interval'
    #     },
    #     {
    #         'name': 'Type',
    #         'data type': 'nominal',
    #         'categories': ['Quebec', 'Mississippi']
    #     },
    #     {
    #         'name': 'conc',
    #         'data type': 'ordinal',
    #         'categories': [95, 175, 250, 350, 500, 675, 1000]
    #     }
    # ]
    # experimental_design = {
    #     'study type': 'experiment',
    #     'independent variables': ['Type', 'conc'],
    #     'dependent variables': 'uptake',
    #     'within subjects': 'conc',
    #     'between subjects': 'Type'
    # }
    # assumptions = {
    #     'Type I (False Positive) Error Rate': 0.05,
    # }

    plant = tea.Unit('Plant')

    uptake = plant.interval('uptake')
    type = plant.nominal('Type',['Quebec', 'Mississippi'])
    conc = plant.ordinal('conc',[95, 175, 250, 350, 500, 675, 1000])

    tea.data(data_path, key=plant)

    # tea.define_variables(variables)
    # Allows for using multiple study designs for the same dataset (could lead to phishing but also practical for saving analyses and reusing as many parts of analyses as possible)
    # tea.define_study_design(experimental_design)
    # tea.assume(assumptions)

    tea.define_experiment([type, conc], [uptake], [type], [conc])
    tea.assume(false_positive_error_rate=0.05)

    # tea.hypothesize(['uptake', 'conc'])
    tea.hypothesize([uptake, conc])

    # print("\nFrom Field et al.")
    # print("Expected outcome: Repeated Measures One Way ANOVA")
    print('++++++++++++')


def test_factorial_anova():
    data_path = get_data_path('gogglesData.csv')

    # Declare and annotate the variables of interest
    # variables = [
    #     {
    #         'name': 'gender',
    #         'data type': 'nominal',
    #         'categories': ['Female', 'Male']
    #     },
    #     {
    #         'name': 'alcohol',
    #         'data type': 'nominal',
    #         'categories': ['None', '2 Pints', '4 Pints']
    #     },
    #     {
    #         'name': 'attractiveness',
    #         'data type': 'interval'
    #     }
    # ]
    # experimental_design = {
    #     'study type': 'experiment',
    #     'independent variables': ['gender', 'alcohol'],
    #     'dependent variables': 'attractiveness',
    #     'between subjects': ['gender', 'alcohol']
    # }
    # assumptions = {
    #     'Type I (False Positive) Error Rate': 0.05,
    # }

    gender = tea.Nominal('gender', ['Female', 'Male'])
    alcohol = tea.Nominal('alcohol',  ['None', '2 Pints', '4 Pints'])
    attractiveness = tea.Interval('attractiveness')

    tea.data(data_path)
    # tea.define_variables(variables)
    # Allows for using multiple study designs for the same dataset (could lead to phishing but also practical for saving analyses and reusing as many parts of analyses as possible)
    # tea.define_study_design(experimental_design)
    # tea.assume(assumptions)

    tea.define_experiment([gender, alcohol], [attractiveness], [gender, alcohol])
    tea.assume(false_positive_error_rate=0.05)

    # tea.hypothesize(['attractiveness', 'gender', 'alcohol'])
    tea.hypothesize([attractiveness, gender, alcohol])
    # alcohol main effect?
    # print("\nFrom Field et al.")
    # print("Expected outcome: Factorial ANOVA")
    print('++++++++++++')


def test_two_way_anova():
    data_path = get_data_path('co2.csv')

    # Declare and annotate the variables of interest
    # variables = [
    #     {
    #         'name': 'uptake',
    #         'data type': 'interval'
    #     },
    #     {
    #         'name': 'Type',
    #         'data type': 'nominal',
    #         'categories': ['Quebec', 'Mississippi']
    #     },
    #     {
    #         'name': 'conc',
    #         'data type': 'ordinal',
    #         'categories': [95, 175, 250, 350, 500, 675, 1000]
    #     }
    # ]
    # experimental_design = {
    #     'study type': 'experiment',
    #     'independent variables': ['Type', 'conc'],
    #     'dependent variables': 'uptake',
    #     'within subjects': 'conc',
    #     'between subjects': 'Type'
    # }
    # assumptions = {
    #     'Type I (False Positive) Error Rate': 0.05,
    #     'groups normally distributed': [['Type', 'uptake'], ['Type', 'conc']],
    #     'equal variance': [['Type', 'uptake'], ['conc', 'uptake']]
    # }

    uptake = tea.Interval('uptake')
    type = tea.Nominal('Type',['Quebec', 'Mississippi'])
    conc = tea.Ordinal('conc',[95, 175, 250, 350, 500, 675, 1000])



    tea.data(data_path)
    # tea.define_variables(variables)
    # Allows for using multiple study designs for the same dataset (could lead to phishing but also practical for saving analyses and reusing as many parts of analyses as possible)
    # tea.define_study_design(experimental_design)
    tea.define_experiment([type, conc], [uptake], [type], [conc])
    # tea.assume(assumptions, mode='relaxed')
    tea.assume(false_positive_error_rate=0.05, groups_normally_distributed=[[type, uptake], [type, conc]], equal_variance=[[type, uptake], [conc, uptake]])

    # Fails: not all groups are normal
    # tea.hypothesize(['uptake', 'conc', 'Type'])
    tea.hypothesize([uptake, conc, type])
    # Type main effect?
    # print('Supposed to be 2 way ANOVA')
    print('++++++++++++')


def test_chi_square():
    data_path = get_data_path('catsData.csv')

    # Declare and annotate the variables of interest
    # variables = [
    #     {
    #         'name': 'Training',
    #         'data type': 'nominal',
    #         'categories': ['Food as Reward', 'Affection as Reward']
    #     },
    #     {
    #         'name': 'Dance',
    #         'data type': 'nominal',
    #         'categories': ['Yes', 'No']
    #     }
    # ]
    # experimental_design = {
    #     'study type': 'observational study',
    #     'contributor variables': 'Training',
    #     'outcome variables': 'Dance'
    # }
    # assumptions = {
    #     'Type I (False Positive) Error Rate': 0.05,
    # }

    training = tea.Nominal('Training', ['Food as Reward', 'Affection as Reward'])
    dance = tea.Nominal('Dance', ['Yes', 'No'])
    tea.define_observational_study([training], [dance])

    tea.data(data_path)
    tea.assume(false_positive_error_rate=0.05)
    # tea.define_variables(variables)
    # Allows for using multiple study designs for the same dataset (could lead to phishing but also practical for saving analyses and reusing as many parts of analyses as possible)
    # tea.define_study_design(experimental_design)
    # tea.assume(assumptions)

    # tea.hypothesize(['Training', 'Dance'])
    tea.hypothesize([training, dance])
    # print('Chi square')
    print('++++++++++++')


def test_chi_square_with_dataframe():
    data_path = get_data_path('catsData.csv')

    data_frame = pd.read_csv(data_path)

    # Declare and annotate the variables of interest
    # variables = [
    #     {
    #         'name': 'Training',
    #         'data type': 'nominal',
    #         'categories': ['Food as Reward', 'Affection as Reward']
    #     },
    #     {
    #         'name': 'Dance',
    #         'data type': 'nominal',
    #         'categories': ['Yes', 'No']
    #     }
    # ]
    # experimental_design = {
    #     'study type': 'observational study',
    #     'contributor variables': 'Training',
    #     'outcome variables': 'Dance'
    # }
    # assumptions = {
    #     'Type I (False Positive) Error Rate': 0.05,
    # }

    training = tea.Nominal('Training', ['Food as Reward', 'Affection as Reward'])
    dance = tea.Nominal('Dance', ['Yes', 'No'])
    tea.define_observational_study([training], [dance])

    tea.data(data_frame)  # Passes data_frame instead of data_path
    # tea.define_variables(variables)
    # Allows for using multiple study designs for the same dataset (could lead to phishing but also practical for saving analyses and reusing as many parts of analyses as possible)
    # tea.define_study_design(experimental_design)
    # tea.assume(assumptions)
    tea.assume(false_positive_error_rate=0.05)

    # tea.hypothesize(['Training', 'Dance'])
    tea.hypothesize([training, dance])
    # print('Chi square')
    print('++++++++++++')
