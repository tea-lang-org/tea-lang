from classes.tea import Experiment

exp = Experiment('Motivation', 'motivation_paper_dataset.csv')
exp.pretty_print()
def test_experiment_init():
    exp = Experiment('Motivation', 'motivation_paper_dataset.csv')

def test_get_column():
    print(exp.data_set)
    # exp.load_data()
    # exp = Experiment.experiment('Motivation', 'motivation2.csv')
   

# def test_experiment_colum():
#     exp = Experiment.load('Motivation', 'motivation2.csv')
#     sleep = exp.column('data_fun')  
#     sleep.normal()
#     print(exp.pretty_print())
