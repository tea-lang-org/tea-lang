import tea
import os

base_url = 'https://homes.cs.washington.edu/~emjun/tea-lang/datasets/'
uscrime_data_path = None

def test_load_data():
    global base_url, uscrime_data_path
    csv_name = 'UScrime.csv'
    csv_url = os.path.join(base_url, csv_name)
    uscrime_data_path = tea.load_data_from_url(csv_url, 'UScrime')

def test_indep_t_test():
    global uscrime_data_path

    # Declare and annotate the variables of interest
    is_south = tea.nominal('So', ['0', '1'])
    probability = tea.ratio('Prob', drange=[0,1])
    variables = [is_south, probability]
    experimental_design = {
                            'study type': 'observational study',
                            'contributor variables': 'So',
                            'outcome variables': 'Prob',
                            # 'alpha': 1
                        }

    assumptions = {
        # no assumptions
    }

    # What happens when have no 
    dataset = tea.load_data(uscrime_data_path, variables)

    
    import pdb; pdb.set_trace()
    # ds = load_data(file_path, variables, 'participant_id')