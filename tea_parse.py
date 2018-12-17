from tea_eval import *

# Helper -- should make private? 
def get_dataset(dataset_name: str) -> Dataset: 
    if (dataset_name not in globals()): 
        raise Exception('Dataset does not exist!') # Have some nicer error message
    
    return globals()[dataset_name]


# @returns a Dataset object? 
def load_data(source: str, vars: Dict[str, Dict[str, list]] = None) -> Dataset: 
    ds = Dataset()
    ds.load_data(source)

    for var_name in vars: 
        v = vars[var_name]
        data_type = None
        categories = None
        if (v['type'] == 'ordinal' or v['type'] == 'nominal'): 
            # Create order tuple
            categories = OrderedDict()
            for i, c in enumerate(v['categories']):
                categories[c] = i+1
        if (v['type'] == 'ordinal'): 
            data_type = DataType.ORDINAL
        elif (v['type'] == 'nominal'): 
            data_type = DataType.NOMINAL
        elif (v['type'] == 'interval'): 
            data_type = DataType.INTERVAL
        elif (v['type'] == 'ratio'): 
            data_type = DataType.RATIO
        else: 
            raise Exception('Variables must be specified as being ordinal, nominal, interval, or ratio')
        ds.set_variable(var_name, data_type, categories)
    
    return ds

def explore_summary(dataset: str, vars: Dict[str, Dict[str, list]]):
        # TODO: do some error handling should the dictionary fields be mispelled, etc

        data = get_dataset(dataset)
        variable = data.get_variable(vars['variable'])
        var = variable[0]
        var_data = variable[1]
       
        if 'characteristics' in vars: 
            props = vars['characteristics']
            if isinstance(props, str) and props.upper() == 'ALL': 
                props = list(univariate_stats.keys())
        else: 
            props = list(univariate_stats.keys())

        for p in props: 
            if (p not in univariate_stats.keys()):
                raise Exception(f"{p} is not a supported property of data")
            
            statistic = univariate_stats[p]
            pretty_print(p, evaluate(data, statistic(var), var, var_data))
            # pretty_print(p, evaluate(data, var, statistic(var)))


def groups(dataset: Dataset, variable: Variable, sub_groups: Dict[str, Relation]=None): 

    # if isinstance()
    if (sub_groups): 
        pass
            # check_value_exists()
            # calculate the values
    else: 
        pass


        


############ TEST PROGRAM ###########
dataset1 = load_data('mini_test.csv', {
    'education': {
        'type': 'ordinal', 
        'categories': ['high school', 'college', 'PhD']
    }, 
    'age': {
        'type': 'ratio'
    }
})

explore_summary('dataset1', {
    'variable': 'age',
    'characteristics': ['mean', 'median', 'standard deviation', 'variance']
})

explore_summary('dataset1', {
    'variable': 'education',
    'characteristics': ['frequency']
    # 'characteristics': ['mean', 'median', 'standard deviation', 'variance']
})

# test comparison()

