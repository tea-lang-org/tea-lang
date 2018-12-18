from tea import load_data,  explore_summary

def test():
    assert True

def test_prog1():
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

