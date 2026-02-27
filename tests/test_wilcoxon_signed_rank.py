import tea

from tea.logging import TeaLoggerConfiguration, TeaLogger
import logging
configuration = TeaLoggerConfiguration()
configuration.logging_level = logging.DEBUG
TeaLogger.initialize_logger(configuration)

# This example is adapted from http://www.real-statistics.com/non-parametric-tests/wilcoxon-signed-ranks-test/
def test_wilcoxon_signed_rank_0():
    tea.data('./tests/data/real_stats_0.csv', key='Person')

    variables = [
        {
            'name': 'Person',
            'data type': 'ratio'
        },
        {
            'name': 'Side',
            'data type': 'nominal',
            'categories': ['Right', 'Left']
        },
        {
            'name': 'Score',
            'data type': 'ratio'
        }
    ]
    experimental_design = {
        'study type': 'experiment',
        'independent variables': 'Side',
        'dependent variables': 'Score',
        'within subjects': 'Side',
        # 'key': 'Person'
    }
    assumptions = {
        'Type I (False Positive) Error Rate': 0.05
    }


    tea.define_variables(variables)
    # Allows for using multiple study designs for the same dataset (could lead to phishing but also practical for saving analyses and reusing as many parts of analyses as possible)
    tea.define_study_design(experimental_design)
    tea.assume(assumptions)

    tea.hypothesize(['Side', 'Score'], ['Side:Right != Left'])


# This example is adapted from Example 1 on http://www.real-statistics.com/non-parametric-tests/wilcoxon-signed-ranks-test/
def test_wilcoxon_signed_rank_1():
    tea.data('./tests/data/real_stats_1.csv')

    variables = [
        {
            'name': 'Subject',
            'data type': 'ratio'
        },
        {
            'name': 'Source',
            'data type': 'nominal',
            'categories': ['Memory', 'Median']
        },
        {
            'name': 'Score',
            'data type': 'ratio'
        }
    ]
    experimental_design = {
        'study type': 'experiment',
        'independent variables': 'Source',
        'dependent variables': 'Score',
        'within subjects': 'Source'
    }
    assumptions = {
        'Type I (False Positive) Error Rate': 0.05
    }


    tea.define_variables(variables)
    # Allows for using multiple study designs for the same dataset (could lead to phishing but also practical for saving analyses and reusing as many parts of analyses as possible)
    tea.define_study_design(experimental_design)
    tea.assume(assumptions)

    tea.hypothesize(['Source', 'Score'], ['Source:Memory != Median'])


# This example is adapted from Example 2 on  http://www.real-statistics.com/non-parametric-tests/wilcoxon-signed-ranks-test/wilcoxon-signed-ranks-exact-test/
def test_wilcoxon_signed_rank_2():
    tea.data('./tests/data/real_stats_2.csv', key='Couple')

    variables = [
        {
            'name': 'Couple',
            'data type': 'ratio'
        },
        {
            'name': 'Person',
            'data type': 'nominal',
            'categories': ['Wife', 'Husband']
        },
        {
            'name': 'Score',
            'data type': 'ratio'
        }
    ]
    experimental_design = {
        'study type': 'observational study',
        'contributor variables': 'Person',
        'outcome variables': 'Score',
        'within subjects': 'Person'
    }
    assumptions = {
        'Type I (False Positive) Error Rate': 0.05
    }


    tea.define_variables(variables)
    # Allows for using multiple study designs for the same dataset (could lead to phishing but also practical for saving analyses and reusing as many parts of analyses as possible)
    tea.define_study_design(experimental_design)
    tea.assume(assumptions)

    tea.hypothesize(['Person', 'Score'], ['Person:Wife != Husband'])


    ## TODO: one-sided!