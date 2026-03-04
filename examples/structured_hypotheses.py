"""
Structured Hypothesis API Examples
===================================

Side-by-side comparison of the string-based syntax and the new structured API.
Each section shows the original string prediction and the equivalent structured call.

The structured API provides:
  - IDE autocompletion for function names and arguments
  - Immediate validation (typos raise ValueError, not silent wrong results)
  - Readable left-to-right: compare('AR', '>', 'TV'), relationship('positive', 'X', 'Y')

To run:  poetry run python examples/structured_hypotheses.py
"""

import tea
import os

DATA_DIR = os.path.join(os.path.dirname(__file__), '..', 'tests', 'data')
EXAMPLES_DIR = os.path.dirname(__file__)


def data_path(filename):
    return os.path.join(DATA_DIR, filename)


# ============================================================================
# 1. Group comparison — categorical "greater than"
#    String:      'Condition:AR > TV'
#    Structured:  tea.compare('AR', '>', 'TV')
# ============================================================================

def example_ar_vs_tv():
    """AR vs TV experiment (Mann-Whitney U)."""
    print("\n=== AR vs TV: compare('AR', '>', 'TV') ===")

    tea.data(os.path.join(EXAMPLES_DIR, 'AR_TV', 'ar_tv_long.csv'), key='ID')
    tea.define_variables([
        {'name': 'ID', 'data type': 'ratio'},
        {'name': 'Condition', 'data type': 'nominal', 'categories': ['AR', 'TV']},
        {'name': 'Score', 'data type': 'ordinal', 'categories': [1, 2, 3, 4, 5]},
    ])
    tea.define_study_design({
        'study type': 'experiment',
        'independent variables': 'Condition',
        'dependent variables': 'Score',
    })
    tea.assume({'Type I (False Positive) Error Rate': 0.01969})

    # String syntax:
    #   tea.hypothesize(['Score', 'Condition'], ['Condition:AR > TV'])

    # Structured API:
    results = tea.hypothesize(['Score', 'Condition'], [tea.compare('AR', '>', 'TV')])
    return results


# ============================================================================
# 2. Group comparison — nominal "greater than" with integer categories
#    String:      'So:1 > 0'
#    Structured:  tea.compare(1, '>', 0)
# ============================================================================

def example_indep_t_test():
    """US Crime: independent t-test (So predicts Prob)."""
    print("\n=== Independent t-test: compare(1, '>', 0) ===")

    tea.data(data_path('UScrime.csv'))
    tea.define_variables([
        {'name': 'So', 'data type': 'nominal', 'categories': [0, 1]},
        {'name': 'Prob', 'data type': 'ratio', 'range': [0, 1]},
    ])
    tea.define_study_design({
        'study type': 'observational study',
        'contributor variables': 'So',
        'outcome variables': 'Prob',
    })
    tea.assume({
        'Type I (False Positive) Error Rate': 0.05,
        'groups normally distributed': [['Prob', 'So']],
    })

    # String syntax:
    #   tea.hypothesize(['So', 'Prob'], ['So:1 > 0'])

    # Structured API:
    results = tea.hypothesize(['So', 'Prob'], [tea.compare(1, '>', 0)])
    return results


# ============================================================================
# 3. Group comparison — "less than"
#    String:      'Sex:F < M'
#    Structured:  tea.compare('F', '<', 'M')
# ============================================================================

def example_less_than():
    """Olympics: Female athletes weigh less than Male athletes."""
    print("\n=== Less-than comparison: compare('F', '<', 'M') ===")

    tea.data(os.path.join(EXAMPLES_DIR, 'Olympics', 'athlete_events_cleaned_weight.csv'), key='ID')
    tea.define_variables([
        {'name': 'ID', 'data type': 'ratio'},
        {'name': 'Sport', 'data type': 'nominal', 'categories': ['Swimming', 'Wrestling']},
        {'name': 'Sex', 'data type': 'nominal', 'categories': ['M', 'F']},
        {'name': 'Weight', 'data type': 'ratio'},
    ])
    tea.define_study_design({
        'study type': 'observational study',
        'contributor variables': ['Sport', 'Sex'],
        'outcome variables': 'Weight',
    })
    tea.assume({
        'groups normally distributed': [['Sport', 'Weight']],
        'Type I (False Positive) Error Rate': 0.05,
    })

    # String syntax:
    #   tea.hypothesize(['Sex', 'Weight'], ['Sex:F < M'])

    # Structured API:
    results = tea.hypothesize(['Sex', 'Weight'], [tea.compare('F', '<', 'M')])
    return results


# ============================================================================
# 4. Group comparison — "not equal" (Wilcoxon signed-rank)
#    String:      'day:sundayBDI != wedsBDI'
#    Structured:  tea.compare('sundayBDI', '!=', 'wedsBDI')
# ============================================================================

def example_wilcoxon():
    """Alcohol data: Sunday vs Wednesday BDI scores differ."""
    print("\n=== Not-equal comparison: compare('sundayBDI', '!=', 'wedsBDI') ===")

    tea.data(data_path('alcohol.csv'))
    tea.define_variables([
        {'name': 'drug', 'data type': 'nominal', 'categories': ['Alcohol']},
        {'name': 'day', 'data type': 'nominal', 'categories': ['sundayBDI', 'wedsBDI']},
        {'name': 'value', 'data type': 'ratio'},
    ])
    tea.define_study_design({
        'study type': 'experiment',
        'independent variables': 'day',
        'dependent variables': 'value',
        'within subjects': 'day',
    })
    tea.assume({'Type I (False Positive) Error Rate': 0.05})

    # String syntax:
    #   tea.hypothesize(['day', 'value'], ['day:sundayBDI != wedsBDI'])

    # Structured API:
    results = tea.hypothesize(['day', 'value'], [tea.compare('sundayBDI', '!=', 'wedsBDI')])
    return results


# ============================================================================
# 5. Group comparison — string categories (paired t-test)
#    String:      'Group:Real Spider > Picture'
#    Structured:  tea.compare('Real Spider', '>', 'Picture')
# ============================================================================

def example_paired_t_test():
    """Spider anxiety: Real Spider causes more anxiety than Picture."""
    print("\n=== Paired t-test: compare('Real Spider', '>', 'Picture') ===")

    tea.data(data_path('spiderLong_within.csv'), key='id')
    tea.define_variables([
        {'name': 'Group', 'data type': 'nominal', 'categories': ['Picture', 'Real Spider']},
        {'name': 'Anxiety', 'data type': 'ratio'},
    ])
    tea.define_study_design({
        'study type': 'experiment',
        'independent variables': 'Group',
        'dependent variables': 'Anxiety',
        'within subjects': 'Group',
    })
    tea.assume({'Type I (False Positive) Error Rate': 0.05})

    # String syntax:
    #   tea.hypothesize(['Group', 'Anxiety'], ['Group:Real Spider > Picture'])

    # Structured API:
    results = tea.hypothesize(['Group', 'Anxiety'], [tea.compare('Real Spider', '>', 'Picture')])
    return results


# ============================================================================
# 6. Multiple group comparisons (Kendall tau)
#    String:      ['Position:1 > 6', 'Position:1 > 2']
#    Structured:  [tea.compare(1, '>', 6), tea.compare(1, '>', 2)]
# ============================================================================

def example_multiple_comparisons():
    """Liar data: multiple ordinal comparisons."""
    print("\n=== Multiple comparisons: [compare(1, '>', 6), compare(1, '>', 2)] ===")

    tea.data(data_path('liar.csv'))
    tea.define_variables([
        {'name': 'Creativity', 'data type': 'interval'},
        {'name': 'Position', 'data type': 'ordinal', 'categories': [6, 5, 4, 3, 2, 1]},
        {'name': 'Novice', 'data type': 'nominal', 'categories': [0, 1]},
    ])
    tea.define_study_design({
        'study type': 'observational study',
        'contributor variables': ['Novice', 'Creativity'],
        'outcome variables': 'Position',
    })
    tea.assume({'Type I (False Positive) Error Rate': 0.05})

    # String syntax:
    #   tea.hypothesize(['Position', 'Creativity'], ['Position:1 > 6', 'Position:1 > 2'])

    # Structured API:
    results = tea.hypothesize(['Position', 'Creativity'], [
        tea.compare(1, '>', 6),
        tea.compare(1, '>', 2),
    ])
    return results


# ============================================================================
# 7. Positive relationship (Pearson correlation)
#    String:      'Illiteracy ~ Life Exp'
#    Structured:  tea.relationship('positive', 'Illiteracy', 'Life Exp')
# ============================================================================

def example_positive_relationship():
    """State data: Illiteracy positively related to Life Exp."""
    print("\n=== Positive relationship: relationship('positive', 'Illiteracy', 'Life Exp') ===")

    tea.data(data_path('statex77.csv'))
    tea.define_variables([
        {'name': 'Illiteracy', 'data type': 'interval', 'categories': [0, 100]},
        {'name': 'Life Exp', 'data type': 'ratio'},
    ])
    tea.define_study_design({
        'study type': 'observational study',
        'contributor variables': ['Illiteracy', 'Life Exp'],
        'outcome variables': '',
    })
    tea.assume({
        'Type I (False Positive) Error Rate': 0.05,
        'normal distribution': ['Illiteracy'],
    }, 'strict')

    # String syntax:
    #   tea.hypothesize(['Illiteracy', 'Life Exp'], ['Illiteracy ~ Life Exp'])

    # Structured API:
    results = tea.hypothesize(['Illiteracy', 'Life Exp'], [
        tea.relationship('positive', 'Illiteracy', 'Life Exp'),
    ])
    return results


# ============================================================================
# 8. Negative relationship
#    String:      'Ineq ~ -Prob'
#    Structured:  tea.relationship('negative', 'Ineq', 'Prob')
# ============================================================================

def example_negative_relationship():
    """US Crime: Inequality negatively related to Probability of imprisonment."""
    print("\n=== Negative relationship: relationship('negative', 'Ineq', 'Prob') ===")

    tea.data(data_path('UScrime.csv'))
    tea.define_variables([
        {'name': 'So', 'data type': 'nominal', 'categories': [0, 1]},
        {'name': 'Prob', 'data type': 'ratio', 'range': [0, 1]},
        {'name': 'Ineq', 'data type': 'ratio'},
    ])
    tea.define_study_design({
        'study type': 'observational study',
        'contributor variables': ['So', 'Prob'],
        'outcome variables': ['Prob', 'Ineq'],
    })
    tea.assume({'Type I (False Positive) Error Rate': 0.05})

    # String syntax:
    #   tea.hypothesize(['Ineq', 'Prob'], ['Ineq ~ -Prob'])

    # Structured API:
    results = tea.hypothesize(['Ineq', 'Prob'], [
        tea.relationship('negative', 'Ineq', 'Prob'),
    ])
    return results


# ============================================================================
# 9. No prediction — just explore the relationship (chi-square)
#    No change needed — the structured API is fully backwards compatible.
# ============================================================================

def example_no_prediction():
    """Cats data: no directional prediction (chi-square)."""
    print("\n=== No prediction (unchanged): hypothesize(['Training', 'Dance']) ===")

    tea.data(data_path('catsData.csv'))
    tea.define_variables([
        {'name': 'Training', 'data type': 'nominal', 'categories': ['Food as Reward', 'Affection as Reward']},
        {'name': 'Dance', 'data type': 'nominal', 'categories': ['Yes', 'No']},
    ])
    tea.define_study_design({
        'study type': 'observational study',
        'contributor variables': 'Training',
        'outcome variables': 'Dance',
    })
    tea.assume({'Type I (False Positive) Error Rate': 0.05})

    # Same for both string and structured API — no prediction to convert:
    results = tea.hypothesize(['Training', 'Dance'])
    return results


# ============================================================================
# 10. Pointbiserial correlation — integer categories
#     String:      'gender:1 > 0'
#     Structured:  tea.compare(1, '>', 0)
# ============================================================================

def example_pointbiserial():
    """Pointbiserial correlation: gender predicts time."""
    print("\n=== Pointbiserial: compare(1, '>', 0) ===")

    tea.data(data_path('pbcorr.csv'))
    tea.define_variables([
        {'name': 'time', 'data type': 'ratio'},
        {'name': 'gender', 'data type': 'nominal', 'categories': [0, 1]},
        {'name': 'recode', 'data type': 'nominal', 'categories': [0, 1]},
    ])
    tea.define_study_design({
        'study type': 'observational study',
        'contributor variables': ['gender', 'recode'],
        'outcome variables': 'time',
    })
    tea.assume({'Type I (False Positive) Error Rate': 0.05})

    # String syntax:
    #   tea.hypothesize(['time', 'gender'], ['gender:1 > 0'])

    # Structured API:
    results = tea.hypothesize(['time', 'gender'], [tea.compare(1, '>', 0)])
    return results


# ============================================================================
# 11. Spearman correlation — ordinal comparison
#     String:      'Position:1 > 6'
#     Structured:  tea.compare(1, '>', 6)
# ============================================================================

def example_spearman():
    """Liar data: single ordinal comparison (Spearman rho)."""
    print("\n=== Spearman: compare(1, '>', 6) ===")

    tea.data(data_path('liar.csv'))
    tea.define_variables([
        {'name': 'Creativity', 'data type': 'interval'},
        {'name': 'Position', 'data type': 'ordinal', 'categories': [6, 5, 4, 3, 2, 1]},
        {'name': 'Novice', 'data type': 'nominal', 'categories': [0, 1]},
    ])
    tea.define_study_design({
        'study type': 'observational study',
        'contributor variables': ['Novice', 'Creativity'],
        'outcome variables': 'Position',
    })
    tea.assume({'Type I (False Positive) Error Rate': 0.05})

    # String syntax:
    #   tea.hypothesize(['Position', 'Creativity'], ['Position:1 > 6'])

    # Structured API:
    results = tea.hypothesize(['Position', 'Creativity'], [tea.compare(1, '>', 6)])
    return results


# ============================================================================
# Run all examples
# ============================================================================

if __name__ == '__main__':
    examples = [
        example_ar_vs_tv,
        example_indep_t_test,
        example_less_than,
        example_wilcoxon,
        example_paired_t_test,
        example_multiple_comparisons,
        example_positive_relationship,
        example_negative_relationship,
        example_no_prediction,
        example_pointbiserial,
        example_spearman,
    ]

    passed = 0
    failed = 0
    for ex in examples:
        try:
            ex()
            passed += 1
        except Exception as e:
            print(f"  FAILED: {e}")
            failed += 1

    print(f"\n{'='*60}")
    print(f"Results: {passed} passed, {failed} failed out of {len(examples)} examples")
