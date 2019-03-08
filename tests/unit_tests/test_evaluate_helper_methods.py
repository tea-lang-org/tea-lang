from tea.evaluate_helper_methods import explanatory_strings_for_assumptions
from tea.solver import Assumptions, Tests, assumptions_for_test

def test_explanatory_string_for_assumptions():
    for test in list(Tests):
        if not test == Tests.NONE:
            assert len(explanatory_strings_for_assumptions(assumptions_for_test(test)))
