from tea.z3_solver.solver import __ALL_TESTS__
from tea.runtimeDataStructures.value import Value
from tea.runtimeDataStructures.combinedData import CombinedData
from tea.global_vals import *

import attr

@attr.s(init=False, repr=False, str=False)
class ResultData(Value):
    test_to_results = attr.ib(type=dict)
    test_to_assumptions = attr.ib(type=dict)

    def __init__(self, test_to_results, combined_data: CombinedData):
        self.test_to_results = test_to_results
        self.test_to_assumptions = {}
        for test in __ALL_TESTS__:
            if test.name in test_to_results:
                print(test.name)
                test_assumptions = []
                # TODO: The names get stale if hypothesize() is called multiple times in a row.
                for applied_prop in test._properties:
                    assumption = f"{applied_prop.property.description}: "

                    if applied_prop.property.name == "has_one_x":
                        assumption += combined_data.get_explanatory_variables()[0].metadata[name]
                    elif applied_prop.property.name == "has_one_y":
                        assumption += combined_data.get_explained_variables()[0].metadata[name]
                    elif applied_prop.property.name == "has_independent_observations" or applied_prop.property.name == "has_paired_observations":
                        assumption += combined_data.get_explanatory_variables()[0].metadata[name]
                    else:
                        for stat_var in applied_prop.vars:
                            assumption += f"{stat_var.name}, "
                        assumption = assumption[:-2]

                    if applied_prop.property_test_results is not None:
                        assumption += f": {applied_prop.property_test_results}"
                    test_assumptions.append(assumption)

                self.test_to_assumptions[test.name] = test_assumptions

    def get_all_test_results(self): 
        results = [v for k,v in self.test_to_results.items()]
        return results

    def _pretty_print(self):
        output = "\nResults:\n--------------"
        for test_name, results in self.test_to_results.items():
            output += f"\nTest: {test_name}\n"
            test_assumptions = "None"
            if test_name in self.test_to_assumptions:
                test_assumptions = ('\n').join(self.test_to_assumptions[test_name])
            output += f"***Test assumptions:\n{test_assumptions}\n\n"
            output += "***Test results:\n"

            if hasattr(results, '__dict__'):
                # for prop, value in results.__dict__.items():
                #     if value is None:
                #         continue

                if results.name:
                    output += f"name = {results.name}\n"
                if results.test_statistic:
                    if isinstance(results.test_statistic, dict):
                        output += f"test_statistic = {results.test_statistic}\n"
                    else:
                        output += f"test_statistic = {'%.5f'%(results.test_statistic)}\n"
                if results.p_value:
                    if isinstance(results.p_value, str):
                        output += f"p_value = {results.p_value}\n"
                    else:
                        output += f"p_value = {'%.5f'%(results.p_value)}\n"
                if results.adjusted_p_value:
                    output += f"adjusted_p_value = {'%.5f'%(results.adjusted_p_value)}\n"
                if results.alpha:
                    output += f"alpha = {results.alpha}\n"
                if results.dof:
                    output += f"dof = {results.dof}\n"
                if results.table is not None:
                    output += f"table = {results.table}\n"
                if "effect_size" in results.__dict__:
                    effect_sizes = results.effect_size.items()
                    output += f"Effect size:\n"
                    for effect_size_name, effect_size_value in effect_sizes:
                        output += f"{effect_size_name} = {'%.5f'%(effect_size_value)}\n"
                if results.null_hypothesis:
                    output += f"Null hypothesis = {results.null_hypothesis}\n"
                if results.interpretation:
                    output += f"Interpretation = {results.interpretation}\n"

            else: 
                output += f"{str(results)}\n"
            # import pdb; pdb.set_trace()
        return output

    def __repr__(self):
        return self._pretty_print()

    def __str__(self):  # Maybe what the user sees?
        return self._pretty_print()