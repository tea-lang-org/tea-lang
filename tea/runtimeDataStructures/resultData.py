# from tea.z3_solver.solver import __ALL_TESTS__
from tea.runtimeDataStructures.value import Value

import attr

@attr.s(init=False, repr=False, str=False)
class ResultData(Value):
    test_to_results = attr.ib(type=dict)
    test_to_assumptions = attr.ib(type=dict)

    def __init__(self, test_to_results):
        self.test_to_results = test_to_results
        self.test_to_assumptions = {}
        # for test in __ALL_TESTS__:
        #     if test.name in test_to_results:
        #         print(test.name)
        #         test_assumptions = []
        #         # TODO: The names get stale if hypothesize() is called multiple times in a row.
        #         for applied_prop in test._properties:
        #             assumption = f"{applied_prop.property.description}: "
        #             for stat_var in applied_prop.vars:
        #                 assumption += f"{stat_var.name}, "

        #             assumption = assumption[:-2]
        #             if applied_prop.property_test_results is not None:
        #                 assumption += f": {applied_prop.property_test_results}"
        #             test_assumptions.append(assumption)

        #         self.test_to_assumptions[test.name] = test_assumptions

    def get_all_test_results(self): 
        results = [v for k,v in self.test_to_results.items()]
        return results

    def adjust_p_values(self, correction): 
        test_results = self.get_all_test_results()

        for result in test_results:
            result.adjust_p_val(correction)
            # import pdb; pdb.set_trace()
        
        # import pdb; pdb.set_trace()

    def _pretty_print(self):
        output = "\nResults:\n--------------"
        for test_name, results in self.test_to_results.items():
            output += f"\nTest: {test_name}\n"
            test_assumptions = "None"
            if test_name in self.test_to_assumptions:
                test_assumptions = ('\n').join(self.test_to_assumptions[test_name])
            output += f"***Test assumptions:\n{test_assumptions}\n\n"
            output += "***Test results:\n"
            if hasattr(results, '_fields'):
                for field in results._fields:
                    output += f"{field}: {getattr(results, field)}\n"
            else:
                output += f"{str(results)}\n"

            import pdb; pdb.set_trace()
        return output

    def __repr__(self):
        return self._pretty_print()

    def __str__(self):  # Maybe what the user sees?
        return self._pretty_print()