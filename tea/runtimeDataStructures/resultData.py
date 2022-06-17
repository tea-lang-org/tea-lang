import contextlib
import html
import io

from tea.z3_solver.solver import all_tests
from tea.runtimeDataStructures.value import Value
from tea.runtimeDataStructures.combinedData import CombinedData
from tea.global_vals import *
from tea.output.tea_console import console
from rich.console import Group
from rich.panel import Panel
from rich.markdown import Markdown

import attr

@attr.s(init=False, repr=False, str=False)
class ResultData(Value):
    test_to_results = attr.ib(type=dict)
    test_to_assumptions = attr.ib(type=dict)
    follow_up_results = attr.ib(type=list, default=None)

    def __init__(self, test_to_results, combined_data: CombinedData):
        self.test_to_results = test_to_results
        self.test_to_assumptions = {}
        ALL_TESTS = all_tests()
        for test in ALL_TESTS:
            if test.name in test_to_results:
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

    def bonferroni_correction(self, num_comparisons):
        for key,value in self.test_to_results.items():
            value.bonferroni_correction(num_comparisons)
        return self

    def output(self):
        console.rule("[bold blue] Results")
        for test_name, results in self.test_to_results.items():
            
            res_tbl = results.get_results_table()
            interp_tbl = results.get_interpretation_table()
            panel_group = Group(
                Markdown(f"""# Statistical test: {results.name}"""),
                res_tbl, 
                interp_tbl
            )
            console.print(Panel(panel_group))
            # console.print(res_tbl)
            # console.print(interp_tbl)
            
        if hasattr(self, 'follow_up_results'): # not empty
            for res in self.follow_up_results:
                print("\nFollow up for multiple comparisons: \n")
                print(res)    

    def add_follow_up(self, follow_up_res_data: list):
        if len(follow_up_res_data) >= 1:
            setattr(self, 'follow_up_results', follow_up_res_data)


    def as_html(self):
        html_out = io.StringIO()
        with contextlib.redirect_stdout(html_out):
            print("<h1>Results</h1>")
            for test_name, results in self.test_to_results.items():
                print("<hr>")
                print(f"<h2>{html.escape(test_name)}</h2>")
                print("<h3>Assumptions</h3>")
                test_assumptions = self.test_to_assumptions.get(test_name, [])
                if test_assumptions:
                    print("<ul>")
                    for assumption in test_assumptions:
                        print(f"<li>{html.escape(assumption)}</li>")
                    print("</ul>")
                else:
                    print("<p>No assumptions</p>")
                print("<h3>Results</h3>")
                if hasattr(results, "__dict__"):
                    def dl_pair(term, definition):
                        dt = html.escape(str(term))
                        dd = html.escape(str(definition))
                        return f"<li><b>{dt}:</b> {dd}</li>"
                    print("<ul>")
                    if results.name:
                        print(dl_pair("name", results.name))
                    if results.test_statistic:
                        if isinstance(results.test_statistic, dict):
                            print(dl_pair("test_statistic", results.test_statistic))
                        else:
                            print(dl_pair("test_statistic", f"{results.test_statistic:.5f}"))
                    if results.p_value:
                        if isinstance(results.p_value, str):
                            print(dl_pair("p_value", results.p_value))
                        else:
                            print(dl_pair("p_value", f"{results.p_value:.5f}"))
                    if results.adjusted_p_value:
                        print(dl_pair("adjusted_p_value", f"{results.adjusted_p_value:.5f}"))
                    if results.alpha:
                        print(dl_pair("alpha", results.alpha))
                    if results.dof:
                        print(dl_pair("dof", results.dof))
                    if results.table is not None:
                        print(dl_pair("table", results.table))
                    if "effect_size" in results.__dict__:
                        effect_sizes = results.effect_size.items()
                        sub_dl = "<ul>"
                        for name, value in results.effect_size.items():
                            sub_dl += dl_pair(name, f"{value:.5f}")
                        sub_dl += "</ul>"
                        print(f"<li><b>Effect size:</b>{sub_dl}</li>")
                    if results.null_hypothesis:
                        print(dl_pair("Null hypothesis", results.null_hypothesis))
                    if results.interpretation:
                        print(dl_pair("Interpretation", results.interpretation))
                    print("</ul>")
                else:
                    print("<p>{html.escape(str(results))}</p>")
        return html_out.getvalue()
