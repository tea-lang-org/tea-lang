from abc import ABC, abstractmethod
import contextlib
from dataclasses import dataclass
import html
import io
from typing import Any, Dict, List, Union, Optional, Tuple

import attr

from tea.global_vals import *
from tea.runtimeDataStructures.combinedData import CombinedData
from tea.runtimeDataStructures.value import Value
from tea.z3_solver.solver import all_tests

# TODO: move the classes outside the file


class DataClassWithOptionalFieldsSetToNoneByDefault:
    def __init_subclass__(cls, *args, **kwargs) -> None:
        for field, annotation in cls.__annotations__.items():
            try:
                # below we check if we have either Union[type, ..., None] or Optional[type]
                if annotation.__origin__ is Union and type(None) in annotation.__args__:
                    if not hasattr(cls, field):  # make sure that we don't have default field already
                        setattr(cls, field, None)
            except AttributeError:
                pass

        super().__init_subclass__(*args, **kwargs)


# below class has potential to replace ResultData in the future
@dataclass(frozen=False)
class TestOutputData(DataClassWithOptionalFieldsSetToNoneByDefault):
    name: str
    result_name: Optional[str]
    statistic: Optional[Union[Dict, float]]
    p_value: Optional[Union[str, float]]
    adjusted_p_value: Optional[float]
    alpha: Optional[float]
    table: Optional[Any]  # type?
    dof: Optional[Any]  # type?
    effect_sizes: Optional[List[Tuple[str, float]]]
    null_hypothesis: Optional[str]
    interpretation: Optional[str]
    results: Optional[str]
    assumption: Union[str, List[str]] = "None"


# Note: This ABC can be implemented by OutputDataHtmlFormatter later on
class AbstractOutputDataFormatter(ABC):
    @abstractmethod
    def format_output_data(self, data: "TestOutputData"):
        return ""

    @abstractmethod
    def format_output_data_list(self, data: List["TestOutputData"]):
        return ""


class OutputDataTextFormatter(AbstractOutputDataFormatter):
    def format_output_data(self, data: "TestOutputData"):
        output = f"\nTest: {data.test_name}\n"
        assumption = "\n".join(data.assumption) if isinstance(data.assumption, list) else data.assumption
        output += f"***Test assumptions:\n{assumption}\n\n"
        output += "***Test results:\n"

        if data.name is not None:
            output += f"name = {data.name}\n"
        if data.test_statistic is not None:
            if isinstance(data.test_statistic, dict):
                output += f"test_statistic = {data.test_statistic}\n"
            else:
                output += f"test_statistic = {'%.5f'%(data.test_statistic)}\n"
        if data.p_value is not None:
            if isinstance(data.p_value, str):
                output += f"p_value = {data.p_value}\n"
            else:
                output += f"p_value = {'%.5f'%(data.p_value)}\n"
        if data.adjusted_p_value is not None:
            output += f"adjusted_p_value = {'%.5f'%(data.adjusted_p_value)}\n"
        if data.alpha is not None:
            output += f"alpha = {data.alpha}\n"
        if data.dof is not None:
            output += f"dof = {data.dof}\n"
        if data.table is not None:
            output += f"table = {data.table}\n"
        for effect_size_name, effect_size_value in data.effect_sizes if data.effect_sizes is not None else []:
            output += f"{effect_size_name} = {'%.5f'%(effect_size_value)}\n"
        if data.null_hypothesis is not None:
            output += f"Null hypothesis = {data.null_hypothesis}\n"
        if data.interpretation is not None:
            output += f"Interpretation = {data.interpretation}\n"
        if data.results is not None:
            output += f"{str(data.results)}\n"

    def format_output_data_list(self, data_list: List["TestOutputData"]) -> str:
        output = "\nResults:\n--------------"
        for data in data_list:
            output += self.write_output_data_list(data)
            output += "\n"


# This class can be seen as a converter fron ResultData to TestOutputData
class OutputBuilder:
    def build_one_result(self, test_name: str, results: Any) -> TestOutputData:
        testOutputData = TestOutputData(test_name)
        if hasattr(results, "__dict__"):
            testOutputData.result_name = results.name
            testOutputData.statistic = results.test_statistics
            testOutputData.p_value = results.p_value
            testOutputData.adjusted_p_value = results.adjusted_p_value
            testOutputData.alpha = results.alpha
            testOutputData.dof = results.dof
            testOutputData.table = results.table
            if "effect_size" in results.__dict__:
                effect_sizes = results.effect_size.items()
                testOutputData.table = results.table = [
                    (effect_size_name, effect_size_value) for effect_size_name, effect_size_value in effect_sizes
                ]
            testOutputData.null_hypothesis = results.null_hypothesis
            testOutputData.interpretation = results.interpretation

        else:
            testOutputData.results = str(results)

    def build_output_from_result_data(
        self, resultData: "ResultData", test_to_results: Dict, test_to_assumptions: Dict, follow_up_results: Dict
    ) -> List[TestOutputData]:
        results = []  # type: List[TestOutputData]
        for test_name, results in test_to_results.items():
            testOutputData = self.build_one_result(test_name, results)
            if test_name in test_to_assumptions:
                testOutputData.assumption = test_to_assumptions[test_name]
            results.append(testOutputData)

        if hasattr(resultData, "follow_up_results"):  # not empty
            raise NotImplementedError("Not implemented yet. How to do that?")
            for res in follow_up_results:
                print("\nFollow up for multiple comparisons: \n")
                print(res)

        return results


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
                    elif (
                        applied_prop.property.name == "has_independent_observations"
                        or applied_prop.property.name == "has_paired_observations"
                    ):
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
        results = [v for k, v in self.test_to_results.items()]
        return results

    def bonferroni_correction(self, num_comparisons):
        for key, value in self.test_to_results.items():
            value.bonferroni_correction(num_comparisons)
        return self

    def _pretty_print_2(self):
        builder = OutputBuilder()
        formatter = OutputDataTextFormatter()
        outputs = builder.build_output_from_result_data(
            self, self.test_to_results, self.test_to_assumptions, self.follow_up_results
        )

        if hasattr(self, "follow_up_results"):  # not empty
            for res in self.follow_up_results:
                print("\nFollow up for multiple comparisons: \n")
                print(res)
        return formatter.format_output_data_list(outputs)

    def _pretty_print(self):
        output = "\nResults:\n--------------"
        for test_name, results in self.test_to_results.items():
            output += f"\nTest: {test_name}\n"
            test_assumptions = "None"
            if test_name in self.test_to_assumptions:
                test_assumptions = ("\n").join(self.test_to_assumptions[test_name])
            output += f"***Test assumptions:\n{test_assumptions}\n\n"
            output += "***Test results:\n"

            if hasattr(results, "__dict__"):

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

        if hasattr(self, "follow_up_results"):  # not empty
            for res in self.follow_up_results:
                print("\nFollow up for multiple comparisons: \n")
                print(res)

        return output

    def add_follow_up(self, follow_up_res_data: list):
        if len(follow_up_res_data) >= 1:
            setattr(self, "follow_up_results", follow_up_res_data)

    # def __repr__(self):
    #     # return self._pretty_print()
    #     return self

    def __str__(self):  # Maybe what the user sees?
        return self._pretty_print_2()
        # return self._pretty_print()

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
