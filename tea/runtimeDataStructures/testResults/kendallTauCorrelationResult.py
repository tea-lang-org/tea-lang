from tea.runtimeDataStructures.testResults.testResult import TestResult, get_variable_type
from tea.runtimeDataStructures.dataset import Dataset
from tea.runtimeDataStructures.varData import VarData
from tea.ast import Relationship

from typing import Any, Dict, List
import altair as alt
from scipy import stats
import numpy as np

class KendallTauCorrelationResult(TestResult): 
    
    def __init__(self, name: str, test_statistic: Any, p_value: float, prediction: Relationship, alpha: float, dof: int, dataset: Dataset, vars: List[VarData], x: VarData = None, y: VarData = None, adjusted_p_value: float = None, corrected_p_value: float = None, table: Any = None, group_descriptive_statistics: Dict = None):
        assert(len(vars) == 2)
        super().__init__(name, test_statistic, p_value, prediction, alpha, dof, dataset, vars, x, y, adjusted_p_value, corrected_p_value, table, group_descriptive_statistics)
        self.set_dof()

    def set_dof(self):
        import pdb; pdb.set_trace()
        self.dof = self.vars[0].get_sample_size() - 2

    def generate_template_text(self):
        p_val = self.p_value
        tau = self.test_statistic

        assert(isinstance(self.dof, int))

        significance = "did not"
        if p_val < 0.05:
            significance = "did"

        # Calculate confidence interval
        stderr = 1.0 / np.sqrt(self.vars[0].get_sample_size() - 3)
        delta = stderr * 1.96
        ci = np.tanh(np.arctanh(tau) - delta), np.tanh(np.arctanh(tau) + delta)

        p_string = "p = " + "{0:.3f}".format(p_val).lstrip('0')
        if p_val < 0.001:
            p_string = "p < .001"

        t_string = "{0:.2f}".format(abs(tau)).lstrip('0')
        if tau < 0:
            t_string = "-" + t_string
        t_string = "r(" + str(self.dof) + ") = " + t_string

        ci_1_string = "{0:.2f}".format(abs(ci[0])).lstrip('0')
        if ci[0] < 0:
            ci_1_string = "-" + ci_1_string 
        ci_2_string = "{0:.2f}".format(abs(ci[1])).lstrip('0')
        if ci[1] < 0:
            ci_2_string = "-" + ci_2_string 

        ci_string = "[" + ci_1_string + ", " + ci_2_string + "]"

        return "The Kendall's Tau correlation " + significance + " detect a significant correlation between " \
            + str(self.vars[0].get_name()) + " and " + str(self.vars[1].get_name()) + ", " + t_string +  ", " \
            + ci_string + ", " + p_string

    def generate_visualization(self):
        var_0 = self.vars[0] 
        var_1 = self.vars[1] 

        # Determine the visual data types
        var_0_type = get_variable_type(var_0)
        var_1_type = get_variable_type(var_1)
        # Create the variable names as strings for altair chart
        var_0_name = var_0.get_name() + ":" + var_0_type
        var_1_name = var_1.get_name() + ":" + var_1_type

        if var_0_type == 'Q' and var_1_type == 'Q':       
            return alt.Chart(self.dataset.data).mark_circle(size=60).encode(
                x=var_0_name,
                y=var_1_name,
                tooltip=[var_0.get_name(), var_1.get_name()]
            ).interactive()
        
        if var_0_type == 'Q' and var_1_type == 'N':
            return alt.Chart(self.dataset.data).mark_bar(size=35).encode(
                y=var_0_name,
                x=var_1_name,
            ).properties(
                height = 300
            )

        if var_0_type == 'N' and var_1_type == 'Q': 
            return alt.Chart(self.dataset.data).mark_bar(size=35).encode(
                x=var_0_name,
                y=var_1_name,
            ).properties(
                width = 300
            )
        
        # return alt.Chart(self.dataset.data).mark_rect().encode(
        #     x=var_0_name,
        #     y=var_1_name,
        #     color='Creativity:Q'
        # )