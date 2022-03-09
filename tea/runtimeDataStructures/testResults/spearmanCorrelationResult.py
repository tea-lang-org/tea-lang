from tea.runtimeDataStructures.testResults.testResult import TestResult, get_variable_type
from tea.runtimeDataStructures.dataset import Dataset
from tea.runtimeDataStructures.varData import VarData
from tea.ast import Relationship

from typing import Any, Dict, List
import altair as alt
from scipy import stats
import numpy as np

class SpearmanCorrelationResult(TestResult): 
    
    def __init__(self, name: str, test_statistic: Any, p_value: float, prediction: Relationship, alpha: float, dof: int, dataset: Dataset, vars: List[VarData], x: VarData = None, y: VarData = None, adjusted_p_value: float = None, corrected_p_value: float = None, table: Any = None, group_descriptive_statistics: Dict = None):
        assert(len(vars) == 2)
        super().__init__(name, test_statistic, p_value, prediction, alpha, dof, dataset, vars, x, y, adjusted_p_value, corrected_p_value, table, group_descriptive_statistics)

    def generate_template_text(self):
        x = self.vars[0]
        y = self.vars[1]
        df = self.vars[0].get_sample_size() - 2 # Determine degrees of freedom 
        rho, p_val = stats.spearmanr(x, y)

        significance = "did not"
        if p_val < 0.05:
            significance = "did"

        # Calculate confidence interval
        stderr = 1.0 / np.sqrt(self.vars[0].get_sample_size() - 3)
        delta = stderr * 1.96
        ci = np.tanh(np.arctanh(rho) - delta), np.tanh(np.arctanh(rho) + delta)

        p_string = "p = " + "{0:.3f}".format(p_val).lstrip('0')
        if p_val < 0.001:
            p_string = "p < .001"

        r_string = "{0:.2f}".format(abs(rho)).lstrip('0')
        if rho < 0:
            r_string = "-" + r_string
        r_string = "r(" + str(df) + ") = " + r_string

        ci_1_string = "{0:.2f}".format(abs(ci[0])).lstrip('0')
        if ci[0] < 0:
            ci_1_string = "-" + ci_1_string 
        ci_2_string = "{0:.2f}".format(abs(ci[1])).lstrip('0')
        if ci[1] < 0:
            ci_2_string = "-" + ci_2_string 

        ci_string = "[" + ci_1_string + ", " + ci_2_string + "]"

        print("The Spearman's rho correlation " + significance + " detect a significant correlation between " \
            + str(self.vars[0]) + " and " + str(self.vars[1]) + ", " + r_string +  ", " \
            + ci_string + ", " + p_string)

    def generate_visualization(self):
        # Visualize statistical test result using Franconceri recommendations
        # Scatterplot
        var_0 = self.vars[0] 
        var_1 = self.vars[1] 

        # Determine the visual data types
        var_0_type = get_variable_type(var_0)
        var_1_type = get_variable_type(var_1)
        # Create the variable names as strings for altair chart
        var_0_name = var_0.get_name() + ":" + var_0_type
        var_1_name = var_1.get_name() + ":" + var_1_type

        # TODO: Are we assigning the correct variable to the X axis???
        return alt.Chart(self.dataset.data).mark_circle(size=60).encode(
            x=var_0_name,
            y=var_1_name,
            tooltip=[var_0.get_name(), var_1.get_name()]
        ).interactive()