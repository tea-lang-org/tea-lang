from tea.runtimeDataStructures.testResults.testResult import TestResult, get_variable_type
from tea.runtimeDataStructures.dataset import Dataset
from tea.runtimeDataStructures.varData import VarData
from tea.ast import Relationship

from typing import Any, Dict, List
import altair as alt
from scipy import stats
import numpy as np

# poetry run pytest tests/  run all tests 
# poetry run pytest tests/<file name>   specific file 
# use Python debugger (pdb): import pdb; pdb.set_trace() 
# Create classes in files for each statistical result in runtimeDataStructures 
    # Inherit from TestResult, implement a constructor, generate viz, generate template 

class PearsonCorrelationResult(TestResult): 
    
    def __init__(self, name: str, test_statistic: Any, p_value: float, prediction: Relationship, alpha: float, dof: int, dataset: Dataset, vars: List[VarData], x: VarData = None, y: VarData = None, adjusted_p_value: float = None, corrected_p_value: float = None, table: Any = None, group_descriptive_statistics: Dict = None):
        assert(len(vars) == 2)
        super().__init__(name, test_statistic, p_value, prediction, alpha, dof, dataset, vars, x, y, adjusted_p_value, corrected_p_value, table, group_descriptive_statistics)

    def generate_template_text(self):
        x = self.dataset[self.vars[0]]
        y = self.dataset[self.vars[1]]
        df = len(x) - 2 # Determine degrees of freedom 
        r_val, p_val = stats.pearsonr(x, y)

        significance = "did not"
        if p_val < 0.05:
            significance = "did"

        # Calculate confidence interval
        # https://zhiyzuo.github.io/Pearson-Correlation-CI-in-Python/
        r_z = np.arctanh(r_val)
        stdev = 1/np.sqrt(len(x)-3)
        alpha = 0.05
        z = stats.norm.ppf(1-alpha/2)
        ci = np.tanh((r_z-z*stdev, r_z+z*stdev))

        p_string = "p = " + "{0:.3f}".format(p_val).lstrip('0')
        if p_val < 0.001:
            p_string = "p < .001"

        r_string = "{0:.2f}".format(abs(r_val)).lstrip('0')
        if r_val < 0:
            r_string = "-" + r_string
        r_string = "r(" + str(df) + ") = " + r_string

        ci_1_string = "{0:.2f}".format(abs(ci[0])).lstrip('0')
        if ci[0] < 0:
            ci_1_string = "-" + ci_1_string 
        ci_2_string = "{0:.2f}".format(abs(ci[1])).lstrip('0')
        if ci[1] < 0:
            ci_2_string = "-" + ci_2_string 

        ci_string = "[" + ci_1_string + ", " + ci_2_string + "]"

        return "The Pearson correlation " + significance + " detect a significant correlation between " \
                + str(self.vars[0]) + " and " + str(self.vars[1]) + ", " + r_string +  ", " \
                + ci_string + ", " + p_string

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

        return alt.Chart(self.dataset.data).mark_circle(size=60).encode(
            x=var_0_name,
            y=var_1_name,
            tooltip=[var_0.get_name(), var_1.get_name()]
        ).interactive()