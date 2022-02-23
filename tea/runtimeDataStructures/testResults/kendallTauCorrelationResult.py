from tea.runtimeDataStructures.testResults.testResult import TestResult, get_variable_type
from tea.runtimeDataStructures.dataset import Dataset
from tea.runtimeDataStructures.varData import VarData
from tea.ast import Relationship

from typing import Any, Dict, List
import altair as alt

class KendallTauCorrelationResult(TestResult): 
    
    def __init__(self, name: str, test_statistic: Any, p_value: float, prediction: Relationship, alpha: float, dof: int, dataset: Dataset, vars: List[VarData], x: VarData = None, y: VarData = None, adjusted_p_value: float = None, corrected_p_value: float = None, table: Any = None, group_descriptive_statistics: Dict = None):
        assert(len(vars) == 2)
        super().__init__(name, test_statistic, p_value, prediction, alpha, dof, dataset, vars, x, y, adjusted_p_value, corrected_p_value, table, group_descriptive_statistics)

    def generate_template_text(self):
        return "text"
        # TODO: Update/customize the specific template for the results
        raise NotImplementedError

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