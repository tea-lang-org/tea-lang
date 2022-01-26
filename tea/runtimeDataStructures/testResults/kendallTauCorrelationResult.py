from tea.runtimeDataStructures.testResults.testResult import TestResult
from tea.runtimeDataStructures.varData import VarData
from tea.ast import Relationship

from typing import Any, Dict

class KendallTauCorrelationResult(TestResult): 
    
    def __init__(self, name: str, test_statistic: Any, p_value: float, prediction: Relationship, alpha: float, dof: int, x: VarData = None, y: VarData = None, adjusted_p_value: float = None, corrected_p_value: float = None, table: Any = None, group_descriptive_statistics: Dict = None):
        super().__init__(name, test_statistic, p_value, prediction, alpha, dof, x, y, adjusted_p_value, corrected_p_value, table, group_descriptive_statistics)

    def generate_template_text(self):
        return "text"
        raise NotImplementedError

    def generate_visualization(self):
        return "vis"
        raise NotImplementedError