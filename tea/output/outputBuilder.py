from tea.runtimeDataStructures.testResults import *
from tea.output.outputFormatter import OutputFormatter

from typing import Dict, List

class OutputBuilder():
    formatter: OutputFormatter

    def __init__(self, test_to_results: Dict[str, TestResult]): 
        # Construct formatter
        self.formatter = OutputFormatter()

        results = list() 

        for name, res in test_to_results.items(): 
            results.append(res)

        self._build_analysis_output(test_results=results)


    def _build_variable_output(self, variables): 
        pass

    def _build_analysis_output(self, test_results: List[TestResult]): 
        # Format each test
        for res in test_results: 
            self.formmater.format_test_result(res)
            
    def _build_preregistration_output(self): 
        pass

    def format(self): 
        pass


class ConstraintSummary(): 
    pass 

class VariableSummary(): 
    pass  

class AnalysisSummary(): 
    pass 

class NotebookSummary(): 
    pass 

# TODO: Identify appropriate output targets, maybe OSF or something else? 
class PreRegistration(): 
    pass 