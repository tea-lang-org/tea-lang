from tea.runtimeDataStructures.testResults.testResult import TestResult


class OutputFormatter(): 
    # TODO: Return formatted table of Test Result
    def format_test_result(self, test_result: TestResult): 
        null_hypotheis = test_result.null_hypothesis
        interp = test_result.interpretation # maybe unnecessary since already have template text
        text = test_result.template_text
        vis = test_result.visualization

    def format_to_string(self): 
        # Idea: format to all the other files and include them as links/paths in the string output
        # For visualizations, we would have to point to other file types (maybe provide the HTML as the most recommended?)
        pass 

    def format_to_text_file(self): 
        pass  

    def format_to_md_file(self): 
        pass  

    def format_to_html_file(self): 
        pass

    def format_to_pdf_file(self): 
        pass