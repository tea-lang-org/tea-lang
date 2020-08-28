from tea.global_vals import *

# Concrete Statistical Test class for Pearson's Correlation
class Pearsons_Correlation_Test(AbstractStatisticalTest):

    # function for determining the encoding type for use with altair 
    def get_variable_type(var):
        if var.is_continuous():
            # indicate variable is quantitative
            return "Q"
        elif var.is_nominal():
            # indicate the variable is nominal
            return "N"
        elif var.is_ordinal():
            # indicate the variable is ordinal 
            return "O"
        else:
            raise ValueError(f"Invalid type, unsure how to resolve this type: {var_0.metadata['dtype']}")

    def get_test_type(self):
        super().get_test_type
    def execute(self, data, design, predictions, combined_data: CombinedData):
        # referencing pearson_corr in evaluateHelperMethods

        """
        # https://docs.scipy.org/doc/scipy-0.14.0/reference/generated/scipy.stats.pearsonr.html
        # Parameters: x (array-like) | y (array-like)
        assert len(combined_data.vars) == 2

        data = []
        for var in combined_data.vars:
            var_data = get_data(dataset, var)
            data.append(var_data)

        assert len(data) == 2

        if predictions:
            if isinstance(predictions[0], list):
                prediction = predictions[0][0]
            else:
                prediction = predictions[0]
        else:
            prediction = None
        t_stat, p_val = stats.pearsonr(data[0], data[1])
        dof = None
        test_result = TestResult(
            name=PEARSON_NAME,
            test_statistic=t_stat,
            p_value=p_val,
            prediction=prediction,
            dof=dof,
            alpha=combined_data.alpha,
        )
        return test_result
        """

        pass

    def visualize(self, dataset: Dataset, design, predictions, combined_data: CombinedData):
        list_vars = combined_data.vars # will return a list of VarData objects

        # What type is each VarData obj in list_vars?
        try:
            # get the variables
            var_0 = list_vars[0]
            var_1 = list_vars[1]

            # determine the visual data types
            var_0_type = get_variable_type(var_0)
            var_1_type = get-variable_type(var_1)

            # create the strings for altair chart
            var_0_name = var_0.get_name() + var_0_type
            var_1_name = var_1.get_name() + var_1_type


            # do something here with the altair visualization
            # how do we determine what goes for the x and y axes?

        except ValueError as e:
            print(e)
    def text_output():
        pass
    def __str__(self):
        super().__str__()