from tea.helpers.study_type_determiner import StudyTypeDeterminer
from tea.ast import (Node, Variable, Literal,
                     Equal, NotEqual, LessThan,
                     LessThanEqual, GreaterThan, GreaterThanEqual,
                     Relate, PositiveRelationship
                     )
from tea.runtimeDataStructures.dataset import Dataset
from tea.runtimeDataStructures.varData import VarData
from tea.runtimeDataStructures.bivariateData import BivariateData
from tea.runtimeDataStructures.multivariateData import MultivariateData
from tea.runtimeDataStructures.resultData import ResultData
from tea.runtimeDataStructures.combinedData import CombinedData
from tea.helpers.evaluateHelperMethods import assign_roles, add_paired_property, execute_test
from tea.z3_solver.solver import synthesize_tests

from typing import Optional
from typing import Dict

import attr
import numpy as np  # Use some stats from numpy instead
import pandas as pd


class VarDataFactory:
    def __init__(self, study_type_determiner: StudyTypeDeterminer):
        self.study_type_determiner = study_type_determiner

    # TODO: Pass participant_id as part of experimental design, not load_data

    def create_vardata(self, dataset: Dataset, expr: Node, assumptions: Dict[str, str], design: Optional[Dict[str, str]] = None) -> Optional[VarData]:
        if isinstance(expr, Variable):
            return self.__create_variable_vardata(dataset, expr)

        elif isinstance(expr, Literal):
            return self.__create_literal_vardata(dataset, expr)

        elif isinstance(expr, Equal):
            return self.__create_equal_vardata(dataset, expr, assumptions, design)

        elif isinstance(expr, NotEqual):
            return self.__create_not_equal_vardata(dataset, expr, assumptions, design)

        elif isinstance(expr, LessThan):
            return self.__create_less_than_vardata(dataset, expr, assumptions, design)

        elif isinstance(expr, LessThanEqual):
            return self.__create_less_than_equal_vardata(dataset, expr, assumptions, design)

        elif isinstance(expr, GreaterThan):
            return self.__create_greater_than_vardata(dataset, expr, assumptions, design)

        elif isinstance(expr, GreaterThanEqual):
            return self.__create_greater_than_equal_vardata(dataset, expr, assumptions, design)

        elif isinstance(expr, Relate):
            return self.__create_relate_vardata(dataset, expr, assumptions, design)

        elif isinstance(expr, PositiveRelationship):
            return self.__create_positive_relationship_vardata(dataset, expr, assumptions, design)

        # elif isinstance(expr, Relationship):
        #     import pdb; pdb.set_trace()

        # elif isinstance(expr, Mean):
        #     var = self.create_vardata(dataset, expr.var)
        #     assert isinstance(var, VarData)

        #     # bs.bootstrap(var.dataframe, stat_func=
        #     # bs_stats.mean)

        #     raise Exception('Not implemented Mean')

    def __create_variable_vardata(self, dataset: Dataset, expr: Variable) -> VarData:
        # dataframe = dataset[expr.name] # I don't know if we want this. We may want to just store query (in metadata?) and
        # then use query to get raw data later....(for user, not interpreter?)
        metadata = dataset.get_variable_data(expr.name)  # (dtype, categories)
        # if expr.name == 'strategy':
        #     import pdb; pdb.set_trace()
        metadata['var_name'] = expr.name
        metadata['query'] = ''
        return VarData(metadata)

    def __create_literal_vardata(self, dataset: Dataset, expr: Literal) -> VarData:
        data = pd.Series([expr.value] * len(dataset.data), index=dataset.data.index)  # Series filled with literal value
        # metadata = None # metadata=None means literal
        metadata = dict()  # metadata=None means literal
        metadata['var_name'] = ''  # because not a var in the dataset
        metadata['query'] = ''
        metadata['value'] = expr.value
        return VarData(metadata, data)

    def __create_equal_vardata(self, dataset: Dataset, expr: Equal, assumptions: Dict[str, str], design: Optional[Dict[str, str]]) -> VarData:
        lhs = self.create_vardata(dataset, expr.lhs, assumptions, design)
        rhs = self.create_vardata(dataset, expr.rhs, assumptions, design)
        assert isinstance(lhs, VarData)
        assert isinstance(rhs, VarData)

        metadata = lhs.metadata
        if (isinstance(expr.rhs, Literal)):
            metadata['query'] = f" == \'{rhs.metadata['value']}\'"  # override lhs metadata for query
        elif (isinstance(expr.rhs, Variable)):
            metadata['query'] = f" == {rhs.metadata['var_name']}"
        else:
            raise ValueError(f"Not implemented for {rhs}")

        return VarData(metadata)

    def __create_not_equal_vardata(self, dataset: Dataset, expr: NotEqual, assumptions: Dict[str, str], design: Optional[Dict[str, str]]) -> VarData:
        rhs = self.create_vardata(dataset, expr.rhs, assumptions, design)
        lhs = self.create_vardata(dataset, expr.lhs, assumptions, design)
        assert isinstance(rhs, VarData)
        assert isinstance(lhs, VarData)

        metadata = lhs.metadata
        if (isinstance(expr.rhs, Literal)):
            metadata['query'] = " != \'\'"  # override lhs metadata for query
        elif (isinstance(expr.rhs, Variable)):
            metadata['query'] = f" != {rhs.metadata['var_name']}"
        else:
            raise ValueError(f"Not implemented for {rhs}")
        return VarData(metadata)

    def __create_less_than_vardata(self,  dataset: Dataset, expr: LessThan, assumptions: Dict[str, str], design: Optional[Dict[str, str]]) -> VarData:
        lhs = self.create_vardata(dataset, expr.lhs, assumptions, design)
        rhs = self.create_vardata(dataset, expr.rhs, assumptions, design)
        assert isinstance(lhs, VarData)
        assert isinstance(rhs, VarData)

        dataframe = None
        metadata = rhs.metadata

        if (not lhs.metadata):
            raise ValueError('Malformed Relation. Filter on Variables must have variable as rhs')
        elif (lhs.metadata['dtype'] is DataType.NOMINAL):
            raise ValueError('Cannot compare nominal values with Less Than')
        elif (lhs.metadata['dtype'] is DataType.ORDINAL):
            # TODO May want to add a case should RHS and LHS both be variables
            # assert (rhs.metadata is None)
            comparison = rhs.dataframe.iloc[0]
            if (isinstance(comparison, str)):
                categories = lhs.metadata['categories']  # OrderedDict
                # Get raw Pandas Series indices for desired data
                ids = [i for i, x in enumerate(lhs.dataframe) if categories[x] < categories[comparison]]
                # Get Pandas Series set indices for desired data
                p_ids = [lhs.dataframe.index.values[i] for i in ids]
                # Create new Pandas Series with only the desired data, using set indices
                dataframe = pd.Series(lhs.dataframe, p_ids)
                dataframe.index.name = dataset.pid_col_name

            elif (np.issubdtype(comparison, np.integer)):
                categories = lhs.metadata['categories']  # OrderedDict
                # Get raw Pandas Series indices for desired data
                ids = [i for i, x in enumerate(lhs.dataframe) if categories[x] < comparison]
                # Get Pandas Series set indices for desired data
                p_ids = [lhs.dataframe.index.values[i] for i in ids]
                # Create new Pandas Series with only the desired data, using set indices
                dataframe = pd.Series(lhs.dataframe, p_ids)
                dataframe.index.name = dataset.pid_col_name

            else:
                raise ValueError(f"Cannot compare ORDINAL variables to {type(rhs.dataframe.iloc[0])}")

        elif (lhs.metadata['dtype'] is DataType.INTERVAL or lhs.metadata['dtype'] is DataType.RATIO):
            comparison = rhs.dataframe.iloc[0]
            # Get raw Pandas Series indices for desired data
            ids = [i for i, x in enumerate(lhs.dataframe) if x < comparison]
            # Get Pandas Series set indices for desired data
            p_ids = [lhs.dataframe.index.values[i] for i in ids]
            # Create new Pandas Series with only the desired data, using set indices
            dataframe = pd.Series(lhs.dataframe, p_ids)
            dataframe.index.name = dataset.pid_col_name

        else:
            raise Exception(f"Invalid Less Than Operation:{lhs} < {rhs}")

        if (isinstance(expr.rhs, Literal)):
            metadata['query'] = " < \'\'"  # override lhs metadata for query
        elif (isinstance(expr.rhs, Variable)):
            metadata['query'] = f" < {rhs.metadata['var_name']}"
        else:
            raise ValueError(f"Not implemented for {rhs}")
        return VarData(metadata)

    def __create_less_than_equal_vardata(self,  dataset: Dataset, expr: LessThanEqual, assumptions: Dict[str, str], design: Optional[Dict[str, str]]) -> VarData:
        lhs = self.create_vardata(dataset, expr.lhs, assumptions, design)
        rhs = self.create_vardata(dataset, expr.rhs, assumptions, design)
        assert isinstance(lhs, VarData)
        assert isinstance(rhs, VarData)

        dataframe = None
        metadata = rhs.metadata

        if (not lhs.metadata):
            raise ValueError('Malformed Relation. Filter on Variables must have variable as rhs')
        elif (lhs.metadata['dtype'] is DataType.NOMINAL):
            raise ValueError('Cannot compare nominal values with Less Than')
        elif (lhs.metadata['dtype'] is DataType.ORDINAL):
            # TODO May want to add a case should RHS and LHS both be variables
            # assert (rhs.metadata is None)
            comparison = rhs.dataframe.iloc[0]
            if (isinstance(comparison, str)):
                categories = lhs.metadata['categories']  # OrderedDict
                # Get raw Pandas Series indices for desired data
                ids = [i for i, x in enumerate(lhs.dataframe) if categories[x] <= categories[comparison]]
                # Get Pandas Series set indices for desired data
                p_ids = [lhs.dataframe.index.values[i] for i in ids]
                # Create new Pandas Series with only the desired data, using set indices
                dataframe = pd.Series(lhs.dataframe, p_ids)
                dataframe.index.name = dataset.pid_col_name

            elif (np.issubdtype(comparison, np.integer)):
                categories = lhs.metadata['categories']  # OrderedDict
                # Get raw Pandas Series indices for desired data
                ids = [i for i, x in enumerate(lhs.dataframe) if categories[x] <= comparison]
                # Get Pandas Series set indices for desired data
                p_ids = [lhs.dataframe.index.values[i] for i in ids]
                # Create new Pandas Series with only the desired data, using set indices
                dataframe = pd.Series(lhs.dataframe, p_ids)
                dataframe.index.name = dataset.pid_col_name

            else:
                raise ValueError(f"Cannot compare ORDINAL variables to {type(rhs.dataframe.iloc[0])}")

        elif (lhs.metadata['dtype'] is DataType.INTERVAL or lhs.metadata['dtype'] is DataType.RATIO):
            comparison = rhs.dataframe.iloc[0]
            # Get raw Pandas Series indices for desired data
            ids = [i for i, x in enumerate(lhs.dataframe) if x <= comparison]
            # Get Pandas Series set indices for desired data
            p_ids = [lhs.dataframe.index.values[i] for i in ids]
            # Create new Pandas Series with only the desired data, using set indices
            dataframe = pd.Series(lhs.dataframe, p_ids)
            dataframe.index.name = dataset.pid_col_name

        else:
            raise Exception(f"Invalid Less Than Equal Operation:{lhs} <= {rhs}")

        if (isinstance(expr.rhs, Literal)):
            metadata['query'] = " <= \'\'"  # override lhs metadata for query
        elif (isinstance(expr.rhs, Variable)):
            metadata['query'] = f" <= {rhs.metadata['var_name']}"
        else:
            raise ValueError(f"Not implemented for {rhs}")

        return VarData(metadata)

    def __create_greater_than_vardata(self,  dataset: Dataset, expr: GreaterThan, assumptions: Dict[str, str], design: Optional[Dict[str, str]]) -> VarData:
        lhs = self.create_vardata(dataset, expr.lhs, assumptions, design)
        rhs = self.create_vardata(dataset, expr.rhs, assumptions, design)
        assert isinstance(lhs, VarData)
        assert isinstance(rhs, VarData)

        dataframe = None
        metadata = rhs.metadata

        if (not lhs.metadata):
            raise ValueError('Malformed Relation. Filter on Variables must have variable as rhs')
        elif (lhs.metadata['dtype'] is DataType.NOMINAL):
            raise ValueError('Cannot compare nominal values with Greater Than')
        elif (lhs.metadata['dtype'] is DataType.ORDINAL):
            # TODO May want to add a case should RHS and LHS both be variables
            # assert (rhs.metadata is None)
            comparison = rhs.dataframe.iloc[0]
            if (isinstance(comparison, str)):
                categories = lhs.metadata['categories']  # OrderedDict
                # Get raw Pandas Series indices for desired data
                ids = [i for i, x in enumerate(lhs.dataframe) if categories[x] > categories[comparison]]
                # Get Pandas Series set indices for desired data
                p_ids = [lhs.dataframe.index.values[i] for i in ids]
                # Create new Pandas Series with only the desired data, using set indices
                dataframe = pd.Series(lhs.dataframe, p_ids)
                dataframe.index.name = dataset.pid_col_name

            elif (np.issubdtype(comparison, np.integer)):
                categories = lhs.metadata['categories']  # OrderedDict
                # Get raw Pandas Series indices for desired data
                ids = [i for i, x in enumerate(lhs.dataframe) if categories[x] > comparison]
                # Get Pandas Series set indices for desired data
                p_ids = [lhs.dataframe.index.values[i] for i in ids]
                # Create new Pandas Series with only the desired data, using set indices
                dataframe = pd.Series(lhs.dataframe, p_ids)
                dataframe.index.name = dataset.pid_col_name

            else:
                raise ValueError(f"Cannot compare ORDINAL variables to {type(rhs.dataframe.iloc[0])}")

        elif (lhs.metadata['dtype'] is DataType.INTERVAL or lhs.metadata['dtype'] is DataType.RATIO):
            comparison = rhs.dataframe.iloc[0]
            # Get raw Pandas Series indices for desired data
            ids = [i for i, x in enumerate(lhs.dataframe) if x > comparison]
            # Get Pandas Series set indices for desired data
            p_ids = [lhs.dataframe.index.values[i] for i in ids]
            # Create new Pandas Series with only the desired data, using set indices
            dataframe = pd.Series(lhs.dataframe, p_ids)
            dataframe.index.name = dataset.pid_col_name

        else:
            raise Exception(f"Invalid Greater Than Operation:{lhs} > {rhs}")

        if (isinstance(expr.rhs, Literal)):
            metadata['query'] = " > \'\'"  # override lhs metadata for query
        elif (isinstance(expr.rhs, Variable)):
            metadata['query'] = f" > {rhs.metadata['var_name']}"
        else:
            raise ValueError(f"Not implemented for {rhs}")

        return VarData(metadata)

    def __create_greater_than_equal_vardata(self,  dataset: Dataset, expr: GreaterThanEqual, assumptions: Dict[str, str], design: Optional[Dict[str, str]]) -> VarData:
        lhs = self.create_vardata(dataset, expr.lhs, assumptions, design)
        rhs = self.create_vardata(dataset, expr.rhs, assumptions, design)
        assert isinstance(lhs, VarData)
        assert isinstance(rhs, VarData)

        dataframe = None
        metadata = rhs.metadata

        if (not lhs.metadata):
            raise ValueError('Malformed Relation. Filter on Variables must have variable as rhs')
        elif (lhs.metadata['dtype'] is DataType.NOMINAL):
            raise ValueError('Cannot compare nominal values with Greater Than Equal')
        elif (lhs.metadata['dtype'] is DataType.ORDINAL):
            # TODO May want to add a case should RHS and LHS both be variables
            # assert (rhs.metadata is None)
            comparison = rhs.dataframe.iloc[0]
            if (isinstance(comparison, str)):
                categories = lhs.metadata['categories']  # OrderedDict
                # Get raw Pandas Series indices for desired data
                ids = [i for i, x in enumerate(lhs.dataframe) if categories[x] >= categories[comparison]]
                # Get Pandas Series set indices for desired data
                p_ids = [lhs.dataframe.index.values[i] for i in ids]
                # Create new Pandas Series with only the desired data, using set indices
                dataframe = pd.Series(lhs.dataframe, p_ids)
                dataframe.index.name = dataset.pid_col_name

            elif (np.issubdtype(comparison, np.integer)):
                categories = lhs.metadata['categories']  # OrderedDict
                # Get raw Pandas Series indices for desired data
                ids = [i for i, x in enumerate(lhs.dataframe) if categories[x] >= comparison]
                # Get Pandas Series set indices for desired data
                p_ids = [lhs.dataframe.index.values[i] for i in ids]
                # Create new Pandas Series with only the desired data, using set indices
                dataframe = pd.Series(lhs.dataframe, p_ids)
                dataframe.index.name = dataset.pid_col_name

            else:
                raise ValueError(f"Cannot compare ORDINAL variables to {type(rhs.dataframe.iloc[0])}")

        elif (lhs.metadata['dtype'] is DataType.INTERVAL or lhs.metadata['dtype'] is DataType.RATIO):
            comparison = rhs.dataframe.iloc[0]
            # Get raw Pandas Series indices for desired data
            ids = [i for i, x in enumerate(lhs.dataframe) if x >= comparison]
            # Get Pandas Series set indices for desired data
            p_ids = [lhs.dataframe.index.values[i] for i in ids]
            # Create new Pandas Series with only the desired data, using set indices
            dataframe = pd.Series(lhs.dataframe, p_ids)
            dataframe.index.name = dataset.pid_col_name

        else:
            raise Exception(f"Invalid Greater Than Equal Operation:{lhs} >= {rhs}")
        if (isinstance(expr.rhs, Literal)):
            metadata['query'] = " >= \'\'"  # override lhs metadata for query
        elif (isinstance(expr.rhs, Variable)):
            metadata['query'] = f" >= {rhs.metadata['var_name']}"
        else:
            raise ValueError(f"Not implemented for {rhs}")
        return VarData(metadata)

    def __create_relate_vardata(self,  dataset: Dataset, expr: Relate, assumptions: Dict[str, str], design: Optional[Dict[str, str]]) -> VarData:
        vars = []
        for v in expr.vars:
            eval_v = self.create_vardata(dataset, v, design)

            if not eval_v:
                raise ValueError("The variables you are referencing are not defined as variables in your list of variables.")
            assert isinstance(eval_v, VarData)

            vars.append(eval_v)

        # What kind of study are we analyzing?
        study_type = self.study_type_determiner.determine_study_type(vars, design)

        # Assign roles to variables we are analyzing
        vars = assign_roles(vars, study_type, design)

        combined_data = None
        assumed_alpha = float(assumptions['alpha']) if 'alpha' in assumptions else attr.fields(CombinedData).alpha.default

        # Do we have a Bivariate analysis?
        if len(vars) == 2:
            combined_data = BivariateData(vars, study_type, alpha=assumed_alpha)
        else:  # Do we have a Multivariate analysis?
            combined_data = MultivariateData(vars, study_type, alpha=assumed_alpha)

        # Add paired property
        add_paired_property(dataset, combined_data, study_type, design)  # check sample sizes are identical

        # Infer stats tests (mingled with)
        tests = synthesize_tests(dataset, assumptions, combined_data)
        
        if dataset.data.empty:
            print("Statistical Tests for empty dataset")
            return tests
        """"
        # verify_properties(properties_and_tests)
        # get_tests
        # execute_tests
        # interpret_tests_results
        # print(tests)
        for test in tests:
            print("\nValid test: %s" % test.name)
            print("Properties:")
            properties = test.properties()
            for prop in properties:
                property_identifier = ""
                if prop.scope == "test":
                    property_identifier = test.name + ": " + prop.name
                else:
                    for var_indices in test.properties_for_vars[prop]:
                        for var_index in var_indices:
                            property_identifier += f"variable {test.test_vars[var_index].name} "
                        property_identifier += ": %s" % prop.name
                print(property_identifier)
        """

        # Else
        # Execute and store results from each valid test
        results = {}
        if len(tests) == 0:
            tests.append('bootstrap')  # Default to bootstrap

        
        # Check to see if there is data on which to execute the synthesized tests
        if dataset.has_empty_data():
            return results

        test_objs = ()

        for test in tests:
            test_result = execute_test(dataset, design, expr.predictions, combined_data, test)
            results[test] = test_result

        for obj in test_objs:
            obj.execute()
            obj.visualize()

        res_data = ResultData(results, combined_data)

        follow_up = []

        # There are multiple hypotheses to follow-up and correct for
        if expr.predictions and len(expr.predictions) > 1:
            for pred in expr.predictions:
                # create follow-up expr Node (to self.create_vardata recursively)
                pred_res = self.create_vardata(dataset, pred, assumptions, design)
                follow_up.append(pred_res)  # add follow-up result to follow_up

        res_data.add_follow_up(follow_up)  # add follow-up results to the res_data object
        """
        # TODO: use a handle here to more generally/modularly support corrections, need a more generic data structure for this!
        if expr.predictions:
            preds = expr.predictions

            # There are multiple comparisons
            # if len(preds > 1): 
            # FOR DEBUGGING: 
            if len(preds) >= 1: 
                correct_multiple_comparison(res_data,  len(preds))
        """
        # import pdb; pdb.set_trace()
        return res_data

    def __create_positive_relationship_vardata(self,  dataset: Dataset, expr: PositiveRelationship, assumptions: Dict[str, str], design: Optional[Dict[str, str]]) -> Optional[VarData]:
        # get variables
        vars = [expr.lhs.var, expr.rhs.var]

        # create a Relate object
        pos_relate_expr = Relate(vars)
        return self.create_vardata(dataset, pos_relate_expr, assumptions, design)
