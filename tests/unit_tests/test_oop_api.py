import tea
from tea.api import Mode
from tea.runtimeDataStructures.dataset import Dataset

import unittest
import os

class ApiTests(unittest.TestCase):
    def test_empty_ctor(self): 
        # ACT
        tea_obj = tea.Tea()
        
        # ASSERT
        # Every field/attribute except mode should be None
        self.assertIsNone(tea_obj.data) 
        self.assertIsNone(tea_obj.variables)
        self.assertIsNone(tea_obj.design)
        self.assertIsNone(tea_obj.hypothesis)

        self.assertEquals(tea_obj.mode, Mode.INFER_MODE)

    def test_add_data(self):
        # ACT
        tea_obj = tea.Tea()
        file_path = DataForTests.get_data_path("UScrime.csv")
        tea_obj.add_data(file_path)

        import pandas as pd
        df = pd.read_csv(file_path)
        self.assertTrue(tea_obj.data.data.equals(df))

        # ASSERT
        self.assertIsNotNone(tea_obj.data) 
        self.assertIsNone(tea_obj.variables)
        self.assertIsNone(tea_obj.design)
        self.assertIsNone(tea_obj.hypothesis)
        self.assertEquals(tea_obj.mode, Mode.INFER_MODE)


    def test_declare_variables_length(self): 
        # ACT
        tea_obj = tea.Tea()
        tea_obj.declare_variables(DataForTests.variables_to_define)

        # ASSERT
        self.assertEqual(len(tea_obj.variables), 4)

    def test_declare_variables_should_have_correct_names(self):
        expected_names = ["NominalT", "IntervalT", "OrdinalT", "RatioT"]

        # ACT
        tea_obj = tea.Tea()
        tea_obj.declare_variables(DataForTests.variables_to_define)
        real_names = [var.name for var in tea_obj.variables]

        # ASSERT
        self.assertCountEqual(real_names, expected_names)
    
    def test_declare_variables_should_have_correct_types(self):
        from tea.runtimeDataStructures.variable import NominalVariable, OrdinalVariable, NumericVariable

        tea_obj = tea.Tea()
        tea_obj.declare_variables(DataForTests.variables_to_define)
        vars_to_test = tea_obj.variables
        sorted_vars = sorted(vars_to_test, key=lambda x: x.name)
        self.assertIsInstance(sorted_vars[0], NumericVariable)  # IntervalT
        self.assertIsInstance(sorted_vars[1], NominalVariable)  # NominalT
        self.assertIsInstance(sorted_vars[2], OrdinalVariable)  # OrdinalT
        self.assertIsInstance(sorted_vars[3], NumericVariable)  # RatioT

    def test_declare_variables_is_atomic(self): 
        # ACT
        tea_obj = tea.Tea()
        tea_obj.declare_variables(DataForTests.variables_to_define)

        # ASSERT
        self.assertIsNone(tea_obj.data) 
        self.assertIsNotNone(tea_obj.variables)
        self.assertIsNone(tea_obj.design)
        self.assertIsNone(tea_obj.hypothesis)
        self.assertEquals(tea_obj.mode, Mode.INFER_MODE)
    
    def test_specify_design(self): 
        pass

    def test_assume(self): 
        pass

    def test_set_mode(self): 
        pass

    def test_hypothesize(self): 
        pass

class DataForTests:

    base_url = "https://homes.cs.washington.edu/~emjun/tea-lang/datasets/"
    file_names = [
        "UScrime.csv",
        "statex77.csv",
        "catsData.csv",
        "cholesterol.csv",
        "soya.csv",
        "co2.csv",
        "exam.csv",
        "liar.csv",
        "pbcorr.csv",
        "spiderLong_within.csv",
        "drug.csv",
        "alcohol.csv",
        "ecstasy.csv",
        "gogglesData.csv",
        "gogglesData_dummy.csv",
    ]
    data_paths = [None] * len(file_names)

    variables_to_define = [
        {"name": "RatioT", "data type": "ratio"},
        {"name": "NominalT", "data type": "nominal", "categories": ["Nominal0"]},
        {"name": "OrdinalT", "data type": "ordinal", "categories": ["Ordinal1", "Ordinal2", "Ordinal3"]},
        {"name": "IntervalT", "data type": "interval",},
    ]

    def get_data_path(filename):
        def load_data():
            for i in range(len(DataForTests.data_paths)):
                csv_name = DataForTests.file_names[i]

                csv_url = os.path.join(DataForTests.base_url, csv_name)
                DataForTests.data_paths[i] = Dataset.load(csv_url, csv_name)

        load_data()
        try:
            data_idx = DataForTests.file_names.index(filename)
        except:
            raise ValueError(f"File is not found!:{filename}")
        data_path = DataForTests.data_paths[data_idx]

        return data_path
