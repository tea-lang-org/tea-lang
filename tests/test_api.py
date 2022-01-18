import tea.api
from tea.api import define_variables
import unittest
from importlib import reload

import os


class ApiTests(unittest.TestCase):
    def setUp(self):
        reload(tea.api)

    def test_load_data_from_csv(self):
        file_path = DataForTests.get_data_path("UScrime.csv")
        data_obj = tea.data(file_path)

        import pandas as pd

        df = pd.read_csv(file_path)
        self.assertTrue(data_obj.data.equals(df))

    def test_load_data_df(self):
        file_path = DataForTests.get_data_path("UScrime.csv")

        import pandas as pd

        df = pd.read_csv(file_path)

        data_obj = tea.data(df)
        self.assertTrue(data_obj.data.equals(df))

    def test_df_is_shallow_copy(self):
        file_path = DataForTests.get_data_path("UScrime.csv")

        import pandas as pd

        df = pd.read_csv(file_path, encoding="utf-8")

        data_obj = tea.data(df)
        df = df.applymap(lambda x: x ** 2)  # square all elements

        self.assertTrue(df.equals(data_obj.data.applymap(lambda x: x ** 2)))

    def test_define_variables_should_give_correct_length(self):
        vars_to_test = define_variables(DataForTests.variables_to_define)

        # ASSERT
        self.assertEqual(len(vars_to_test), 4)

    def test_define_variables_should_have_correct_names(self):
        expected_names = ["NominalT", "IntervalT", "OrdinalT", "RatioT"]

        # ACT
        vars_to_test = define_variables(DataForTests.variables_to_define)
        real_names = [var.name for var in vars_to_test]

        # ASSERT
        self.assertCountEqual(real_names, expected_names)

    def test_define_variables_should_have_correct_types(self):
        from tea.runtimeDataStructures.variable import NominalVariable, OrdinalVariable, NumericVariable

        vars_to_test = define_variables(DataForTests.variables_to_define)
        sorted_vars = sorted(vars_to_test, key=lambda x: x.name)
        self.assertIsInstance(sorted_vars[0], NumericVariable)  # IntervalT
        self.assertIsInstance(sorted_vars[1], NominalVariable)  # NominalT
        self.assertIsInstance(sorted_vars[2], OrdinalVariable)  # OrdinalT
        self.assertIsInstance(sorted_vars[3], NumericVariable)  # RatioT


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

    def get_data_path(filename):
        def load_data():
            for i in range(len(DataForTests.data_paths)):
                csv_name = DataForTests.file_names[i]

                csv_url = os.path.join(DataForTests.base_url, csv_name)
                DataForTests.data_paths[i] = tea.download_data(csv_url, csv_name)

        load_data()
        try:
            data_idx = DataForTests.file_names.index(filename)
        except:
            raise ValueError(f"File is not found!:{filename}")
        data_path = DataForTests.data_paths[data_idx]

        return data_path

    variables_to_define = [
        {"name": "RatioT", "data type": "ratio"},
        {"name": "NominalT", "data type": "nominal", "categories": ["Nominal0"]},
        {"name": "OrdinalT", "data type": "ordinal", "categories": ["Ordinal1", "Ordinal2", "Ordinal3"]},
        {"name": "IntervalT", "data type": "interval",},
    ]
