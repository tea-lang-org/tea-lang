import tea
from tea.api import Mode

import unittest

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
        import pdb; pdb.set_trace()
        # self.assertTrue(tea_obj.data.equals(df))

        # ASSERT
        self.assertIsNotNone(tea_obj.data) 
        self.assertIsNone(tea_obj.variables)
        self.assertIsNone(tea_obj.design)
        self.assertIsNone(tea_obj.hypothesis)
        self.assertEquals(tea_obj.mode, Mode.INFER_MODE)
        
    
    def test_incremental_ctor(self): 
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
