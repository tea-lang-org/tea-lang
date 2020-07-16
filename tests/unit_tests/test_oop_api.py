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

    
    def test_incremental_ctor(self): 
        pass