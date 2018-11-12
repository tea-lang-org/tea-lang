from typing import Any, Dict

class ColumnProperties:
    def normal(self):
        pass

class Experiment:
    data: Any
    column_properties: Dict[str, ColumnProperties]

    def __init__(self) -> None:
        self.data = None
        self.column_properties = {}
    
    def column(self, name):
        return self.column_properties[name]
    
    @staticmethod
    def load(name, file):
        exp = Experiment()
        exp.column_properties['sleep_hours'] = ColumnProperties()
        return exp
    
    def pretty_print(self):
        exp = """Experiment {
            name: ...
            file: ...
            sleep: number,
            age: range(0, 10),
        }
        """
        return exp

exp = Experiment.load('BlueStudies', 'file_path')
sleep = exp.column('sleep_hours')
sleep.normal()
print(exp.pretty_print())

