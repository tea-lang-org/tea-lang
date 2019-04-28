import attr
from .value import Value
from .combinedData import CombinedData

@attr.s(init=True, auto_attribs=True)
class MultivariateData(CombinedData):
    pass