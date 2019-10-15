import attr
from .combinedData import CombinedData


@attr.s(init=True, auto_attribs=True)
class BivariateData(CombinedData):
    pass