import attr
from enum import Enum
from typing import Union


class Node(object): 
    def relate(self, other):
        return Relate(self, other)

    # def compare(self, other):
    #     return Compare(self, other)
    
    def select(self, other):
        return Select(self, other)

    def __add__(self, other):
        return Add(self, other)

    def __sub__(self, other):
        return Sub(self, other)

    def __mul__(self, other):
        return Mul(self, other)

    def __truediv__(self, other):
        return Div(self, other)
    
    # MAY NOT NEED TO OVERRIDE AND, OR
    def __and__(self, other):
        return And(self, other)
    
    def __or__(self, other):
        return Or(self, other)


@attr.s(repr=False)
class DataType(Enum):  
    ORDINAL = 0
    NOMINAL = 1
    # for CALCULATIONS, INTERVAL vs. RATIO data is not important distinction
    # for INTERPRETATIONS, important distinction (?)
    INTERVAL = 2 
    RATIO = 3


@attr.s(hash=True, repr=False, cmp=False)
class Variable(Node): 
    # meta data about the variable, determines how the operators are to be/can be executed
    name = attr.ib()
    dtype = attr.ib(type=DataType)
    categories = attr.ib()
    drange = attr.ib()
    
    # children from which self/this Variable is "derived"
    rhs = attr.ib(type=Node)
    lhs = attr.ib(type=Node)

    @classmethod
    def from_spec(cls, name: str, dtype: DataType, cat: list=None, drange: list=None, rhs: Node=None, lhs: Node=None):
        return cls(name, dtype, cat, drange, rhs, lhs)
    
    def category_exists(self, category: str):
        return self.categories and category in self.categories
    
    def subset_equals(self, other: Node):
        return Equal(self, other)
    
    def subset_not_equals(self, other: Node):
        return NotEqual(self, other)

    def subset_lt(self, other: Node):
        return LessThan(self, other)

    def subset_le(self, other: Node):
        return LessThanEqual(self, other)
    
    def subset_ge(self, other: Node):
        return GreaterThanEqual(self, other)
    
    def subset_gt(self, other: Node):
        return GreaterThan(self, other)

    def __repr__(self): 
        return self.name


@attr.s(hash=True, repr=False)
class Select(Node):
    var: Variable # variable to filter on
    condition: tuple # inclusive bounding on both sides
    
    def __repr__(self):
        return (f"Select {self.var} on [{self.condition}]")


@attr.s(hash=True, repr=False)
class Equal(Node):
    lhs = attr.ib(type=Node)
    rhs = attr.ib(type=Node)


@attr.s(hash=True, repr=False)
class NotEqual(Node):
    lhs = attr.ib(type=Node)
    rhs = attr.ib(type=Node)


@attr.s(hash=True, repr=False)
class LessThan(Node):
    lhs = attr.ib(type=Node)
    rhs = attr.ib(type=Node)


@attr.s(hash=True, repr=False)
class LessThanEqual(Node):
    lhs = attr.ib(type=Node)
    rhs = attr.ib(type=Node)


@attr.s(hash=True, str=False)
class GreaterThan(Node):
    lhs = attr.ib(type=Node)
    rhs = attr.ib(type=Node)

    def __str__(self): 
        return f"{self.lhs.value} > {self.rhs.value}"


@attr.s(hash=True, repr=False)
class GreaterThanEqual(Node):
    lhs = attr.ib(type=Node)
    rhs = attr.ib(type=Node)


@attr.s(hash=True, repr=False)
class Relate(Node):
    vars = attr.ib(type=list) # list of vars that are imbued meaning as IV/DV/Variables at runtime during interpretation
    predictions = attr.ib(type=list, default=None) # list of Nodes

    @classmethod
    def from_str_names(cls, iv: str, dv: str, predictions: list):

        data = {'X': x, 'Y': y}
        df = pd.DataFrame.from_dict(data)

        x_var = Variable('X', dtype=DataType.INTERVAL, categories=None, drange=None)
        y_var = Variable('Y', dtype=DataType.INTERVAL, categories=None, drange=None)

        return cls(dfile='', variables=[x_var,y_var], data=df)


@attr.s(hash=True, repr=False)
class Mean(Node):
    var = attr.ib(type=Node)


# TODO: Should definitely check that the values that are passed are correct/exist/legit
@attr.s(hash=True, cmp=False)
class Literal(Node):
    value = attr.ib(type=Union[int, float, str])

    def __lt__(self, other):
        return LessThan(self, other)

    def __gt__(self, other):
        return GreaterThan(self, other)

    def __eq__(self, other):
        return Equal(self, other)
    
    def __ne__(self, other):
        return NotEqual(self, other)


@attr.s(hash=True, cmp=False)
class Relationship(Node):
    var = attr.ib(type=Variable)
    
    def positive(self, other):
        # import pdb; pdb.set_trace()
        # return Relate([self.var, other.var])
        return PositiveRelationship(self, other)

    def negative(self, other):
        return NegativeRelationship(self, other)


@attr.s(hash=True, cmp=False)
class PositiveRelationship(Node):
    lhs = attr.ib(type=Variable)
    rhs = attr.ib(type=Variable)


@attr.s(hash=True, cmp=False)
class NegativeRelationship(Node):
    lhs = attr.ib(type=Node)
    rhs = attr.ib(type=Node)