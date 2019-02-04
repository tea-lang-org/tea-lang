# Runtime data structures used by interpreter

import attr
from typing import Any
from types import SimpleNamespace # allows for dot notation access for dictionaries

class Value(object):
    pass

@attr.s(init=True, auto_attribs=True)
class VarData(Value):
    dataframe: Any
    metadata: Any

@attr.s(init=True, auto_attribs=True)
class CompData(Value): # TODO probably want to rename this
    dataframes: dict # or SimpleNamespace?
    # metadata: Any  # not totally sure but could include vardata types? 
    # set of characteristics about the groups that are used to determine statistical test
    properties: SimpleNamespace


@attr.s(init=True, auto_attribs=True, str=False)
class ResData(Value):
    # groups: Any # What groups were compared?
    # ci_intervals: Any # CI intervals for each group
    # point_estimates: Any # point estimate for each group
    # # interpretation: Any ????
    
    ivs: Any # Results from central tendency procedure for groups compared??
    dv: Any
    group_results: Any # Results from central tendency procedure for groups compared??
    test: Any # name? of test conducted to compare groups (whose results are stored in group_results)
    test_results: Any # result of conducting above test

    def __str__(self):
        summary = f"Compared {self.dv} as dependent variables between independent variables: {self.ivs}"
        test = f"\nConducted {self.test}: test statistic: {self.test_results[0]}, p-value: {self.test_results[1]}"

        return summary + test