from .ast import *
from .dataset import Dataset

from scipy import stats # Stats library used
import statsmodels.api as sm
import statsmodels.formula.api as smf
import numpy as np # Use some stats from numpy instead

# Eval : Dataset -> Model -> List[Hyps] -> ????

# Eval : Model -> List[Hyps] -> (Dataset -> Result)

# eval(x + x)(x -> 1)
# def check_thing(ds):
#     return Eval(model, hyps)(ds)

# m1 = ????
# m2 - ????

# ds = ... 

# for m in all_models:
#     eval(ds, model, hyps)

class Evaluator(object):
    def __init__(self, dataset, experiment_setup):
        self.dataset = dataset.data #access to pd.DataFrame directly
        self.experiment_setup = experiment_setup
        self.stats = {}
    
    def eval(self, model: Model):
        self.stats = {}
        eq = str(model.dependent_var) + '~' + str(model.eq_independent_vars)

        m = smf.ols(formula=eq, data=self.dataset) # use patsy for R-style equations
        results = m.fit()
        self.stats[eq] = results._results.__dict__


def evaluate(dataset: Dataset, experiment_setup: Experiment_SetUp, model: Model, hypothesis: Hypothesis):
    e = Evaluator(dataset, experiment_setup)
    e.eval(model)
    return e.stats

