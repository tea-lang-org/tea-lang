from tea.helpers.constants.default_values import DEFAULT_ALPHA_PARAMETER
from tea.global_vals import *
from tea.ast import *
import attr
from .value import Value

# CombinedData is the runtime data structure used to unify experimental design and variable declarations
@attr.s(init=True)
class CombinedData(Value):
    vars = attr.ib(default=[]) # list of VarData objects 
    study_type = attr.ib(default=observational_identifier)
    # set of characteristics about the groups that are used to determine statistical test
    alpha = attr.ib(type=float, default=DEFAULT_ALPHA_PARAMETER)
    properties = attr.ib(default=dict())
    

    def _update_vars(self):
        self.vars = self.get_explanatory_variables() + self.get_explained_variables()

    # Null Hypothesis: Groups come from populations with equal variance
    def has_equal_variance(self): 
        global eq_variance, alpha
        
        if self.properties[eq_variance]: 
            return self.properties[eq_variance][1] >= self.alpha  # Cannot reject null hypothesis of equal variances
        else: 
            return False

    def has_paired_observations(self):
        global paired 

        return self.properties[paired]

    def has_independent_observations(self):
        global paired
        
        return not self.properties[paired]

    def difference_between_paired_value_is_normal(self):
        if not self.has_paired_observations():
            return False
        assert False, "Implement this property to convey information about whether difference" \
                      "between paired values is normally distributed."
    
    # @return list of VarData instances that are in this object's 
    # vars that have the @param role
    def get_vars(self, role: str): 
        role_vars = []
        for v in self.vars:
            if v.role == role: 
                role_vars.append(v) 
        
        return role_vars

    def get_explanatory_variables(self): 
        explanatory_variables = None
        
        if self.study_type == experiment_identifier:
            explanatory_variables = self.get_vars(iv_identifier)
        else: 
            assert(self.study_type == observational_identifier)
            explanatory_variables  = self.get_vars(contributor_identifier)
            
        return explanatory_variables
    
    def get_explained_variables(self): 
        explained_variables = None
        
        if self.study_type == experiment_identifier:
            explained_variables = self.get_vars(dv_identifier)
        else: 
            assert(self.study_type == observational_identifier)
            explained_variables  = self.get_vars(outcome_identifier)
            
        return explained_variables

    def has_one_x(self): 
        xs = self.get_explanatory_variables()

        return len(xs) == 1
    
    def has_one_y(self): 
        ys = self.get_explained_variables()

        return len(ys) == 1