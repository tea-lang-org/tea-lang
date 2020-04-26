from typing import Dict

from tea.global_vals import dv_identifier, iv_identifier, \
    contributor_identifier, experiment_identifier, observational_identifier, outcome_identifier, study_type_identifier


class StudyTypeDeterminer:
    def determine_study_type(self, vars_data: list, design: Dict[str, str]):
        if design:
            # Is the study type explicit? If so...
            if study_type_identifier in design:
                # Is this study an experiment or observational study?
                if design[study_type_identifier] == experiment_identifier:
                    return experiment_identifier
                # Is this study an observational study?
                elif design[study_type_identifier] == observational_identifier:
                    return observational_identifier
                # We don't know what kind of study this is.
                else:
                    raise ValueError(f"Type of study is not supported:{design[study_type_identifier]}. Is it an experiment or an observational study?")
            # The study type is not explicit, so let's check the other properties...
            else:
                # This might be an experiment.
                if iv_identifier in design and dv_identifier in design:  # dv_identifier??
                    return experiment_identifier
                elif contributor_identifier in design and outcome_identifier in design:
                    return observational_identifier
                # We don't know what kind of study this is.
                else:
                    raise ValueError(f"Type of study is not supported:{design}. Is it an experiment or an observational study?")
