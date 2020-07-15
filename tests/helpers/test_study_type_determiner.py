import unittest
from parameterized import parameterized
from tea.helpers.study_type_determiner import StudyTypeDeterminer
from tea.global_vals import (
    dv_identifier,
    iv_identifier,
    contributor_identifier,
    experiment_identifier,
    observational_identifier,
    outcome_identifier,
    study_type_identifier,
)


class StudyTypeDeterminerTests(unittest.TestCase):
    def setUp(self) -> None:
        self.determiner = StudyTypeDeterminer()

    @parameterized.expand(
        [[experiment_identifier, experiment_identifier], [observational_identifier, observational_identifier],]
    )
    def test_method_should_return_study_type_for_known_identifier(self, expected_identifier, input_identifier):
        design = {study_type_identifier: input_identifier}

        # ACT
        ret_value = self.determiner.determine_study_type([], design)

        # ASSERT
        self.assertEqual(ret_value, expected_identifier)

    @parameterized.expand(
        [["test"], ["test2"],]
    )
    def test_method_should_throw_for_unknown_identifier_explicit_study(self, input_identifier):
        design = {study_type_identifier: input_identifier}

        # ASSERT
        self.assertRaises(ValueError, self.determiner.determine_study_type, [], design)

    def test_method_should_throw_for_wrongly_created_desgin(self):
        design = {"test": "test"}

        # ASSERT
        self.assertRaises(ValueError, self.determiner.determine_study_type, [], design)

    def test_method_should_return_experiment_identifier_when_non_explicit_type_and_existing_variables(self):
        design = {iv_identifier: "x", dv_identifier: "y"}

        # ACT
        ret_value = self.determiner.determine_study_type([], design)

        # ASSERT
        self.assertEqual(ret_value, experiment_identifier)

    def test_method_should_return_experiment_identifier_when_non_explicit_type_and_existing_contributor_and_outcome(
        self,
    ):
        design = {contributor_identifier: "x", outcome_identifier: "y"}

        # ACT
        ret_value = self.determiner.determine_study_type([], design)

        # ASSERT
        self.assertEqual(ret_value, observational_identifier)
