"""Tests for the structured hypothesis API (compare / relationship)."""

import os
import pytest
import tea
from tea.hypotheses import compare, relationship, _RelationshipSpec
from tea.ast import (
    GreaterThan, LessThan, Equal, NotEqual, Literal,
    PositiveRelationship, NegativeRelationship, Relationship,
)

DATA_DIR = os.path.join(os.path.dirname(__file__), 'data')


def get_data_path(filename):
    path = os.path.join(DATA_DIR, filename)
    if not os.path.exists(path):
        raise ValueError(f"Test fixture not found: {path}")
    return path


# ---------------------------------------------------------------------------
# Unit tests — compare()
# ---------------------------------------------------------------------------

class TestCompare:
    def test_greater_than_strings(self):
        result = compare('AR', '>', 'TV')
        assert len(result) == 1
        node = result[0]
        assert isinstance(node, GreaterThan)
        assert isinstance(node.lhs, Literal)
        assert isinstance(node.rhs, Literal)
        assert node.lhs.value == 'AR'
        assert node.rhs.value == 'TV'

    def test_less_than(self):
        result = compare('A', '<', 'B')
        assert isinstance(result[0], LessThan)

    def test_equal(self):
        result = compare('X', '==', 'Y')
        assert isinstance(result[0], Equal)

    def test_equal_single(self):
        result = compare('X', '=', 'Y')
        assert isinstance(result[0], Equal)

    def test_not_equal_ints(self):
        result = compare(1, '!=', 6)
        node = result[0]
        assert isinstance(node, NotEqual)
        assert node.lhs.value == 1
        assert node.rhs.value == 6

    def test_invalid_operator(self):
        with pytest.raises(ValueError, match="Unsupported operator"):
            compare('A', 'bad', 'B')


# ---------------------------------------------------------------------------
# Unit tests — relationship()
# ---------------------------------------------------------------------------

class TestRelationship:
    def test_positive(self):
        spec = relationship('positive', 'A', 'B')
        assert isinstance(spec, _RelationshipSpec)
        assert spec.direction == 'positive'
        assert spec.var1_name == 'A'
        assert spec.var2_name == 'B'

    def test_negative(self):
        spec = relationship('negative', 'X', 'Y')
        assert isinstance(spec, _RelationshipSpec)
        assert spec.direction == 'negative'

    def test_invalid_direction(self):
        with pytest.raises(ValueError, match="direction must be"):
            relationship('bad', 'A', 'B')


# ---------------------------------------------------------------------------
# Integration tests — structured API produces same results as string API
# ---------------------------------------------------------------------------

class TestPearsonCorrStructured:
    """Mirrors test_pearson_corr using relationship()."""

    def test_pearson_corr_structured(self):
        data_path = get_data_path('statex77.csv')
        variables = [
            {'name': 'Illiteracy', 'data type': 'interval', 'categories': [0, 100]},
            {'name': 'Life Exp', 'data type': 'ratio'},
        ]
        experimental_design = {
            'study type': 'observational study',
            'contributor variables': ['Illiteracy', 'Life Exp'],
            'outcome variables': '',
        }
        assumptions = {
            'Type I (False Positive) Error Rate': 0.05,
            'normal distribution': ['Illiteracy'],
        }

        tea.data(data_path)
        tea.define_variables(variables)
        tea.define_study_design(experimental_design)
        tea.assume(assumptions, 'strict')

        results = tea.hypothesize(
            ['Illiteracy', 'Life Exp'],
            [tea.relationship('positive', 'Illiteracy', 'Life Exp')],
        )
        assert results is not None


class TestIndepTTestStructured:
    """Mirrors test_indep_t_test using compare()."""

    def test_indep_t_test_structured(self):
        data_path = get_data_path('UScrime.csv')
        variables = [
            {'name': 'So', 'data type': 'nominal', 'categories': [0, 1]},
            {'name': 'Prob', 'data type': 'ratio', 'range': [0, 1]},
        ]
        experimental_design = {
            'study type': 'observational study',
            'contributor variables': 'So',
            'outcome variables': 'Prob',
        }
        assumptions = {
            'Type I (False Positive) Error Rate': 0.05,
            'groups normally distributed': [['Prob', 'So']],
        }

        tea.data(data_path)
        tea.define_variables(variables)
        tea.define_study_design(experimental_design)
        tea.assume(assumptions)

        results = tea.hypothesize(
            ['So', 'Prob'],
            [tea.compare(1, '>', 0)],
        )
        assert results is not None


class TestWilcoxonSignedRankStructured:
    """Mirrors test_wilcoxon_signed_rank using compare()."""

    def test_wilcoxon_signed_rank_structured(self):
        data_path = get_data_path('alcohol.csv')
        variables = [
            {'name': 'drug', 'data type': 'nominal', 'categories': ['Alcohol']},
            {'name': 'day', 'data type': 'nominal', 'categories': ['sundayBDI', 'wedsBDI']},
            {'name': 'value', 'data type': 'ratio'},
        ]
        experimental_design = {
            'study type': 'experiment',
            'independent variables': 'day',
            'dependent variables': 'value',
            'within subjects': 'day',
        }
        assumptions = {
            'Type I (False Positive) Error Rate': 0.05,
        }

        tea.data(data_path)
        tea.define_variables(variables)
        tea.define_study_design(experimental_design)
        tea.assume(assumptions)

        results = tea.hypothesize(
            ['day', 'value'],
            [tea.compare('sundayBDI', '!=', 'wedsBDI')],
        )
        assert results is not None


class TestKendallTauStructured:
    """Mirrors test_kendall_tau_corr using multiple compare() predictions."""

    def test_kendall_tau_structured(self):
        data_path = get_data_path('liar.csv')
        variables = [
            {'name': 'Creativity', 'data type': 'interval'},
            {'name': 'Position', 'data type': 'ordinal', 'categories': [6, 5, 4, 3, 2, 1]},
            {'name': 'Novice', 'data type': 'nominal', 'categories': [0, 1]},
        ]
        experimental_design = {
            'study type': 'observational study',
            'contributor variables': ['Novice', 'Creativity'],
            'outcome variables': 'Position',
        }
        assumptions = {
            'Type I (False Positive) Error Rate': 0.05,
        }

        tea.data(data_path)
        tea.define_variables(variables)
        tea.define_study_design(experimental_design)
        tea.assume(assumptions)

        results = tea.hypothesize(
            ['Position', 'Creativity'],
            [tea.compare(1, '>', 6), tea.compare(1, '>', 2)],
        )
        assert results is not None


class TestSpearmanCorrStructured:
    """Mirrors test_spearman_corr using compare()."""

    def test_spearman_corr_structured(self):
        data_path = get_data_path('liar.csv')
        variables = [
            {'name': 'Creativity', 'data type': 'interval'},
            {'name': 'Position', 'data type': 'ordinal', 'categories': [6, 5, 4, 3, 2, 1]},
            {'name': 'Novice', 'data type': 'nominal', 'categories': [0, 1]},
        ]
        experimental_design = {
            'study type': 'observational study',
            'contributor variables': ['Novice', 'Creativity'],
            'outcome variables': 'Position',
        }
        assumptions = {
            'Type I (False Positive) Error Rate': 0.05,
        }

        tea.data(data_path)
        tea.define_variables(variables)
        tea.define_study_design(experimental_design)
        tea.assume(assumptions)

        results = tea.hypothesize(
            ['Position', 'Creativity'],
            [tea.compare(1, '>', 6)],
        )
        assert results is not None


class TestPointbiserialCorrStructured:
    """Mirrors test_pointbiserial_corr using compare()."""

    def test_pointbiserial_corr_structured(self):
        data_path = get_data_path('pbcorr.csv')
        variables = [
            {'name': 'time', 'data type': 'ratio'},
            {'name': 'gender', 'data type': 'nominal', 'categories': [0, 1]},
            {'name': 'recode', 'data type': 'nominal', 'categories': [0, 1]},
        ]
        experimental_design = {
            'study type': 'observational study',
            'contributor variables': ['gender', 'recode'],
            'outcome variables': 'time',
        }
        assumptions = {
            'Type I (False Positive) Error Rate': 0.05,
        }

        tea.data(data_path)
        tea.define_variables(variables)
        tea.define_study_design(experimental_design)
        tea.assume(assumptions)

        results = tea.hypothesize(
            ['time', 'gender'],
            [tea.compare(1, '>', 0)],
        )
        assert results is not None


class TestPairedTTestStructured:
    """Mirrors test_paired_t_test using compare()."""

    def test_paired_t_test_structured(self):
        data_path = get_data_path('spiderLong_within.csv')
        variables = [
            {'name': 'Group', 'data type': 'nominal', 'categories': ['Picture', 'Real Spider']},
            {'name': 'Anxiety', 'data type': 'ratio'},
        ]
        experimental_design = {
            'study type': 'experiment',
            'independent variables': 'Group',
            'dependent variables': 'Anxiety',
            'within subjects': 'Group',
        }
        assumptions = {
            'Type I (False Positive) Error Rate': 0.05,
        }

        tea.data(data_path, key='id')
        tea.define_variables(variables)
        tea.define_study_design(experimental_design)
        tea.assume(assumptions)

        results = tea.hypothesize(
            ['Group', 'Anxiety'],
            [tea.compare('Real Spider', '>', 'Picture')],
        )
        assert results is not None


class TestNegativeRelationshipStructured:
    """Mirrors the 'Ineq ~ -Prob' string-based prediction."""

    def test_negative_relationship_structured(self):
        data_path = get_data_path('UScrime.csv')
        variables = [
            {'name': 'So', 'data type': 'nominal', 'categories': [0, 1]},
            {'name': 'Prob', 'data type': 'ratio', 'range': [0, 1]},
            {'name': 'Ineq', 'data type': 'ratio'},
        ]
        experimental_design = {
            'study type': 'observational study',
            'contributor variables': ['So', 'Prob'],
            'outcome variables': ['Prob', 'Ineq'],
        }
        assumptions = {
            'Type I (False Positive) Error Rate': 0.05,
        }

        tea.data(data_path)
        tea.define_variables(variables)
        tea.define_study_design(experimental_design)
        tea.assume(assumptions)

        results = tea.hypothesize(
            ['Ineq', 'Prob'],
            [tea.relationship('negative', 'Ineq', 'Prob')],
        )
        assert results is not None
