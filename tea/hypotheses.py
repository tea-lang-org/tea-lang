"""Structured hypothesis builders for Tea.

Provides ``compare()`` and ``relationship()`` — functional builders that
produce the same AST nodes as the string-based prediction syntax, but with
IDE autocompletion and immediate validation.

Examples::

    tea.hypothesize(['Score', 'Condition'], [tea.compare('AR', '>', 'TV')])
    tea.hypothesize(['Illiteracy', 'Life Exp'],
                    [tea.relationship('positive', 'Illiteracy', 'Life Exp')])
"""

from dataclasses import dataclass

from tea.ast import (
    Literal,
    GreaterThan,
    LessThan,
    Equal,
    NotEqual,
)

_OP_MAP = {
    '>': GreaterThan,
    '<': LessThan,
    '==': Equal,
    '=': Equal,
    '!=': NotEqual,
}


def compare(lhs, op: str, rhs) -> list:
    """Build a group-comparison prediction.

    >>> compare('AR', '>', 'TV')
    [GreaterThan(Literal('AR'), Literal('TV'))]

    Supported operators: ``>``, ``<``, ``==``, ``=``, ``!=``
    """
    if op not in _OP_MAP:
        raise ValueError(
            f"Unsupported operator {op!r}. "
            f"Supported: {', '.join(sorted(_OP_MAP))}"
        )
    node_cls = _OP_MAP[op]
    return [node_cls(Literal(lhs), Literal(rhs))]


@dataclass(frozen=True)
class _RelationshipSpec:
    """Intermediate spec resolved to AST nodes in ``hypothesize()``."""
    direction: str
    var1_name: str
    var2_name: str


def relationship(direction: str, var1_name: str, var2_name: str) -> _RelationshipSpec:
    """Build a continuous-relationship prediction.

    >>> relationship('positive', 'Illiteracy', 'Life Exp')
    >>> relationship('negative', 'Ineq', 'Prob')

    *direction* must be ``'positive'`` or ``'negative'``.
    """
    if direction not in ('positive', 'negative'):
        raise ValueError(
            f"direction must be 'positive' or 'negative', got {direction!r}"
        )
    return _RelationshipSpec(direction, var1_name, var2_name)
