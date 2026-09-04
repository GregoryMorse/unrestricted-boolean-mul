#!/usr/bin/env python3
"""Search for sparse polynomial certificates for retained return history.

Every coefficient is represented as a Boolean polynomial in the parameters;
parameter monomials are Python integer bit masks and addition is symmetric
difference.  The first search asks whether the forbidden missing-target
coefficient is already in the linear span of the zero high/quotient
coefficients.  This is theorem discovery, not a proof premise.
"""

from __future__ import annotations

import argparse
from collections.abc import Iterable
import json
from itertools import combinations, product
import subprocess

from quadratic_return_class_sample import FIRST_ORDER_MASKS, target_from_mask
from quadratic_return_history_sat import PAIR_MASKS
from quadratic_return_population_probe import REDUCE_TARGET
from w_pq_analysis import form_to_anf, iterbits, r0, r1, rinf


Polynomial = frozenset[int]
SymbolicANF = dict[int, Polynomial]
Certificate = dict[str, Polynomial]


ZERO: Polynomial = frozenset()
ONE: Polynomial = frozenset({0})


def pvar(index: int) -> Polynomial:
    return frozenset({1 << index})


def padd(*values: Polynomial) -> Polynomial:
    result: set[int] = set()
    for value in values:
        result.symmetric_difference_update(value)
    return frozenset(result)


def pmul(left: Polynomial, right: Polynomial) -> Polynomial:
    result: set[int] = set()
    for x in left:
        for y in right:
            monomial = x | y
            if monomial in result:
                result.remove(monomial)
            else:
                result.add(monomial)
    return frozenset(result)


def substitute(polynomial: Polynomial, assignment: dict[int, bool]) -> Polynomial:
    """Evaluate selected Boolean variables while retaining the others."""
    fixed_mask = sum(1 << index for index in assignment)
    false_mask = sum(1 << index for index, value in assignment.items() if not value)
    result: set[int] = set()
    for monomial in polynomial:
        if monomial & false_mask:
            continue
        reduced = monomial & ~fixed_mask
        if reduced in result:
            result.remove(reduced)
        else:
            result.add(reduced)
    return frozenset(result)


def substitute_variable(
    polynomial: Polynomial, index: int, replacement: Polynomial
) -> Polynomial:
    """Substitute one Boolean variable by a Boolean polynomial."""
    variable = 1 << index
    result = ZERO
    for monomial in polynomial:
        if monomial & variable:
            rest = monomial ^ variable
            result = padd(result, pmul(frozenset({rest}), replacement))
        else:
            result = padd(result, frozenset({monomial}))
    return result


def certificate_add(left: Certificate, right: Certificate) -> Certificate:
    """Add sparse ideal-membership certificates over the Boolean ring."""
    result = dict(left)
    for name, multiplier in right.items():
        value = padd(result.get(name, ZERO), multiplier)
        if value:
            result[name] = value
        elif name in result:
            del result[name]
    return result


def certificate_scale(multiplier: Polynomial, value: Certificate) -> Certificate:
    """Multiply every coefficient in an ideal-membership certificate."""
    if not multiplier:
        return {}
    return {
        name: product
        for name, coefficient in value.items()
        if (product := pmul(multiplier, coefficient))
    }


def boolean_derivative(polynomial: Polynomial, index: int) -> Polynomial:
    """Squarefree derivative used to certify one Boolean substitution."""
    variable = 1 << index
    return padd(*(
        frozenset({monomial ^ variable})
        for monomial in polynomial if monomial & variable
    ))


def substitute_variable_with_certificate(
    polynomial: Polynomial, certificate: Certificate,
    index: int, replacement: Polynomial,
    substitution_certificate: Certificate,
) -> tuple[Polynomial, Certificate]:
    """Substitute `x := p` while lifting through the equation `x+p = 0`."""
    derivative = boolean_derivative(polynomial, index)
    return (
        substitute_variable(polynomial, index, replacement),
        certificate_add(
            certificate,
            certificate_scale(derivative, substitution_certificate),
        ),
    )


def affine_eliminate_with_certificate(
    constraints: list[tuple[str, Polynomial]], target: Polynomial,
) -> tuple[
    list[tuple[str, Polynomial, Certificate]], Polynomial,
    dict[int, Polynomial],
]:
    """Run the affine eliminator while lifting every row to the input ideal."""
    current = [
        (name, polynomial, {name: ONE}) for name, polynomial in constraints
    ]
    current_target = target
    all_substitutions: dict[int, Polynomial] = {}
    while True:
        affine = [
            (polynomial, certificate)
            for _name, polynomial, certificate in current
            if all(monomial.bit_count() <= 1 for monomial in polynomial)
        ]
        basis: dict[int, tuple[Polynomial, Certificate]] = {}
        inconsistent: Certificate | None = None
        for original, original_certificate in affine:
            value = original
            certificate = original_certificate
            while True:
                variables = [
                    monomial.bit_length() - 1
                    for monomial in value if monomial
                ]
                if not variables:
                    if value == ONE:
                        inconsistent = certificate
                    break
                pivot = max(variables)
                if pivot not in basis:
                    basis[pivot] = (value, certificate)
                    break
                row, row_certificate = basis[pivot]
                value = padd(value, row)
                certificate = certificate_add(certificate, row_certificate)
        if inconsistent is not None:
            return [(
                "affine-inconsistency", ONE, inconsistent
            )], ZERO, all_substitutions
        if not basis:
            break
        substitutions = {
            pivot: padd(row, pvar(pivot))
            for pivot, (row, _certificate) in basis.items()
        }
        substitution_certificates = {
            pivot: certificate for pivot, (_row, certificate) in basis.items()
        }
        for pivot in sorted(substitutions, reverse=True):
            equation = padd(pvar(pivot), substitutions[pivot])
            certificate = substitution_certificates[pivot]
            for lower in sorted(substitutions):
                if lower < pivot:
                    equation, certificate = substitute_variable_with_certificate(
                        equation, certificate, lower, substitutions[lower],
                        substitution_certificates[lower],
                    )
            substitutions[pivot] = padd(equation, pvar(pivot))
            substitution_certificates[pivot] = certificate
        reduced: list[tuple[str, Polynomial, Certificate]] = []
        for name, polynomial, certificate in current:
            value = polynomial
            lifted = certificate
            for pivot in sorted(substitutions, reverse=True):
                value, lifted = substitute_variable_with_certificate(
                    value, lifted, pivot, substitutions[pivot],
                    substitution_certificates[pivot],
                )
            if value:
                reduced.append((name, value, lifted))
        for pivot in sorted(substitutions, reverse=True):
            current_target = substitute_variable(
                current_target, pivot, substitutions[pivot]
            )
        current = reduced
        all_substitutions.update(substitutions)
    return current, current_target, all_substitutions


def affine_eliminate(
    constraints: list[tuple[str, Polynomial]], target: Polynomial
) -> tuple[list[tuple[str, Polynomial]], Polynomial, dict[int, Polynomial]]:
    """Eliminate all pivots visible in affine consequences.

    This is only a discovery simplifier.  Each substitution is oriented from
    an affine generator already present in the ideal.
    """
    current = constraints
    current_target = target
    all_substitutions: dict[int, Polynomial] = {}
    while True:
        affine = [
            polynomial for _name, polynomial in current
            if all(monomial.bit_count() <= 1 for monomial in polynomial)
        ]
        basis: dict[int, Polynomial] = {}
        inconsistent = False
        for original in affine:
            value = original
            while True:
                variables = [
                    monomial.bit_length() - 1
                    for monomial in value if monomial
                ]
                if not variables:
                    if value == ONE:
                        inconsistent = True
                    break
                pivot = max(variables)
                if pivot not in basis:
                    basis[pivot] = value
                    break
                value = padd(value, basis[pivot])
        if inconsistent:
            return [("affine-inconsistency", ONE)], ZERO, all_substitutions
        if not basis:
            break
        substitutions = {
            pivot: padd(row, pvar(pivot)) for pivot, row in basis.items()
        }
        for pivot in sorted(substitutions, reverse=True):
            replacement = substitutions[pivot]
            for lower in sorted(substitutions):
                if lower < pivot:
                    replacement = substitute_variable(
                        replacement, lower, substitutions[lower]
                    )
            substitutions[pivot] = replacement
        reduced: list[tuple[str, Polynomial]] = []
        for name, polynomial in current:
            value = polynomial
            for pivot in sorted(substitutions, reverse=True):
                value = substitute_variable(value, pivot, substitutions[pivot])
            if value:
                reduced.append((name, value))
        for pivot in sorted(substitutions, reverse=True):
            current_target = substitute_variable(
                current_target, pivot, substitutions[pivot]
            )
        current = reduced
        all_substitutions.update(substitutions)
    return current, current_target, all_substitutions


def anf_add(*values: SymbolicANF) -> SymbolicANF:
    result: SymbolicANF = {}
    supports = set().union(*(value.keys() for value in values))
    for support in supports:
        coefficient = padd(*(value.get(support, ZERO) for value in values))
        if coefficient:
            result[support] = coefficient
    return result


def anf_mul(left: SymbolicANF, right: SymbolicANF) -> SymbolicANF:
    result: SymbolicANF = {}
    for x_support, x_coefficient in left.items():
        for y_support, y_coefficient in right.items():
            support = x_support | y_support
            coefficient = pmul(x_coefficient, y_coefficient)
            old = result.get(support, ZERO)
            new = padd(old, coefficient)
            if new:
                result[support] = new
            elif support in result:
                del result[support]
    return result


def symbolic_linear(variables: list[Polynomial]) -> SymbolicANF:
    return {1 << i: variable for i, variable in enumerate(variables)}


def fixed_anf(poly: int) -> SymbolicANF:
    return {support: ONE for support in iterbits(poly)}


def scaled_fixed_anf(poly: int, scalar: Polynomial) -> SymbolicANF:
    return {support: scalar for support in iterbits(poly)}


def quotient_coefficients(two: dict[int, Polynomial]) -> dict[int, Polynomial]:
    columns = [REDUCE_TARGET(1 << i) for i in range(45)]
    positions = sorted({
        bit for column in columns for bit in range(45)
        if (column >> bit) & 1
    })
    result: dict[int, Polynomial] = {}
    for position in positions:
        result[position] = padd(*(
            two.get(support, ZERO)
            for support, column in zip(PAIR_MASKS, columns, strict=True)
            if (column >> position) & 1
        ))
    return result


def missing_coefficient(two: dict[int, Polynomial]) -> Polynomial:
    pairs = ((0, 7), (0, 8), (1, 9), (2, 9))
    return padd(*(
        two.get((1 << i) | (1 << j), ZERO) for i, j in pairs
    ))


def add_named_constraints(
    output: list[tuple[str, Polynomial]], prefix: str,
    value: SymbolicANF, minimum_degree: int,
) -> None:
    for support, coefficient in sorted(value.items()):
        if support.bit_count() >= minimum_degree and coefficient:
            output.append((f"{prefix}-{support:#05x}", coefficient))


def reduce_with_certificate(
    constraints: list[tuple[str, Polynomial]], target: Polynomial
) -> tuple[Polynomial, list[str]]:
    basis: dict[int, tuple[Polynomial, int]] = {}
    for index, (_name, original) in enumerate(constraints):
        value = original
        certificate = 1 << index
        while value:
            pivot = max(value)
            if pivot not in basis:
                basis[pivot] = (value, certificate)
                break
            row, row_certificate = basis[pivot]
            value = padd(value, row)
            certificate ^= row_certificate

    value = target
    remainder: set[int] = set()
    certificate = 0
    while value:
        pivot = max(value)
        if pivot not in basis:
            remainder.add(pivot)
            value = frozenset(set(value) - {pivot})
            continue
        row, row_certificate = basis[pivot]
        value = padd(value, row)
        certificate ^= row_certificate
    names = [
        name for index, (name, _polynomial) in enumerate(constraints)
        if (certificate >> index) & 1
    ]
    return frozenset(remainder), names


def multiplied_constraints(
    constraints: list[tuple[str, Polynomial]], variable_names: list[str],
    maximum_degree: int,
) -> list[tuple[str, Polynomial]]:
    multipliers: list[tuple[str, int]] = [("1", 0)]
    for degree in range(1, maximum_degree + 1):
        multipliers.extend(
            ("*".join(variable_names[i] for i in indices),
             sum(1 << i for i in indices))
            for indices in combinations(range(len(variable_names)), degree)
        )
    result: list[tuple[str, Polynomial]] = []
    for name, polynomial in constraints:
        for multiplier_name, multiplier in multipliers:
            value = pmul(polynomial, frozenset({multiplier}))
            if value:
                result.append((f"({multiplier_name})*({name})", value))
    return result


def constraints_times_monomials(
    constraints: list[tuple[str, Polynomial]], monomials: Iterable[int],
    variable_names: list[str],
) -> list[tuple[str, Polynomial]]:
    result: list[tuple[str, Polynomial]] = []
    for name, polynomial in constraints:
        for monomial in monomials:
            value = pmul(polynomial, frozenset({monomial}))
            if value:
                result.append((
                    f"({monomial_name(monomial, variable_names)})*({name})",
                    value,
                ))
    return result


def monomial_name(monomial: int, variable_names: list[str]) -> str:
    factors = [
        name for index, name in enumerate(variable_names)
        if (monomial >> index) & 1
    ]
    return "*".join(factors) if factors else "1"


def generated_label_parts(
    label: str, variable_names: list[str]
) -> tuple[str, Polynomial]:
    """Recover the semantic generator and multiplier from a search label."""
    if not label.startswith("("):
        return label, ONE
    raw_multiplier, separator, raw_generator = label.partition(")*(")
    if not separator or not raw_generator.endswith(")"):
        raise ValueError(f"unrecognized generated label: {label}")
    multiplier_name = raw_multiplier[1:]
    generator_name = raw_generator[:-1]
    multiplier = ONE
    if multiplier_name != "1":
        for variable_name in multiplier_name.split("*"):
            multiplier = pmul(
                multiplier, pvar(variable_names.index(variable_name))
            )
    return generator_name, multiplier


def add_certificate_term(
    aggregate: dict[str, Polynomial], label: str, coefficient: Polynomial,
    variable_names: list[str],
) -> None:
    generator_name, multiplier = generated_label_parts(label, variable_names)
    aggregate[generator_name] = padd(
        aggregate.get(generator_name, ZERO), pmul(coefficient, multiplier)
    )


def singular_polynomial(polynomial: Polynomial, variable_names: list[str]) -> str:
    if not polynomial:
        return "0"
    return "+".join(
        monomial_name(monomial, variable_names)
        for monomial in sorted(polynomial)
    )


def lean_polynomial(polynomial: Polynomial) -> str:
    """Render a Boolean polynomial on `v : Fin 71 → F₂`."""
    terms: list[str] = []
    for monomial in sorted(polynomial):
        variables = [f"v {index}" for index in range(71) if monomial >> index & 1]
        terms.append(" * ".join(variables) if variables else "1")
    return " + ".join(terms) if terms else "0"


def parse_singular_squarefree(
    expression: str, variable_names: list[str]
) -> Polynomial:
    """Parse the `+`/`*` fragment printed by the sparse lift certificates."""
    indices = {name: index for index, name in enumerate(variable_names)}
    result = ZERO
    for raw_term in expression.split("+"):
        term = raw_term.strip()
        monomial = 0
        if term != "1":
            for raw_factor in term.split("*"):
                name = raw_factor.partition("^")[0]
                monomial |= 1 << indices[name]
        result = padd(result, frozenset({monomial}))
    return result


def singular_unit_certificate(
    constraints: list[tuple[str, Polynomial]], variable_names: list[str],
    executable: str, active_polynomial: Polynomial = ZERO,
) -> dict[str, Polynomial]:
    """Discover and independently replay a unit certificate with Singular.

    Singular works in an ordinary polynomial ring, so Boolean field equations
    are appended during discovery.  Their rows are discarded afterwards:
    they are identically zero in this script's squarefree Boolean quotient.
    """
    active_indices = sorted({
        index
        for _name, polynomial in constraints
        for monomial in polynomial
        for index in range(len(variable_names))
        if (monomial >> index) & 1
    } | {
        index
        for monomial in active_polynomial
        for index in range(len(variable_names))
        if (monomial >> index) & 1
    })
    active_names = [variable_names[index] for index in active_indices]
    if not active_names:
        raise ValueError("unit certificate has no active variables")
    generator_strings = [
        singular_polynomial(polynomial, variable_names)
        for _name, polynomial in constraints
    ]
    generator_strings.extend(
        f"{variable_names[index]}^2+{variable_names[index]}"
        for index in active_indices
    )
    source = "\n".join([
        f"ring coefficientRing=2,({','.join(active_names)}),dp;",
        "ideal historyIdeal=",
        ",\n".join(generator_strings) + ";",
        "matrix historyLift;",
        "ideal historyBasis=liftstd(historyIdeal,historyLift);",
        'print("BASIS");',
        "print(historyBasis[1]);",
        'print("ROWS");',
        "int historyRow;",
        "for (historyRow=1; historyRow<=nrows(historyLift); historyRow=historyRow+1)",
        "{",
        "  if (historyLift[historyRow,1] != 0)",
        "  {",
        "    print(historyRow);",
        "    print(historyLift[historyRow,1]);",
        "  }",
        "}",
        "quit;",
    ])
    completed = subprocess.run(
        [executable, "-q"], input=source, text=True,
        capture_output=True, check=True,
    )
    lines = [
        line.strip() for line in completed.stdout.splitlines() if line.strip()
    ]
    try:
        basis_marker = lines.index("BASIS")
        rows_marker = lines.index("ROWS")
    except ValueError as error:
        raise RuntimeError(
            "Singular certificate output is missing its markers:\n" +
            completed.stdout
        ) from error
    if lines[basis_marker + 1] != "1":
        raise RuntimeError("exceptional constraint ideal is not the unit ideal")
    row_lines = lines[rows_marker + 1:]
    if len(row_lines) % 2:
        raise RuntimeError("malformed Singular certificate row output")
    result: dict[str, Polynomial] = {}
    for raw_row, expression in zip(
        row_lines[::2], row_lines[1::2], strict=True
    ):
        row = int(raw_row)
        if row <= len(constraints):
            label = constraints[row - 1][0]
            result[label] = parse_singular_squarefree(
                expression, variable_names
            )
    combination = ZERO
    constraint_by_name = dict(constraints)
    for label, multiplier in result.items():
        combination = padd(
            combination, pmul(multiplier, constraint_by_name[label])
        )
    if combination != ONE:
        raise RuntimeError("Singular unit certificate failed Boolean replay")
    return result


def exceptional_branch_certificate(
    constraints: list[tuple[str, Polynomial]], target: Polynomial,
    variable_names: list[str], assignment: dict[int, bool],
    correction_return: int, executable: str,
) -> dict[str, Polynomial]:
    """Lift one aligned exceptional branch back to semantic generators.

    After the supplied assignments, the returned semantic-generator
    combination is one.  Fixed-coordinate generator terms disappear under
    that specialization and therefore are omitted from the result.
    """
    correction_index = variable_names.index("correctionReturn0")
    fixed = {**assignment, correction_index: bool(correction_return)}
    print(
        "exceptional-singular-start " +
        " ".join(
            f"{variable_names[index]}={int(value)}"
            for index, value in sorted(fixed.items())
        ),
        flush=True,
    )
    extended = [*constraints]
    for index, value in fixed.items():
        extended.append((
            f"fix-{variable_names[index]}-{int(value)}",
            padd(pvar(index), ONE) if value else pvar(index),
        ))
    lifted, reduced_target, _eliminated = affine_eliminate_with_certificate(
        extended, target
    )
    print(
        f"exceptional-affine-lift-done rows={len(lifted)}",
        flush=True,
    )
    reduced_constraints = [
        (label, polynomial) for label, polynomial, _certificate in lifted
    ]
    reduced_multipliers = singular_unit_certificate(
        reduced_constraints, variable_names, executable, reduced_target
    )
    print(
        f"exceptional-singular-done terms={len(reduced_multipliers)}",
        flush=True,
    )
    raw: Certificate = {}
    lifted_by_name = {
        label: certificate for label, _polynomial, certificate in lifted
    }
    for label, multiplier in reduced_multipliers.items():
        raw = certificate_add(
            raw,
            certificate_scale(multiplier, lifted_by_name[label]),
        )
    semantic_names = {name for name, _polynomial in constraints}
    result = {
        label: multiplier
        for label, multiplier in raw.items()
        if label in semantic_names
    }
    combination = ZERO
    constraint_by_name = dict(constraints)
    for label, multiplier in result.items():
        combination = padd(
            combination, pmul(multiplier, constraint_by_name[label])
        )
    if substitute(combination, fixed) != ONE:
        raise RuntimeError("lifted exceptional branch identity failed replay")
    return result


EXCEPTIONAL_LIFT_MULTIPLIERS: dict[int, dict[int, str]] = {
    0: {
        4: "ell5*m7+factorLinear6",
        5: "ell5*m7*factorLinear6+m7*factorLinear5",
        13: "factorLinear5+1",
        20: "m1",
        21: "factorLinear0+1",
        22: "m7",
        27: (
            "ell5*m1*m7+ell5*m2*factorLinear6+m7*factorLinear0+"
            "m2*factorLinear5+factorLinear0"
        ),
        28: "ell5*factorLinear0+ell5+m7+1",
        30: "m7+1",
        32: "m2",
        95: "m7+1",
        101: "1",
        102: "ell5*m7",
        107: "ell5*m7",
        117: "m2",
        120: "ell5*m2",
    },
    1: {
        4: "ell5*m7+m7*x5+factorLinear6",
        5: (
            "ell5*m7*factorLinear6+m7*x5*factorLinear6+"
            "m7*factorLinear5"
        ),
        13: "factorLinear5+1",
        20: "m1+1",
        21: "factorLinear0+1",
        22: "m7",
        27: (
            "ell5*m1*m7+m1*m7*x5+ell5*m2*factorLinear6+"
            "m2*x5*factorLinear6+ell5*m7+m7*x5+m7*factorLinear0+"
            "m2*factorLinear5+factorLinear0"
        ),
        28: (
            "ell5*factorLinear0+x5*factorLinear0+ell5+m7+x5+1"
        ),
        30: "m7+1",
        32: "m2",
        95: "m7+1",
        101: "1",
        102: "ell5*m7+m7*x5",
        107: "ell5*m7+m7*x5",
        117: "m2",
        120: "ell5*m2+m2*x5",
    },
}


EQUAL_FACTOR_EXCEPTIONAL_LIFT_MULTIPLIERS: dict[int, dict[int, str]] = {
    0: {
        4: "ell7*m5+factorLinear6",
        5: "ell7*m5*factorLinear6+ell7*factorLinear5",
        13: "factorLinear5+1",
        20: "ell1",
        21: "factorLinear0+1",
        27: (
            "ell1*ell7*m5+ell2*m5*factorLinear6+ell7*factorLinear0+"
            "ell2*factorLinear5+factorLinear0"
        ),
        28: "m5*factorLinear0+m5",
        95: "ell7+1",
        101: "1",
        102: "ell7*m5",
        107: "ell7*m5",
        117: "ell2",
        120: "ell2*m5",
    },
    1: {
        4: "ell7*m5+ell7*x5+ell7*y5+factorLinear6",
        5: (
            "ell7*m5*factorLinear6+ell7*x5*factorLinear6+"
            "ell7*y5*factorLinear6+ell7*factorLinear5"
        ),
        13: "factorLinear5+1",
        20: "ell1+1",
        21: "factorLinear0+1",
        27: (
            "ell1*ell7*m5+ell1*ell7*x5+ell1*ell7*y5+"
            "ell2*m5*factorLinear6+ell2*x5*factorLinear6+"
            "ell2*y5*factorLinear6+ell7*m5+ell7*x5+ell7*y5+"
            "ell7*factorLinear0+ell2*factorLinear5+factorLinear0"
        ),
        28: (
            "m5*factorLinear0+x5*factorLinear0+y5*factorLinear0+"
            "m5+x5+y5"
        ),
        95: "ell7+1",
        101: "1",
        102: "ell7*m5+ell7*x5+ell7*y5",
        107: "ell7*m5+ell7*x5+ell7*y5",
        117: "ell2",
        120: "ell2*m5+ell2*x5+ell2*y5",
    },
}


def verify_exceptional_lift_certificates() -> list[dict[str, object]]:
    """Independently replay the two sparse Singular unit certificates."""
    reports: list[dict[str, object]] = []
    fixed_values = {
        "ell1": 0, "ell2": 0, "ell4": 0, "ell6": 1, "ell7": 0,
        "y1": 1, "y2": 0, "y4": 0, "y6": 0, "y7": 0,
    }
    for correction_return, multipliers in EXCEPTIONAL_LIFT_MULTIPLIERS.items():
        constraints, target, names = equations(0, r0, r0)
        assignments = {**fixed_values, "correctionReturn0": correction_return}
        for name, value in assignments.items():
            index = names.index(name)
            constraints.append((
                f"fix-{name}-{value}",
                padd(pvar(index), ONE) if value else pvar(index),
            ))
        reduced, _target, eliminated = affine_eliminate(constraints, target)
        combination = ZERO
        used_labels: list[str] = []
        for row, expression in multipliers.items():
            label, generator = reduced[row - 1]
            multiplier = parse_singular_squarefree(expression, names)
            combination = padd(combination, pmul(multiplier, generator))
            used_labels.append(label)
        reports.append({
            "case": "zero_one",
            "correction_return": correction_return,
            "reduced_constraints": len(reduced),
            "eliminated_variables": len(eliminated),
            "semantic_generators": used_labels,
            "certificate_terms": len(multipliers),
            "combination_is_one_in_boolean_quotient": combination == ONE,
            "combination_remainder": singular_polynomial(combination, names),
        })
    equal_factor_fixed = {
        "m1": 0, "m2": 0, "m4": 0, "m6": 1, "m7": 0,
        "x1": 1, "x2": 0, "x4": 0, "x6": 0, "x7": 0,
    }
    for correction_return, multipliers in (
        EQUAL_FACTOR_EXCEPTIONAL_LIFT_MULTIPLIERS.items()
    ):
        constraints, target, names = equations(
            r0, r0, r0, equal_factor_difference_coordinates=True
        )
        assignments = {
            **equal_factor_fixed, "correctionReturn0": correction_return
        }
        for name, value in assignments.items():
            index = names.index(name)
            constraints.append((
                f"fix-{name}-{value}",
                padd(pvar(index), ONE) if value else pvar(index),
            ))
        reduced, _target, eliminated = affine_eliminate(constraints, target)
        combination = ZERO
        used_labels: list[str] = []
        for row, expression in multipliers.items():
            label, generator = reduced[row - 1]
            multiplier = parse_singular_squarefree(expression, names)
            combination = padd(combination, pmul(multiplier, generator))
            used_labels.append(label)
        reports.append({
            "case": "one_one_difference_coordinates",
            "correction_return": correction_return,
            "reduced_constraints": len(reduced),
            "eliminated_variables": len(eliminated),
            "semantic_generators": used_labels,
            "certificate_terms": len(multipliers),
            "combination_is_one_in_boolean_quotient": combination == ONE,
            "combination_remainder": singular_polynomial(combination, names),
        })
    return reports


def lift_zero_one_exceptional_certificates_to_raw() -> list[dict[str, object]]:
    """Lift the two reduced exceptional certificates to original equations."""
    reports: list[dict[str, object]] = []
    fixed_values = {
        "ell1": 0, "ell2": 0, "ell4": 0, "ell6": 1, "ell7": 0,
        "y1": 1, "y2": 0, "y4": 0, "y6": 0, "y7": 0,
    }
    for correction_return, multipliers in EXCEPTIONAL_LIFT_MULTIPLIERS.items():
        constraints, target, names = equations(0, r0, r0)
        assignments = {**fixed_values, "correctionReturn0": correction_return}
        for name, value in assignments.items():
            index = names.index(name)
            constraints.append((
                f"fix-{name}-{value}",
                padd(pvar(index), ONE) if value else pvar(index),
            ))
        ordinary, ordinary_target, ordinary_eliminated = affine_eliminate(
            constraints, target
        )
        lifted, lifted_target, lifted_eliminated = (
            affine_eliminate_with_certificate(constraints, target)
        )
        assert ordinary_target == lifted_target
        assert ordinary_eliminated == lifted_eliminated
        assert [
            (name, polynomial) for name, polynomial, _certificate in lifted
        ] == ordinary
        raw_certificate: Certificate = {}
        reduced_combination = ZERO
        for row, expression in multipliers.items():
            _label, polynomial, certificate = lifted[row - 1]
            multiplier = parse_singular_squarefree(expression, names)
            reduced_combination = padd(
                reduced_combination, pmul(multiplier, polynomial)
            )
            raw_certificate = certificate_add(
                raw_certificate, certificate_scale(multiplier, certificate)
            )
        original = dict(constraints)
        raw_combination = ZERO
        for name, multiplier in raw_certificate.items():
            raw_combination = padd(
                raw_combination, pmul(multiplier, original[name])
            )
        reports.append({
            "case": "zero_one",
            "correction_return": correction_return,
            "reduced_combination_is_one": reduced_combination == ONE,
            "raw_combination_is_one": raw_combination == ONE,
            "raw_remainder": singular_polynomial(raw_combination, names),
            "raw_generator_count": len(raw_certificate),
            "raw_multiplier_monomials": sum(
                len(multiplier) for multiplier in raw_certificate.values()
            ),
            "raw_max_multiplier_degree": max(
                (monomial.bit_count()
                 for multiplier in raw_certificate.values()
                 for monomial in multiplier),
                default=0,
            ),
        })
    return reports


def equations(
    q: int, c: int, direction: int,
    equal_factor_difference_coordinates: bool = False,
) -> tuple[
    list[tuple[str, Polynomial]], Polynomial, list[str]
]:
    names: list[str] = []

    def variables(prefix: str, count: int) -> list[Polynomial]:
        start = len(names)
        names.extend(f"{prefix}{i}" for i in range(count))
        return [pvar(start + i) for i in range(count)]

    ell = variables("ell", 10)
    m_parameters = variables("m", 10)
    m = [
        padd(m_parameter, ell_coordinate)
        if equal_factor_difference_coordinates else m_parameter
        for m_parameter, ell_coordinate in zip(m_parameters, ell, strict=True)
    ]
    x = variables("x", 10)
    y = variables("y", 10)
    factor_constant = variables("factorConstant", 1)[0]
    factor_linear = variables("factorLinear", 10)
    correction_constant = variables("correctionConstant", 1)[0]
    correction_linear = variables("correctionLinear", 10)
    correction_targets = variables("correctionTarget", 8)
    correction_return = variables("correctionReturn", 1)[0]

    q_anf = fixed_anf(form_to_anf(q, 2))
    c_anf = fixed_anf(form_to_anf(c, 2))
    first_left = anf_add(symbolic_linear(ell), q_anf)
    first_right = anf_add(symbolic_linear(m), c_anf)
    shifted_left = anf_add(first_left, symbolic_linear(x))
    shifted_right = anf_add(first_right, symbolic_linear(y))
    first = anf_mul(first_left, first_right)
    shifted = anf_mul(shifted_left, shifted_right)
    returned = anf_add(first, shifted)

    correction: SymbolicANF = {0: correction_constant}
    correction = anf_add(correction, symbolic_linear(correction_linear))
    for scalar, mask in zip(
        correction_targets, FIRST_ORDER_MASKS, strict=True
    ):
        correction = anf_add(
            correction,
            scaled_fixed_anf(form_to_anf(target_from_mask(mask), 2), scalar),
        )
    correction = anf_add(
        correction,
        {support: pmul(coefficient, correction_return)
         for support, coefficient in returned.items()},
    )
    high_factor = anf_add(first, correction)
    feedback_factor = anf_add(
        {0: factor_constant}, symbolic_linear(factor_linear),
        fixed_anf(form_to_anf(direction, 2)),
    )
    product = anf_mul(high_factor, feedback_factor)

    constraints: list[tuple[str, Polynomial]] = []
    add_named_constraints(constraints, "return-high", returned, 3)
    add_named_constraints(constraints, "product-high", product, 3)
    return_quotient = quotient_coefficients(returned)
    product_quotient = quotient_coefficients(product)
    for position in return_quotient:
        constraint = padd(
            return_quotient[position], product_quotient[position]
        )
        if constraint:
            constraints.append((f"quotient-{position}", constraint))
    target = padd(missing_coefficient(returned), missing_coefficient(product))
    return constraints, target, names


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--case", required=True,
        choices=("zero_one", "one_one", "one_two", "one_three"),
    )
    parser.add_argument(
        "--direction", required=True, choices=("r0", "r1", "rinf")
    )
    parser.add_argument("--multiplier-degree", type=int, default=0)
    parser.add_argument("--targeted-degree-two", action="store_true")
    parser.add_argument(
        "--case-split-residual", action="store_true",
        help=(
            "split on the variables in the degree-one residual and test whether "
            "each residual-one branch has a degree-one Nullstellensatz certificate"
        ),
    )
    parser.add_argument(
        "--aggregate-branch-certificate", action="store_true",
        help=(
            "interpolate all successful residual-one branch certificates "
            "into one Boolean-polynomial identity"
        ),
    )
    parser.add_argument(
        "--exceptional-singular", metavar="PATH",
        help=(
            "use the named Singular executable to discover, lift, and replay "
            "unit certificates for residual branches not closed by the "
            "sparse span search"
        ),
    )
    parser.add_argument(
        "--print-aggregate-certificate", action="store_true",
        help="include the interpolated multiplier dictionary in JSON output",
    )
    parser.add_argument(
        "--print-aggregate-lean", action="store_true",
        help="print the compact aggregate target, generators, and multipliers as Lean expressions",
    )
    parser.add_argument(
        "--emit-aggregate-lean-file", action="store_true",
        help="emit a standalone Lean leaf for the compact aggregate certificate",
    )
    parser.add_argument(
        "--singular", action="store_true",
        help="emit a Singular Gröbner-basis calculation instead of running the span search",
    )
    parser.add_argument(
        "--polybori", action="store_true",
        help="use Singular's PolyBoRi backend in emitted input",
    )
    parser.add_argument(
        "--slimgb", action="store_true",
        help="use Singular's slimgb algorithm in emitted input",
    )
    parser.add_argument(
        "--fix", action="append", default=[], metavar="NAME=BIT",
        help="add a Boolean parameter assignment (repeatable)",
    )
    parser.add_argument(
        "--reduce-one", action="store_true",
        help="ask Singular whether the assigned constraint ideal contains one",
    )
    parser.add_argument(
        "--assume-target-one", action="store_true",
        help=(
            "adjoin target + 1 to the constraint ideal; a unit certificate "
            "then proves that all semantic zero constraints force target = 0"
        ),
    )
    parser.add_argument(
        "--affine-eliminate", action="store_true",
        help="substitute affine pivots before certificate search or Singular output",
    )
    parser.add_argument(
        "--singular-certificate", action="store_true",
        help="use liftstd and print a generator-to-unit transformation column",
    )
    parser.add_argument(
        "--lift-after-basis", action="store_true",
        help="compute a standard basis first, then lift its first row to the generators",
    )
    parser.add_argument(
        "--verify-exceptional-certificate", action="store_true",
        help="replay the two stored exceptional lift certificates in Python",
    )
    parser.add_argument(
        "--lift-exceptional-to-raw", action="store_true",
        help=(
            "lift the two zero_one exceptional certificates through affine "
            "elimination and replay them in the original constraint ideal"
        ),
    )
    parser.add_argument(
        "--equal-factor-difference-coordinates", action="store_true",
        help="parameterize the second linear part by its difference from the first",
    )
    parser.add_argument(
        "--dump-generator", action="append", type=int, default=[], metavar="ROW",
        help="print a selected one-based generator after affine elimination",
    )
    args = parser.parse_args()
    if args.verify_exceptional_certificate:
        for report in verify_exceptional_lift_certificates():
            print(report)
        return
    if args.lift_exceptional_to_raw:
        for report in lift_zero_one_exceptional_certificates_to_raw():
            print(report)
        return
    cases = {
        "zero_one": (0, r0),
        "one_one": (r0, r0),
        "one_two": (r0, r1),
        "one_three": (r0, r0 ^ r1),
    }
    directions = {"r0": r0, "r1": r1, "rinf": rinf}
    constraints, target, names = equations(
        *cases[args.case], directions[args.direction],
        equal_factor_difference_coordinates=args.equal_factor_difference_coordinates,
    )
    fixed: dict[int, bool] = {}
    for specification in args.fix:
        name, separator, raw_value = specification.partition("=")
        if not separator or raw_value not in ("0", "1") or name not in names:
            parser.error(f"invalid --fix {specification!r}; expected an existing NAME=0|1")
        fixed[names.index(name)] = raw_value == "1"
    if fixed:
        constraints.extend(
            (
                f"fix-{names[index]}-{int(value)}",
                padd(pvar(index), ONE) if value else pvar(index),
            )
            for index, value in fixed.items()
        )
    if args.assume_target_one:
        constraints.append(("assume-target-one", padd(target, ONE)))
    eliminated: dict[int, Polynomial] = {}
    if args.affine_eliminate:
        constraints, target, eliminated = affine_eliminate(
            constraints, target
        )
    if args.dump_generator:
        for row in args.dump_generator:
            if not 1 <= row <= len(constraints):
                parser.error(f"--dump-generator row {row} is out of range")
            label, polynomial = constraints[row - 1]
            print({
                "row": row,
                "label": label,
                "polynomial": singular_polynomial(polynomial, names),
            })
        return
    if args.case_split_residual or args.aggregate_branch_certificate:
        degree_one = multiplied_constraints(constraints, names, 1)
        residual, target_certificate = reduce_with_certificate(degree_one, target)
        split_indices = sorted({
            index
            for monomial in residual
            for index in range(len(names))
            if (monomial >> index) & 1 and index not in fixed
        })
        remaining_indices = [
            index for index in range(len(names))
            if index not in split_indices and index not in fixed
        ]
        residual_one = 0
        degree_zero_certificates = 0
        degree_one_certificates = 0
        targeted_degree_two_certificates = 0
        exceptional_singular_certificates = 0
        exceptional_singular_reports: list[dict[str, object]] = []
        unresolved: list[dict[str, int]] = []
        aggregate: dict[str, Polynomial] = {}
        for label in target_certificate:
            add_certificate_term(aggregate, label, ONE, names)
        for values in product((False, True), repeat=len(split_indices)):
            assignment = {
                **dict(zip(split_indices, values, strict=True)),
                **fixed,
            }
            if substitute(residual, assignment) != ONE:
                continue
            residual_one += 1
            specialized = [
                (name, value)
                for name, polynomial in constraints
                if (value := substitute(polynomial, assignment))
            ]
            delta = ONE
            for index, value in zip(split_indices, values, strict=True):
                factor = pvar(index) if value else padd(ONE, pvar(index))
                delta = pmul(delta, factor)
            branch_remainder, branch_certificate = reduce_with_certificate(
                specialized, ONE
            )
            if not branch_remainder:
                degree_zero_certificates += 1
                for label in branch_certificate:
                    add_certificate_term(aggregate, label, delta, names)
                continue
            generated = [*specialized]
            for name, polynomial in specialized:
                for index in remaining_indices:
                    value = pmul(polynomial, pvar(index))
                    if value:
                        generated.append((f"({names[index]})*({name})", value))
            branch_remainder, branch_certificate = reduce_with_certificate(
                generated, ONE
            )
            if not branch_remainder:
                degree_one_certificates += 1
                for label in branch_certificate:
                    add_certificate_term(aggregate, label, delta, names)
            else:
                targeted = [
                    *generated,
                    *constraints_times_monomials(
                        specialized, branch_remainder, names
                    ),
                ]
                targeted_remainder, targeted_certificate = (
                    reduce_with_certificate(targeted, ONE)
                )
                if not targeted_remainder:
                    targeted_degree_two_certificates += 1
                    for label in targeted_certificate:
                        add_certificate_term(aggregate, label, delta, names)
                    continue
                if args.exceptional_singular:
                    for correction_return in (0, 1):
                        exceptional = exceptional_branch_certificate(
                            constraints, target, names, assignment,
                            correction_return, args.exceptional_singular,
                        )
                        exceptional_singular_reports.append({
                            "assignment": {
                                names[index]: int(value)
                                for index, value in assignment.items()
                            },
                            "correction_return": correction_return,
                            "raw_generator_count": len(exceptional),
                            "raw_multiplier_monomials": sum(
                                len(multiplier)
                                for multiplier in exceptional.values()
                            ),
                            "raw_max_multiplier_degree": max(
                                (monomial.bit_count()
                                 for multiplier in exceptional.values()
                                 for monomial in multiplier),
                                default=0,
                            ),
                        })
                        exceptional_singular_certificates += 1
                branch_summary: dict[str, int | list[int]] = {
                    names[index]: int(assignment[index]) for index in split_indices
                }
                branch_summary["remainder_monomials"] = len(targeted_remainder)
                branch_summary["remainder_degrees"] = sorted({
                    monomial.bit_count() for monomial in targeted_remainder
                })
                unresolved.append(branch_summary)
        aggregate_combination = ZERO
        constraint_by_name = dict(constraints)
        for name, multiplier in aggregate.items():
            aggregate_combination = padd(
                aggregate_combination,
                pmul(multiplier, constraint_by_name[name]),
            )
        report: dict[str, object] = {
            "case": args.case,
            "direction": args.direction,
            "residual": sorted(monomial_name(m, names) for m in residual),
            "split_variables": [names[index] for index in split_indices],
            "residual_one_branches": residual_one,
            "degree_zero_certificates": degree_zero_certificates,
            "degree_one_certificates": degree_one_certificates,
            "targeted_degree_two_certificates": targeted_degree_two_certificates,
            "exceptional_singular_certificates": exceptional_singular_certificates,
            "exceptional_singular_reports": exceptional_singular_reports,
            "unresolved_count": len(unresolved),
            "first_unresolved": unresolved[:8],
            "aggregate_generator_count": sum(bool(value) for value in aggregate.values()),
            "aggregate_multiplier_monomials": sum(len(value) for value in aggregate.values()),
            "aggregate_max_multiplier_degree": max(
                (monomial.bit_count() for value in aggregate.values() for monomial in value),
                default=0,
            ),
            "aggregate_identity_remainder_monomials": len(
                padd(target, aggregate_combination)
            ),
        }
        if args.print_aggregate_certificate:
            report["aggregate_certificate"] = {
                name: singular_polynomial(multiplier, names)
                for name, multiplier in aggregate.items() if multiplier
            }
        print(json.dumps(report, sort_keys=True))
        if args.print_aggregate_lean:
            selected = [
                (name, constraint_by_name[name], multiplier)
                for name, multiplier in aggregate.items() if multiplier
            ]
            print("TARGET=" + lean_polynomial(target))
            for index, (name, constraint, multiplier) in enumerate(selected):
                print(f"GENERATOR[{index}]={name}=" + lean_polynomial(constraint))
                print(f"MULTIPLIER[{index}]=" + lean_polynomial(multiplier))
        if args.emit_aggregate_lean_file:
            selected = [
                (name, constraint_by_name[name], multiplier)
                for name, multiplier in aggregate.items() if multiplier
            ]
            coordinate_count = len(names)
            generator_count = len(selected)
            case_stem = {
                "zero_one": "zeroOne",
                "one_one": "oneOne",
                "one_two": "oneTwo",
                "one_three": "oneThree",
            }[args.case]
            direction_stem = {
                "r0": "R0",
                "r1": "R1",
                "rinf": "RInf",
            }[args.direction]
            if args.case == "zero_one" and args.direction == "r1":
                stem = "zeroOneReduced" if args.affine_eliminate else "zeroOneRaw"
                theorem_name = (
                    "zeroOne_offAxis_reduced_history_missing_eq_zero"
                    if args.affine_eliminate else
                    "zeroOne_offAxis_raw_history_missing_eq_zero"
                )
            else:
                variant = "Reduced" if args.affine_eliminate else "Raw"
                stem = f"{case_stem}{direction_stem}{variant}"
                theorem_name = f"{case_stem}_{direction_stem}_{variant}_history_missing_eq_zero"
            print("import UnrestrictedBooleanMul.ANF")
            print()
            print("/-!")
            print("# Explicit history certificate for a rational return")
            print()
            print("This generated module checks an explicit sparse Boolean-polynomial")
            print("identity over `F₂`; it uses no decision procedure or additional axiom.")
            print("-/")
            print()
            print("namespace UnrestrictedBooleanMul.N5")
            print("noncomputable section")
            print("set_option linter.unreachableTactic false")
            print("set_option linter.unusedTactic false")
            print("set_option linter.unusedSimpArgs false")
            print("set_option linter.unnecessarySeqFocus false")
            print("set_option maxRecDepth 8192")
            print()
            print("/-- The missing-target coefficient in this certificate. -/")
            print(f"def {stem}Target (v : Fin {coordinate_count} → F₂) : F₂ :=")
            print("  " + lean_polynomial(target))
            print()
            print(f"/-- The {generator_count} constraint polynomials used by the sparse certificate. -/")
            print(
                f"def {stem}Constraint (v : Fin {coordinate_count} → F₂) : "
                f"Fin {generator_count} → F₂ :="
            )
            print("  ![")
            for index, (name, constraint, _multiplier) in enumerate(selected):
                comma = "," if index + 1 < len(selected) else ""
                print(f"    -- {name}")
                print("    " + lean_polynomial(constraint) + comma)
            print("  ]")
            print()
            print(
                f"private def {stem}Multiplier (v : Fin {coordinate_count} → F₂) : "
                f"Fin {generator_count} → F₂ :="
            )
            print("  ![")
            for index, (name, _constraint, multiplier) in enumerate(selected):
                comma = "," if index + 1 < len(selected) else ""
                print(f"    -- {name}")
                print("    " + lean_polynomial(multiplier) + comma)
            print("  ]")
            print()
            print(
                f"private def {stem}Product (v : Fin {coordinate_count} → F₂) : "
                f"Fin {generator_count} → F₂ :="
            )
            print("  ![")
            for index, (name, constraint, multiplier) in enumerate(selected):
                comma = "," if index + 1 < len(selected) else ""
                print(f"    -- {name}")
                print("    " + lean_polynomial(pmul(multiplier, constraint)) + comma)
            print("  ]")
            print()
            print(f"private def {stem}Combination (v : Fin {coordinate_count} → F₂) : F₂ :=")
            for index in range(len(selected)):
                suffix = " +" if index + 1 < len(selected) else ""
                print(
                    f"  {stem}Multiplier v {index} * "
                    f"{stem}Constraint v {index}{suffix}"
                )
            print()
            print("private theorem f2_mul_self (x : F₂) : x * x = x := by")
            print("  rcases f2_eq_zero_or_one x with h | h <;> simp [h]")
            print()
            print("private theorem f2_two_eq_zero : (2 : F₂) = 0 :=")
            print("  CharTwo.two_eq_zero")
            print()
            for index, (_name, _constraint, _multiplier) in enumerate(selected):
                print("set_option maxHeartbeats 1000000 in")
                print(f"private theorem {stem}_product_{index} (v : Fin {coordinate_count} → F₂) :")
                print(f"    {stem}Multiplier v {index} * {stem}Constraint v {index} =")
                print(f"      {stem}Product v {index} := by")
                print(f"  simp [{stem}Multiplier, {stem}Constraint,")
                print(f"    {stem}Product, add_mul, mul_add]")
                print("  all_goals ring_nf")
                print("  all_goals simp only [pow_two, f2_mul_self]")
                print("  all_goals (try rw [f2_two_eq_zero])")
                print("  all_goals (try simp only [mul_zero, add_zero, zero_add])")
                print("  all_goals ring_nf")
                print("  all_goals simp [f2_two_eq_zero]")
                print()
            print("set_option maxHeartbeats 3000000 in")
            print("set_option maxRecDepth 8192 in")
            print(f"private theorem {stem}_certificate (v : Fin {coordinate_count} → F₂) :")
            print(f"    {stem}Target v = {stem}Combination v := by")
            product_lemmas = ", ".join(
                f"{stem}_product_{index}" for index in range(len(selected))
            )
            print(f"  unfold {stem}Combination")
            print("  rw [" + product_lemmas + "]")
            print(f"  simp [{stem}Target, {stem}Product] <;>")
            print("    ring_nf <;>")
            print("    simp [CharTwo.ofNat_eq_mod] <;>")
            print("    ring")
            print()
            print("set_option maxRecDepth 8192 in")
            print(f"theorem {theorem_name}")
            print(f"    (v : Fin {coordinate_count} → F₂)")
            print(
                f"    (hzero : ∀ i : Fin {generator_count}, "
                f"{stem}Constraint v i = 0) :"
            )
            print(f"    {stem}Target v = 0 := by")
            print(f"  rw [{stem}_certificate v]")
            print(f"  simp [{stem}Combination, hzero]")
            print()
            print("end")
            print("end UnrestrictedBooleanMul.N5")
        return
    if args.singular:
        if args.polybori:
            print('LIB "polybori.lib";')
        active_indices = sorted({
            index
            for _name, polynomial in constraints
            for monomial in polynomial
            for index in range(len(names))
            if (monomial >> index) & 1
        } | {
            index
            for monomial in target
            for index in range(len(names))
            if (monomial >> index) & 1
        })
        active_names = [names[index] for index in active_indices]
        if not active_names:
            active_names = ["unusedParameter"]
        print(f"ring coefficientRing=2,({','.join(active_names)}),dp;")
        generator_labels = [name for name, _polynomial in constraints]
        generator_strings = [
            singular_polynomial(polynomial, names)
            for _name, polynomial in constraints
        ]
        if not args.polybori:
            # `Polynomial` already lives in the Boolean quotient, so x*x is
            # represented as x there.  Singular's ordinary polynomial ring
            # needs the field equations emitted textually before quotienting.
            generator_strings.extend(
                f"{names[index]}^2+{names[index]}"
                for index in active_indices
            )
            generator_labels.extend(
                f"boolean-{names[index]}" for index in active_indices
            )
        for index, label in enumerate(generator_labels, start=1):
            print(f"// generator {index}: {label}")
        print("ideal historyIdeal=")
        print(",\n".join(generator_strings) + ";")
        if args.polybori:
            print("ideal historyBasis=boolean_std(historyIdeal);")
        elif args.singular_certificate:
            print("matrix historyLift;")
            print("ideal historyBasis=liftstd(historyIdeal,historyLift);")
        else:
            print("option(redSB);")
            algorithm = "slimgb" if args.slimgb else "std"
            print(f"ideal historyBasis={algorithm}(historyIdeal);")
            if args.lift_after_basis:
                print("matrix historyLift=lift(historyIdeal,historyBasis);")
        print('print("basis-size");')
        print("print(size(historyBasis));")
        print('print("target-remainder");')
        reduction_target = ONE if args.reduce_one else target
        print(
            f"print(reduce({singular_polynomial(reduction_target, names)}, historyBasis));"
        )
        if args.singular_certificate or args.lift_after_basis:
            print('print("certificate-column");')
            print("int historyRow;")
            print("for (historyRow=1; historyRow<=nrows(historyLift); historyRow=historyRow+1)")
            print("{")
            print("  if (historyLift[historyRow,1] != 0)")
            print("  {")
            print("    print(historyRow);")
            print("    print(historyLift[historyRow,1]);")
            print("  }")
            print("}")
        print("quit;")
        return
    generated = multiplied_constraints(
        constraints, names, args.multiplier_degree
    )
    if args.targeted_degree_two:
        degree_one = multiplied_constraints(constraints, names, 1)
        first_remainder, _ = reduce_with_certificate(degree_one, target)
        generated = [
            *degree_one,
            *constraints_times_monomials(
                constraints, first_remainder, names
            ),
        ]
    remainder, certificate = reduce_with_certificate(generated, target)
    print({
        "case": args.case,
        "direction": args.direction,
        "parameter_count": len(names),
        "constraint_count": len(constraints),
        "affine_eliminated_variables": sorted(names[index] for index in eliminated),
        "generated_constraint_count": len(generated),
        "multiplier_degree": args.multiplier_degree,
        "target_monomials": len(target),
        "linear_span_certificate": not remainder,
        "certificate_size": len(certificate),
        "certificate": certificate,
        "remainder_monomials": len(remainder),
        "remainder_degrees": sorted({m.bit_count() for m in remainder}),
        "remainder": sorted(monomial_name(m, names) for m in remainder),
    })


if __name__ == "__main__":
    main()
