#!/usr/bin/env python3
"""SAT falsification of the parameterized rational-return history lemma.

For one of the four rational factor-pair types and one rational exterior
kernel direction, this asks whether an unpopulated equal-high return can feed
back through that direction and expose the missing first-order target coset.
The old high representative is retained.  The encoding works with all ANF
coefficients algebraically; it does not enumerate circuits.

An independently replayed SAT model is a counterexample.  UNSAT is discovery
evidence until accompanied by a checked certificate or a Lean proof.
"""

from __future__ import annotations

import argparse
import json
import time

import pycryptosat

from quadratic_return_class_sample import FIRST_ORDER_MASKS, target_from_mask
from quadratic_return_feedback_probe import target_missing_functional
from quadratic_return_kernel_counterexample import low_product
from quadratic_return_population_probe import (
    REDUCE_TARGET,
    minimum_target_coset_rank,
    populated_quotient_classes,
)
from target_tight_suffix_probe import (
    ALL_ONES,
    FIRST_ORDER_TARGETS,
    TARGETS,
    WIDTH,
    X,
    xor_all,
)
from w_pq_analysis import (
    anf_degree_part,
    anf_multiply,
    form_to_anf,
    r0,
    r1,
    rinf,
)


PAIR_MASKS = [
    (1 << i) | (1 << j)
    for i in range(10) for j in range(i + 1, 10)
]


def anf_truth_table(poly: int) -> int:
    result = 0
    monomial = poly
    while monomial:
        unit = monomial & -monomial
        support = unit.bit_length() - 1
        table = ALL_ONES
        for variable in range(10):
            if (support >> variable) & 1:
                table &= X[variable]
        result ^= table
        monomial ^= unit
    return result


def twoform_truth_table(form: int) -> int:
    return anf_truth_table(form_to_anf(form, 2))


class Encoding:
    def __init__(
        self, q: int, c: int, rational_direction: int,
        timeout_seconds: float, require_unpopulated: bool = True,
        require_feedback: bool = True, extract_core: bool = False,
    ) -> None:
        self.q = q
        self.c = c
        self.rational_direction = rational_direction
        self.require_unpopulated = require_unpopulated
        self.require_feedback = require_feedback
        self.extract_core = extract_core
        self.assumption_labels: dict[int, str] = {}
        self.solver = pycryptosat.Solver(
            threads=1, time_limit=timeout_seconds
        )
        self.next_variable = 1
        self.clauses = 0
        self.xors = 0

        self.ell = [self.var() for _ in range(10)]
        self.m = [self.var() for _ in range(10)]
        self.x = [self.var() for _ in range(10)]
        self.y = [self.var() for _ in range(10)]
        self.factor_constant = self.var()
        self.factor_linear = [self.var() for _ in range(10)]
        self.correction_affine = [self.var() for _ in range(11)]
        self.correction_targets = [self.var() for _ in FIRST_ORDER_MASKS]
        self.correction_return = self.var()

        self.g_values: list[int] = []
        self.return_values: list[int] = []
        self.product_values: list[int] = []
        self.return_quadratic = [self.var() for _ in PAIR_MASKS]
        self.product_quadratic = [self.var() for _ in PAIR_MASKS]

    def var(self) -> int:
        result = self.next_variable
        self.next_variable += 1
        return result

    def add_clause(self, literals: list[int]) -> None:
        self.solver.add_clause(literals)
        self.clauses += 1

    def add_xor(self, variables: list[int], rhs: bool = False) -> None:
        parity: dict[int, bool] = {}
        for variable in variables:
            parity[variable] = not parity.get(variable, False)
        normalized = [variable for variable, odd in parity.items() if odd]
        if normalized:
            self.solver.add_xor_clause(normalized, rhs)
            self.xors += 1
        elif rhs:
            self.add_clause([])

    def xor_var(self, terms: list[int], constant: bool = False) -> int:
        result = self.var()
        self.add_xor([result, *terms], constant)
        return result

    def and_var(self, left: int, right: int) -> int:
        result = self.var()
        self.add_clause([-result, left])
        self.add_clause([-result, right])
        self.add_clause([result, -left, -right])
        return result

    def require_clause(self, literals: list[int], label: str) -> None:
        if not self.extract_core:
            self.add_clause(literals)
            return
        assumption = self.var()
        self.assumption_labels[assumption] = label
        self.add_clause([-assumption, *literals])

    def require_xor(
        self, variables: list[int], rhs: bool, label: str
    ) -> None:
        if not self.extract_core:
            self.add_xor(variables, rhs)
            return
        parity = self.xor_var(variables)
        assumption = self.var()
        self.assumption_labels[assumption] = label
        self.add_clause([-assumption, parity if rhs else -parity])

    @staticmethod
    def selected_linear(
        selectors: list[int], assignment: int
    ) -> list[int]:
        return [
            selectors[i] for i in range(10)
            if (assignment >> i) & 1
        ]

    def anf_coefficient_var(self, values: list[int], monomial: int) -> int:
        terms: list[int] = []
        assignment = monomial
        while True:
            terms.append(values[assignment])
            if assignment == 0:
                break
            assignment = (assignment - 1) & monomial
        return self.xor_var(terms)

    def build_values(self) -> None:
        q_table = twoform_truth_table(self.q)
        c_table = twoform_truth_table(self.c)
        direction_table = twoform_truth_table(self.rational_direction)
        for assignment in range(WIDTH):
            ell_terms = self.selected_linear(self.ell, assignment)
            m_terms = self.selected_linear(self.m, assignment)
            x_terms = self.selected_linear(self.x, assignment)
            y_terms = self.selected_linear(self.y, assignment)
            left = self.xor_var(
                ell_terms, bool((q_table >> assignment) & 1)
            )
            right = self.xor_var(
                m_terms, bool((c_table >> assignment) & 1)
            )
            shifted_left = self.xor_var(
                [*ell_terms, *x_terms],
                bool((q_table >> assignment) & 1),
            )
            shifted_right = self.xor_var(
                [*m_terms, *y_terms],
                bool((c_table >> assignment) & 1),
            )
            g = self.and_var(left, right)
            shifted = self.and_var(shifted_left, shifted_right)
            returned = self.xor_var([g, shifted])
            self.g_values.append(g)
            self.return_values.append(returned)

            correction_terms = [self.correction_affine[0]]
            correction_terms.extend(
                self.correction_affine[i + 1] for i in range(10)
                if (assignment >> i) & 1
            )
            correction_terms.extend(
                selector
                for selector, table in zip(
                    self.correction_targets,
                    FIRST_ORDER_TARGETS,
                    strict=True,
                )
                if (table >> assignment) & 1
            )
            returned_correction = self.and_var(
                self.correction_return, returned
            )
            high_factor = self.xor_var(
                [g, returned_correction, *correction_terms]
            )
            feedback = self.xor_var(
                [
                    self.factor_constant,
                    *self.selected_linear(self.factor_linear, assignment),
                ],
                bool((direction_table >> assignment) & 1),
            )
            self.product_values.append(self.and_var(high_factor, feedback))

    def constrain_low_coordinates(self) -> None:
        for coefficient, monomial in zip(
            self.return_quadratic, PAIR_MASKS, strict=True
        ):
            actual = self.anf_coefficient_var(
                self.return_values, monomial
            )
            self.add_xor([coefficient, actual])
        for monomial in range(WIDTH):
            if monomial.bit_count() < 3:
                continue
            coefficient = self.anf_coefficient_var(
                self.return_values, monomial
            )
            self.require_clause(
                [-coefficient], f"return-high-{monomial:#05x}"
            )

        if not self.require_feedback:
            return
        for coefficient, monomial in zip(
            self.product_quadratic, PAIR_MASKS, strict=True
        ):
            actual = self.anf_coefficient_var(
                self.product_values, monomial
            )
            self.add_xor([coefficient, actual])
        for monomial in range(WIDTH):
            if monomial.bit_count() < 3:
                continue
            coefficient = self.anf_coefficient_var(
                self.product_values, monomial
            )
            self.require_clause(
                [-coefficient], f"product-high-{monomial:#05x}"
            )

    def constrain_first_product_high(self) -> None:
        high_coefficients: list[int] = []
        for monomial in range(WIDTH):
            if monomial.bit_count() < 3:
                continue
            coefficient = self.var()
            terms: list[int] = []
            assignment = monomial
            while True:
                terms.append(self.g_values[assignment])
                if assignment == 0:
                    break
                assignment = (assignment - 1) & monomial
            self.add_xor([coefficient, *terms])
            high_coefficients.append(coefficient)
        self.require_clause(high_coefficients, "first-product-high-nonzero")

    @staticmethod
    def reduction_columns() -> list[int]:
        return [REDUCE_TARGET(1 << i) for i in range(len(PAIR_MASKS))]

    def quotient_variables(self, quadratic: list[int]) -> dict[int, int]:
        columns = self.reduction_columns()
        positions = sorted({
            bit
            for column in columns
            for bit in range(45)
            if (column >> bit) & 1
        })
        if len(positions) != 36:
            raise AssertionError(f"expected 36 quotient coordinates, got {len(positions)}")
        result: dict[int, int] = {}
        for position in positions:
            result[position] = self.xor_var([
                coefficient
                for coefficient, column in zip(
                    quadratic, columns, strict=True
                )
                if (column >> position) & 1
            ])
        return result

    def constrain_unpopulated_return(self) -> None:
        quotient = self.quotient_variables(self.return_quadratic)
        for populated in populated_quotient_classes():
            self.add_clause([
                -variable if (populated >> position) & 1 else variable
                for position, variable in quotient.items()
            ])

    def constrain_missing_target_difference(self) -> None:
        return_quotient = self.quotient_variables(self.return_quadratic)
        product_quotient = self.quotient_variables(self.product_quadratic)
        for position in return_quotient:
            self.require_xor([
                return_quotient[position], product_quotient[position]
            ], False, f"quotient-equality-{position}")

        # On a target-valued difference this is the coefficient of the
        # missing first-order target class used by the other return probes.
        missing_pairs = {(0, 7), (0, 8), (1, 9), (2, 9)}
        missing_terms: list[int] = []
        for variables in (self.return_quadratic, self.product_quadratic):
            missing_terms.extend(
                coefficient
                for coefficient, support in zip(
                    variables, PAIR_MASKS, strict=True
                )
                if tuple(i for i in range(10) if (support >> i) & 1)
                in missing_pairs
            )
        self.require_xor(
            missing_terms, True, "missing-functional-one"
        )

    def build(self) -> None:
        self.build_values()
        self.constrain_low_coordinates()
        self.constrain_first_product_high()
        if self.require_unpopulated:
            self.constrain_unpopulated_return()
        if self.require_feedback:
            self.constrain_missing_target_difference()

    def parameter_variables(self) -> dict[str, int]:
        """Names shared with the polynomial-certificate discovery script."""
        result: dict[str, int] = {}
        for prefix, variables in (
            ("ell", self.ell),
            ("m", self.m),
            ("x", self.x),
            ("y", self.y),
            ("factorLinear", self.factor_linear),
            ("correctionLinear", self.correction_affine[1:]),
            ("correctionTarget", self.correction_targets),
        ):
            result.update({f"{prefix}{i}": variable for i, variable in enumerate(variables)})
        result["factorConstant0"] = self.factor_constant
        result["correctionConstant0"] = self.correction_affine[0]
        result["correctionReturn0"] = self.correction_return
        return result

    @staticmethod
    def selected_mask(
        model: tuple[bool | None, ...], variables: list[int]
    ) -> int:
        return sum(
            1 << i for i, variable in enumerate(variables)
            if model[variable]
        )

    def replay(self, model: tuple[bool | None, ...]) -> dict[str, object]:
        ell = self.selected_mask(model, self.ell)
        m = self.selected_mask(model, self.m)
        x = self.selected_mask(model, self.x)
        y = self.selected_mask(model, self.y)
        factor_constant = int(bool(model[self.factor_constant]))
        factor_linear = self.selected_mask(model, self.factor_linear)
        correction_affine = self.selected_mask(
            model, self.correction_affine
        )
        correction_targets = self.selected_mask(
            model, self.correction_targets
        )
        correction_return = int(bool(model[self.correction_return]))
        g = low_product(ell, m, self.q, self.c)
        shifted = low_product(ell ^ x, m ^ y, self.q, self.c)
        returned = g ^ shifted
        return_two = anf_degree_part(returned, 2)
        assert any(anf_degree_part(g, degree) for degree in range(3, 11))
        assert all(
            anf_degree_part(returned, degree) == 0
            for degree in range(3, 11)
        )
        if self.require_unpopulated:
            assert minimum_target_coset_rank(return_two) > 2

        if self.require_feedback:
            correction = (
                (correction_affine & 1)
                ^ form_to_anf(correction_affine >> 1, 1)
                ^ xor_all(
                    form_to_anf(target_from_mask(mask), 2)
                    for index, mask in enumerate(FIRST_ORDER_MASKS)
                    if (correction_targets >> index) & 1
                )
                ^ (returned if correction_return else 0)
            )
            factor = (
                factor_constant
                ^ form_to_anf(factor_linear, 1)
                ^ form_to_anf(self.rational_direction, 2)
            )
            product = anf_multiply(g ^ correction, factor)
            assert all(
                anf_degree_part(product, degree) == 0
                for degree in range(3, 11)
            )
            difference_two = anf_degree_part(product, 2) ^ return_two
            assert REDUCE_TARGET(difference_two) == 0
            assert target_missing_functional(difference_two) == 1

        report = {
            "ell": ell,
            "m": m,
            "x": x,
            "y": y,
            "factor_constant": factor_constant,
            "factor_linear": factor_linear,
            "correction_affine": correction_affine,
            "correction_targets": correction_targets,
            "correction_return": correction_return,
            "minimum_target_coset_rank": minimum_target_coset_rank(return_two),
        }
        return report


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--case", required=True,
        choices=("zero_one", "one_one", "one_two", "one_three"),
    )
    parser.add_argument(
        "--direction", required=True, choices=("r0", "r1", "rinf")
    )
    parser.add_argument("--timeout-seconds", type=float, default=600.0)
    parser.add_argument(
        "--allow-populated", action="store_true",
        help="omit unpopulatedness as a positive-control relaxation",
    )
    parser.add_argument(
        "--return-only-positive-control", action="store_true",
        help="check only that a nonzero-high unpopulated return exists",
    )
    parser.add_argument(
        "--extract-core", action="store_true",
        help="guard semantic assertions and print a CryptoMiniSat UNSAT core",
    )
    parser.add_argument(
        "--fix", action="append", default=[], metavar="NAME=BIT",
        help="fix a named algebraic parameter (repeatable)",
    )
    args = parser.parse_args()

    cases = {
        "zero_one": (0, r0),
        "one_one": (r0, r0),
        "one_two": (r0, r1),
        "one_three": (r0, r0 ^ r1),
    }
    directions = {"r0": r0, "r1": r1, "rinf": rinf}
    started = time.monotonic()
    encoding = Encoding(
        *cases[args.case], directions[args.direction], args.timeout_seconds,
        require_unpopulated=not args.allow_populated,
        require_feedback=not args.return_only_positive_control,
        extract_core=args.extract_core,
    )
    encoding.build()
    parameter_variables = encoding.parameter_variables()
    for specification in args.fix:
        name, separator, raw_value = specification.partition("=")
        if not separator or raw_value not in ("0", "1") or name not in parameter_variables:
            parser.error(f"invalid --fix {specification!r}; expected an existing NAME=0|1")
        variable = parameter_variables[name]
        encoding.add_clause([variable if raw_value == "1" else -variable])
    built = time.monotonic()
    assumptions = list(encoding.assumption_labels)
    result, model = encoding.solver.solve(assumptions=assumptions)
    finished = time.monotonic()
    report = {
        "case": args.case,
        "direction": args.direction,
        "require_unpopulated": not args.allow_populated,
        "require_feedback": not args.return_only_positive_control,
        "variables": encoding.next_variable - 1,
        "clauses": encoding.clauses,
        "xor_clauses": encoding.xors,
        "result": result,
        "build_seconds": round(built - started, 3),
        "solve_seconds": round(finished - built, 3),
    }
    print(json.dumps(report, sort_keys=True), flush=True)
    if result is False and args.extract_core:
        conflict = encoding.solver.get_conflict()
        core = [
            encoding.assumption_labels[abs(literal)]
            for literal in conflict
            if abs(literal) in encoding.assumption_labels
        ]
        print(json.dumps({
            "core_size": len(core),
            "core": sorted(core),
        }, sort_keys=True), flush=True)
    if result is True:
        assert model is not None
        print(json.dumps(encoding.replay(model), sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
