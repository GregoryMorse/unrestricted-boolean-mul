from __future__ import annotations

import w_pq_analysis as e
from first_order_cubic_rigidity_probe import LINEARS, UBASIS, form


LEFT = form(0x46)
RIGHT = form(0x83)


def boolean_contraction(linear: int, two: int) -> int:
    out = 0
    for k in e.iterbits(two):
        support = e.COMBS[2][k]
        parity = sum((linear >> i) & 1 for i in e.iterbits(support)) & 1
        if parity:
            out ^= 1 << k
    return out


def main() -> None:
    columns = [e.wedge(linear, 1, RIGHT, 2) for linear in LINEARS]
    columns += [e.wedge(linear, 1, LEFT, 2) for linear in LINEARS]
    kernel = e.nullspace_columns(columns)
    envelope = e.basis(UBASIS)
    z_values: list[int] = []
    u_values: list[int] = []
    for mask in range(16):
        relation = e.span_vector(kernel, mask)
        x = e.span_vector(LINEARS, relation & ((1 << 10) - 1))
        y = e.span_vector(LINEARS, relation >> 10)
        correction = (
            e.wedge(x, 1, y, 1)
            ^ boolean_contraction(x, RIGHT)
            ^ boolean_contraction(y, LEFT)
        )
        z = next(
            (candidate for candidate in range(1 << 10)
             if e.rank(envelope +
                       [correction ^ e.wedge(x, 1, candidate, 1)]) == 8),
            None,
        )
        envelope_coeff = None
        if z is not None:
            solved = e.solve_columns(
                envelope,
                correction ^ e.wedge(x, 1, z, 1),
            )
            envelope_coeff = None if solved is None else solved[0]
        assert z is not None and envelope_coeff is not None
        z_values.append(z)
        u_values.append(envelope_coeff)
        print(
            f"{mask:04b} x={x:010b} y={y:010b} "
            f"z={'none' if z is None else format(z, '010b')} "
            f"u={'none' if envelope_coeff is None else format(envelope_coeff, '08b')}"
        )

    def anf_coefficients(values: list[int]) -> list[int]:
        result = values[:]
        for bit in range(4):
            for mask in range(16):
                if mask & (1 << bit):
                    result[mask] ^= result[mask ^ (1 << bit)]
        return result

    print("z ANF", [(f"{mask:04b}", f"{value:010b}")
                    for mask, value in enumerate(anf_coefficients(z_values))
                    if value])
    print("u ANF", [(f"{mask:04b}", f"{value:08b}")
                    for mask, value in enumerate(anf_coefficients(u_values))
                    if value])

    # Solve once for a low-degree symbolic identity
    # correction = envelope + x wedge z.  Parameter monomials use the
    # four-bit masks p,q,r,s; multiplication is Boolean union of masks.
    x_basis = [
        sum(1 << i for i in (0, 1, 3, 4)),
        sum(1 << i for i in (0, 2, 3)),
        sum(1 << i for i in (5, 6, 8, 9)),
        sum(1 << i for i in (5, 7, 8)),
    ]
    y_basis = [
        sum(1 << i for i in (0, 2, 3)),
        sum(1 << i for i in (1, 2, 4)),
        sum(1 << i for i in (5, 7, 8)),
        sum(1 << i for i in (6, 7, 9)),
    ]
    correction_coeff = [0] * 16
    for i in range(4):
        correction_coeff[1 << i] ^= boolean_contraction(x_basis[i], RIGHT)
        correction_coeff[1 << i] ^= boolean_contraction(y_basis[i], LEFT)
        for j in range(4):
            correction_coeff[(1 << i) | (1 << j)] ^= e.wedge(
                x_basis[i], 1, y_basis[j], 1
            )

    def flatten(poly: list[int]) -> int:
        return sum(value << (45 * monomial)
                   for monomial, value in enumerate(poly))

    z_monomials = [
        mask for mask in range(16) if mask.bit_count() <= 3
    ]
    envelope_monomials = list(range(16))
    columns: list[int] = []
    labels: list[tuple[str, int, int]] = []
    for coordinate in range(10):
        basis_linear = 1 << coordinate
        for monomial in z_monomials:
            poly = [0] * 16
            for i in range(4):
                poly[monomial | (1 << i)] ^= e.wedge(
                    x_basis[i], 1, basis_linear, 1
                )
            columns.append(flatten(poly))
            labels.append(("z", coordinate, monomial))
    for direction, two in enumerate(UBASIS):
        for monomial in envelope_monomials:
            poly = [0] * 16
            poly[monomial] = two
            columns.append(flatten(poly))
            labels.append(("u", direction, monomial))
    solution = e.solve_columns(columns, flatten(correction_coeff))
    print("cubic-z symbolic identity", solution is not None)
    if solution is not None:
        selected, _ = solution
        print([labels[i] for i in e.iterbits(selected)])


if __name__ == "__main__":
    main()
