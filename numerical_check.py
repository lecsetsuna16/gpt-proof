#!/usr/bin/env python3
"""Independent arithmetic and numerical audit of the alternating-chain example.

Python 3.10 or later, standard library only.  Run:
    python3 numerical_check.py
    python3 numerical_check.py --json

This is NOT the Lean proof and does not replace it.  Exact Fraction arithmetic
checks finite pair counting, the first block, and the polynomial certificate.
Finite image sums are explicitly numerical approximations to infinite sums.

Convention used by the Lean project:
    E = (1/4) sum_{i,j=0..3} sum_{m in Z}' V(x_j + 4m - x_i).
The prime removes only i=j,m=0.  This counts ordered pairs.  The conventional
physical energy per particle with an extra factor 1/2 is E/2; the ordering of
configurations is unchanged.  The +/- symbols denote species: the bounded
Cauchy part attracts like species and repels unlike species, so it should
not be described as the ordinary electric Coulomb interaction.
"""

from __future__ import annotations

import argparse
from fractions import Fraction as F
import json
import math
from typing import Iterable


UNIFORM = (0, 2, 4, 6)  # half-units; physical coordinates (0, 1, 2, 3)
SHIFTED = (0, 3, 4, 5)  # physical coordinates (0, 3/2, 2, 5/2)
SIGNS = (1, -1, 1, -1)
LAMBDA = F(1, 1000)
PERIOD = 4


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def shell_counts(cell: tuple[int, ...], n: int) -> tuple[int, int]:
    """Count ordered images at displacements +n/2 and -n/2 independently."""
    signed = unsigned = 0
    for i, xi in enumerate(cell):
        for j, xj in enumerate(cell):
            for displacement in (n, -n):
                # xj - xi + 8m = displacement has exactly one integer m
                # precisely when its right-hand side is divisible by eight.
                if (displacement - (xj - xi)) % 8 == 0:
                    signed += SIGNS[i] * SIGNS[j]
                    unsigned += 1
    return signed, unsigned


def direct_exact_components(
    cell: tuple[int, ...], image_radius: int, spatial_cutoff: int | None = None
) -> tuple[F, F]:
    """Finite physical-coordinate image sum, with exact rational arithmetic.

    Returns (bounded signed energy, all-pair inverse-square energy), both in
    the project's ordered-pair convention.  A spatial cutoff, if supplied,
    is measured in half-units and permits an exact finite shell comparison.
    """
    soft = F(0)
    core = F(0)
    for i, xi in enumerate(cell):
        for j, xj in enumerate(cell):
            for m in range(-image_radius, image_radius + 1):
                if i == j and m == 0:
                    continue
                r = F(xj, 2) + PERIOD * m - F(xi, 2)
                require(r != 0, "Unexpected collision in an admissible cell")
                if spatial_cutoff is not None and abs(2 * r) > spatial_cutoff:
                    continue
                soft -= SIGNS[i] * SIGNS[j] * F(4) / (4 + r * r)
                core += 1 / (r * r)
    return soft / 4, core / 4


def shell_exact_gaps(nmax: int) -> tuple[F, F]:
    """Return soft E(U)-E(X), and core E(X)-E(U), through shell nmax."""
    soft_gap = F(0)
    core_cost = F(0)
    for n in range(1, nmax + 1):
        su, uu = shell_counts(UNIFORM, n)
        sx, ux = shell_counts(SHIFTED, n)
        soft_gap += F(sx - su, 4) * F(16, 16 + n * n)
        core_cost += F(ux - uu, n * n)
    return soft_gap, core_cost


def cauchy_block(x: F) -> F:
    coefficients = (-1, F(5, 2), -1, -1, -1, F(5, 2), -1, 0)
    return sum(
        (F(c) * 16 / (16 + (8 * x + j) ** 2)
         for j, c in enumerate(coefficients, start=1)),
        F(0),
    )


# Small exact polynomial routines.  Coefficients are in ascending degree.
Poly = tuple[F, ...]


def trim(poly: Iterable[F]) -> Poly:
    p = list(map(F, poly))
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return tuple(p or [F(0)])


def poly_add(a: Poly, b: Poly) -> Poly:
    return trim(
        (a[i] if i < len(a) else F(0))
        + (b[i] if i < len(b) else F(0))
        for i in range(max(len(a), len(b)))
    )


def poly_scale(a: Poly, coefficient: F) -> Poly:
    return trim(coefficient * x for x in a)


def poly_mul(a: Poly, b: Poly) -> Poly:
    out = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return trim(out)


def poly_div_exact(a: Poly, b: Poly) -> Poly:
    """Polynomial long division, rejecting any nonzero remainder."""
    a, b = trim(a), trim(b)
    require(b != (F(0),), "Polynomial division by zero")
    remainder = list(a)
    quotient = [F(0)] * max(1, len(a) - len(b) + 1)
    while len(remainder) >= len(b) and any(remainder):
        degree = len(remainder) - len(b)
        coefficient = remainder[-1] / b[-1]
        quotient[degree] += coefficient
        for j, value in enumerate(b):
            remainder[degree + j] -= coefficient * value
        remainder = list(trim(remainder))
    require(not any(remainder), "Certificate denominator did not divide exactly")
    return trim(quotient)


def shift_by_one(a: Poly) -> Poly:
    """Compute a(y+1), exactly, using the binomial theorem."""
    out = [F(0)] * len(a)
    for degree, coefficient in enumerate(a):
        for j in range(degree + 1):
            out[j] += coefficient * math.comb(degree, j)
    return trim(out)


def exact_polynomial_certificate() -> tuple[int, ...]:
    """Independently derive the positive-coefficient numerator from B(x).

    D(x) is 800*x^2 times the product of the primitive quadratic denominators.
    We compute P(x)=D(x)*(B(x)+1/(800*x^2)) by exact polynomial divisions, and
    then expand P(y+1).  No Lean output or CAS package is used as an oracle.
    """
    quadratics = [trim((16 + j * j, 16 * j, 64)) for j in range(1, 8)]
    primitive_product = trim((1,))
    for q in quadratics:
        divisor = math.gcd(*(int(c) for c in q))
        primitive_product = poly_mul(primitive_product, poly_scale(q, F(1, divisor)))
    denominator = poly_mul(trim((0, 0, 800)), primitive_product)
    numerator = primitive_product  # contribution of 1/(800*x^2)
    for coefficient, q in zip((-16, 40, -16, -16, -16, 40, -16), quadratics):
        numerator = poly_add(
            numerator, poly_scale(poly_div_exact(denominator, q), F(coefficient))
        )
    shifted = shift_by_one(numerator)
    expected = (
        522821915525, 8331458859750, 52359233436594,
        181181572322688, 398348693063104, 600784141988352,
        649893142782464, 517518751432704, 307430271352832,
        136616991522816, 45036234342400, 10755671851008,
        1770063396864, 180388626432, 8589934592,
    )
    require(shifted == tuple(map(F, expected)), "Independent polynomial coefficients disagree")
    require(all(x > 0 and x.denominator == 1 for x in shifted),
            "Expected strictly positive integer coefficients")
    return tuple(int(x) for x in shifted)


def direct_float_gaps(image_radius: int) -> tuple[float, float]:
    """Independent, explicitly approximate symmetric-image calculation."""
    u = tuple(x / 2 for x in UNIFORM)
    x = tuple(p / 2 for p in SHIFTED)

    def soft_terms() -> Iterable[float]:
        for i in range(4):
            for j in range(4):
                for m in range(-image_radius, image_radius + 1):
                    if i == j and m == 0:
                        continue
                    ru = u[j] + 4 * m - u[i]
                    rx = x[j] + 4 * m - x[i]
                    yield SIGNS[i] * SIGNS[j] * (
                        4 / (4 + rx * rx) - 4 / (4 + ru * ru)
                    ) / 4

    def core_terms() -> Iterable[float]:
        for i in range(4):
            for j in range(4):
                for m in range(-image_radius, image_radius + 1):
                    if i == j and m == 0:
                        continue
                    ru = u[j] + 4 * m - u[i]
                    rx = x[j] + 4 * m - x[i]
                    yield (1 / (rx * rx) - 1 / (ru * ru)) / 4

    return math.fsum(soft_terms()), math.fsum(core_terms())


def run_audit(args: argparse.Namespace) -> dict:
    require(args.images >= 1, "--images must be positive")
    require(args.blocks >= 1, "--blocks must be positive")
    require(args.float_images >= 1, "--float-images must be positive")

    expected_signed_u = (0, -8, 0, 8, 0, -8, 0, 8)
    expected_signed_x = (-4, 2, -4, 4, -4, 2, -4, 8)
    expected_unsigned_u = (0, 8, 0, 8, 0, 8, 0, 8)
    expected_unsigned_x = (4, 2, 4, 4, 4, 2, 4, 8)
    counts_u = [shell_counts(UNIFORM, n) for n in range(1, 9)]
    counts_x = [shell_counts(SHIFTED, n) for n in range(1, 9)]
    require(tuple(c[0] for c in counts_u) == expected_signed_u, "Uniform signed counts disagree")
    require(tuple(c[0] for c in counts_x) == expected_signed_x, "Shifted signed counts disagree")
    require(tuple(c[1] for c in counts_u) == expected_unsigned_u, "Uniform unsigned counts disagree")
    require(tuple(c[1] for c in counts_x) == expected_unsigned_x, "Shifted unsigned counts disagree")

    coefficients = [F(x[0] - u[0], 4) for u, x in zip(counts_u, counts_x)]
    core_coefficients = [x[1] - u[1] for u, x in zip(counts_u, counts_x)]
    first_block = cauchy_block(F(0))
    require(first_block == F(23403, 453050), "First block fraction disagrees")
    require(first_block > F(103, 2000), "First-block lower bound failed")
    positive_coefficients = exact_polynomial_certificate()

    # This equality is a finite exact enumeration, not a comparison of two
    # different truncation conventions.  Both sides include exactly |r|<=N/2.
    nmax = 8 * args.blocks
    enough_images = (nmax + 7) // 8 + 1
    u_soft, u_core = direct_exact_components(UNIFORM, enough_images, nmax)
    x_soft, x_core = direct_exact_components(SHIFTED, enough_images, nmax)
    shell_soft, shell_core = shell_exact_gaps(nmax)
    require(u_soft - x_soft == shell_soft, "Exact direct-image and shell soft sums disagree")
    require(x_core - u_core == shell_core, "Exact direct-image and shell core sums disagree")

    # A second truncation, by image index m, is computed independently.
    us, uk = direct_exact_components(UNIFORM, args.images)
    xs, xk = direct_exact_components(SHIFTED, args.images)
    finite_image_soft = us - xs
    finite_image_core = xk - uk

    soft_gap, core_cost = direct_float_gaps(args.float_images)
    reference_core_cost = 9 * math.pi * math.pi / 32

    # These are arithmetic consequences of the infinite-series bounds proved
    # in Lean, NOT claims that a finite Python sum proves those bounds.
    certified_soft_arithmetic = first_block - F(1, 400)
    certified_total_arithmetic = certified_soft_arithmetic - LAMBDA * 16
    require(certified_soft_arithmetic > F(49, 1000), "Margin arithmetic failed")
    require(certified_total_arithmetic > F(33, 1000) > F(1, 32), "Final margin arithmetic failed")

    return {
        "status": "All finite exact arithmetic checks passed; numerical sums are not proofs.",
        "energy_convention": "E=(1/4)*ordered-pair sum; conventional physical energy per particle is E/2.",
        "potential": "V_lambda(r,sigma,tau)=lambda/r^2-sigma*tau*4/(4+r^2)",
        "lambda": str(LAMBDA),
        "uniform_coordinates": [str(F(n, 2)) for n in UNIFORM],
        "shifted_coordinates": [str(F(n, 2)) for n in SHIFTED],
        "signed_gap_coefficients_n_1_to_8": [str(c) for c in coefficients],
        "unsigned_core_cost_coefficients_n_1_to_8": core_coefficients,
        "first_block_exact": str(first_block),
        "first_block_decimal": float(first_block),
        "polynomial_degree": len(positive_coefficients) - 1,
        "positive_polynomial_coefficients_ascending": positive_coefficients,
        "exact_finite_radial_check": {
            "maximum_half_grid_distance": nmax,
            "direct_equals_shells": True,
            "soft_gap": float(shell_soft),
            "core_cost": float(shell_core),
            "total_gap_at_lambda": float(shell_soft - LAMBDA * shell_core),
        },
        "exact_finite_image_check": {
            "image_indices": f"-{args.images}..{args.images}",
            "soft_gap": float(finite_image_soft),
            "core_cost": float(finite_image_core),
            "total_gap_at_lambda": float(finite_image_soft - LAMBDA * finite_image_core),
        },
        "approximate_large_image_sum_NOT_A_PROOF": {
            "image_indices": f"-{args.float_images}..{args.float_images}",
            "soft_gap": soft_gap,
            "core_cost": core_cost,
            "reference_9_pi_squared_over_32": reference_core_cost,
            "core_cost_minus_reference": core_cost - reference_core_cost,
            "total_gap_at_lambda": soft_gap - float(LAMBDA) * core_cost,
        },
        "margin_arithmetic_using_bounds_that_require_the_Lean_proof": {
            "soft_lower_margin": str(certified_soft_arithmetic),
            "soft_lower_margin_decimal": float(certified_soft_arithmetic),
            "total_lower_margin": str(certified_total_arithmetic),
            "total_lower_margin_decimal": float(certified_total_arithmetic),
            "claimed_simple_strict_margin": "1/32",
            "conventional_energy_margin_is_half": "1/64",
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--images", type=int, default=32,
                        help="radius of the exact finite image-index sum (default: 32)")
    parser.add_argument("--blocks", type=int, default=32,
                        help="eight-shell blocks for exact direct/shell equality (default: 32)")
    parser.add_argument("--float-images", type=int, default=10000,
                        help="radius for the explicitly approximate image sum (default: 10000)")
    parser.add_argument("--json", action="store_true", help="print machine-readable JSON")
    args = parser.parse_args()
    report = run_audit(args)
    if args.json:
        print(json.dumps(report, indent=2))
        return
    print(report["status"])
    print(report["energy_convention"])
    print("Potential:", report["potential"])
    print("Soft-gap coefficients n=1..8:", ", ".join(report["signed_gap_coefficients_n_1_to_8"]))
    print("Core-cost coefficients n=1..8:", report["unsigned_core_cost_coefficients_n_1_to_8"])
    print("Exact B_0:", report["first_block_exact"], "=", report["first_block_decimal"])
    print("Polynomial certificate: exact identity checked; all 15 integer coefficients are positive.")
    print("Finite direct-image/shell equality: exact, through half-grid distance", 8 * args.blocks)
    for key in ("exact_finite_image_check", "approximate_large_image_sum_NOT_A_PROOF",
                "margin_arithmetic_using_bounds_that_require_the_Lean_proof"):
        print("\n" + key + ":")
        for name, value in report[key].items():
            print(f"  {name}: {value}")


if __name__ == "__main__":
    main()
