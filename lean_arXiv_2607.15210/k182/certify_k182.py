#!/usr/bin/env python3
"""Rigorous numerical certificate for a Bell-witness violation at k = 182.

Install: python -m pip install python-flint==0.9.0
Run:     python certify_k182.py

All numerical proof steps use Arb real-ball arithmetic. Decimal output is
for readability only; inequalities are checked before rounding for display.
No optimizer, sampling, binary float input, or conjectured minimizer is used.

The analytic entropy-minimizer reduction and scalar dual bound are proved
in k182_revision.tex. Together with the output-set and Bell-limit theorems
in the manuscript, this certifies k_high(1) <= 182, NOT equality.
This is a rigorous numerical certificate, not a Lean proof.
"""

import argparse
import sys

try:
    import flint
    from flint import arb, ctx
except ImportError:
    sys.exit("Install the dependency: python -m pip install python-flint==0.9.0")


def require(condition, description):
    """Fail closed: an indeterminate ball comparison also causes failure."""
    if not condition:
        raise ArithmeticError("NOT CERTIFIED: " + description)


def rational(numerator, denominator=1):
    return arb(numerator) / arb(denominator)


def certify(precision=256):
    if precision < 64:
        raise ValueError("Use at least 64 bits of precision.")
    ctx.prec = precision

    # Exact rational mathematical inputs; Arb encloses every division.
    k = 182
    t = rational(27, 100000)
    L = rational(162513, 1000000)
    z = rational(2077, 2000)
    one = arb(1)

    # Hypotheses for the output limit and the entropy-minimizer lemma.
    require(t > rational(1, k * k), "t > 1/k^2")
    require(t > rational(1, k * (k - 1)), "t > 1/[k(k-1)]")
    require(t < one - rational(1, k), "t < 1-1/k")
    require(z > 0, "positive dual multiplier")
    require(L > rational(1, k), "L > 1/k")
    require(L < one, "L < 1")

    U = ((t * (one - rational(1, k))).sqrt()
         + ((one - t) / k).sqrt()) ** 2
    require(U < rational(1, 4), "every unnormalized coordinate is below 1/4")

    # Exact scalar maximization identity:
    # max_{0<=v<=1} [a*v-z*c_t(v)]
    #       = (a-z + sqrt(a^2-2*a*z*(1-2*t)+z^2))/2.
    def scalar_dual(a):
        radicand = (a - z) ** 2 + 4 * t * a * z
        require(radicand > 0, "positive scalar-dual radicand")
        return (a - z + radicand.sqrt()) / 2

    dual_bound = z / k + scalar_dual(one - L) + (k - 1) * scalar_dual(-L)
    require(dual_bound < 0, "global eigenvalue bound lambda_max <= L")

    # By the analytic reduction, an entropy minimizer has spectrum
    # (x, (1-x)/(k-1), ..., (1-x)/(k-1)), with 1/k < x <= L.
    # Its entropy decreases in x, giving a GLOBAL lower bound.
    entropy_lower = -L * L.log() - (one - L) * ((one - L) / (k - 1)).log()

    # Exact limiting Bell-output eigenvalues from the manuscript.
    m = k * k
    denominator = (m - 1) ** 2 * t + one - t
    require(denominator > 0, "positive Bell coefficient denominator")
    r = m * (one - t) / denominator
    require(r > 0, "r > 0")
    require(r < one, "r < 1")
    alpha = (one + (m - 1) * r) / m
    beta = (one - r) / m
    require(alpha > 0, "alpha > 0")
    require(beta > 0, "beta > 0")
    bell_entropy = -alpha * alpha.log() - (m - 1) * beta * beta.log()

    # The actual entropy gap is AT LEAST this certified scalar quantity.
    gap_lower = 2 * entropy_lower - bell_entropy
    require(gap_lower > rational(477, 1000000), "gap lower bound > 0.000477 nats")

    # Check the outward decimal enclosures quoted in the LaTeX proof.
    require(dual_bound > rational(-1660, 100000000000), "dual > -1.660e-8")
    require(dual_bound < rational(-1659, 100000000000), "dual < -1.659e-8")
    require(entropy_lower > rational(479748729461169, 100000000000000),
            "entropy lower bound > 4.79748729461169")
    require(entropy_lower < rational(479748729461170, 100000000000000),
            "entropy lower bound < 4.79748729461170")
    require(bell_entropy > rational(959449702812108, 100000000000000),
            "Bell entropy > 9.59449702812108")
    require(bell_entropy < rational(959449702812109, 100000000000000),
            "Bell entropy < 9.59449702812109")

    print(f"python-flint {flint.__version__}; Arb precision {ctx.prec} bits")
    print("Exact inputs: k=182, t=27/100000, L=162513/1000000, z=2077/2000")
    for name, value in (
        ("Coordinate upper bound U", U),
        ("Scalar dual upper bound", dual_bound),
        ("Global single-output entropy lower bound", entropy_lower),
        ("Limiting Bell entropy", bell_entropy),
        ("Lower bound on the entropy gap", gap_lower),
    ):
        print(f"{name}: {value.str(35)}")
    print("CERTIFIED: 2 min_{K_182,t} S_1 - S_1(Bell_182,t) > 0.000477 nats.")
    print("CONCLUSION: k_high(1) <= 182, using the manuscript's limit theorems.")
    print("No exclusion of dimensions 2,...,181 is claimed.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prec", type=int, default=256, help="Arb precision in bits (default: 256)")
    args = parser.parse_args()
    certify(args.prec)
