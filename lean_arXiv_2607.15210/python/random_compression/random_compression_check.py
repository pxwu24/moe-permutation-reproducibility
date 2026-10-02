#!/usr/bin/env python3
"""Reproducible checks of the random-compression variational formula.

The arbitrary-sign Legendre identity and convex duality are proved in Lean.
These high-precision checks exercise their formulas, including the boundary
case whose infimum is attained only at infinity. The Haar matrix experiment
is a finite-size sanity check, not a proof of an almost-sure limiting theorem.
No numerical optimization is used to assert a global spectral-edge theorem.
"""
import argparse
import json
import os
from pathlib import Path

os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
import mpmath as mp
import numpy as np

mp.mp.dps = 85


def cost(t, u):
    return (mp.sqrt(t * (1 - u)) - mp.sqrt((1 - t) * u)) ** 2


def delta(t, y):
    return mp.sqrt((y + 2 * t - 1) ** 2 + 4 * t * (1 - t))


def dual(t, y):
    return (y - 1 + delta(t, y)) / 2


def maximizer(t, y):
    return (1 + (y + 2 * t - 1) / delta(t, y)) / 2


def profile(t, a, w):
    k = len(a)
    return mp.fsum(cost(t, maximizer(t, ai * w / k)) for ai in a)


def inverse_branch(t, a, w):
    k = len(a)
    return (1 + k * mp.fsum(dual(t, ai * w / k) for ai in a)) / w


def support_data(t, a):
    """Evaluate the dual and a matching feasible witness, with all signs."""
    k = len(a)
    endpoint = [mp.mpf(1) if ai > 0 else mp.mpf(0) if ai < 0 else t for ai in a]
    budget = mp.fsum(cost(t, u) for u in endpoint)
    threshold = mp.mpf(1) / k
    if budget <= threshold:
        return {
            "regime": "infinite_parameter",
            "edge": mp.fsum(max(ai, 0) for ai in a),
            "u": endpoint,
            "w": None,
            "endpoint_budget": budget,
        }
    lo, hi = mp.mpf(0), mp.mpf(1)
    while profile(t, a, hi) < threshold:
        hi *= 2
    for _ in range(270):
        mid = (lo + hi) / 2
        if profile(t, a, mid) < threshold:
            lo = mid
        else:
            hi = mid
    w = (lo + hi) / 2
    u = [maximizer(t, ai * w / k) for ai in a]
    return {
        "regime": "finite_critical_parameter",
        "edge": inverse_branch(t, a, w),
        "u": u,
        "w": w,
        "endpoint_budget": budget,
    }


def check_scalar_formulas():
    rng = np.random.default_rng(260715210)
    maximum_error = mp.mpf(0)
    count = 0
    for t in map(mp.mpf, [".01", ".2", ".5", ".9", ".99"]):
        for y in map(mp.mpf, ["-100", "-3", "-.2", "0", ".8", "4", "100"]):
            u = maximizer(t, y)
            assert 0 < u < 1
            residual = abs(y * u - cost(t, u) - dual(t, y))
            maximum_error = max(maximum_error, residual)
            assert residual < mp.mpf("1e-78")
            for v in map(mp.mpf, ["0", ".0001", ".2", ".5", ".9", "1"]):
                assert y * v - cost(t, v) <= dual(t, y) + mp.mpf("1e-78")
                count += 1
    cases = []
    regimes = {"finite_critical_parameter": 0, "infinite_parameter": 0}
    for k in range(1, 7):
        for t in map(mp.mpf, [".01", ".2", ".5", ".9", ".99"]):
            coefficient_lists = [[mp.mpf(0)] * k, [mp.mpf(1)] * k,
                                 [mp.mpf(-1)] * k,
                                 [mp.mpf(1)] + [mp.mpf(0)] * (k - 1)]
            coefficient_lists += [list(map(lambda x: mp.mpf(str(x)),
                                          rng.uniform(-2, 2, k))) for _ in range(3)]
            for a in coefficient_lists:
                data = support_data(t, a)
                u, edge, w = data["u"], data["edge"], data["w"]
                regimes[data["regime"]] += 1
                primal = mp.fsum(ai * ui for ai, ui in zip(a, u))
                constraint = mp.fsum(cost(t, ui) for ui in u)
                assert all(0 <= ui <= 1 for ui in u)
                assert constraint <= mp.mpf(1) / k + mp.mpf("1e-70")
                assert abs(primal - edge) < mp.mpf("1e-70")
                for parameter in map(mp.mpf, [".01", ".2", "1", "10", "10000"]):
                    assert edge <= inverse_branch(t, a, parameter) + mp.mpf("1e-70")
                if w is not None:
                    derivative = mp.diff(lambda v: inverse_branch(t, a, v), w)
                    assert abs(derivative) < mp.mpf("1e-69")
                    assert abs(constraint - mp.mpf(1) / k) < mp.mpf("1e-70")
                cases.append({"k": k, "t": str(t), "regime": data["regime"]})
    # At this equality threshold there is no finite stationary point.
    boundary = support_data(mp.mpf(".5"), [mp.mpf(1), mp.mpf(0)])
    assert boundary["regime"] == "infinite_parameter"
    assert boundary["endpoint_budget"] == mp.mpf(".5")
    assert boundary["edge"] == 1
    return {"legendre_inequalities": count,
            "maximum_legendre_equality_error": str(maximum_error),
            "duality_cases": len(cases), "regimes": regimes,
            "equality_threshold_case": "passed"}


def haar_experiment():
    rng = np.random.default_rng(260715210)
    rows = []
    for a, t in [([1., -.8], .3), ([1., .1, -.7], .4)]:
        k = len(a)
        edge = float(support_data(mp.mpf(str(t)), list(map(lambda x: mp.mpf(str(x)), a)))["edge"])
        for n in [24, 72, 160]:
            d = round(t * n * k)
            g = rng.standard_normal((n * k, d)) + 1j * rng.standard_normal((n * k, d))
            q, _ = np.linalg.qr(g, mode="reduced")
            blocks = [q[i::k, :] for i in range(k)]
            s = sum(ai * (block @ block.conj().T) for ai, block in zip(a, blocks))
            top = float(np.linalg.eigvalsh(s)[-1])
            assert np.max(np.abs(s - s.conj().T)) < 1e-12
            assert sum(min(ai, 0) for ai in a) - 1e-12 <= top
            assert top <= sum(max(ai, 0) for ai in a) + 1e-12
            rows.append({"k": k, "n": n, "rank": d, "t": t,
                         "a": a, "largest_eigenvalue": top,
                         "limiting_formula": edge, "finite_size_error": top - edge})
    return rows


def main():
    if not __debug__:
        raise RuntimeError("Run without -O: assertions are part of verification.")
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path("random_compression_results.json"))
    parser.add_argument("--skip-haar", action="store_true")
    args = parser.parse_args()
    result = {"status": "passed", "precision_decimal_digits": mp.mp.dps,
              "scope": "Numerical checks; not a proof of the random matrix limit.",
              "scalar": check_scalar_formulas(),
              "haar_finite_size_experiments": [] if args.skip_haar else haar_experiment()}
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
