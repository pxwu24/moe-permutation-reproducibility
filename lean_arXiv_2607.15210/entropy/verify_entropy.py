#!/usr/bin/env python3
"""Reproducible numerical and exact-arithmetic checks for Appendix B.

Run: python verify_entropy.py --output python_results.json
Dependency: numpy (the high-precision checks use standard-library Decimal).

Every check has an assertion. Integer/Fraction identities are exact for the
tested parameters. Decimal calculations use 90 significant digits, but are
NOT directed-rounding interval certificates. Finite samples and asymptotic
tables do NOT prove universal bounds, entropy minimization, or asymptotics.
The one-channel tables evaluate the explicit feasible two-spike witness;
they do not purport to compute the minimum over the whole output body.
"""

from __future__ import annotations

import argparse
from decimal import Decimal as D, localcontext
from fractions import Fraction
from itertools import combinations
import json
from math import comb
from pathlib import Path
import platform

import numpy as np


SEED = 260715210
PRECISION = 90
TOL = D("1e-70")


def power(x: D, p: D) -> D:
    assert x > 0
    return (p * x.ln()).exp()


def psi(p: D, y: D) -> D:
    if p == 1:
        return (1 + y) * (1 + y).ln() - y
    return power(1 + y, p) - 1 - p * y


def entropy(p: D, spectrum: list[tuple[int, D]]) -> D:
    assert all(mult > 0 and value > 0 for mult, value in spectrum)
    assert abs(sum(D(mult) * value for mult, value in spectrum) - 1) < TOL
    if p == 1:
        return -sum(D(mult) * value * value.ln() for mult, value in spectrum)
    return sum(D(mult) * power(value, p) for mult, value in spectrum).ln() / (1 - p)


def num(x: D | float) -> str:
    return format(x, ".18g")


def exact_combinatorics() -> dict:
    rng = np.random.default_rng(SEED)
    subset_cases = 0
    for k in range(2, 11):
        e = [int(v) for v in rng.integers(-7, 8, k - 1)]
        e += [-sum(e)]
        for r in range(1, k + 1):
            sums = [sum(e[i] for i in I) for I in combinations(range(k), r)]
            assert sum(sums) == 0
            lhs = sum(x * x for x in sums)
            assert lhs == comb(k - 2, r - 1) * sum(x * x for x in e)
            assert Fraction(lhs, r * r * comb(k, r)) == Fraction(k - r, r * k * (k - 1)) * sum(x * x for x in e)
            assert k * comb(k - 1, r - 1) == r * comb(k, r)
            subset_cases += 1
    trace_cases = 0
    for k in range(2, 61):
        for r in range(1, k // 2 + 1):
            N, M = comb(k - 1, r - 1), comb(k, r) ** 2
            d = [comb(k, m) ** 2 - (comb(k, m - 1) ** 2 if m else 0) for m in range(r + 1)]
            assert min(d) > 0 and sum(d) == M
            assert sum((k - 2 * m) * comb(k, m) ** 2 for m in range(r)) == k * N * N
            assert sum(d[m] * Fraction((r - m) * (k - r - m + 1), k * N * N) for m in range(r + 1)) == 1
            for m in range(r):
                assert (r - 1 - m) * (k - r - m + 2) + k - 2 * r + 2 == (r - m) * (k - r - m + 1)
            trace_cases += 1
    return {"status": "pass", "arithmetic": "exact integers and Fraction", "subset_parameter_pairs": subset_cases, "trace_parameter_pairs": trace_cases}


def local_scalar_checks() -> dict:
    max_rpow_ratio = D(0)
    max_xlog_ratio = D(0)
    max_log_ratio = D(0)
    cases = 0
    ps = [D(s) for s in ("0.05", "0.3", "0.7", "0.99999999", "1.5", "3", "10", "40", "200")]
    for p in ps:
        eta = min(D("0.5"), 1 / (4 * p))
        for j in list(range(-100, 101)):
            if j == 0:
                continue
            for y in (eta * D(j) / 100, D(j) * D("1e-12")):
                err = abs(psi(p, y) - p * (p - 1) / 2 * y * y)
                bound = (8 * p ** 3 + 3 * p ** 2 + 2 * p) * abs(y) ** 3
                assert err <= bound
                max_rpow_ratio = max(max_rpow_ratio, err / bound)
                cases += 1
    for j in range(-100, 101):
        if j == 0:
            continue
        y = D(j) / 200
        r1 = abs(psi(D(1), y) - y * y / 2) / (4 * abs(y) ** 3)
        r2 = abs((1 + y).ln() - y) / (2 * y * y)
        assert r1 <= 1 and r2 <= 1
        max_xlog_ratio, max_log_ratio = max(max_xlog_ratio, r1), max(max_log_ratio, r2)
    # Exact entropy expansion, evaluated independently from a spectrum.
    identity_error = D(0)
    multiplicities, ys = [1, 2, 4], [D("0.3"), D("-0.2"), D("0.025")]
    assert sum(D(d) * y for d, y in zip(multiplicities, ys)) == 0
    M = sum(multiplicities)
    for p in ps + [D(1)]:
        X = sum(D(d) * psi(p, y) for d, y in zip(multiplicities, ys)) / M
        F = -X if p == 1 else (1 + X).ln() / (1 - p)
        actual = entropy(p, [(d, (1 + y) / M) for d, y in zip(multiplicities, ys)])
        err = abs(actual - D(M).ln() - F)
        assert err < TOL
        identity_error = max(identity_error, err)
    return {"status": "pass", "precision_digits": PRECISION, "rpow_samples": cases,
            "max_rpow_bound_ratio": num(max_rpow_ratio), "max_xlogx_bound_ratio": num(max_xlog_ratio),
            "max_log_bound_ratio": num(max_log_ratio), "entropy_identity_max_error": num(identity_error)}


def cost(t, u):
    return (np.sqrt(t * (1 - u)) - np.sqrt((1 - t) * u)) ** 2


def sampled_localization() -> dict:
    rng = np.random.default_rng(SEED)
    t, u = rng.uniform(0, 1, (2, 20000))
    c = cost(t, u)
    rhs = np.sqrt(c) * (2 * np.sqrt(t * (1 - t)) + np.sqrt(2 * c))
    violation = float(np.max(np.abs(u - t) - rhs))
    assert violation <= 5e-15
    feasible_cases, max_variance_ratio = 0, 0.0
    for t in (0.01, 0.1, 0.3, 0.5, 0.8, 0.99):
        for k in (int(np.ceil(8 / t)), int(np.ceil(16 / t))):
            for _ in range(12):
                # On [0,pi/2], cost(sin(theta)^2,sin(theta+delta)^2)=sin(delta)^2.
                theta = np.arcsin(np.sqrt(t))
                v = rng.normal(size=k)
                v /= np.linalg.norm(v)
                scale = min(1 / np.sqrt(k), 0.9 * min(theta, np.pi / 2 - theta) / np.max(np.abs(v)))
                u = np.sin(theta + rng.uniform(0.2, 1) * scale * v) ** 2
                c = cost(t, u)
                assert c.sum() <= 1 / k + 2e-14
                w = u - t
                assert np.max(np.abs(w)) <= 2 / np.sqrt(k) + 2e-14
                w_bound = (2 * np.sqrt(t * (1 - t)) + np.sqrt(2 / k)) ** 2 / k
                assert w @ w <= w_bound + 2e-14
                eps = k * u / u.sum() - 1
                bound = w_bound / (t - 2 / k) ** 2
                assert eps @ eps <= bound + 2e-11
                max_variance_ratio = max(max_variance_ratio, float((eps @ eps) / bound))
                feasible_cases += 1
    return {"status": "pass", "scalar_samples": 20000, "maximum_signed_scalar_violation": violation,
            "feasible_body_samples": feasible_cases, "max_explicit_variance_bound_ratio": max_variance_ratio,
            "scope": "floating-point sample checks; no universal bound or minimizer claim"}


def two_spike(k: int, t: D) -> tuple[D, D]:
    s2 = 1 / D(2 * k)
    assert s2 <= min(t, 1 - t)
    a, b, c, s = t.sqrt(), (1 - t).sqrt(), (1 - s2).sqrt(), s2.sqrt()
    up, um = (a * c + b * s) ** 2, (a * c - b * s) ** 2
    for u in (up, um):
        assert 0 <= u <= 1
        ct = ((t * (1 - u)).sqrt() - ((1 - t) * u).sqrt()) ** 2
        assert abs(ct - s2) < TOL
    mean = (up + um + (k - 2) * t) / k
    eps2 = (up / mean - 1) ** 2 + (um / mean - 1) ** 2 + (k - 2) * (t / mean - 1) ** 2
    gamma = (1 - t) / t
    assert eps2 >= 4 * gamma / k - 14 / (t ** 4 * k ** 2)
    return up, um


def single_witness_spectrum(k: int, r: int, t: D) -> list[tuple[int, D]]:
    up, um = two_spike(k, t)
    total = up + um + (k - 2) * t
    N = comb(k - 1, r - 1)
    spectrum = []
    # Group subsets by whether they contain each of the two exceptional entries.
    for contains_plus in (0, 1):
        for contains_minus in (0, 1):
            ordinary = r - contains_plus - contains_minus
            if not 0 <= ordinary <= k - 2:
                continue
            multiplicity = comb(k - 2, ordinary)
            value = (contains_plus * up + contains_minus * um + ordinary * t) / (N * total)
            spectrum.append((multiplicity, value))
    assert sum(d for d, _ in spectrum) == comb(k, r)
    return spectrum


def bell_spectrum(k: int, r: int, t: D) -> list[tuple[int, D]]:
    rho = D(k * k) * (1 - t) / (k ** 4 * t - 2 * k * k * t + 1)
    assert k * k * t > 1 and 0 < rho < 1
    N, dim = comb(k - 1, r - 1), comb(k, r)
    return [(comb(k, m) ** 2 - (comb(k, m - 1) ** 2 if m else 0),
             rho * D((r - m) * (k - r - m + 1)) / (k * N * N) + (1 - rho) / (dim * dim)) for m in range(r + 1)]


def coefficient(p: D, r: int, t: D) -> D:
    gamma = (1 - t) / t
    x = gamma / (r * r)
    if p == 1:
        return (r * r + gamma) * (1 + x).ln() - gamma
    return (r * r * (power(1 + x, p) - 1) - p * gamma) / (p - 1)


def asymptotic_checks() -> dict:
    records = []
    ks = [100, 200, 400, 800, 1600]
    for t in map(D, ("0.2", "0.5", "0.8")):
        for p in map(D, ("0.3", "1", "2", "5")):
            for r in (1, 2, 3):
                gamma, b = (1 - t) / t, coefficient(p, r, t)
                single_leading = 2 * p * gamma / r
                samples = []
                single_errors, bell_errors = [], []
                for k in ks:
                    logdim = D(comb(k, r)).ln()
                    s1 = entropy(p, single_witness_spectrum(k, r, t))
                    sb = entropy(p, bell_spectrum(k, r, t))
                    residual1 = s1 - logdim + single_leading / (k * k)
                    residualb = sb - 2 * logdim + b / (k * k)
                    single_errors.append(abs(residual1 * k * k))
                    bell_errors.append(abs(residualb * k * k))
                    samples.append({"k": k, "single_witness_k2_deficit": num((logdim - s1) * k * k),
                                    "single_witness_k5over2_residual": num(residual1 * D(k * k) * D(k).sqrt()),
                                    "bell_k2_deficit": num((2 * logdim - sb) * k * k),
                                    "bell_scaled_residual": num(residualb * k ** (4 if r == 1 else 3))})
                # Finite regression tests for approach to the proposed leading constants.
                # These empirical inequalities are deliberately NOT asymptotic proofs.
                assert single_errors[-1] <= D("0.02") * max(1, abs(single_leading))
                assert bell_errors[-1] <= D("0.02") * max(1, abs(b))
                assert single_errors[-1] < single_errors[0]
                assert bell_errors[-1] < bell_errors[0]
                records.append({"t": str(t), "p": str(p), "r": r,
                                "single_leading_coefficient": num(single_leading), "bell_leading_coefficient": num(b),
                                "bell_remainder_scaling": "k^4" if r == 1 else "k^3", "samples": samples})
    return {"status": "pass", "parameter_triples": len(records), "precision_digits": PRECISION,
            "scope": "sampled asymptotic consistency; the single-output spectrum is a feasible witness, not a computed global minimum", "records": records}


def annihilators(k: int, m: int) -> list[np.ndarray]:
    upper, lower = list(combinations(range(k), m)), list(combinations(range(k), m - 1))
    index = {I: i for i, I in enumerate(lower)}
    maps = [np.zeros((len(lower), len(upper))) for _ in range(k)]
    for col, I in enumerate(upper):
        for pos, a in enumerate(I):
            maps[a][index[I[:pos] + I[pos + 1:]], col] = (-1) ** pos
    return maps


def exterior_matrix_checks() -> dict:
    rng = np.random.default_rng(SEED)
    rows = []
    for k, r in ((2, 1), (4, 2), (5, 2), (6, 3)):
        dim, N = comb(k, r), comb(k - 1, r - 1)
        a = annihilators(k, r)
        # Kraus operators a_j/sqrt(r) implement the ordinary one-particle partial trace.
        R = sum(np.kron(v, v) for v in a) / r
        G, H = R.T @ R, R @ R.T
        L = [[a[i].T @ a[j] for j in range(k)] for i in range(k)]
        twirl = sum(np.kron(L[i][j], L[i][j]) for i in range(k) for j in range(k))
        twirl_error = float(np.max(np.abs(twirl - r * r * G)))
        assert twirl_error < 2e-12
        if r == 1:
            lift_error = float(np.max(np.abs(H - k)))
        else:
            prev_a = annihilators(k, r - 1)
            prev_R = sum(np.kron(v, v) for v in prev_a) / (r - 1)
            prev_G = prev_R.T @ prev_R
            target_H = ((k - 2 * r + 2) * np.eye(H.shape[0]) + (r - 1) ** 2 * prev_G) / (r * r)
            lift_error = float(np.max(np.abs(H - target_H)))
        assert lift_error < 2e-12
        # W is built directly from (E tensor conjugate(E))(Bell), using E(E_ab)=L_ab/N.
        W = twirl / (k * N * N)
        eigenvalues = np.linalg.eigvalsh(W)
        expected = np.sort(np.concatenate([np.full(comb(k, m) ** 2 - (comb(k, m - 1) ** 2 if m else 0),
                                                   (r - m) * (k - r - m + 1) / (k * N * N)) for m in range(r + 1)]))
        spectrum_error = float(np.max(np.abs(eigenvalues - expected)))
        assert spectrum_error < 2e-12
        assert abs(np.trace(W) - 1) < 2e-12 and eigenvalues.min() > -2e-12
        # Verify the shuffled spectrum without assuming rho diagonal.
        v = rng.normal(size=(k, k)) + 1j * rng.normal(size=(k, k))
        rho = v @ v.conj().T
        rho /= np.trace(rho)
        out = sum(rho[i, j] * L[i][j] for i in range(k) for j in range(k)) / N
        lam = np.linalg.eigvalsh(rho)
        shuffled = np.sort([sum(lam[i] for i in I) / N for I in combinations(range(k), r)])
        shuffle_error = float(np.max(np.abs(np.linalg.eigvalsh(out) - shuffled)))
        assert shuffle_error < 2e-12
        rows.append({"k": k, "r": r, "operator_dimension": dim, "W_dimension": dim * dim,
                     "twirl_max_entry_error": twirl_error, "lift_reduce_max_entry_error": lift_error,
                     "W_spectrum_max_error": spectrum_error, "shuffled_spectrum_max_error": shuffle_error})
    return {"status": "pass", "scope": "independent finite matrix checks in the exterior-power basis", "cases": rows}


def main() -> None:
    if not __debug__:
        raise RuntimeError("Run without -O: assertions are required for verification.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("python_results.json"))
    args = parser.parse_args()
    results = {"status": "running", "python": platform.python_version(), "numpy": np.__version__, "seed": SEED,
               "limitations": ["Finite numerical tests do not establish universal theorems.",
                               "Decimal arithmetic is high precision, not a rigorous interval enclosure.",
                               "The explicit one-channel witness is not a global entropy minimizer certification."]}
    with localcontext() as ctx:
        ctx.prec = PRECISION
        for name, check in (("exact_combinatorics", exact_combinatorics), ("local_scalar_checks", local_scalar_checks),
                            ("sampled_localization", sampled_localization), ("exterior_matrix_checks", exterior_matrix_checks),
                            ("asymptotic_checks", asymptotic_checks)):
            results[name] = check()
            print(f"{name}: PASS", flush=True)
    results["status"] = "pass"
    args.output.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(f"Saved {args.output}")


if __name__ == "__main__":
    main()
