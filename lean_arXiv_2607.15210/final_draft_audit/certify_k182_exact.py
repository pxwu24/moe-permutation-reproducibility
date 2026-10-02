#!/usr/bin/env python3
"""Exact-rational interval certificate for the paper's k=182 witness.

Python 3.10+ standard library only. No floating-point arithmetic, optimizer,
sampling, or disabled-by-``python -O`` assertions enter the certificate.

Square roots are enclosed by integer square roots on a rational decimal grid.
Logarithms use log(x)=m*log(2)+2*atanh(z), 1<=x/2**m<2 and
0<=z<1/3, with an explicit positive geometric-series remainder.

The numerical certificate uses the paper's analytically proved one-high
entropy-minimizer lemma and its random-matrix limit theorems. It certifies
k_high(1)<=182, not minimality or an explicit finite input dimension.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction as F
from math import isqrt
import json
from pathlib import Path


def require(condition: bool, description: str) -> None:
    if not condition:
        raise ArithmeticError("NOT CERTIFIED: " + description)


@dataclass(frozen=True)
class Interval:
    lo: F
    hi: F

    def __post_init__(self) -> None:
        require(self.lo <= self.hi, "ordered interval endpoints")

    @staticmethod
    def point(value: int | F) -> Interval:
        return Interval(F(value), F(value))

    def __add__(self, other: Interval | int | F) -> Interval:
        other = as_interval(other)
        return Interval(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self) -> Interval:
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other: Interval | int | F) -> Interval:
        return self + (-as_interval(other))

    def __rsub__(self, other: Interval | int | F) -> Interval:
        return as_interval(other) - self

    def __mul__(self, other: Interval | int | F) -> Interval:
        other = as_interval(other)
        endpoints = [a * b for a in (self.lo, self.hi)
                     for b in (other.lo, other.hi)]
        return Interval(min(endpoints), max(endpoints))

    __rmul__ = __mul__

    def reciprocal(self) -> Interval:
        require(self.hi < 0 or self.lo > 0, "division interval excludes zero")
        return Interval(1 / self.hi, 1 / self.lo)

    def __truediv__(self, other: Interval | int | F) -> Interval:
        return self * as_interval(other).reciprocal()

    def __rtruediv__(self, other: Interval | int | F) -> Interval:
        return as_interval(other) / self

    def square(self) -> Interval:
        if self.lo >= 0:
            return Interval(self.lo**2, self.hi**2)
        if self.hi <= 0:
            return Interval(self.hi**2, self.lo**2)
        return Interval(F(0), max(self.lo**2, self.hi**2))


def as_interval(value: Interval | int | F) -> Interval:
    return value if isinstance(value, Interval) else Interval.point(value)


def sqrt_point(x: F, digits: int) -> Interval:
    require(x >= 0, "nonnegative square-root argument")
    scale = 10**digits
    a = isqrt((x.numerator * scale**2) // x.denominator)
    lo = F(a, scale)
    hi = lo if lo**2 == x else F(a + 1, scale)
    require(lo >= 0 and lo**2 <= x <= hi**2, "square-root enclosure")
    return Interval(lo, hi)


def sqrt_interval(x: Interval, digits: int) -> Interval:
    return Interval(sqrt_point(x.lo, digits).lo, sqrt_point(x.hi, digits).hi)


def atanh_series(z: F, terms: int) -> Interval:
    require(0 <= z <= F(1, 3), "atanh series range")
    partial = 2 * sum((z ** (2*j+1) / (2*j+1) for j in range(terms)), F(0))
    remainder = 2 * z ** (2*terms+1) / ((2*terms+1) * (1-z*z))
    return Interval(partial, partial + remainder)


def log_point(x: F, terms: int) -> Interval:
    require(x > 0, "positive logarithm argument")
    m, reduced = 0, x
    while reduced >= 2:
        reduced /= 2
        m += 1
    while reduced < 1:
        reduced *= 2
        m -= 1
    z = (reduced-1) / (reduced+1)
    return m * atanh_series(F(1, 3), terms) + atanh_series(z, terms)


def log_interval(x: Interval, terms: int) -> Interval:
    return Interval(log_point(x.lo, terms).lo, log_point(x.hi, terms).hi)


def decimal_endpoint(x: F, places: int, upper: bool) -> str:
    scale = 10**places
    a = -((-x.numerator * scale) // x.denominator) if upper else (
        x.numerator * scale // x.denominator)
    sign = "-" if a < 0 else ""
    a = abs(a)
    return f"{sign}{a // scale}.{a % scale:0{places}d}"


def display(x: Interval, places: int = 26) -> list[str]:
    return [decimal_endpoint(x.lo, places, False),
            decimal_endpoint(x.hi, places, True)]


def certify(terms: int = 48, sqrt_digits: int = 70) -> dict:
    require(terms >= 20 and sqrt_digits >= 30, "sufficient precision parameters")
    k = 182
    t, L, z = F(27, 100000), F(162513, 1000000), F(2077, 2000)
    checks: list[str] = []

    def check(ok: bool, name: str) -> None:
        require(ok, name)
        checks.append(name)

    check(F(1, k*(k-1)) < t < 1-F(1, k), "minimizer lemma: t range")
    check(t > F(1, k*k), "random-channel limit: t>1/k^2")
    check(F(1, k) < L < 1 and z > 0, "scalar dual: L and z ranges")
    ubar = (sqrt_point(t*(1-F(1, k)), sqrt_digits)
            + sqrt_point((1-t)/k, sqrt_digits)).square()
    check(ubar.hi < F(1, 4), "minimizer lemma: coordinate bound<1/4")

    def q(a: F) -> Interval:
        return (a-z + sqrt_point(a*a-2*a*z*(1-2*t)+z*z, sqrt_digits)) / 2

    dual = z/k + q(1-L) + (k-1)*q(-L)
    check(dual.hi < 0, "global scalar dual is negative")
    h = -L*log_point(L, terms) - (1-L)*log_point((1-L)/(k-1), terms)
    m = k*k
    den = m*m*t - 2*m*t + 1
    alpha = (m*m-(1+t)*m+1)/(m*den)
    beta = (m-1)*(m*t-1)/(m*den)
    check(den > 0 and alpha > 0 and beta > 0, "Bell coefficients are positive")
    check(alpha+(m-1)*beta == 1, "Bell trace is exactly one")
    bell = -alpha*log_point(alpha, terms) - (m-1)*beta*log_point(beta, terms)
    gap = 2*h-bell
    check(F("-1.660e-8") < dual.lo and dual.hi < F("-1.659e-8"),
          "exact decimal enclosure of scalar dual")
    check(F("4.79748729461169") < h.lo and h.hi < F("4.79748729461170"),
          "exact decimal enclosure of one-copy entropy lower bound")
    check(F("9.59449702812108") < bell.lo and bell.hi < F("9.59449702812109"),
          "exact decimal enclosure of Bell entropy")
    check(gap.lo > F(477, 1000000), "gap>477/1000000")
    return {
        "status": "certified",
        "arithmetic": "exact rational interval endpoints; no floats",
        "inputs": {"k": k, "t": str(t), "L": str(L), "z": str(z)},
        "parameters": {"log_series_terms": terms, "sqrt_grid_digits": sqrt_digits},
        "outward_decimal_enclosures": {name: display(value) for name, value in [
            ("ubar", ubar), ("dual", dual), ("one_copy_lower", h),
            ("bell_entropy", bell), ("gap_lower_bound", gap)]},
        "checks": checks,
        "analytic_dependencies": [
            "one-high entropy-minimizer reduction",
            "scalar dual upper bound for every feasible eigenvalue",
            "output-set and Bell-output limits to infer finite channel violation"],
        "conclusion": "k_high(1)<=182; minimality and an explicit finite n are not certified",
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--terms", type=int, default=48)
    parser.add_argument("--sqrt-digits", type=int, default=70)
    parser.add_argument("--json", type=Path)
    args = parser.parse_args()
    result = certify(args.terms, args.sqrt_digits)
    rendered = json.dumps(result, indent=2)
    if args.json:
        args.json.write_text(rendered+"\n")
    print(rendered)
