"""Reproduce the central numerical values in the finite-size estimates.

This script checks, at high floating-point precision,

1. the unconditional Fannes--Audenaert (AF) certificate; and
2. the sharper, conditional three-level local-branch (NA) calculation.

The NA calculation is a reproducibility/sanity check only.  It does not
provide the outward-rounded verification of every stationary, boundary, and
order-equality branch that would be required to make the sharper NA result
unconditional.

Dependency: mpmath==1.3.0
Run with:   python reproduce_numerics.py
"""

from __future__ import annotations

from fractions import Fraction

import mpmath as mp


mp.mp.dps = 100

# Parameters used in the paper.
k = 195
m = 39
q = 5
ell = 197
t = mp.mpf(q) / m

s = k**2 * m**2
r0 = k**2 * q * m * ell
d0 = k**2 - 1

# Common integer upper bounds in the explicit size estimate.
PI_R0_OVER_3_UPPER = 1_529_673_402
THETA_D0_UPPER = 680_695
LOG_S_FACTOR_UPPER = 151


def as_mpf(value: Fraction) -> mp.mpf:
    """Convert an exact rational number to an mp.mpf at the working precision."""

    return mp.mpf(value.numerator) / value.denominator


def entropy(values: tuple[mp.mpf, ...]) -> mp.mpf:
    """Von Neumann/Shannon entropy of a probability vector (natural logs)."""

    return -mp.fsum(x * mp.log(x) for x in values if x != 0)


def binary_entropy(T: mp.mpf) -> mp.mpf:
    return -T * mp.log(T) - (1 - T) * mp.log(1 - T)


def show(name: str, value: mp.mpf) -> None:
    print(f"{name} = {mp.nstr(value, 60)}")


def scientific_mantissa(log10_value: mp.mpf) -> mp.mpf:
    return mp.power(10, log10_value - mp.floor(log10_value))


def log10_pre_ceiling_bound(
    ratio_numerator: int,
    ratio_denominator: int,
    tail_factor: int,
) -> mp.mpf:
    """Logarithm of the displayed product P before N = 1 + ceil(P)."""

    return (
        mp.log10(mp.mpf(PI_R0_OVER_3_UPPER))
        + mp.log10(mp.mpf(THETA_D0_UPPER))
        + d0
        * mp.log10(mp.mpf(ratio_numerator) / ratio_denominator)
        + 8 * mp.log10(mp.mpf(LOG_S_FACTOR_UPPER))
        + 9 * mp.log10(mp.mpf(tail_factor))
    )


# ---------------------------------------------------------------------------
# Bell-output entropy, common to both estimates.
# ---------------------------------------------------------------------------

alpha = t + (1 - t) / k**2
beta_iso = (1 - t) / k**2
H_bell = -alpha * mp.log(alpha) - (k**2 - 1) * beta_iso * mp.log(beta_iso)


# ---------------------------------------------------------------------------
# Unconditional Fannes--Audenaert certificate.
# ---------------------------------------------------------------------------

T_AF_Q = Fraction(3, 12_500)
ETA_AF_Q = Fraction(11_997, 50_000_000)
BETA_AF_Q = Fraction(3, 25_000_000)
assert ETA_AF_Q + BETA_AF_Q / 2 == T_AF_Q

T_AF = as_mpf(T_AF_Q)
eta_AF = as_mpf(ETA_AF_Q)
beta_AF = as_mpf(BETA_AF_Q)

a = (
    mp.sqrt(1 - t) + mp.sqrt((k - 1) * t)
) ** 2 / k
b = (1 - a) / (k - 1)
H_star = -a * mp.log(a) - (k - 1) * b * mp.log(b)

Omega_AF = binary_entropy(T_AF) + T_AF * mp.log(k - 1)
Delta = 2 * H_star - H_bell
margin_AF = Delta - 2 * Omega_AF

AF_RATIO_NUMERATOR = 50_011_997
AF_RATIO_DENOMINATOR = 11_997
AF_TAIL_FACTOR = 2_500_599_850

assert Fraction(1, 1) + 1 / ETA_AF_Q == Fraction(
    AF_RATIO_NUMERATOR, AF_RATIO_DENOMINATOR
)
assert 300 * (1 + ETA_AF_Q) / BETA_AF_Q == AF_TAIL_FACTOR

log10_pre_ceiling_N_AF = log10_pre_ceiling_bound(
    AF_RATIO_NUMERATOR,
    AF_RATIO_DENOMINATOR,
    AF_TAIL_FACTOR,
)
log10_pre_ceiling_input_AF = log10_pre_ceiling_N_AF + mp.log10(r0)


# ---------------------------------------------------------------------------
# Conditional three-level local-branch refinement.
# ---------------------------------------------------------------------------

T_NA_Q = Fraction(44_259, 50_000_000)
ETA_NA_Q = Fraction(88_497, 100_000_000)
BETA_NA_Q = Fraction(42, 100_000_000)
assert ETA_NA_Q + BETA_NA_Q / 2 == T_NA_Q

T_NA = as_mpf(T_NA_Q)
eta_NA = as_mpf(ETA_NA_Q)
beta_NA = as_mpf(BETA_NA_Q)


def xyz(z: mp.mpf) -> tuple[mp.mpf, mp.mpf, mp.mpf]:
    """Three-level branch (x, y repeated k-2 times, z)."""

    B = mp.sqrt(k * (1 - t)) - mp.sqrt(z)
    d = mp.sqrt(((k - 1) * (1 - z) - B**2) / (k - 2))
    v = (B - d) / (k - 1)
    u = B - (k - 2) * v
    return u**2, v**2, z


def steepened_entropy(z: mp.mpf, T: mp.mpf) -> mp.mpf:
    x, y, z_value = xyz(z)
    return (
        -(x + T) * mp.log(x + T)
        - (k - 2) * y * mp.log(y)
        - (z_value - T) * mp.log(z_value - T)
    )


def stationary_z(T: mp.mpf) -> mp.mpf:
    return mp.findroot(
        lambda z: mp.diff(lambda u: steepened_entropy(u, T), z),
        (mp.mpf("0.0032"), mp.mpf("0.0035")),
    )


z_star = stationary_z(T_NA)
x_star, y_star, _ = xyz(z_star)
E_local = steepened_entropy(z_star, T_NA)
margin_NA_local = 2 * E_local - H_bell

# This is the zero of the selected three-level local branch only; it is not a
# globally certified critical radius.
T_zero_three_level_branch = mp.findroot(
    lambda T: 2 * steepened_entropy(stationary_z(T), T) - H_bell,
    (mp.mpf("0.00088518"), mp.mpf("0.00088519")),
)

NA_RATIO_NUMERATOR = 100_088_497
NA_RATIO_DENOMINATOR = 88_497
NA_TAIL_FACTOR = 714_917_836

assert Fraction(1, 1) + 1 / ETA_NA_Q == Fraction(
    NA_RATIO_NUMERATOR, NA_RATIO_DENOMINATOR
)
assert 300 * (1 + ETA_NA_Q) / BETA_NA_Q < NA_TAIL_FACTOR

log10_pre_ceiling_N_NA = log10_pre_ceiling_bound(
    NA_RATIO_NUMERATOR,
    NA_RATIO_DENOMINATOR,
    NA_TAIL_FACTOR,
)
log10_pre_ceiling_input_NA = log10_pre_ceiling_N_NA + mp.log10(r0)


# ---------------------------------------------------------------------------
# Numerical sanity checks against the displayed manuscript intervals.
# These assertions are not a substitute for a formal interval proof.
# ---------------------------------------------------------------------------

theta_d0 = d0 * (mp.log(d0) + mp.log(mp.log(d0)) + 5)
assert s == 57_836_025
assert r0 == 1_460_730_375
assert d0 == 38_024
assert mp.pi * r0 / 3 < PI_R0_OVER_3_UPPER
assert theta_d0 < THETA_D0_UPPER
assert 8 * (1 + mp.log(s)) < LOG_S_FACTOR_UPPER

assert abs(a + (k - 1) * b - 1) < mp.mpf("1e-90")
assert mp.mpf("4.7918716999329") < H_star < mp.mpf("4.7918716999330")
assert mp.mpf("9.5766876122353") < H_bell < mp.mpf("9.5766876122354")
assert 2 * Omega_AF < mp.mpf("0.0070092526964")
assert Delta > mp.mpf("0.0070557876304")
assert margin_AF > mp.mpf("0.0000465349340")

normalization_residual = x_star + (k - 2) * y_star + z_star - 1
fidelity_residual = (
    mp.sqrt(x_star)
    + (k - 2) * mp.sqrt(y_star)
    + mp.sqrt(z_star)
    - mp.sqrt(k * (1 - t))
)
stationarity_residual = mp.diff(
    lambda z: steepened_entropy(z, T_NA), z_star
)
second_derivative = mp.diff(
    lambda z: steepened_entropy(z, T_NA), z_star, 2
)

assert x_star >= y_star >= z_star > T_NA
assert abs(normalization_residual) < mp.mpf("1e-90")
assert abs(fidelity_residual) < mp.mpf("1e-90")
assert abs(stationarity_residual) < mp.mpf("1e-80")
assert second_derivative > 0
assert mp.mpf("0.1797208952964") < x_star < mp.mpf("0.1797208952966")
assert mp.mpf("0.0042326498177") < y_star < mp.mpf("0.0042326498179")
assert mp.mpf("0.0033776898759") < z_star < mp.mpf("0.0033776898762")
assert mp.mpf("4.7883438200717") < E_local < mp.mpf("4.7883438200718")
assert margin_NA_local > mp.mpf("2.79e-8")
assert T_NA < T_zero_three_level_branch


if __name__ == "__main__":
    print("FLOATING-POINT CHECK FOR THE UNCONDITIONAL FANNES--AUDENAERT RESULT")
    show("a", a)
    show("b", b)
    show("H_star", H_star)
    show("H_Bell", H_bell)
    show("Delta", Delta)
    show("2_Omega_AF", 2 * Omega_AF)
    show("AF_margin", margin_AF)
    show("T_AF", T_AF)
    show("eta_AF", eta_AF)
    show("beta_AF", beta_AF)
    show("log10_pre_ceiling_N_AF", log10_pre_ceiling_N_AF)
    show(
        "pre_ceiling_N_AF_mantissa",
        scientific_mantissa(log10_pre_ceiling_N_AF),
    )
    show("log10_pre_ceiling_input_AF", log10_pre_ceiling_input_AF)
    show(
        "pre_ceiling_input_AF_mantissa",
        scientific_mantissa(log10_pre_ceiling_input_AF),
    )

    print("\nCONDITIONAL THREE-LEVEL LOCAL-BRANCH CHECK")
    show("x", x_star)
    show("y", y_star)
    show("z", z_star)
    show("E_local", E_local)
    show("local_NA_margin", margin_NA_local)
    show("T_NA", T_NA)
    show("T_zero_three_level_branch", T_zero_three_level_branch)
    show("eta_NA", eta_NA)
    show("beta_NA", beta_NA)
    show("normalization_residual", normalization_residual)
    show("fidelity_residual", fidelity_residual)
    show("stationarity_residual", stationarity_residual)
    show("second_derivative", second_derivative)
    show("log10_pre_ceiling_N_NA", log10_pre_ceiling_N_NA)
    show(
        "pre_ceiling_N_NA_mantissa",
        scientific_mantissa(log10_pre_ceiling_N_NA),
    )
    show("log10_pre_ceiling_input_NA", log10_pre_ceiling_input_NA)
    show(
        "pre_ceiling_input_NA_mantissa",
        scientific_mantissa(log10_pre_ceiling_input_NA),
    )

    print("\nAll floating-point sanity checks passed.")
