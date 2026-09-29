#!/usr/bin/env python3
"""Reproduce the scalar PRL parameter checks using standard-library Decimal.

This is a high-precision numerical cross-check, not a Lean certificate or an
interval-arithmetic proof. Integer parameters and the grid ceiling are exact.
The trace calculation uses the conservative analytic inequality
  log((4*M-1)**(4*L)+1) <= 4*L*log(4*M-1)+log(2).
It never attempts to construct the enormous powers or the channel matrices.
"""

import argparse
import json
from decimal import Decimal as D, localcontext
from math import isqrt
from pathlib import Path


def ceil_sqrt(value: int) -> int:
    root = isqrt(value)
    return root if root * root == value else root + 1


def check_parameters() -> dict:
    with localcontext() as ctx:
        ctx.prec = 100
        m = 2**27
        c1 = 200_000_000
        power_l = 261 * 10**19  # 2.61 * 10^21, exactly.
        q_choices = {
            "supplement": 4355 * 10**20,  # 4.355 * 10^23.
            "letter": 44 * 10**22,  # 4.4 * 10^23.
        }
        gamma = D(999_999) / 1_000_000
        epsilon = D(15) / 1000
        theta = D(10001) / 10000
        # sqrt(C1) = 10000*sqrt(2), C2 = 30003*sqrt(2).
        effective_c = D(30003) / 9999
        grid_ceiling = ceil_sqrt(c1 * m * m)
        log_p = D(m * (m - 1)) * D(2 * grid_ceiling).ln()
        log_2 = D(2).ln()
        log_first = log_p - 2 * power_l * theta.ln()
        log_b_lower = 4 * power_l * D(4 * m - 1).ln()
        log_b_upper = log_b_lower + log_2
        # (sqrt(C1*m*(m-1))/C2)^(2L) = [m*(m-1)/(9*theta^2)]^L.
        log_ratio = (D(m * (m - 1)) / (9 * theta**2)).ln()
        log_half_target = (epsilon / 2).ln()
        trace_results = {}
        for label, q in q_choices.items():
            log_second_upper = log_p + log_b_upper - q * log_2 + power_l * log_ratio
            checked = max(log_first, log_second_upper) < log_half_target
            assert checked, f"Trace upper bound failed for {label}"
            assert q * log_2 > log_b_upper, "Q > B_L was not verified"
            trace_results[label] = {
                "q": q,
                "log_first_term": str(log_first),
                "log_second_term_upper": str(log_second_upper),
                "log_epsilon_over_two": str(log_half_target),
                "both_terms_below_epsilon_over_two": checked,
                "Q_greater_than_B_L": True,
            }

        # This historical q is deliberately not an accepted parameter choice.
        old_q = 4353 * 10**20
        old_log_second_lower = log_p + log_b_lower - old_q * log_2 + power_l * log_ratio
        assert old_log_second_lower > epsilon.ln()

        def deficit(eps: D) -> D:
            s = gamma**2 / (1 + eps) ** 2
            x = 1 + (m - 1) * s
            return (x * x.ln() + (m - 1) * (1 - s) * (1 - s).ln()) / m**2

        penalty = 2 * (1 + effective_c**2 * gamma**2 / m).ln()
        gap = deficit(epsilon) - penalty
        assert gap > 0
        lo, hi = D("0.015"), D("0.016")
        for _ in range(200):
            middle = (lo + hi) / 2
            if deficit(middle) > penalty:
                lo = middle
            else:
                hi = middle
        assert deficit(lo) > penalty and deficit(hi) < penalty

        beta = (D(10001) * gamma / 9999) ** 2
        main_deficit = deficit(D(1) / 1_000_000)
        main_slope = main_deficit - 2 * (1 + D(9) / m).ln()
        repository_slope = main_deficit - 2 * (1 + 9 * beta / m).ln()
        assert repository_slope > D(5) / 1_000_000_000

        return {
            "verification_kind": "100-digit Decimal numerical cross-check; not a Lean certificate or interval proof",
            "logarithm_base": "natural",
            "M": m,
            "C1": c1,
            "C2": "30003*sqrt(2)",
            "L": power_l,
            "ceil_sqrt_C1_times_M": grid_ceiling,
            "log_P": str(log_p),
            "trace_bound_method": "Each summand < epsilon/2, with log B_L <= 4L log(4M-1)+log 2",
            "trace_checks": trace_results,
            "historical_insufficient_q": {
                "q": old_q,
                "log_second_term_lower": str(old_log_second_lower),
                "fails_trace_bound": True,
            },
            "entropy_checks": {
                "epsilon": str(epsilon),
                "deficit": str(deficit(epsilon)),
                "twice_one_copy_penalty": str(penalty),
                "strict_gap": str(gap),
                "critical_epsilon_numerical_bracket": [str(lo), str(hi)],
                "main_slope": str(main_slope),
                "repository_beta_slope": str(repository_slope),
                "repository_slope_greater_than_5e_minus_9": True,
            },
        }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Write reproducible JSON to this path.")
    args = parser.parse_args()
    report = json.dumps(check_parameters(), indent=2) + "\n"
    if args.output is None:
        print(report, end="")
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(report, encoding="utf-8")
        print(f"Numerical checks passed; JSON written to {args.output}")
        print("This high-precision calculation is not a Lean certificate.")


if __name__ == "__main__":
    main()
