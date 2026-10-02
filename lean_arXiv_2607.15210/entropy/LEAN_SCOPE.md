> Historical scope/report. The current numbered results and complete Lean dependencies are listed in [the project README](../README.md). Statements below about missing proofs describe the earlier snapshot.

# Formal verification scope

The formal objects are the spectra defined in `Entropy/Defs.lean`:

- `Dset` and `Lam`: the cost-constrained body and its normalization;
- `shuffle`: the antisymmetric single-output eigenvalue list;
- `rkt`, `alphaB`, `betaB`: the Bell mixing parameter and eigenvalues;
- `dm`, `wm`, `bellNu`: the multiplicities and postprocessed Bell spectrum;
- `renyi`: the spectral Rényi entropy, with a separate Shannon branch at p = 1.

The main declarations are:

| Paper result | Lean theorem | Error |
|---|---|---|
| Single output, r = 1 | `single_output_r1`; `single_output_r1_infimum` | k^(-5/2) |
| Single output, fixed r ≥ 1 | `single_output`; `single_output_infimum` | k^(-5/2) |
| Bell output, r = 1 | `bell_output_r1` | k^(-4) |
| Bell output, fixed r ≥ 1 | `bell_output` | k^(-3) |

All names are in namespace `AppendixB`. The statements quantify over every fixed real t∈(0,1), p>0, and, where applicable, every fixed natural r≥1. They assert explicit eventual bounds `∃ C k₀, ∀ k ≥ k₀, ...`; they do not infer asymptotics from finitely many computations. The infimum wrappers additionally choose C≥0.

The single-output proofs establish a uniform lower bound over every q∈Lam and an explicit feasible witness giving the matching upper bound. The `Infimum` module converts these into an absolute error bound for the actual infimum. Minimum attainment is now proved for all sufficiently large k in `Entropy/Minimum.lean`. Its `single_output_minimum` and `single_output_r1_minimum` include both an actual minimizing point and the entropy error bound.

Intermediate results include the exact entropy identity, Taylor remainder bounds, uniform expansion, subset variance identity, localization, feasible two-spike witness, multiplicity and trace identities, and the Bell coefficient evaluation. The final sources contain no diagnostic interface assumptions. `verify_statements.py` checks that all 54 original public lemma/theorem statements are preserved; proof repairs do not weaken their hypotheses or conclusions.

The operator construction of the antisymmetric channel, its identification with `shuffle` and `bellNu`, and the probabilistic channel limits are outside this Lean development. The accompanying LaTeX proves the operator spectral identities, and Python independently checks small exterior-power matrix models. Those checks do not amount to a Lean formalization of the operators or the full random-channel theorem.

`Audit.lean` prints the axiom dependencies of every public theorem and the types of the four optimized/spectral conclusions. `check_axioms.py` requires a result for every listed theorem and rejects any axiom other than Lean/mathlib's standard `propext`, `Classical.choice`, and `Quot.sound`. Private arithmetic helpers are covered transitively by the audited theorems.

## Additional verified components

`MainCoefficient` and `MainSpectral` prove the explicit coefficient gap and eventual spectral nonadditivity for every fixed real p>0. `OutputSpace` and `OutputSpaceBody` prove the deterministic convergence steps and concrete feasible-body geometry. The four `BellLimit`/`BellFiniteDifference`/`BellMatrixIdentities` modules prove rational identities, uniform logarithmic remainders, finite Choi contractions, and limit transfer. Their hypotheses and remaining measure/operator bridges are described in the [final-draft report](../final_draft_audit/README.md). The combined root project also proves the actual growing-matrix normalized compression convergence, conditional on the compression limit.
