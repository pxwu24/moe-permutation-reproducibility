# Lean verification of the Supplement

This collection accompanies *Explicit channels with unbounded gains in
classical communication using entangled inputs*. Result numbering follows
the supplied 18-page manuscript: Lemmas 3–6, Corollaries 1–2, and
Propositions 3–4.

The section **Details in the proof of the main theorem**, starting on page 17,
and the parameter table on page 18 are excluded. In particular, this collection
does not claim to verify the final theorem about vanishing one-copy Holevo
information and diverging two-copy Holevo information. Corollary 2 is a
technical entropy-gap result in the Supplement and remains included.

## Projects

| Directory | Toolchain | Dependencies | Subject |
| --- | --- | --- | --- |
| [`entropy`](entropy/) | Lean 4.33.0 | Physlib and mathlib, pinned commits | Entropy, coordinate marginals, and the uniform measurement estimate |
| [`adder-trace`](adder-trace/) | Lean 4.24.0 | mathlib, pinned commit | The prescribed modular adders, word and moment bounds, and filter trace |

The projects intentionally use separate toolchains: these are the versions
under which the recovered proofs were verified. They should not be imported
into one another. Both use the unnormalized Hilbert–Schmidt norm.

## Reproduce

Install Git, Python 3, Bash, and the
[elan Lean toolchain manager](https://github.com/leanprover/elan).
From this directory run:

```sh
bash verify-all.sh
```

The scripts download the pinned dependencies and may use their standard
mathlib caches. All proof modules in this repository are compiled from source.
The audit rejects `sorryAx` and any additional axiom; only `propext`,
`Classical.choice`, and `Quot.sound` are allowed.

See [COVERAGE.md](COVERAGE.md) for the correspondence between the paper and
Lean statements. Dependency notices are preserved in
[`entropy/NOTICE.md`](entropy/NOTICE.md).
