# Python checks and certificates

| Folder | Content |
| --- | --- |
| [random_compression/](random_compression/) | Numerical cross-check of the compression spectral edge |
| [entropy/](entropy/) | Entropy asymptotics and antisymmetric output spectra |
| [bell_output/](bell_output/) | Bell-output identities and finite-dimensional checks |
| [nonadditivity/](nonadditivity/) | Main nonadditivity coefficient inequalities |
| [dimension_182/](dimension_182/) | Exact rational certificate and exploratory numerical program |

Run all maintained programs through `bash lean_arXiv_2607.15210/verify-all.sh`.
The exact dimension-182 certificate uses only the standard library:

```sh
python3 lean_arXiv_2607.15210/python/dimension_182/certify_k182_exact.py
```

It certifies a scalar gap greater than 477/1000000 nats at t = 27/100000.
The other numerical programs are cross-checks, not universal proofs.
Exact finite Haar moment calculations are in [partial_progress/](../partial_progress/).
