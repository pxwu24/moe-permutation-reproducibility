# Lemma II.2: Full local support of a Haar-random subspace

**Status: Complete.**

Actual unitary Haar probability measure, projection conjugation, partial-trace rank min(n,k*d), and almost-sure positive-definiteness iff n<=k*d.

## Check this result

First run `bash lean_arXiv_2607.15210/verify-all.sh` from the repository root. Then, from `lean_arXiv_2607.15210/`, run:

```sh
cat > InspectResult.lean <<'LEAN'
import AllProofs

#check HaarProjection.haar_projection_partialTrace_rank_fin
#print axioms HaarProjection.haar_projection_partialTrace_rank_fin
#check HaarProjection.haar_projection_full_local_support_iff_fin
#print axioms HaarProjection.haar_projection_full_local_support_iff_fin
LEAN
lake env lean InspectResult.lean
rm InspectResult.lean
```

The displayed hypotheses are part of the checked statement. A theorem conditional on an intermediate assertion does not verify that assertion.

## Entry files

- [HaarFullLocalSupport](../HaarFullLocalSupport.lean)

## All related Lean files

This is the complete transitive local import closure of the entry files. Mathlib dependencies are pinned in `lake-manifest.json`.

- [GaussianMatrixLaw.lean](../GaussianMatrixLaw.lean)
- [GaussianRadial.lean](../GaussianRadial.lean)
- [GaussianRank.lean](../GaussianRank.lean)
- [GaussianUnitary.lean](../GaussianUnitary.lean)
- [GaussianWhitening.lean](../GaussianWhitening.lean)
- [HaarFullLocalSupport.lean](../HaarFullLocalSupport.lean)
- [HaarLocalSupport.lean](../HaarLocalSupport.lean)
- [HaarMeasure.lean](../HaarMeasure.lean)
- [HaarOrbitUnique.lean](../HaarOrbitUnique.lean)
- [HaarProjection.lean](../HaarProjection.lean)
- [MatrixRankMeasurable.lean](../MatrixRankMeasurable.lean)
- [PreliminariesMatrix.lean](../PreliminariesMatrix.lean)
- [ProjectionOrbit.lean](../ProjectionOrbit.lean)

## Assumptions and dependencies

- n,k,d natural, 1<=d<=n*k; P0 Hermitian idempotent of rank d. No external Gaussian/Haar rank premise.
