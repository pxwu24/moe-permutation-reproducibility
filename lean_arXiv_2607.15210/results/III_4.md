# Lemma III.4: Channel support and generalized-eigenvalue threshold

Complete.

For the actual normalized channel output of Eq. (20), maximization over positive-semidefinite trace-one matrices equals the largest normalized compression eigenvalue, and its infimum threshold is exactly the paper formula. The density eigenstate attaining the maximum and all trace identities are proved.

## Check this result

First run `bash lean_arXiv_2607.15210/verify-all.sh` from the repository root. Then, from `lean_arXiv_2607.15210/`, run:

```sh
cat > InspectResult.lean <<'LEAN'
import AllProofs

#check RevisionOutput.normalized_output_support
#print axioms RevisionOutput.normalized_output_support
#check RevisionOutput.local_channel_support_threshold
#print axioms RevisionOutput.local_channel_support_threshold
#check RevisionOutput.density_expectation_isGreatest
#print axioms RevisionOutput.density_expectation_isGreatest
#check RevisionOutput.normalizedOutput_pairing
#print axioms RevisionOutput.normalizedOutput_pairing
LEAN
lake env lean InspectResult.lean
rm InspectResult.lean
```

The displayed hypotheses are part of the checked statement. A theorem conditional on an intermediate assertion does not verify that assertion.

## Entry files

- [OutputStates.RevisionOutputChannel](../lean/OutputStates/RevisionOutputChannel.lean)

## All related Lean files

This is the complete transitive local import closure of the entry files. Mathlib dependencies are pinned in `lake-manifest.json`.

- [lean/OutputStates/OutputSpaceMatrix.lean](../lean/OutputStates/OutputSpaceMatrix.lean)
- [lean/OutputStates/RevisionOutputChannel.lean](../lean/OutputStates/RevisionOutputChannel.lean)
- [lean/Preliminaries/PreliminariesAnalysis.lean](../lean/Preliminaries/PreliminariesAnalysis.lean)
- [lean/Preliminaries/PreliminariesChoi.lean](../lean/Preliminaries/PreliminariesChoi.lean)
- [lean/Preliminaries/PreliminariesLegendre.lean](../lean/Preliminaries/PreliminariesLegendre.lean)
- [lean/Preliminaries/PreliminariesMatrix.lean](../lean/Preliminaries/PreliminariesMatrix.lean)
- [lean/RandomCompression/CompressionSpectral.lean](../lean/RandomCompression/CompressionSpectral.lean)

## Assumptions and dependencies

- Positive-definite marginal P_A,n and Hermitian H.
