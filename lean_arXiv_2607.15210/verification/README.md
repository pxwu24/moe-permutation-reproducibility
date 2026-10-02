# Current verification records

| Record | Meaning |
| --- | --- |
| [verification_status.json](verification_status.json) | Compiler outcome, versions, hashes, and declaration counts |
| [source_manifest.json](source_manifest.json) | Every rebuilt Lean source and its imports |
| [axiom_audit.log](axiom_audit.log) | Transitive axiom audit of all maintained declarations |
| [result_sources.json](result_sources.json) | Numbered results and complete local source dependencies |
| [paper_coverage.json](paper_coverage.json) | Checked deductions and the remaining unconditional proof obligation |
| [python_verification.json](python_verification.json) | Python check outcomes and source hashes |
| [entropy_statements.json](entropy_statements.json) | Comparison with the 54 original public entropy statements |
| [exit_code.txt](exit_code.txt) | Last full verifier exit code |

A passing compiler and axiom audit verifies the displayed theorem statements,
including their hypotheses. It does not prove the [remaining convergence input](../README.md#remaining-unverified-theorem).

The optional `--require-unconditional` flag makes the full verifier fail while
that theorem remains unproved. To inspect this condition without rebuilding:

```sh
cd lean_arXiv_2607.15210
python3 scripts/check_coverage.py --require-unconditional
```

The current expected exit code for this strict check is 2.

## Inspect a theorem

After running the full verifier, enter `lean_arXiv_2607.15210/` and run:

```sh
cat > InspectResult.lean <<'LEAN'
import AllProofs
#check HaarProjection.haar_projection_partialTrace_rank_fin
#print axioms HaarProjection.haar_projection_partialTrace_rank_fin
LEAN
lake env lean InspectResult.lean
rm InspectResult.lean
```

The [numbered guides](../results/) provide the exact declaration names.
To rebuild an individual source, after its dependencies have been built:

```sh
lake env lean --root=lean lean/Dimension182/RevisionScalarCertificate.lean
```

[Back to the verification summary](../README.md)
