# Verification tools

Run `bash lean_arXiv_2607.15210/verify-all.sh` from the repository root.

- `verify_lean.py`: rebuild every module in `lean/` and audit transitive axioms.
- `result_index.py`: regenerate numbered result guides and source dependencies.
- `verify_python.py`: run the numerical checks and exact certificates.
- `verify_entropy_statements.py`: preserve the original 54 entropy theorem statements.
- `check_coverage.py`: distinguish checked deductions from unconditional paper verification.

These scripts support the [main verification guide](../README.md).
