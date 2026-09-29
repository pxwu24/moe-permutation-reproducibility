# Verification runtime

The compiler is the unmodified official Lean 4.33.0 Linux release:

https://github.com/leanprover/lean4/releases/download/v4.33.0/lean-4.33.0-linux.tar.zst

- Release archive SHA-256: `4b3fb03c29a1e0a253fb1d11f9bae3725f19a0dc6fc09b3ea16d2c9df3349e2c`
- `bin/lean` SHA-256: `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`
- Reported compiler commit: `d8b18978322de05a8f3dba51ef03cf5461676c17`

This execution environment uses a separate PID namespace with host procfs.
The stock compiler initially reported `failed to locate application` because
`/proc/<getpid()>/exe` does not identify its executable here. An external
`LD_PRELOAD` library redirects only that exact calling-process path in `readlink`
to `/proc/self/exe`. All other paths and operations are unchanged. This restores
normal own-executable discovery; it does not modify Lean, its kernel, standard
library, proof sources, or theorem statements. Ordinary Linux does not require
this environment-specific compatibility library.

Physlib and Mathlib were fetched at the commits in `environment.txt`. The
published `upstream.patch` is the only tracked Physlib change. Standard Mathlib
dependency artifacts came from the normal exact-hash cache; the selected Physlib
modules were built locally. Every local proof module is rebuilt from source by
the repository verifier, and its declarations are audited transitively against
`propext`, `Classical.choice`, and `Quot.sound` only.

The run uses the unchanged verifier, with its output isolated from historical
verification records:

```bash
VERIFICATION_DIR="$PWD/lean/entropy/verification" bash lean/verify-all.sh
```

`verification_status.json`, `exit_code.txt`, `verification.log`, and
`generated/source_manifest.json` are the authoritative outcome and source
identity records for this run.
