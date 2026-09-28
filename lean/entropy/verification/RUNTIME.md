Runtime restoration for current verification
==========================================

The stock Lean 4.33.0 release archive was downloaded from
https://github.com/leanprover/lean4/releases/download/v4.33.0/lean-4.33.0-linux.tar.zst
and extracted without altering the compiler, kernel, or standard library.
The compiler reports commit d8b18978322de05a8f3dba51ef03cf5461676c17.
Physlib and mathlib were restored at their existing pinned commits. The existing
published upstream.patch is the only tracked Physlib source modification.

This execution environment unshares the PID namespace while mounting host
procfs. Consequently getpid() disagrees with /proc/self/status, and Lean's
readlink("/proc/<getpid>/exe") fails. A small shared library outside the proof
collection redirects only the exact path for the calling process to
"/proc/self/exe", which reads the same own-executable link. All other libc
operations are untouched. No proof theorem, compiler, or kernel is modified.
This environment-only compatibility shim is not required on ordinary Linux
and is not part of the published Lean proof sources or build procedure.

Standard dependencies were restored through their normal exact-hash Lake
artifact cache. All local proof modules are compiled afresh by the published verifier;
verification.log and verification_status.json record the final combined run.
