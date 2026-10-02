#!/usr/bin/env python3
"""Independent checks of the final draft's tensor/Slater spectral bridge.

Slater embeddings are built directly from signed permutations, independently
of the exterior-annihilation implementation in verify_entropy.py. Integer
matrix equalities are exact for the tested dimensions; eigenvalue comparisons
are floating-point regression tests, not general proofs or interval certificates.
"""
from __future__ import annotations
import argparse
from itertools import combinations, permutations
import json
from math import comb, factorial
from pathlib import Path
import numpy as np
from verify_entropy import annihilators


def slater_numerator(k: int, r: int) -> np.ndarray:
    """sqrt(r!) times the normalized Slater embedding, integer entries."""
    sets = list(combinations(range(k), r))
    B = np.zeros((k**r, len(sets)), dtype=np.int64)
    for column, I in enumerate(sets):
        for perm in permutations(range(r)):
            sign = (-1)**sum(perm[a] > perm[b] for a in range(r) for b in range(a+1, r))
            row = 0
            for j in perm:
                row = k*row + I[j]
            B[row, column] = sign
    assert np.array_equal(B.T @ B, factorial(r)*np.eye(len(sets), dtype=np.int64))
    return B


def check(k: int, r: int) -> dict:
    B, Bprev = slater_numerator(k, r), slater_numerator(k, r-1)
    D, N, fac = comb(k,r), comb(k-1,r-1), factorial(r)
    assert k*N == r*D
    A = annihilators(k,r)
    L = [[(A[a].T @ A[b]).astype(np.int64) for b in range(k)] for a in range(k)]
    identity = np.eye(k**(r-1), dtype=np.int64)
    exact_compression_checks = 0
    for a in range(k):
        for b in range(k):
            E = np.zeros((k,k),dtype=np.int64)
            E[a,b] = 1
            compressed = B.T @ np.kron(E,identity) @ B
            # E(X)=k/(D*r!) B^T(X tensor I)B=L(X)/N.
            assert np.array_equal(k*N*compressed, D*fac*L[a][b])
            assert int(np.trace(L[a][b])) == (N if a == b else 0)
            exact_compression_checks += 1
    # Direct ordinary partial trace, with the integer Slater numerators on
    # both sides. The normalization denominator is r! (r-1)!.
    Rnumerator = np.empty((Bprev.shape[1]**2, D**2),dtype=np.int64)
    for i in range(D):
        for j in range(D):
            Y = np.outer(B[:,i],B[:,j]).reshape(k**(r-1),k,k**(r-1),k)
            traced = np.einsum('abcb->ac',Y)
            reduced = Bprev.T @ traced @ Bprev
            Rnumerator[:,i*D+j] = reduced.ravel()
    annihilator_sum = sum(np.kron(a,a).astype(np.int64) for a in A)
    denominator = factorial(r)*factorial(r-1)
    assert np.array_equal(r*Rnumerator, denominator*annihilator_sum)
    twirl = sum(np.kron(L[a][b],L[a][b]) for a in range(k) for b in range(k))
    assert np.array_equal(denominator**2*twirl, r*r*(Rnumerator.T @ Rnumerator))
    W = twirl/(k*N*N)
    eigenvalues = np.linalg.eigvalsh(W)
    assert np.min(eigenvalues) > -2e-12
    assert abs(np.trace(W)-1) < 2e-12
    error = None
    if k >= 2*r:
        expected = np.sort(np.concatenate([
            np.full(comb(k,j)**2-(comb(k,j-1)**2 if j else 0),
                    (r-j)*(k-r-j+1)/(k*N*N)) for j in range(r+1)]))
        error = float(np.max(np.abs(eigenvalues-expected)))
        assert error < 2e-12
    return {'k':k,'r':r,'exact_compression_identities':exact_compression_checks,
            'exact_partial_trace_and_twirl':'pass',
            'bell_eigenvalue_max_error':error,
            'spectrum_formula_scope':'k >= 2r' if k>=2*r else 'not asserted for k < 2r'}


def main():
    if not __debug__:
        raise RuntimeError('Assertions are required; do not run with -O.')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).with_name('tensor_spectra_results.json'))
    args=parser.parse_args()
    rows=[check(k,r) for k,r in [(2,1),(2,2),(3,2),(3,3),(4,2),(4,3),(4,4),(5,2),(6,3)]]
    result={'status':'pass','cases':rows,
            'limitations':['Exact integer identities cover only the listed finite dimensions.',
                           'Floating-point eigenvalue checks are not universal proofs.']}
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(f'PASS: {len(rows)} direct Slater tensor cases; saved {args.output}')

if __name__=='__main__':
    main()
