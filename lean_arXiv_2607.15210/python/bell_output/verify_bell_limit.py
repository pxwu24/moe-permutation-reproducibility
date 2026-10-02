#!/usr/bin/env python3
"""Independent numerical checks for the final draft's Bell-limit calculation.

Checks exact finite-matrix identities and finite-difference error estimates,
then high-precision scalar negative-root/Hessian formulas. These numerical
checks are not proofs of almost-sure convergence or of the free-convolution
log-potential identity. Run with assertions enabled.
"""
import json
import pathlib
import sys
import numpy as np
import mpmath as mp

if not __debug__:
    raise SystemExit('Run without -O; assertions implement the checks.')
mp.mp.dps = 75
rng = np.random.default_rng(26071002)


def bernoulli_r(t, y):
    """Cancellation-free real Bernoulli R transform, including y=0."""
    return 2*t/(1-y+mp.sqrt((1-y)**2+4*t*y))


def g(t, y):
    return y*bernoulli_r(t, y)


def root(t, a):
    k = len(a)
    f = lambda w: 1+k*sum(g(t, ai*w/k) for ai in a)
    lo, hi = mp.mpf(-1), mp.mpf(0)
    while f(lo) >= 0:
        lo *= 2
    for _ in range(280):
        mid = (lo+hi)/2
        if f(mid) > 0:
            hi = mid
        else:
            lo = mid
    return (lo+hi)/2


def potential(t, a):
    k = len(a)
    w = root(t, a)
    # The identity equating this expression to the free-convolution log moment
    # is an analytic input; this check tests the subsequent calculus only.
    L = lambda y: mp.quad(lambda v: bernoulli_r(t, v), [0, y])
    return -mp.log(-w)-1-k*sum(L(ai*w/k) for ai in a)


def scalar_checks():
    out = []
    h = mp.mpf('1e-13')
    for k, ts in [(2,'0.27'), (2,'0.7'), (3,'0.12'),
                   (3,'0.5'), (5,'0.08'), (5,'0.9')]:
        t = mp.mpf(ts)
        D = k**4*t-2*k*k*t+1
        c1 = -k*(1-t)/D
        c0 = (-1-k*c1)/(k*k)
        y = -mp.mpf(k*k-1)/(k*k*(k*k*t-1))
        assert abs(g(t,y)+mp.mpf(1)/(k*k)) < mp.mpf('1e-70')
        assert abs(root(t,[mp.mpf(1)]*k)/k-y) < mp.mpf('1e-68')
        assert abs(y*y*mp.diff(lambda v: bernoulli_r(t,v),y)
                   - (1-t)/D) < mp.mpf('1e-68')
        dirs = [list(range(1,k+1)), [1,-1]+[0]*(k-2), [1]*k]
        F0 = potential(t,[mp.mpf(1)]*k)
        errors = []
        for direction in dirs:
            Fp = potential(t,[1+h*x for x in direction])
            Fm = potential(t,[1-h*x for x in direction])
            second = (Fp+Fm-2*F0)/h**2
            target = c0*sum(direction)**2+c1*sum(x*x for x in direction)
            error = abs(second-target)
            assert error < mp.mpf('1e-20'), (k,t,direction,error)
            errors.append(mp.nstr(error,12))
        rr = k*k*(1-t)/D
        beta = (1-rr)/(k*k)
        alpha = beta+rr
        assert abs(-c0-beta) < mp.mpf('1e-70')
        assert abs(-c0-k*c1-alpha) < mp.mpf('1e-70')
        assert 0 < beta < alpha < 1
        out.append(dict(k=k,t=ts,negative_root=mp.nstr(y,24),hessian_errors=errors))
    return out


def finite_matrix_checks():
    out = []
    for n,k,d in [(4,2,3),(8,2,8),(8,3,6),(12,3,15),(15,4,20)]:
        G = rng.standard_normal((n*k,d))+1j*rng.standard_normal((n*k,d))
        U = np.linalg.qr(G,mode='reduced')[0]
        P = U@U.conj().T
        P4 = P.reshape(n,k,n,k)
        PA = np.einsum('aibi->ab', P4)
        val,V = np.linalg.eigh(PA)
        assert val.min() > 0
        A = (V/np.sqrt(val))@V.conj().T
        J = np.kron(A,np.eye(k))@P@np.kron(A,np.eye(k))
        J4 = J.reshape(n,k,n,k)
        blocks = J4.transpose(1,3,0,2)
        # Channel-action formula on |Omega><Omega|, without block-trace reuse.
        Z1 = np.einsum('aibj,apbq->ipjq',J4,J4.conj()).reshape(k*k,k*k)/n
        Z2 = np.einsum('ijab,qpba->ipjq',blocks,blocks).reshape(k*k,k*k)/n
        err = float(np.max(np.abs(Z1-Z2)))
        assert err < 1e-12
        bell = np.eye(k).reshape(-1)/np.sqrt(k)
        overlap = np.vdot(bell,Z1@bell).real
        purity = np.trace(J@J).real/(n*k)
        assert abs(overlap-purity) < 1e-12
        assert np.max(np.abs(sum(blocks[i,i] for i in range(k))-np.eye(n))) < 1e-11
        assert abs(np.trace(Z1)-1) < 1e-12
        assert np.linalg.eigvalsh(Z1).min() > -1e-12
        H0 = rng.standard_normal((k,k))+1j*rng.standard_normal((k,k))
        H = (H0+H0.conj().T)/2
        H /= np.linalg.norm(H,2)
        TH = np.einsum('aibj,ji->ab',P4,H)
        C = A@TH@A
        cv = np.linalg.eigvalsh(C)
        assert max(abs(cv)) <= 1+1e-12
        x = 0.05
        # Exact scalarized central difference avoids logdet cancellation.
        central = np.mean(np.log1p(x*cv)+np.log1p(-x*cv))/x**2
        moment = np.trace(C@C).real/n
        remainder = abs(central+moment)
        bound = 4*x*x*np.linalg.norm(H,2)**4
        assert remainder <= bound
        # Independent determinant identity, relative logdet differences.
        F0 = np.linalg.slogdet(PA)[1]/n
        Fx = np.linalg.slogdet(PA+x*TH)[1]/n
        delta = np.mean(np.log1p(x*cv))
        assert abs(Fx-F0-delta) < 1e-12
        out.append(dict(n=n,k=k,rank=d,entry_identity_error=err,
                        overlap_purity_error=abs(overlap-purity),
                        central_difference_error=float(remainder),
                        central_difference_bound=float(bound)))
    return out


if __name__ == '__main__':
    results = dict(seed=26071002,mpmath_digits=mp.mp.dps,
                   finite_matrix=finite_matrix_checks(),scalar=scalar_checks(),
                   status='all assertions passed',
                   scope='Finite examples and scalar formulas only; no stochastic convergence certificate.')
    path = pathlib.Path(__file__).with_name('bell_limit_results.json')
    path.write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(results,indent=2))
