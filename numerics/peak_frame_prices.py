"""Exact prices for background configurations in the frame of the peak.

The peak sits at offset 0 and holds an unbounded reservoir of mass. Background
particles sit at offsets 1..L-1 of a ring of L sites. In the frame of the peak:

  * the peak moves at rate 1: every offset drops by one, and mass at offset 1
    merges into the peak;
  * the peak chips at rate w: one particle lands at offset 1;
  * every occupied background site chips one particle forward at rate w;
  * every background site holding two or more particles moves whole at rate 1;
  * mass that moves forward from offset L-1 merges into the peak from behind.

The background mass is capped at M: a peak chip that would exceed M is
suppressed, so the chain is finite.

Split of the certificate. The linear moment F1 = sum of offsets, divided by
1 - w, has drift -S + w (P + 1)/(1 - w) - (rear term <= 0), where S and P are
the background singles and piles. It pays exactly one per single. What is left
is a pile price E with

    G E <= -P / (1 - w) + C'.

The smallest C' is the stationary mean of P / (1 - w), and the price with
equality solves the Poisson equation G E = C' - P / (1 - w), E(empty) = 0.
The certificate V = F1 / (1 - w) + E then bounds the mean number of occupied
background sites by C = w / (1 - w) + C'.

usage: python peak_frame_prices.py w L M [--profile] [--target occ|piles]
"""
import sys
from collections import Counter
from itertools import combinations_with_replacement

import numpy as np
from scipy.sparse import csr_matrix
from scipy.sparse.linalg import LinearOperator, gmres, spilu


def spsolve(A, b):
    """Sparse solve by GMRES with an incomplete LU preconditioner. A direct LU
    factorization fills in badly on these configuration spaces."""
    A = A.tocsc()
    ilu = spilu(A, drop_tol=1e-6, fill_factor=20)
    x, info = gmres(A, b, M=LinearOperator(A.shape, ilu.solve), rtol=1e-12,
                    restart=100, maxiter=1000)
    if info != 0:
        raise RuntimeError(f'gmres did not converge (info={info})')
    return x


def states(L, M):
    out = []
    for m in range(M + 1):
        out.extend(combinations_with_replacement(range(1, L), m))
    return out


def canon(positions):
    return tuple(sorted(positions))


def transitions(s, w, L, M):
    """All moves out of s: (rate, new state)."""
    out = [(1.0, canon(p - 1 for p in s if p > 1))]
    if len(s) < M:
        out.append((w, canon(s + (1,))))
    c = Counter(s)
    for p, a in c.items():
        rest = list(s)
        rest.remove(p)
        out.append((w, canon(rest + ([p + 1] if p + 1 < L else []))))
        if a >= 2:
            others = [q for q in s if q != p]
            moved = [p + 1] * a if p + 1 < L else []
            out.append((1.0, canon(others + moved)))
    return out


def generator(w, L, M):
    S = states(L, M)
    idx = {s: k for k, s in enumerate(S)}
    n = len(S)
    rows, cols, vals = [], [], []
    for k, s in enumerate(S):
        out = 0.0
        for r, t in transitions(s, w, L, M):
            if t == s:
                continue
            rows.append(k); cols.append(idx[t]); vals.append(r)
            out += r
        rows.append(k); cols.append(k); vals.append(-out)
    return S, idx, csr_matrix((vals, (rows, cols)), shape=(n, n))


def pin_first_row(A):
    """Replace row 0 of a CSR matrix by the first unit vector."""
    A = A.tolil()
    A.rows[0] = [0]
    A.data[0] = [1.0]
    return A.tocsr()


def solve(w, L, M, target):
    S, idx, Q = generator(w, L, M)
    n = len(S)
    piles = np.array([sum(1 for a in Counter(s).values() if a >= 2) for s in S], float)
    occ = np.array([len(set(s)) for s in S], float)
    mass = np.array([len(s) for s in S], float)
    f = occ if target == 'occ' else piles / (1 - w)
    # stationary law with pi(empty) pinned to 1, then normalized
    b = np.zeros(n); b[0] = 1.0
    pi = spsolve(pin_first_row(Q.T.tocsr()), b)
    pi = pi / pi.sum()
    Cp = float(pi @ f)
    rhs = Cp - f
    rhs[0] = 0.0
    E = spsolve(pin_first_row(Q), rhs)
    stats = dict(occ=float(pi @ occ), piles=float(pi @ piles), mass=float(pi @ mass),
                 top=float(pi[mass == M].sum()))
    return S, idx, E, Cp, stats


def main():
    w, L, M = float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    target = 'piles'
    if '--target' in sys.argv:
        target = sys.argv[sys.argv.index('--target') + 1]
    S, idx, E, Cp, st = solve(w, L, M, target)
    C = Cp + (w / (1 - w) if target == 'piles' else 0.0)
    print(f"w={w} L={L} M={M} states={len(S)}  E[occ]={st['occ']:.6f}  E[piles]={st['piles']:.6f}  "
          f"C'={Cp:.6f}  C={C:.6f}  P(mass=M)={st['top']:.2e}")
    if '--profile' in sys.argv:
        ds = [d for d in (1, 2, 3, 5, 8, 12, 18, 25, 35, 50, 70, 100) if d < L]
        print('offset d               ' + ' '.join(f'{d:>8d}' for d in ds))
        for m in range(2, M + 1):
            row = [E[idx[(d,) * m]] for d in ds]
            print(f'E(pile of {m})           ' + ' '.join(f'{v:8.2f}' for v in row))
        if M >= 3:
            row = [E[idx[canon((d, d, d + 1))]] if d + 1 < L else float('nan') for d in ds]
            print('E(pile 2, single ahead) ' + ' '.join(f'{v:8.2f}' for v in row))
            row = [E[idx[canon((d, d + 1))]] if d + 1 < L else float('nan') for d in ds]
            print('E(two adjacent singles) ' + ' '.join(f'{v:8.2f}' for v in row))


if __name__ == '__main__':
    main()
