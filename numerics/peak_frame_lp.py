"""Group-additive pile prices in the frame of the peak, by linear programming.

The chain is the one of peak_frame_prices.py: background mass capped at M on
a ring of L sites, seen from the peak. A group is a maximal set of background
particles whose consecutive offsets differ by at most R. The price is additive
over groups,

    E(s) = sum over groups g of Phi(shape(g), offset(g)),

where the offset is the position of the first particle of the group and the
shape lists the other positions relative to it. The program asks for

    G E(s) <= -P(s) / (1 - w) + C'     for every configuration s,

with P the number of background piles, and minimizes C'. Together with the
linear moment divided by 1 - w, such a price bounds the mean number of
occupied background sites by w / (1 - w) + C'. The unrestricted optimum is
the exact value computed by peak_frame_prices.py; R limits the interactions
the price may describe.

With --ramp D1,D2,... the price of each shape is restricted to the closed form
Phi(shape, d) = alpha(shape) + sum_k beta_k(shape) * min(d, D_k), a piecewise
linear function of the offset with breakpoints D_k.

--ramp-mass k applies the closed form only to shapes of at most k particles
and leaves heavier shapes free.

With --killed l1,l2,... the basis min(d, D_k) is replaced by 1 - l_k^d, the
profiles of a random walk absorbed at the peak and killed at the rate kappa
with l + 1/l = 2 + kappa.

usage: python peak_frame_lp.py w L M R [--table] [--ramp D1,D2,...] [--ramp-mass k]
"""
import sys
from collections import Counter

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix

from peak_frame_prices import solve, states, transitions


def groups(s, R):
    out, cur = [], []
    for p in s:
        if cur and p - cur[-1] > R:
            out.append(cur)
            cur = []
        cur.append(p)
    if cur:
        out.append(cur)
    return [(tuple(q - g[0] for q in g), g[0]) for g in out]


def build(w, L, M, R, ramp=None, ramp_mass=None):
    S = states(L, M)
    col = {}

    def c(key):
        if key not in col:
            col[key] = len(col)
        return col[key]

    def add(coef, g, r):
        if ramp is None or (ramp_mass is not None and len(g[0]) > ramp_mass):
            coef[c(g)] += r
        else:
            shape, d = g
            coef[c((shape, 'a'))] += r
            for k, D in enumerate(ramp):
                coef[c((shape, k))] += r * (min(d, D) if D >= 1 else 1 - D ** d)

    rows, cols, vals, rhs = [], [], [], []
    for k, s in enumerate(S):
        coef = Counter()
        out = 0.0
        for r, t in transitions(s, w, L, M):
            if t == s:
                continue
            out += r
            for g in groups(t, R):
                add(coef, g, r)
        for g in groups(s, R):
            add(coef, g, -out)
        for j, v in coef.items():
            if v != 0.0:
                rows.append(k); cols.append(j); vals.append(v)
        rhs.append(-sum(1 for a in Counter(s).values() if a >= 2) / (1 - w))
    nvar = len(col)
    # the last column is C'
    rows.extend(range(len(S))); cols.extend([nvar] * len(S)); vals.extend([-1.0] * len(S))
    A = csr_matrix((vals, (rows, cols)), shape=(len(S), nvar + 1))
    return S, col, A, np.array(rhs)


def main():
    w, L, M, R = float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    ramp = None
    if '--ramp' in sys.argv:
        ramp = [int(x) for x in sys.argv[sys.argv.index('--ramp') + 1].split(',')]
    if '--killed' in sys.argv:
        ramp = [float(x) for x in sys.argv[sys.argv.index('--killed') + 1].split(',')]
    ramp_mass = None
    if '--ramp-mass' in sys.argv:
        ramp_mass = int(sys.argv[sys.argv.index('--ramp-mass') + 1])
    S, col, A, b = build(w, L, M, R, ramp, ramp_mass)
    nvar = len(col)
    cost = np.zeros(nvar + 1); cost[-1] = 1.0
    bounds = [(-1e5, 1e5)] * nvar + [(None, None)]
    res = linprog(cost, A_ub=A, b_ub=b, bounds=bounds, method='highs')
    if res.status != 0:
        print('LP failed:', res.message)
        return
    Cp = res.x[-1]
    exact = solve(w, L, M, 'piles')[3]
    print(f'w={w} L={L} M={M} R={R} ramp={ramp} states={len(S)} variables={nvar}  '
          f"C'(group-additive)={Cp:.6f}  C'(exact)={exact:.6f}  "
          f"C={w / (1 - w) + Cp:.6f}")
    if '--table' in sys.argv and ramp is not None:
        print('shape               alpha ' + ' '.join(f'{"b@" + str(D):>8s}' for D in ramp))
        for shape in [(0,), (0, 0), (0, 1), (0, 0, 0), (0, 0, 1), (0, 1, 1), (0, 0, 0, 0)]:
            if (shape, 'a') in col:
                print(f'{str(shape):<19s} {res.x[col[(shape, "a")]]:8.3f} ' +
                      ' '.join(f'{res.x[col[(shape, k)]]:8.3f}' for k in range(len(ramp))))
    elif '--table' in sys.argv:
        ds = [d for d in (1, 2, 3, 5, 8, 12, 18, 25) if d < L]
        print('offset d            ' + ' '.join(f'{d:>8d}' for d in ds))
        for shape in [(0,), (0, 0), (0, 1), (0, 0, 0), (0, 0, 1), (0, 1, 1), (0, 0, 0, 0)]:
            if len(shape) > M or (len(shape) > 1 and max(shape) > R):
                continue
            vals = [res.x[col[(shape, d)]] if (shape, d) in col else float('nan') for d in ds]
            print(f'{str(shape):<19s} ' + ' '.join(f'{v:8.2f}' for v in vals))


if __name__ == '__main__':
    main()
