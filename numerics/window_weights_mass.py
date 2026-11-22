"""Window weights for groups of at most M background particles.

Generalizes window_weights.py from three particles to any M. A group is a
maximal set of particles in which consecutive occupied sites are at most R
apart, and the value of a configuration is the sum of the values of its
groups. Groups of one particle, and groups of more than M particles, are worth
zero. The linear program asks for V >= 0 on all groups of 2..M particles with

  * drift QV + d <= -c on the bare pile of M particles,
  * drift QV + d <= -c3 on the bare pile of three (c3 is fixed, default 0),
  * drift QV + d <= 0 on every other group,
  * no merge raises the potential: when a gap of R + 1 closes to R, the new
    group is worth at most its two parts after the move,

where d = w * (occupied sites) - (singles) is the share of the first moment.
It maximizes c and reports the value of the bare piles and the support of V.

usage: python window_weights_mass.py w R M [--c3 value] [--fixed] [--pile-credit] [--dump file]

--fixed keeps the closed-form VariableWindow prices on groups of two and three
and solves only for the larger groups. --pile-credit asks instead for drift at
most -c (mass in piles of three or more) / M on every group. --r3 r evaluates
the fixed VariableWindow prices at radius r instead of R, so that groups of
four may use a larger window than the proven prices.
"""
import sys
from itertools import product

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix


def normalize(conf):
    d = {}
    for p, n in conf:
        d[p] = d.get(p, 0) + n
    items = sorted((p, n) for p, n in d.items() if n > 0)
    p0 = items[0][0]
    return tuple((p - p0, n) for p, n in items)


def transitions(conf, w):
    out = []
    for k, (p, n) in enumerate(conf):
        rest = [c for j, c in enumerate(conf) if j != k]
        out.append((w, k, False, normalize(rest + [(p, n - 1), (p + 1, 1)])))
        if n >= 2:
            out.append((1.0, k, True, normalize(rest + [(p + 1, n)])))
    return out


def components(conf, R):
    comps, cur = [], [conf[0]]
    for a, b in zip(conf, conf[1:]):
        if b[0] - a[0] <= R:
            cur.append(b)
        else:
            comps.append(cur)
            cur = [b]
    comps.append(cur)
    return [normalize(c) for c in comps]


def mass(conf):
    return sum(n for _, n in conf)


def drift_F1(conf, w):
    return w * len(conf) - sum(1 for _, n in conf if n == 1)


def compositions(m):
    if m == 0:
        yield ()
        return
    for first in range(1, m + 1):
        for rest in compositions(m - first):
            yield (first,) + rest


def groups(m, R):
    out = []
    for comp in compositions(m):
        k = len(comp)
        for gaps in product(range(1, R + 1), repeat=k - 1):
            pos, p = [0], 0
            for g in gaps:
                p += g
                pos.append(p)
            out.append(tuple(zip(pos, comp)))
    return out


def variable_window_price(g, w, R):
    """The closed-form prices of VariableWindow for groups of two and three."""
    if R3 is not None:
        R = R3
    K = 1.0 / w
    ramp = lambda t: max(t, 0.0)
    ahead = lambda d: 3 + ramp(R - d)
    ns = tuple(n for _, n in g)
    ps = [p for p, _ in g]
    if ns == (2,):
        return 3.0
    if ns == (1, 1):
        return 0.0
    if ns == (3,):
        return ahead(1) + 1 + 1 / (64 * w)
    if ns == (2, 1):
        return ahead(ps[1])
    if ns == (1, 2):
        return 3 + ramp(R - K * ps[1]) / 2
    if ns == (1, 1, 1):
        return ramp(R - (ps[2] - ps[1]) - K * ps[1])
    raise ValueError(g)


PILE_CREDIT = "--pile-credit" in sys.argv
# radius of the fixed VariableWindow prices; defaults to the grouping radius R
R3 = int(sys.argv[sys.argv.index("--r3") + 1]) if "--r3" in sys.argv else None


def build(w, R, M, c3, fixed=False):
    states = [g for m in range(2, M + 1) for g in groups(m, R)]
    index = {s: i for i, s in enumerate(states)}
    nV = len(states)
    ic = nV
    bareM = ((0, M),)
    bare3 = ((0, 3),)

    def terms(conf):
        out = {}
        for comp in components(conf, R):
            if 2 <= mass(comp) <= M:
                j = index[comp]
                out[j] = out.get(j, 0.0) + 1.0
        return out

    rows, rhs = [], []
    for s in states:
        i = index[s]
        row = {}
        for rate, _, _, t in transitions(s, w):
            for j, cf in terms(t).items():
                row[j] = row.get(j, 0.0) + rate * cf
            row[i] = row.get(i, 0.0) - rate
        r = -drift_F1(s, w)
        if PILE_CREDIT:
            # credit proportional to the mass held in piles of three or more
            big = sum(n for _, n in s if n >= 3)
            if big:
                row[ic] = row.get(ic, 0.0) + big / M
        elif s == bareM:
            row[ic] = row.get(ic, 0.0) + 1.0
        elif s == bare3:
            r -= c3
        rows.append(row)
        rhs.append(r)
    nd = len(rows)
    # merges: two groups at gap R + 1, the rear one's last site moves forward
    for m1 in range(1, M):
        for m2 in range(1, M - m1 + 1):
            for g1 in (groups(m1, R) if m1 >= 2 else [((0, 1),)]):
                for g2 in (groups(m2, R) if m2 >= 2 else [((0, 1),)]):
                    last = g1[-1][0]
                    off = last + R + 1
                    conf = g1 + tuple((p + off, n) for p, n in g2)
                    k = len(g1) - 1
                    p, n = g1[-1]
                    rest = list(conf[:k]) + list(conf[k + 1:])
                    moves = [list(rest) + [(p, n - 1), (p + 1, 1)]]
                    if n >= 2:
                        moves.append(list(rest) + [(p + 1, n)])
                    for mv in moves:
                        t = normalize(mv)
                        comps = components(t, R)
                        if len(comps) != 1:
                            continue
                        # parts after the move, split at the closed gap
                        rear = normalize([c for c in mv if c[0] <= p + 1 and not
                                          (c[0] >= off)])
                        front = g2
                        row = {}
                        for j, cf in terms(t).items():
                            row[j] = row.get(j, 0.0) + cf
                        for part in (rear, front):
                            if 2 <= mass(part) <= M:
                                for jj, cf in terms(part).items():
                                    row[jj] = row.get(jj, 0.0) - cf
                        rows.append(row)
                        rhs.append(0.0)
    if fixed:
        # equality rows fixing the values of groups of two and three
        for s in states:
            if mass(s) <= 3:
                v = variable_window_price(s, w, R)
                rows.append({index[s]: 1.0}); rhs.append(v)
                rows.append({index[s]: -1.0}); rhs.append(-v)
    A = lil_matrix((len(rows), nV + 1))
    for r, row in enumerate(rows):
        for j, cf in row.items():
            if cf != 0.0:
                A[r, j] = cf
    return states, index, A.tocsr(), np.array(rhs), nd


def main():
    w, R, M = float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    c3 = float(sys.argv[sys.argv.index("--c3") + 1]) if "--c3" in sys.argv else 0.0
    fixed = "--fixed" in sys.argv
    states, index, A, b, nd = build(w, R, M, c3, fixed)
    if fixed:
        # check the fixed rows of groups of two and three on their own
        Vf = np.zeros(len(states) + 1)
        for s in states:
            if mass(s) <= 3:
                Vf[index[s]] = variable_window_price(s, w, R)
        worst = max((A[r].toarray()[0] @ Vf - b[r]) for r in range(nd)
                    if mass(states[r]) <= 3)
        print(f"  VariableWindow prices at w={w}, R={R}: worst mass<=3 drift excess {worst:.4f}")
    nV = len(states)
    cost = np.zeros(nV + 1)
    cost[nV] = -1.0
    # small penalty on the total value picks a sparse optimum among the maximizers
    bounds = [(0, None)] * nV + [(None, 10.0)]
    res = linprog(cost, A_ub=A, b_ub=b, bounds=bounds, method="highs")
    if res.status != 0:
        print("LP status", res.status, res.message)
        return
    c = res.x[nV]
    res2 = linprog(np.r_[np.ones(nV), 0.0], A_ub=A, b_ub=b,
                   bounds=[(0, None)] * nV + [(0.999 * c, 0.999 * c)], method="highs")
    V = res2.x[:nV] if res2.status == 0 else res.x[:nV]
    print(f"w={w} R={R} M={M} c3={c3}: groups {nV}, drift rows {nd}, rows {A.shape[0]}")
    print(f"  largest credit c = {c:.4f}; with c fixed at 0.999 c the smallest values give")
    for m in range(3, M + 1):
        print(f"  V(bare {m}) = {V[index[((0, m),)]]:.3f}   w^2 V = {w * w * V[index[((0, m),)]]:.3f}")
    print(f"  V(pile of two) = {V[index[((0, 2),)]]:.3f}")
    nz = [(states[i], V[i]) for i in range(nV) if V[i] > 1e-6]
    print(f"  nonzero values: {len(nz)} of {nV}")
    by_shape = {}
    for s, v in nz:
        key = tuple(n for _, n in s)
        by_shape.setdefault(key, []).append((s, v))
    for key in sorted(by_shape, key=lambda k: (sum(k), k)):
        lst = by_shape[key]
        top = sorted(lst, key=lambda e: -e[1])[:4]
        print(f"    multiplicities {key}: {len(lst)} nonzero, largest",
              ", ".join(f"{[p for p, _ in s]}:{v:.2f}" for s, v in top))
    if "--dump" in sys.argv:
        fn = sys.argv[sys.argv.index("--dump") + 1]
        with open(fn, "w") as f:
            print(w, R, M, c, file=f)
            for s, v in nz:
                print(" ".join(f"{p} {n}" for p, n in s), ":", repr(float(v)), file=f)


if __name__ == "__main__":
    main()
