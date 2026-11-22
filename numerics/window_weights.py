"""Window weights for groups of at most three background particles.

A group is a maximal set of background particles in which consecutive
occupied sites are at most R apart. The potential is

    Phi = F1 + sum over groups of V(group),

where F1 is the first moment in the frame of the largest pile. F1 contributes
the drift d = w * (occupied sites) - (singles) of each group. Groups of one
particle get V = 0. This script solves a linear program for V on groups of two
and of three particles. It requires:

  * every group of two has drift QV + d <= 0;
  * every group of three has drift QV + d <= -c [bare pile of three];
  * V >= 0, so absorption by the peak never increases Phi;
  * no merge increases Phi: when a gap of R + 1 closes to R, the value of the
    new group is at most the sum of the values of its parts (J = 0).

It maximises c. Transitions that split a group give the sum of the parts.

Mode "fixed2" instead keeps the proven weights of groups of two, V(pile of
two) = 1/w and V(two singles) = 0, fixes c, and takes the smallest V on groups
of three. Merges then cost the jumps J it reports.

usage: python window_weights.py w R [--table] [--verify]
       python window_weights.py w R --fixed2 c [--dump file]
"""
import sys
from fractions import Fraction

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix


def normalize(conf):
    """Merge equal positions, shift the first to 0, return a tuple of (pos, n)."""
    d = {}
    for p, n in conf:
        d[p] = d.get(p, 0) + n
    items = sorted((p, n) for p, n in d.items() if n > 0)
    p0 = items[0][0]
    return tuple((p - p0, n) for p, n in items)


def transitions(conf, w):
    """All moves of a configuration: (rate, new configuration)."""
    out = []
    for k, (p, n) in enumerate(conf):
        rest = [c for j, c in enumerate(conf) if j != k]
        # chip at rate w
        new = rest + [(p, n - 1), (p + 1, 1)]
        out.append((w, normalize(new)))
        if n >= 2:
            out.append((1.0, normalize(rest + [(p + 1, n)])))
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


def drift_F1(conf, w):
    return w * len(conf) - sum(1 for _, n in conf if n == 1)


def enumerate_groups(R):
    g2 = [((0, 2),)] + [((0, 1), (g, 1)) for g in range(1, R + 1)]
    g3 = [((0, 3),)]
    g3 += [((0, 2), (d, 1)) for d in range(1, R + 1)]
    g3 += [((0, 1), (d, 2)) for d in range(1, R + 1)]
    g3 += [((0, 1), (a, 1), (a + b, 1)) for a in range(1, R + 1) for b in range(1, R + 1)]
    return g2, g3


def mass(conf):
    return sum(n for _, n in conf)


def build(w, R):
    g2, g3 = enumerate_groups(R)
    states = g2 + g3
    index = {s: i for i, s in enumerate(states)}
    nV = len(states)
    ic = nV  # index of c
    nvar = nV + 1

    def value_terms(conf):
        """Linear form {var: coeff} of V(conf), conf of at most 3 particles."""
        terms = {}
        for comp in components(conf, R):
            if mass(comp) >= 2:
                j = index[comp]
                terms[j] = terms.get(j, 0.0) + 1.0
        return terms

    rows, rhs, kinds = [], [], []
    for s in states:
        i = index[s]
        row = {}
        for rate, t in transitions(s, w):
            for j, cf in value_terms(t).items():
                row[j] = row.get(j, 0.0) + rate * cf
            row[i] = row.get(i, 0.0) - rate
        if s == ((0, 3),):
            row[ic] = row.get(ic, 0.0) + 1.0
        rows.append(row)
        rhs.append(-drift_F1(s, w))
        kinds.append(("drift", s))
    # merges: configurations of 3 particles with one gap R+1 and the other <= R
    split = []
    for d in range(1, R + 1):
        pass
    cand = []
    for a in range(1, R + 2):
        for b in range(1, R + 2):
            if (a == R + 1) != (b == R + 1):
                cand.append(((0, 1), (a, 1), (a + b, 1)))
    cand += [((0, 2), (R + 1, 1)), ((0, 1), (R + 1, 2))]
    for s in cand:
        before = value_terms(s)
        for rate, t in transitions(s, w):
            if len(components(t, R)) == 1:
                row = dict()
                for j, cf in value_terms(t).items():
                    row[j] = row.get(j, 0.0) + cf
                for j, cf in before.items():
                    row[j] = row.get(j, 0.0) - cf
                rows.append(row)
                rhs.append(0.0)
                kinds.append(("merge", s, t))
    # two singles merging into a group of two
    rows.append({index[((0, 1), (R, 1))]: 1.0})
    rhs.append(0.0)
    kinds.append(("merge2",))
    A = lil_matrix((len(rows), nvar))
    for r, row in enumerate(rows):
        for j, cf in row.items():
            A[r, j] = cf
    return states, index, A.tocsr(), np.array(rhs), kinds


def solve(w, R):
    states, index, A, b, kinds = build(w, R)
    nvar = len(states) + 1
    cost = np.zeros(nvar)
    cost[-1] = -1.0
    bounds = [(0, None)] * len(states) + [(None, None)]
    res = linprog(cost, A_ub=A, b_ub=b, bounds=bounds, method="highs")
    return states, index, res, A, b, kinds


def verify(w, R, states, index, V, c):
    """Check every constraint exactly with rational arithmetic."""
    wf = Fraction(w).limit_denominator(10 ** 6)
    Vq = {s: Fraction(V[index[s]]).limit_denominator(10 ** 6) for s in states}
    cq = Fraction(c).limit_denominator(10 ** 6)

    def val(conf):
        return sum((Vq[comp] for comp in components(conf, R) if mass(comp) >= 2), Fraction(0))

    worst = None
    for s in states:
        q = sum(((Fraction(1) if r == 1.0 else wf) * (val(t) - Vq[s]) for r, t in transitions(s, w)),
                Fraction(0))
        dr = wf * len(s) - sum(1 for _, n in s if n == 1)
        tot = q + dr + (cq if s == ((0, 3),) else 0)
        if worst is None or tot > worst[0]:
            worst = (tot, s)
    neg = min(Vq.values())
    return worst, neg


def solve_fixed2(w, R, c):
    """Smallest V on groups of three, with the level-two weights fixed."""
    g2, g3 = enumerate_groups(R)
    V2 = {((0, 2),): 1.0 / w}
    for g in range(1, R + 1):
        V2[((0, 1), (g, 1))] = 0.0
    index = {s: i for i, s in enumerate(g3)}

    def value_terms(conf):
        terms, const = {}, 0.0
        comps = components(conf, R)
        for comp in comps:
            m = mass(comp)
            if m == 3:
                terms[index[comp]] = terms.get(index[comp], 0.0) + 1.0
            elif m == 2:
                const += V2[comp]
        return terms, const

    A = lil_matrix((len(g3), len(g3)))
    b = np.zeros(len(g3))
    for s in g3:
        i = index[s]
        rhs = -drift_F1(s, w) - (c if s == ((0, 3),) else 0.0)
        for rate, t in transitions(s, w):
            terms, const = value_terms(t)
            for j, cf in terms.items():
                A[i, j] += rate * cf
            A[i, i] -= rate
            rhs -= rate * const
        b[i] = rhs
    res = linprog(np.ones(len(g3)), A_ub=A.tocsr(), b_ub=b, bounds=[(0, None)] * len(g3),
                  method="highs")
    V3 = {s: res.x[index[s]] for s in g3} if res.status == 0 else None
    return V2, V3, res


def solve_maxc2(w, R, eps=0.0):
    """Largest c with the level-two weights fixed and no merge raising Phi.

    With eps > 0 every drift constraint holds with slack eps, so that rounded
    weights can be checked exactly."""
    g2, g3 = enumerate_groups(R)
    V2 = {((0, 2),): 1.0 / w}
    for g in range(1, R + 1):
        V2[((0, 1), (g, 1))] = 0.0
    index = {s: i for i, s in enumerate(g3)}
    n = len(g3)
    ic = n

    def value_terms(conf):
        terms, const = {}, 0.0
        for comp in components(conf, R):
            m = mass(comp)
            if m == 3:
                terms[index[comp]] = terms.get(index[comp], 0.0) + 1.0
            elif m == 2:
                const += V2[comp]
        return terms, const

    rows, rhs = [], []
    for s in g3:
        i = index[s]
        row = {}
        r = -drift_F1(s, w) - eps
        for rate, t in transitions(s, w):
            terms, const = value_terms(t)
            for j, cf in terms.items():
                row[j] = row.get(j, 0.0) + rate * cf
            row[i] = row.get(i, 0.0) - rate
            r -= rate * const
        if s == ((0, 3),):
            row[ic] = 1.0
        rows.append(row)
        rhs.append(r)
    cand = []
    for a in range(1, R + 2):
        for b in range(1, R + 2):
            if (a == R + 1) != (b == R + 1):
                cand.append(((0, 1), (a, 1), (a + b, 1)))
    cand += [((0, 2), (R + 1, 1)), ((0, 1), (R + 1, 2))]
    for s in cand:
        tb, cb = value_terms(s)
        for rate, t in transitions(s, w):
            if len(components(t, R)) == 1:
                ta, ca = value_terms(t)
                row = dict(ta)
                for j, cf in tb.items():
                    row[j] = row.get(j, 0.0) - cf
                rows.append(row)
                rhs.append(cb - ca)
    A = lil_matrix((len(rows), n + 1))
    for k, row in enumerate(rows):
        for j, cf in row.items():
            A[k, j] = cf
    cost = np.zeros(n + 1)
    cost[ic] = -1.0
    cost[:n] = 1e-9  # among optimal solutions, prefer small weights
    res = linprog(cost, A_ub=A.tocsr(), b_ub=np.array(rhs),
                  bounds=[(0, None)] * n + [(None, None)], method="highs")
    if res.status != 0:
        return V2, None, None, res
    V3 = {s: res.x[index[s]] for s in g3}
    return V2, V3, res.x[ic], res


def verify_exact(w, R, V2, V3, c, digits=8):
    """Round the weights and check every drift and merge constraint exactly."""
    wq = Fraction(w).limit_denominator(10 ** 6)
    den = 10 ** digits
    q = lambda x: Fraction(round(x * den), den)
    V2q = {s: (1 / wq if s == ((0, 2),) else Fraction(0)) for s in V2}
    V3q = {s: q(x) for s, x in V3.items()}
    cq = q(c)

    def val(conf):
        tot = Fraction(0)
        for comp in components(conf, R):
            m = mass(comp)
            if m == 3:
                tot += V3q[comp]
            elif m == 2:
                tot += V2q[comp]
        return tot

    def drift(s, Vs):
        tot = wq * len(s) - sum(1 for _, n in s if n == 1)
        for rate, t in transitions(s, w):
            tot += (Fraction(1) if rate == 1.0 else wq) * (val(t) - Vs)
        return tot

    worst3 = max((drift(s, V3q[s]) + (cq if s == ((0, 3),) else 0), s) for s in V3q)
    worst2 = max((drift(s, V2q[s]), s) for s in V2q)
    jumps = [(val(t) - val(s0)) for (_, _, s0, t) in merge_jumps(w, R, V2q, V3q)]
    return worst3, worst2, max(jumps), min(V3q.values())


def merge_jumps(w, R, V2, V3):
    """Jumps of the group potential at every merge into a group of three."""
    def val(conf):
        tot = 0.0
        for comp in components(conf, R):
            m = mass(comp)
            if m == 3:
                tot += V3[comp]
            elif m == 2:
                tot += V2[comp]
        return tot
    out = []
    for a in range(1, R + 2):
        for b in range(1, R + 2):
            if (a == R + 1) != (b == R + 1):
                out.append(((0, 1), (a, 1), (a + b, 1)))
    out += [((0, 2), (R + 1, 1)), ((0, 1), (R + 1, 2))]
    jumps = []
    for s in out:
        for rate, t in transitions(s, w):
            if len(components(t, R)) == 1:
                jumps.append((val(t) - val(s), rate, s, t))
    return jumps


def main_fixed2(w, R, c):
    V2, V3, res = solve_fixed2(w, R, c)
    if V3 is None:
        print(f"w={w} R={R} c={c}: infeasible ({res.message})")
        return
    jumps = merge_jumps(w, R, V2, V3)
    jmax = max(jumps, key=lambda j: j[0])
    v = lambda s: V3[s]
    print(f"w={w} R={R} c={c}  V(T)={v(((0,3),)):.2f} (w^2 V(T)={w*w*v(((0,3),)):.3f})"
          f"  V(A1)={v(((0,2),(1,1))):.2f}  V(B1)={v(((0,1),(1,2))):.2f}"
          f"  V(111)={v(((0,1),(1,1),(2,1))):.2f}  max merge jump {jmax[0]:.2f}"
          f" ({jmax[2]} -> {jmax[3]})")
    if "--dump" in sys.argv:
        fn = sys.argv[sys.argv.index("--dump") + 1]
        with open(fn, "w") as f:
            print(w, R, c, file=f)
            for s, x in list(V2.items()) + list(V3.items()):
                print(" ".join(f"{p} {n}" for p, n in s) + f" : {x:.12g}", file=f)
        print(f"  wrote {fn}")


def main():
    w = float(sys.argv[1])
    R = int(sys.argv[2])
    if "--maxc2" in sys.argv:
        V2, V3, c, res = solve_maxc2(w, R, eps=1e-4 if "--verify" in sys.argv else 0.0)
        if V3 is None:
            print(f"w={w} R={R}: {res.message}")
            return
        print(f"w={w} R={R} max c={c:.4f}  V(T)={V3[((0,3),)]:.2f}"
              f" (w^2 V(T)={w*w*V3[((0,3),)]:.3f})  V(A1)={V3[((0,2),(1,1))]:.2f}"
              f"  max V3={max(V3.values()):.2f}")
        if "--verify" in sys.argv:
            w3, w2, jm, vmin = verify_exact(w, R, V2, V3, c)
            print(f"  exact: worst slack groups of three {float(w3[0]):+.3e} at {w3[1]},"
                  f" groups of two {float(w2[0]):+.3e} at {w2[1]},"
                  f" max merge jump {float(jm):+.3e}, min V3 {float(vmin):.3e}")
        if "--dump" in sys.argv:
            fn = sys.argv[sys.argv.index("--dump") + 1]
            with open(fn, "w") as f:
                print(w, R, c, file=f)
                for s0, x in list(V2.items()) + list(V3.items()):
                    print(" ".join(f"{p} {n}" for p, n in s0) + f" : {x:.12g}", file=f)
        return
    if "--fixed2" in sys.argv:
        main_fixed2(w, R, float(sys.argv[sys.argv.index("--fixed2") + 1]))
        return
    states, index, res, A, b, kinds = solve(w, R)
    if res.status != 0:
        print(f"w={w} R={R}: LP status {res.status}: {res.message}")
        return
    V = res.x[:-1]
    c = res.x[-1]
    v = lambda s: V[index[s]]
    print(f"w={w} R={R} c*={c:.4f}  V(P)={v(((0,2),)):.3f}  V(T)={v(((0,3),)):.3f}"
          f"  V(A1)={v(((0,2),(1,1))):.3f}  V(B1)={v(((0,1),(1,2))):.3f}"
          f"  V(111)={v(((0,1),(1,1),(2,1))):.3f}  w^2 V(T)={w*w*v(((0,3),)):.3f}")
    if "--table" in sys.argv:
        print("A(d):", " ".join(f"{v(((0,2),(d,1))):.2f}" for d in range(1, R + 1)))
        print("B(d):", " ".join(f"{v(((0,1),(d,2))):.2f}" for d in range(1, R + 1)))
        print("G(g):", " ".join(f"{v(((0,1),(g,1))):.2f}" for g in range(1, R + 1)))
    if "--verify" in sys.argv:
        worst, neg = verify(w, R, states, index, V, c)
        print(f"  exact check (rounded weights): worst drift slack {float(worst[0]):+.2e} at {worst[1]},"
              f" min V {float(neg):.2e}")


if __name__ == "__main__":
    main()
