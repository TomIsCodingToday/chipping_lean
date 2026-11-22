"""Exact stationary law of the chipping model on small rings, by power
iteration of the uniformized chain. Reports E[S], w E[K], E[B], E[H] and the
first-moment identity residual in the frame of the peak."""
import itertools, sys


def states(L, N):
    # compositions of N into L nonnegative parts
    for bars in itertools.combinations(range(N + L - 1), L - 1):
        prev, parts = -1, []
        for b in bars + (N + L - 1,):
            parts.append(b - prev - 1)
            prev = b
        yield tuple(parts)


def moves(x, w):
    L = len(x)
    for i, a in enumerate(x):
        j = (i + 1) % L
        if a >= 1:
            y = list(x); y[i] -= 1; y[j] += 1
            yield w, tuple(y)
        if a >= 2:
            y = list(x); y[i] = 0; y[j] += a
            yield 1.0, tuple(y)


def stationary(L, N, w, iters=200000, tol=1e-14):
    S = list(states(L, N))
    idx = {s: k for k, s in enumerate(S)}
    R = L * (1 + w)
    trans = []
    for s in S:
        out = [(r / R, idx[y]) for r, y in moves(s, w)]
        stay = 1 - sum(p for p, _ in out)
        trans.append((stay, out))
    p = [1.0 / len(S)] * len(S)
    for it in range(iters):
        q = [0.0] * len(S)
        for k, (stay, out) in enumerate(trans):
            pk = p[k]
            if pk == 0: continue
            q[k] += stay * pk
            for pr, j in out:
                q[j] += pr * pk
        diff = sum(abs(a - b) for a, b in zip(p, q))
        p = q
        if diff < tol: break
    return S, p


def report(L, N, w):
    S, p = stationary(L, N, w)
    ES = EK = EB = EH = 0.0
    for s, pr in zip(S, p):
        K = sum(1 for a in s if a >= 1)
        Sg = sum(1 for a in s if a == 1)
        M = max(s)
        ES += pr * Sg; EK += pr * K; EB += pr * (N - M)
        EH += pr * (1 - sum(a * a for a in s) / N ** 2)
    print(f"L={L} N={N} w={w:<5} E[S]={ES:.6f} wE[K]={w*EK:.6f} diff(wK-S)={w*EK-ES:+.6f} E[B]={EB:.5f} E[H]={EH:.5f}")


if __name__ == '__main__':
    for (L, N) in [(4, 4), (5, 5), (5, 10), (6, 6), (6, 3)]:
        for w in [0.1, 0.3, 0.6, 1.0, 2.0]:
            report(L, N, w)
