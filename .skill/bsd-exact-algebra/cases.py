"""The battery: every finite claim of the paper, with its expected value.

Run `python3 cases.py` (from this directory) and it prints one line per case and
exits 1 if anything does not match.  A green run is the fast path: it means the
numbers of Remark 2.4, Example 4.2, Example 4.3, Proposition 4.4, Example 4.5(b)
and Remark 4.6 all still reproduce, and the harness still agrees with brute
force where brute force is possible.

Add a case by writing the structure constants, the product P, and the expected
dimension; put it in `CASES`.  Never "fix" an expected value to make the run
green: if a value moved, either the paper changed or the harness broke, and the
difference is the finding.
"""

import sys
from fractions import Fraction

from harness import (add, scal, basis, apply, mulmat, Qmul, nullity,
                     conditions, dim, in_relation, commutes, brute,
                     nullity_q, conditions_q, dim_q)

FAILS = []


def mk(n, terms, p):
    A = {}
    for i in range(n):
        for j in range(n):
            v = [0] * n
            for k, c in terms.get((i, j), {}).items():
                v[k] = c % p
            A[(i, j)] = tuple(v)
    return A


def qtable(M, n, p):
    return [[M[(i, j)] for j in range(n)] for i in range(n)]


def alpha_product(M, al, n, p):
    """x . y = xy + alpha(y) alpha(x)   (the sigma_alpha product)."""
    return [[add(M[i][j],
                 tuple(sum(al[j][b] * al[i][c] * M[b][c][k]
                           for b in range(n) for c in range(n)) % p
                       for k in range(n)), p)
             for j in range(n)] for i in range(n)]


def ader_forms(M, al, n, p):
    """Q1(u,y) = u alpha(y),  Q2(x,v) = alpha(x) v."""
    Q1 = [[tuple(sum(M[b][t][k] * al[t][j] for t in range(n)) % p
                 for k in range(n)) for j in range(n)] for b in range(n)]
    Q2 = [[tuple(sum(al[i][t] * M[t][j][k] for t in range(n)) % p
                 for k in range(n)) for j in range(n)] for i in range(n)]
    return Q1, Q2


def check(name, got, want):
    ok = got == want
    print(f"  {'OK ' if ok else 'BAD'}  {name:58s} got {str(got):>10s}  want {str(want):>10s}")
    if not ok:
        FAILS.append((name, got, want))


# ---------------------------------------------------------------- algebras
def dual(p):
    """F_p[e]/(e^2), basis 1, e."""
    return mk(2, {(0, 0): {0: 1}, (0, 1): {1: 1}, (1, 0): {1: 1}}, p)


def uv(p):
    """F_p[u,v]/(u^2, v^2), basis 1, u, v, uv."""
    return mk(4, {(0, 0): {0: 1}, (0, 1): {1: 1}, (1, 0): {1: 1},
                  (0, 2): {2: 1}, (2, 0): {2: 1}, (0, 3): {3: 1},
                  (3, 0): {3: 1}, (1, 2): {3: 1}, (2, 1): {3: 1}}, p)


def m2(p):
    """M_2(F_p), basis E11, E12, E21, E22."""
    idx = lambda a, b: 2 * a + b
    terms = {}
    for a in range(2):
        for b in range(2):
            for c in range(2):
                for d in range(2):
                    if b == c:
                        terms[(idx(a, b), idx(c, d))] = {idx(a, d): 1}
    return mk(4, terms, p)


def e3(p):
    """F_p[e]/(e^3), basis 1, e, e^2."""
    return mk(3, {(0, 0): {0: 1}, (0, 1): {1: 1}, (0, 2): {2: 1},
                  (1, 0): {1: 1}, (2, 0): {2: 1}, (1, 1): {2: 1}}, p)


def f2f2():
    """F_2 x F_2, basis p, q."""
    return mk(2, {(0, 0): {0: 1}, (1, 1): {1: 1}}, 2)


def rem46(p):
    """Remark 4.6: basis 1, t, v, w; t^2=0, v^2=w^2=wv=t, vw=0, t annihilates."""
    terms = {}
    for i in range(4):
        terms[(0, i)] = {i: 1}
        terms[(i, 0)] = {i: 1}
    terms.update({(1, 1): {}, (1, 2): {}, (2, 1): {}, (1, 3): {}, (3, 1): {},
                  (2, 2): {1: 1}, (3, 3): {1: 1}, (3, 2): {1: 1}, (2, 3): {}})
    return mk(4, terms, p)


# ------------------------------------------------------------- Q algebras
def qmul(x, y):
    a1, b1, c1, d1 = x
    a2, b2, c2, d2 = y
    return (a1 * a2 - b1 * b2 - c1 * c2 - d1 * d2,
            a1 * b2 + b1 * a2 + c1 * d2 - d1 * c2,
            a1 * c2 - b1 * d2 + c1 * a2 + d1 * b2,
            a1 * d2 + b1 * c2 - c1 * b2 + d1 * a2)


Q4 = [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]


def quat_table():
    return [[qmul(Q4[i], Q4[j]) for j in range(4)] for i in range(4)]


def hq_table():
    """H (x)_Q Q(sqrt 2), basis q_m (x) (sqrt2)^n, index m + 4n."""
    B = [tuple(1 if t == (m + 4 * n) else 0 for t in range(8))
         for n in range(2) for m in range(4)]

    def mul(x, y):
        out = [Fraction(0)] * 8
        for m1 in range(4):
            for n1 in range(2):
                c1 = x[m1 + 4 * n1]
                if not c1:
                    continue
                for m2 in range(4):
                    for n2 in range(2):
                        c2 = y[m2 + 4 * n2]
                        if not c2:
                            continue
                        q = qmul(Q4[m1], Q4[m2])
                        n = n1 + n2
                        if n == 2:
                            q = tuple(2 * z for z in q)
                            n = 0
                        for t in range(4):
                            if q[t]:
                                out[t + 4 * n] += c1 * c2 * q[t]
        return tuple(out)
    return [[mul(B[i], B[j]) for j in range(8)] for i in range(8)]


def qalpha_product(M, al, n):
    return [[tuple(Fraction(M[i][j][k]) +
                   sum(Fraction(al[j][b]) * Fraction(al[i][c]) * Fraction(M[b][c][k])
                       for b in range(n) for c in range(n))
                   for k in range(n)) for j in range(n)] for i in range(n)]


def qader(M, al, n):
    Q1 = [[tuple(sum(Fraction(M[b][t][k]) * Fraction(al[t][j]) for t in range(n))
                 for k in range(n)) for j in range(n)] for b in range(n)]
    Q2 = [[tuple(sum(Fraction(al[i][t]) * Fraction(M[t][j][k]) for t in range(n))
                 for k in range(n)) for j in range(n)] for i in range(n)]
    return Q1, Q2


# ============================================================== the battery
print("validation against brute force (F_5[e]/e^2, all 625 maps)")
p = 5
A = dual(p)
M = qtable(A, 2, p)
for kind, Q, want, bwant in [
        ("id", [[scal(2, M[i][j], p) for j in range(2)] for i in range(2)], 1, 5),
        ("tau", [[add(M[i][j], M[j][i], p) for j in range(2)] for i in range(2)], 1, 5),
        ("negid", [[(0, 0)] * 2 for _ in range(2)], 4, 625),
        ("negtau", [[add(M[i][j], scal(-1, M[j][i], p), p) for j in range(2)]
                    for i in range(2)], 4, 625)]:
    check(f"F5[e]/e2 BSDer_{kind} dim", dim(Q, Q, Q, 2, p), want)
    check(f"F5[e]/e2 BSDer_{kind} brute force", brute(Q, Q, Q, 2, p), bwant)

print("\nvalidation against a known table (M_2(F_5))")
M = qtable(m2(5), 4, 5)
Qid = [[scal(2, M[i][j], 5) for j in range(4)] for i in range(4)]
Qtau = [[add(M[i][j], M[j][i], 5) for j in range(4)] for i in range(4)]
Qnid = [[(0, 0, 0, 0)] * 4 for _ in range(4)]
Qntau = [[add(M[i][j], scal(-1, M[j][i], 5), 5) for j in range(4)] for i in range(4)]
check("M2(F5) dim Der", dim(M, M, M, 4, 5), 3)
check("M2(F5) BSDer_id", dim(Qid, Qid, Qid, 4, 5), 3)
check("M2(F5) BSDer_tau", dim(Qtau, Qtau, Qtau, 4, 5), 3)
check("M2(F5) BSDer_negid", dim(Qnid, Qnid, Qnid, 4, 5), 16)
check("M2(F5) BSDer_negtau", dim(Qntau, Qntau, Qntau, 4, 5), 4)

print("\nSection 2")
# line 262: sigma = (T (x) T^-1) o tau on F_5[e]/e^2, T(1)=1, T(e)=1+e
T = [[1, 1], [0, 1]]        # columns: T(e0)=e0, T(e1)=e0+e1
Tinv = [[1, 4], [0, 1]]
A = dual(5)
def Q262(i, j):
    u = apply(T, basis(2, j, 5), 5)
    v = apply(Tinv, basis(2, i, 5), 5)
    return (u[0] * v[0] % 5, (u[0] * v[1] + u[1] * v[0]) % 5)
Q = [[Q262(i, j) for j in range(2)] for i in range(2)]
check("line 262: F5[e]/e2, sigma=(T x T^-1) o tau, dim BSDer_sigma", dim(Q, Q, Q, 2, 5), 0)

print("\nSection 4: Example 4.2 (F_5[u,v]/(u^2,v^2), D(uv)=uv)")
A = uv(5)
M = qtable(A, 4, 5)
alpha = [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 4, 0], [0, 0, 0, 4]]
Qa = alpha_product(M, alpha, 4, 5)
D = [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]]
check("Ex4.2 D in BSDer^alpha", int(in_relation(Qa, Qa, Qa, 4, 5, D)), 1)
check("Ex4.2 D commutes with alpha", int(commutes(D, alpha, 4, 5)), 1)
check("Ex4.2 D is a derivation", int(in_relation(M, M, M, 4, 5, D)), 0)

print("\nSection 4: Example 4.3 (F_2 x F_2, D(p)=D(q)=e)")
A = f2f2()
M = qtable(A, 2, 2)
alpha = [[0, 1], [1, 0]]
Qa = alpha_product(M, alpha, 2, 2)
D = [[1, 1], [1, 1]]
check("Ex4.3 D in BSDer^alpha", int(in_relation(Qa, Qa, Qa, 2, 2, D)), 1)
check("Ex4.3 D commutes", int(commutes(D, alpha, 2, 2)), 1)
check("Ex4.3 D is a derivation", int(in_relation(M, M, M, 2, 2, D)), 0)
check("Ex4.3 dim BSDer^alpha", dim(Qa, Qa, Qa, 2, 2, alpha), 1)
check("Ex4.3 dim Der", dim(M, M, M, 2, 2), 0)

print("\nSection 4: Proposition 4.4 (F_3[e]/e^3, alpha(e)=-e)")
A = e3(3)
M = qtable(A, 3, 3)
alpha = [[1, 0, 0], [0, 2, 0], [0, 0, 1]]
Q1, Q2 = ader_forms(M, alpha, 3, 3)
Qa = alpha_product(M, alpha, 3, 3)
check("Prop4.4 dim Der", dim(M, M, M, 3, 3), 3)
check("Prop4.4 dim ADer^alpha", dim(M, Q1, Q2, 3, 3, alpha), 1)
check("Prop4.4 dim BSDer_sigma^alpha", dim(Qa, Qa, Qa, 3, 3, alpha), 1)
D = [[0, 0, 0], [0, 1, 0], [0, 0, 1]]          # D(a + be + ce^2) = be + ce^2
check("Prop4.4 witness in ADer", int(in_relation(M, Q1, Q2, 3, 3, D)), 1)
check("Prop4.4 witness NOT in BSDer", int(in_relation(Qa, Qa, Qa, 3, 3, D)), 0)
d = [[0, 0, 0], [0, 1, 0], [0, 0, 2]]          # d(e^i) = i e^i
check("Prop4.4 d is a derivation", int(in_relation(M, M, M, 3, 3, d)), 1)
check("Prop4.4 d NOT in ADer", int(in_relation(M, Q1, Q2, 3, 3, d)), 0)
check("Prop4.4 d in BSDer", int(in_relation(Qa, Qa, Qa, 3, 3, d)), 1)

print("\nSection 4: Example 4.5(b) (K[e]/e^2)")
for p, want in [(5, (1, 1, 1)), (3, (1, 1, 1)), (2, (2, 2, 4))]:
    A = dual(p)
    M = qtable(A, 2, p)
    alpha = [[1, 0], [0, (-1) % p]]
    Q1, Q2 = ader_forms(M, alpha, 2, p)
    Qa = alpha_product(M, alpha, 2, p)
    got = (dim(M, Q1, Q2, 2, p, alpha), dim(M, M, M, 2, p),
           dim(Qa, Qa, Qa, 2, p, alpha))
    check(f"Ex4.5(b) F_{p}: (ADer^a, Der, BSDer^a)", got, want)

print("\nSection 4: Remark 4.6 (4-dim F_3 algebra)")
A = rem46(3)
M = qtable(A, 4, 3)
alpha = [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 2, 0], [0, 0, 0, 2]]
Qa = alpha_product(M, alpha, 4, 3)
check("Rem4.6 dim BSDer^alpha", dim(Qa, Qa, Qa, 4, 3, alpha), 3)
check("Rem4.6 dim Der^alpha", dim(M, M, M, 4, 3, alpha), 2)
check("Rem4.6 dim Der", dim(M, M, M, 4, 3), 4)
check("Rem4.6 dim BSDer", dim(Qa, Qa, Qa, 4, 3), 3)
D = [[0] * 4 for _ in range(4)]
D[2][2] = 1
D[3][2] = 1
check("Rem4.6 D in BSDer^alpha", int(in_relation(Qa, Qa, Qa, 4, 3, D)), 1)
check("Rem4.6 D is a derivation", int(in_relation(M, M, M, 4, 3, D)), 0)
def E(i, j):
    return tuple((sum(D[k][b] * M[i][j][b] for b in range(4))
                  - sum(D[t][i] * M[t][j][k] for t in range(4))
                  - sum(D[t][j] * M[i][t][k] for t in range(4))) % 3
                 for k in range(4))
check("Rem4.6 E(v,w) = -t", E(2, 3), (0, 2, 0, 0))
check("Rem4.6 (v+w)^2 = 0", add(M[2][3], add(M[2][2], add(M[3][2], M[3][3], 3), 3), 3),
      (0, 0, 0, 0))

print("\nRemark 4.6: quaternions over Q")
Mq = quat_table()
idq = [[1 if i == j else 0 for j in range(4)] for i in range(4)]
conj_i = [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, -1, 0], [0, 0, 0, -1]]
Qa_q = qalpha_product(Mq, conj_i, 4)
check("H dim Der", dim_q(Mq, Mq, Mq, 4), 3)
check("H dim Der^alpha", dim_q(Mq, Mq, Mq, 4, conj_i), 1)
check("H dim BSDer_sigma^alpha", dim_q(Qa_q, Qa_q, Qa_q, 4, conj_i), 1)
check("H dim BSDer_sigma", dim_q(Qa_q, Qa_q, Qa_q, 4), 1)

print("\nRemark 4.6 / this review: H (x)_Q Q(sqrt 2), alpha = id (x) conj")
Mh = hq_table()
ah = [[0] * 8 for _ in range(8)]
for m in range(4):
    ah[m][m] = 1
    ah[m + 4][m + 4] = -1
Qh = qalpha_product(Mh, ah, 8)
check("H(x)Q(sqrt2) dim Der", dim_q(Mh, Mh, Mh, 8), 6)
check("H(x)Q(sqrt2) dim Der^alpha", dim_q(Mh, Mh, Mh, 8, ah), 3)
check("H(x)Q(sqrt2) dim BSDer_sigma", dim_q(Qh, Qh, Qh, 8), 3)
check("H(x)Q(sqrt2) dim BSDer_sigma^alpha", dim_q(Qh, Qh, Qh, 8, ah), 3)

print()
if FAILS:
    print(f"FAILED: {len(FAILS)} case(s)")
    for f in FAILS:
        print("   ", f)
    sys.exit(1)
print("all cases reproduce")
