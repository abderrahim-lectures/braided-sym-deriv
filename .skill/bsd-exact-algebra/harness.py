"""Exact linear algebra for the derivation spaces of this paper.

Conventions
-----------
* An algebra of dimension n over F_p is a dict `A[(i, j)] -> tuple`, the
  structure constants of `e_i * e_j`.
* A linear map D is an n x n integer matrix with `D[a][b]` = the a-th
  coordinate of `D(e_b)` (column convention).  The unknown vector is flattened
  as index `a*n + b`.
* A *product* P is a bilinear map given as `P[i][j] = e_i * e_j` (a tuple).

The condition solved is

    D(P(x, y)) = Q1(Dx, y) + Q2(x, Dy)      for all basis pairs and components

with `P = Q1 = Q2` for a braided-symmetric derivation, `Q1 = Q2 = mul` for a
derivation, and `Q1(u,y) = u*alpha(y)`, `Q2(x,v) = alpha(x)*v` for an
alpha-derivation.

Two bugs this file exists to prevent
------------------------------------
1. **Collapsing a vector equation to one scalar row.**  Every component k is a
   separate equation.  Summing over k gives a strictly weaker system; the first
   harness of the v73 review did this and reported `dim Der(M_2(F_5)) = 5`
   instead of 3.
2. **Transposing the commutation rows.**  `D(alpha e_i) = alpha(D e_i)` in
   component k is `sum_b D[k][b] alpha[b][i] = sum_t alpha[k][t] D[t][i]`, so
   the coefficient of the unknown `D[t][i]` is `alpha[k][t]` at index
   `t*n + i` -- not at `k*n + t`.  Getting this wrong leaves the constraint
   inactive and silently inflates the dimension.

Validate any change to this file with `cases.py`: four cases are checked
against brute-force enumeration of *all* `p^(n^2)` maps, and the rest against
values proved independently (in Lean, or by hand in `BASELINE.md`).
"""

from itertools import product as iproduct
from fractions import Fraction


# ---------------------------------------------------------------- F_p helpers
def add(a, b, p):
    return tuple((x + y) % p for x, y in zip(a, b))


def scal(c, a, p):
    return tuple((c * x) % p for x in a)


def basis(n, i, p):
    v = [0] * n
    v[i] = 1
    return tuple(v)


def apply(M, x, p):
    """Apply the matrix M (M[k][i] = k-th coordinate of M(e_i)) to x over F_p."""
    n = len(x)
    out = [0] * n
    for i in range(n):
        if x[i]:
            for k in range(n):
                out[k] = (out[k] + x[i] * M[k][i]) % p
    return tuple(out)


def mulmat(A, n):
    return [[A[(i, j)] for j in range(n)] for i in range(n)]


def Qmul(Q, x, y, n, p):
    out = [0] * n
    for i in range(n):
        if x[i]:
            for j in range(n):
                if y[j]:
                    c = x[i] * y[j] % p
                    for k in range(n):
                        out[k] = (out[k] + c * Q[i][j][k]) % p
    return tuple(out)


def nullity(rows, ncols, p):
    """Dimension and basis of the nullspace of an integer matrix over F_p."""
    M = [list(r) for r in rows]
    piv = []
    r = 0
    for c in range(ncols):
        pr = None
        for i in range(r, len(M)):
            if M[i][c] % p:
                pr = i
                break
        if pr is None:
            continue
        M[r], M[pr] = M[pr], M[r]
        inv = pow(M[r][c], p - 2, p)
        M[r] = [(v * inv) % p for v in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] % p:
                f = M[i][c]
                M[i] = [(a - f * b) % p for a, b in zip(M[i], M[r])]
        piv.append(c)
        r += 1
        if r == len(M):
            break
    free = [c for c in range(ncols) if c not in piv]
    basisv = []
    for fc in free:
        v = [0] * ncols
        v[fc] = 1
        for i, pc in enumerate(piv):
            v[pc] = (-M[i][fc]) % p
        basisv.append(tuple(v))
    return len(free), basisv


def conditions(P, Q1, Q2, n, p, alpha=None):
    """Rows of the linear system on the n*n entries of D."""
    rows = []
    for i in range(n):
        for j in range(n):
            for k in range(n):                       # every component: see (1)
                row = [0] * (n * n)
                for b in range(n):
                    row[k * n + b] += P[i][j][b]
                for t in range(n):
                    row[t * n + i] -= Q1[t][j][k]
                for t in range(n):
                    row[t * n + j] -= Q2[i][t][k]
                rows.append([v % p for v in row])
    if alpha is not None:
        for i in range(n):
            ax = apply(alpha, basis(n, i, p), p)
            for k in range(n):
                row = [0] * (n * n)
                for b in range(n):
                    row[k * n + b] += ax[b]
                for t in range(n):
                    avec = apply(alpha, basis(n, t, p), p)
                    row[t * n + i] -= avec[k]         # see (2)
                rows.append([v % p for v in row])
    return rows


def dim(P, Q1, Q2, n, p, alpha=None):
    return nullity(conditions(P, Q1, Q2, n, p, alpha), n * n, p)[0]


# ------------------------------------------------------------ F_p predicates
def in_relation(P, Q1, Q2, n, p, D):
    """Does the map given by the matrix D satisfy the relation?"""
    for i in range(n):
        for j in range(n):
            for k in range(n):
                lhs = sum(D[k][b] * P[i][j][b] for b in range(n))
                r1 = sum(D[t][i] * Q1[t][j][k] for t in range(n))
                r2 = sum(D[t][j] * Q2[i][t][k] for t in range(n))
                if (lhs - r1 - r2) % p:
                    return False
    return True


def commutes(D, alpha, n, p):
    for i in range(n):
        if apply(alpha, tuple(D[k][i] for k in range(n)), p) != \
           tuple(sum(D[k][b] * alpha[b][i] for b in range(n)) % p for k in range(n)):
            return False
    return True


def brute(P, Q1, Q2, n, p, alpha=None):
    """Enumerate ALL p^(n*n) linear maps and count those satisfying the relation.

    Only for tiny cases (n <= 2, p <= 5).  This is the independent
    implementation the linear solver is validated against.
    """
    cnt = 0
    for vals in iproduct(range(p), repeat=n * n):
        D = [list(vals[a * n:(a + 1) * n]) for a in range(n)]
        if in_relation(P, Q1, Q2, n, p, D) and \
           (alpha is None or commutes(D, alpha, n, p)):
            cnt += 1
    return cnt


# ------------------------------------------------------------- Q / any field
def nullity_q(rows, ncols):
    """Dimension of the nullspace over Q, by elimination with Fractions."""
    M = [[Fraction(x) for x in r] for r in rows]
    piv = []
    r = 0
    for c in range(ncols):
        pr = None
        for i in range(r, len(M)):
            if M[i][c] != 0:
                pr = i
                break
        if pr is None:
            continue
        M[r], M[pr] = M[pr], M[r]
        inv = M[r][c]
        M[r] = [v / inv for v in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        piv.append(c)
        r += 1
        if r == len(M):
            break
    return ncols - len(piv)


def conditions_q(P, Q1, Q2, n, alpha=None):
    rows = []
    for i in range(n):
        for j in range(n):
            for k in range(n):
                row = [Fraction(0)] * (n * n)
                for b in range(n):
                    row[k * n + b] += Fraction(P[i][j][b])
                for t in range(n):
                    row[t * n + i] -= Fraction(Q1[t][j][k])
                for t in range(n):
                    row[t * n + j] -= Fraction(Q2[i][t][k])
                rows.append(row)
    if alpha is not None:
        for i in range(n):
            for k in range(n):
                row = [Fraction(0)] * (n * n)
                for b in range(n):
                    row[k * n + b] += Fraction(alpha[b][i])
                for t in range(n):
                    row[t * n + i] -= Fraction(alpha[k][t])
                rows.append(row)
    return rows


def dim_q(P, Q1, Q2, n, alpha=None):
    return nullity_q(conditions_q(P, Q1, Q2, n, alpha), n * n)
