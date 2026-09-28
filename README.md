# The Iwasawa decomposition of $GL_n(\mathbb{R})$ in Lean

[![build](https://github.com/CuteSurtr/Iwasawa_Decomposition/actions/workflows/build.yml/badge.svg)](https://github.com/CuteSurtr/Iwasawa_Decomposition/actions/workflows/build.yml)

A Lean 4 + Mathlib proof that every invertible real $n \times n$ matrix $g$
factors uniquely as $g = kau$, with $k$ orthogonal, $a$ diagonal with
positive entries, and $u$ upper triangular with ones on the diagonal. This
was my final project for Math 157.

I followed the proof in Lang's *Linear Algebra* (3rd ed., Appendix II).
Existence is Gram-Schmidt on the columns of $g$. Uniqueness comes down to one
lemma: an orthogonal upper triangular matrix with positive diagonal has to be
the identity.

As of the Mathlib version pinned here, this result isn't in Mathlib. The only
things there with Iwasawa in the name are a group simplicity criterion and a
TODO about "Iwasawa matrices".

Everything is in [`Iwasawa.lean`](Iwasawa.lean). Its comments refer to the
section numbers below.

## 1. Setup

Write $\langle x, y \rangle = \sum_j x_j y_j$ for the dot product on
$\mathbb{R}^n$ and $g^{(i)}$ for the $i$-th column of $g$. The three groups are

- $K = \{ Q : QQ^T = I \}$, the orthogonal matrices,
- $A$, the diagonal matrices with positive diagonal entries,
- $N$, the upper triangular matrices with ones on the diagonal.

In Lean they are plain predicates on `Matrix (Fin n) (Fin n) ℝ`:

```lean
def IsUpperTriangular (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Matrix.BlockTriangular M (id : Fin n → Fin n)

def IsUpperUnipotent (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsUpperTriangular M ∧ ∀ i, M i i = 1

def IsPositiveDiagonal (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, i ≠ j → M i j = 0) ∧ ∀ i, 0 < M i i

def IsOrthogonal (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  M * Mᵀ = 1
```

## 2. The theorem

**Theorem.** If $\det g \neq 0$, there are unique $k \in K$, $a \in A$ and
$u \in N$ with $g = kau$.

```lean
theorem iwasawaDecomposition (g : Matrix (Fin n) (Fin n) ℝ) (hg : g.det ≠ 0) :
    ∃! (kau : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ ×
              Matrix (Fin n) (Fin n) ℝ),
      IsOrthogonal kau.1 ∧ IsPositiveDiagonal kau.2.1 ∧ IsUpperUnipotent kau.2.2 ∧
      g = kau.1 * kau.2.1 * kau.2.2
```

## 3. The key lemma

**Lemma.** If $M$ is orthogonal and upper triangular with $M_{ii} > 0$ for
all $i$, then $M = I$.

*Proof.* $MM^T = I$ means $M^{-1} = M^T$. The inverse of an upper triangular
matrix is upper triangular, so $M^T$ is upper triangular too, which means $M$
is also lower triangular. So $M$ is diagonal, and the $(i, i)$ entry of
$MM^T = I$ reads $M_{ii}^2 = 1$. Since $M_{ii} > 0$, we get $M_{ii} = 1$.
$\blacksquare$

## 4. Existence

Fix $g$ with $\det g \neq 0$.

**4.1** The columns of $g$ are linearly independent, so Gram-Schmidt applies:

$$\tilde{e}_i = g^{(i)} - \sum_{k < i} \langle g^{(i)}, e_k \rangle e_k, \qquad e_i = \frac{\tilde{e}_i}{\lVert \tilde{e}_i \rVert}.$$

Independence also means no $\tilde{e}_i$ is zero, and $e_1, \dots, e_n$ are
orthonormal.

**4.2** Let $Q$ be the matrix with columns $e_1, \dots, e_n$. Orthonormal
columns give $Q^TQ = I$, and for a square matrix that implies $QQ^T = I$, so
$Q \in K$.

**4.3** Let $R = Q^Tg$, so $R_{ij} = \langle e_i, g^{(j)} \rangle$.
Rearranging 4.1,

$$g^{(j)} = \lVert \tilde{e}_j \rVert \, e_j + \sum_{k < j} \langle g^{(j)}, e_k \rangle e_k,$$

so $g^{(j)}$ is in the span of $e_1, \dots, e_j$ and $R_{ij} = 0$ for $i > j$.
For the diagonal, $\tilde{e}_i$ is orthogonal to every $e_k$ with $k < i$, so
pairing it with the same identity gives
$\langle \tilde{e}_i, g^{(i)} \rangle = \lVert \tilde{e}_i \rVert^2$ and

$$R_{ii} = \frac{\langle \tilde{e}_i, g^{(i)} \rangle}{\lVert \tilde{e}_i \rVert} = \lVert \tilde{e}_i \rVert > 0.$$

**4.4** Let $a$ be the diagonal matrix with the same diagonal as $R$ (it's in
$A$ by 4.3) and put $u = a^{-1}R$. Then $u$ is upper triangular with
$u_{ii} = R_{ii}^{-1} R_{ii} = 1$, so $u \in N$ and $R = au$.

**4.5** Finally $g = QQ^Tg = QR = Qau$, so $k = Q$ works.

## 5. Uniqueness

Suppose $g = k_1a_1u_1 = k_2a_2u_2$.

**5.1** Let $M = k_2^Tk_1$.

**5.2** $MM^T = k_2^T(k_1k_1^T)k_2 = k_2^Tk_2 = I$, so $M$ is orthogonal.

**5.3** Multiplying $k_1a_1u_1 = k_2a_2u_2$ on the left by $k_2^T$ and on the
right by $(a_1u_1)^{-1} = u_1^{-1}a_1^{-1}$ gives

$$M = a_2u_2u_1^{-1}a_1^{-1}.$$

Inverses of upper unipotent matrices are upper unipotent and inverses of
positive diagonal matrices are positive diagonal, so all four factors are upper
triangular and so is $M$. Its diagonal is the product of their diagonals:
$M_{ii} = (a_2)_{ii} / (a_1)_{ii} > 0$.

**5.4** By the key lemma $M = I$, and then $k_1 = k_2k_2^Tk_1 = k_2$.

**5.5** Cancelling $k$ leaves $a_1u_1 = a_2u_2$, i.e.
$a_2^{-1}a_1 = u_2u_1^{-1}$. The left side is diagonal and the right side is
upper unipotent, so both are $I$, which gives $a_1 = a_2$ and $u_1 = u_2$. The
Lean proof gets there a little differently: it writes
$a_2(u_2u_1^{-1}) = a_1$ and compares entries
(`posDiag_mul_upperUnip_eq_diag_iff`).

## 6. Putting it together

Sections 4 and 5 give the theorem. Unwinding the construction: $k$ has the
Gram-Schmidt vectors $e_i$ as its columns, $a$ holds the norms
$\lVert \tilde{e}_i \rVert$, and $u$ holds the coefficients that write each
column $g^{(j)}$ in terms of $\tilde{e}_1, \dots, \tilde{e}_j$.

## Where things are in the Lean file

| Section | Declarations |
| --- | --- |
| 1 | `IsOrthogonal`, `IsPositiveDiagonal`, `IsUpperUnipotent` |
| 2 | `IwasawaFactorization`, `iwasawaDecomposition` |
| 3 | `orthogonal_upperTriangular_posDiag_eq_one` |
| 4 | `qMat`, `rMat`, `dMat`, `uMat` (that's $Q$, $R$, $a$, $u$), `exists_iwasawa` |
| 5 | `iwasawa_unique`, `posDiag_mul_upperUnip_eq_diag_iff` |
| 6 | `iwasawaDecomposition` |

## Building

The Lean version is pinned in `lean-toolchain` (v4.30.0-rc1).

```sh
lake exe cache get   # prebuilt Mathlib
lake build
```

The four main results depend only on `propext`, `Classical.choice` and
`Quot.sound`. The file ends with a `#print axioms` for each of them wrapped in
`#guard_msgs`, so if one of them ever picks up a `sorry` (or any other axiom),
`lake build` fails. CI runs the same build on every push to `main`.

## Notes on the formalization

Some things that were one line on paper and not in Lean:

- I used plain predicates for $K$, $A$, $N$ rather than Mathlib `Subgroup`s.
  Less machinery, but the closure facts I needed are proved by hand.
- Mathlib's Gram-Schmidt wants an inner product space, and `Fin n → ℝ` has
  the sup norm, not the $\ell^2$ one. So `gCol` puts each column in
  `EuclideanSpace ℝ (Fin n)`, and `gCol_linearIndependent` moves linear
  independence across `WithLp.linearEquiv`.
- Mathlib defines `M⁻¹` through the adjugate, which is awkward to compute
  with. For the diagonal factor I use `diagInv` (the diagonal matrix of
  reciprocals) and only match it up with `M⁻¹` at the end, in
  `IsPositiveDiagonal.matInv_eq_diagInv`.
- `rMat_diag` doesn't assume $\det g \neq 0$, so it has to deal with
  $\tilde{e}_i = 0$, a case that never comes up once the columns are
  independent.
- Upper triangular is `Matrix.BlockTriangular M id`. Products and inverses
  then come straight from Mathlib (`Matrix.BlockTriangular.mul`,
  `Matrix.blockTriangular_inv_of_blockTriangular`); the price is a few goals
  of the form `id i < id i`.
- "The diagonal of a product of upper triangular matrices is the product of
  the diagonals" took three separate steps (`hdiag1` to `hdiag3`) inside
  `iwasawa_unique`.

## Reference

S. Lang, *Linear Algebra*, 3rd ed., Springer, 1987. Appendix II, "Iwasawa
Decomposition and Others".
