# The Iwasawa Decomposition of $GL_n(\mathbb{R})$

This document records a complete proof of the Iwasawa decomposition
for the real general linear group $GL_n(\mathbb{R})$: every invertible
$n \times n$ real matrix factors uniquely as the product of an
orthogonal matrix, a positive diagonal matrix, and an upper-triangular
matrix with ones on the diagonal. The proof follows the one given by
Lang in *Linear Algebra* (3rd edition, 1987, Appendix II).

Every step is formalized and verified by machine in the companion
Lean 4 file [`Iwasawa.lean`](Iwasawa.lean); the section numbers below
match the `§` markers in that file (see
[Formalization in Lean](#formalization-in-lean) at the end).

The exposition is organized into six sections:

1. Notation and the three subgroups involved.
2. The statement of the theorem.
3. The key lemma on which the uniqueness argument turns.
4. The existence proof, by Gram–Schmidt orthonormalization of the
   columns of the matrix.
5. The uniqueness proof, by reduction to the key lemma.
6. A short conclusion summarizing the result.

The diagram below shows how the pieces fit together: the three
subgroups support both halves of the argument, the key lemma drives
uniqueness, and existence together with uniqueness give the theorem.

```mermaid
flowchart TD
    KAN["Three subgroups K, A, N<br/>IsOrthogonal, IsPositiveDiagonal, IsUpperUnipotent"]
    KEY["§3 Key lemma<br/>orthogonal + upper triangular + positive diagonal = identity"]
    EX["§4 Existence<br/>build (k, a, u) by Gram-Schmidt on the columns of g"]
    UNIQ["§5 Uniqueness<br/>two factorizations of g must agree"]
    THM["§2 and §6 Iwasawa decomposition<br/>unique (k, a, u) with g = k a u"]
    KAN --> KEY
    KAN --> EX
    KEY --> UNIQ
    EX --> THM
    UNIQ --> THM
```

---

## 1. Notation

Let $M_n(\mathbb{R})$ denote the set of all $n \times n$ matrices
with real entries. Write $I$ for the $n \times n$ identity matrix and
$A^T$ for the transpose of a matrix $A$. The standard inner product
on $\mathbb{R}^n$ is denoted

$$\langle x, y \rangle = \sum_{j=1}^{n} x_j y_j \qquad \text{for } x, y \in \mathbb{R}^n,$$

and the corresponding norm is

$$\lVert x \rVert = \sqrt{\langle x, x \rangle}.$$

We single out three subgroups of the general linear group
$GL_n(\mathbb{R})$.

The **orthogonal group** $K$ consists of those matrices $Q$ that
satisfy $Q Q^T = I$:

$$K = \{ Q \in M_n(\mathbb{R}) : Q Q^T = I \}.$$

The **positive diagonal group** $A$ consists of diagonal matrices
whose diagonal entries are all strictly positive:

$$A = \{ D \in M_n(\mathbb{R}) : D_{ij} = 0 \text{ for } i \neq j, \text{ and } D_{ii} > 0 \text{ for all } i \}.$$

The **upper unipotent group** $N$ consists of upper-triangular
matrices whose diagonal entries are all equal to $1$:

$$N = \{ U \in M_n(\mathbb{R}) : U_{ij} = 0 \text{ for } i > j, \text{ and } U_{ii} = 1 \text{ for all } i \}.$$

For a matrix $g \in M_n(\mathbb{R})$, its $i$-th column is denoted
$g^{(i)}$ and is regarded as a vector in $\mathbb{R}^n$. Concretely,
the $j$-th coordinate of $g^{(i)}$ is the matrix entry $g_{ji}$:

$$\bigl( g^{(i)} \bigr)_{j} = g_{ji}.$$

---

## 2. Statement of the theorem

**Theorem (Iwasawa decomposition).** Let $g \in M_n(\mathbb{R})$ be a
matrix with $\det g \neq 0$. Then there exist unique matrices
$k \in K$, $a \in A$, and $u \in N$ such that

$$g = k \cdot a \cdot u.$$

The proof is given in three parts:

- **Section 3 (Key lemma).** A matrix that is simultaneously
  orthogonal, upper triangular, and has a strictly positive diagonal
  must be the identity.
- **Section 4 (Existence).** Given $g$ with $\det g \neq 0$, an
  explicit triple $(k, a, u) \in K \times A \times N$ satisfying
  $g = k \cdot a \cdot u$ is constructed by applying Gram–Schmidt
  orthonormalization to the columns of $g$.
- **Section 5 (Uniqueness).** If two triples both satisfy the
  factorization equation, then they are equal componentwise; the
  proof reduces to the key lemma applied to the matrix
  $k_2^T k_1$.

---

## 3. Key lemma

**Lemma.** Let $M \in M_n(\mathbb{R})$. Suppose

- $M$ is orthogonal, that is, $M M^T = I$;
- $M$ is upper triangular, that is, $M_{ij} = 0$ whenever $i > j$;
- $M$ has strictly positive diagonal, that is, $M_{ii} > 0$ for every
  $i$.

Then $M = I$.

**Proof.** From $M M^T = I$ we read off that $M$ is invertible, with
inverse

$$M^{-1} = M^T.$$

The inverse of an invertible upper-triangular matrix is itself upper
triangular. Hence $M^{-1} = M^T$ is upper triangular, which is the
same as saying that $M$ itself is *lower* triangular.

Combined with the original hypothesis that $M$ is upper triangular,
the matrix $M$ is now both upper and lower triangular. This forces
all off-diagonal entries to vanish: $M$ is diagonal.

Now equate the $(i, i)$-entries on both sides of $M M^T = I$. Because
$M$ is diagonal, the sum that defines the matrix product collapses
to a single term:

$$
\begin{aligned}
\sum_{k=1}^{n} M_{ik} \cdot (M^T)_{ki}
&= \sum_{k=1}^{n} M_{ik} \cdot M_{ik} \\
&= M_{ii}^{2} = 1.
\end{aligned}
$$

Since $M_{ii} > 0$ by hypothesis, this equation forces $M_{ii} = 1$
for every index $i$. Therefore $M$ is the identity matrix.
$\blacksquare$

---

## 4. Existence

Throughout this section, fix a matrix $g \in M_n(\mathbb{R})$ with
$\det g \neq 0$. We will construct an explicit triple
$(k, a, u) \in K \times A \times N$ satisfying $g = k \cdot a \cdot u$.

The construction proceeds in five steps:

- 4.1: Apply Gram–Schmidt to the columns of $g$ to obtain an
  orthonormal family.
- 4.2: Assemble the orthogonal matrix $Q$ from the orthonormal
  columns.
- 4.3: Define $R = Q^T g$ and verify that it is upper triangular with
  strictly positive diagonal.
- 4.4: Split $R$ as $R = a \cdot u$ where $a$ is positive diagonal
  and $u$ is upper unipotent.
- 4.5: Combine to obtain the factorization $g = Q \cdot a \cdot u$.

As a pipeline, the construction reads left to right:

```mermaid
flowchart LR
    G["g with det g ≠ 0"]
    GS["Gram-Schmidt<br/>orthonormal columns (§4.1)"]
    Q["Q = qMat g<br/>orthogonal (§4.2)"]
    R["R = Qᵀ g<br/>upper triangular,<br/>positive diagonal (§4.3)"]
    AU["split R = a u<br/>a = dMat g, u = uMat g (§4.4)"]
    OUT["g = Q a u (§4.5)"]
    G --> GS --> Q --> R --> AU --> OUT
```

### 4.1 Gram–Schmidt on the columns of $g$

Because $\det g \neq 0$, the columns

$$g^{(1)}, \quad g^{(2)}, \quad \dots, \quad g^{(n)}$$

form a linearly independent family in $\mathbb{R}^n$.

Apply the Gram–Schmidt orthonormalization procedure to this family.
Define recursively, for $i = 1, 2, \dots, n$,

$$\tilde{e}_i = g^{(i)} - \sum_{k=1}^{i-1} \langle g^{(i)}, e_k \rangle e_k,$$

$$e_i = \frac{ \tilde{e}_i }{ \lVert \tilde{e}_i \rVert }.$$

For $i = 1$, the empty sum is zero, so the recursion reduces to

$$\tilde{e}_1 = g^{(1)}, \qquad e_1 = \frac{ g^{(1)} }{ \lVert g^{(1)} \rVert }.$$

Linear independence of the columns guarantees that $\tilde{e}_i$ is
nonzero at every stage of the recursion: if $\tilde{e}_i$ were zero
for some $i$, then $g^{(i)}$ would lie in the span of
$g^{(1)}, \dots, g^{(i-1)}$, contradicting linear independence.
Hence each $e_i$ is well-defined.

By the standard properties of Gram–Schmidt, the resulting family

$$(e_1, \quad e_2, \quad \dots, \quad e_n)$$

is orthonormal: for every pair of indices $i$ and $j$,

$$
\langle e_i, e_j \rangle =
\begin{cases}
1 & \text{if } i = j, \\
0 & \text{if } i \neq j.
\end{cases}
$$

### 4.2 The orthogonal matrix $Q$

Let $Q \in M_n(\mathbb{R})$ be the matrix whose $i$-th column is the
vector $e_i$. In coordinates,

$$Q_{ji} = (e_i)_j \qquad \text{for } i, j \in \{ 1, 2, \dots, n \}.$$

The columns of $Q$ are orthonormal by construction, which is exactly
the statement that

$$Q^T Q = I.$$

For square matrices, the relations $Q^T Q = I$ and $Q Q^T = I$ are
equivalent: a square matrix that has a left inverse necessarily has
that same left inverse on the right. Therefore $Q Q^T = I$ as well,
so $Q \in K$.

### 4.3 The matrix $R = Q^T g$

Define

$$R = Q^T g.$$

In coordinates, the entry $R_{ij}$ equals the inner product of the
$i$-th column of $Q$ with the $j$-th column of $g$:

$$
\begin{aligned}
R_{ij}
&= \sum_{k=1}^{n} (Q^T)_{ik} g_{kj}
= \sum_{k=1}^{n} Q_{ki} g_{kj} \\
&= \sum_{k=1}^{n} (e_i)_k (g^{(j)})_k
= \langle e_i, g^{(j)} \rangle.
\end{aligned}
$$

We will now show two things about $R$:

- $R$ is upper triangular: $R_{ij} = 0$ whenever $i > j$.
- The diagonal entries of $R$ are strictly positive: $R_{ii} > 0$
  for every $i$.

#### Upper triangularity of $R$

Rearranging the recursive formula from Section 4.1,

$$g^{(j)} = \tilde{e}_j + \sum_{k=1}^{j-1} \langle g^{(j)}, e_k \rangle e_k.$$

Using $\tilde{e}_j = \lVert \tilde{e}_j \rVert \cdot e_j$ in the first
term,

$$
\begin{aligned}
g^{(j)}
&= \lVert \tilde{e}_j \rVert \cdot e_j \\
&\quad + \sum_{k=1}^{j-1} \langle g^{(j)}, e_k \rangle e_k.
\end{aligned}
$$

This expresses $g^{(j)}$ as a linear combination of
$e_1, e_2, \dots, e_j$. In other words,

$$g^{(j)} \in \mathrm{span}(e_1, e_2, \dots, e_j).$$

Now let $i > j$. The vector $e_i$ is orthogonal to every vector in
$\mathrm{span}(e_1, e_2, \dots, e_j)$, by orthonormality of the
family $(e_1, \dots, e_n)$. In particular, $e_i$ is orthogonal to
$g^{(j)}$, so

$$R_{ij} = \langle e_i, g^{(j)} \rangle = 0.$$

This proves that $R$ is upper triangular.

#### Positivity of the diagonal of $R$

By the construction of Gram–Schmidt, the vector $\tilde{e}_i$ is
orthogonal to all earlier orthonormalized vectors:

$$\langle \tilde{e}_i, e_k \rangle = 0 \quad \text{for } k < i.$$

Pair $\tilde{e}_i$ against $g^{(i)}$ using the rearranged recursion:

$$
\langle \tilde{e}_i, g^{(i)} \rangle
= \Bigl\langle
\tilde{e}_i,
\tilde{e}_i + \sum_{k=1}^{i-1} \langle g^{(i)}, e_k \rangle e_k
\Bigr\rangle.
$$

By bilinearity of the inner product,

$$
\begin{aligned}
\langle \tilde{e}_i, g^{(i)} \rangle
= {}& \langle \tilde{e}_i, \tilde{e}_i \rangle \\
&+ \sum_{k=1}^{i-1}
\langle g^{(i)}, e_k \rangle \cdot \langle \tilde{e}_i, e_k \rangle.
\end{aligned}
$$

Each of the cross terms vanishes, because $\tilde{e}_i$ is orthogonal
to all earlier orthonormalized vectors:

$$\langle \tilde{e}_i, e_k \rangle = 0 \quad \text{for all } k < i.$$

The first term is the squared norm:

$$\langle \tilde{e}_i, \tilde{e}_i \rangle = \lVert \tilde{e}_i \rVert^{2}.$$

Combining the two,

$$\langle \tilde{e}_i, g^{(i)} \rangle = \lVert \tilde{e}_i \rVert^{2}.$$

Now compute the diagonal entry:

$$
\begin{aligned}
R_{ii}
&= \langle e_i, g^{(i)} \rangle \\
&= \Bigl\langle \frac{ \tilde{e}_i }{ \lVert \tilde{e}_i \rVert }, g^{(i)} \Bigr\rangle \\
&= \frac{ 1 }{ \lVert \tilde{e}_i \rVert } \cdot
\langle \tilde{e}_i, g^{(i)} \rangle \\
&= \frac{ \lVert \tilde{e}_i \rVert^{2} }{ \lVert \tilde{e}_i \rVert } \\
&= \lVert \tilde{e}_i \rVert.
\end{aligned}
$$

Since $\tilde{e}_i \neq 0$, we have $\lVert \tilde{e}_i \rVert > 0$,
hence

$$R_{ii} > 0.$$

### 4.4 Splitting $R = a \cdot u$

Let $a \in M_n(\mathbb{R})$ be the diagonal matrix whose
$(i, i)$-entry equals the $(i, i)$-entry of $R$:

$$a_{ii} = R_{ii}, \qquad a_{ij} = 0 \quad \text{for } i \neq j.$$

By the previous step, $a_{ii} > 0$, so $a \in A$.

The matrix $a$ is invertible (its diagonal entries are all nonzero),
and its inverse is the diagonal matrix with entries

$$
(a^{-1})_{ii} = \frac{ 1 }{ R_{ii} }, \qquad
(a^{-1})_{ij} = 0 \quad \text{for } i \neq j.
$$

Define

$$u = a^{-1} R.$$

Since $a^{-1}$ is diagonal and $R$ is upper triangular, the product
$u$ is upper triangular. The $(i, i)$-entry of $u$ is

$$u_{ii} = (a^{-1})_{ii} \cdot R_{ii} = \frac{ 1 }{ R_{ii} } \cdot R_{ii} = 1.$$

Hence $u \in N$.

By construction $a \cdot u = a \cdot a^{-1} R = R$. So we have
written $R$ as a product

$$R = a \cdot u, \qquad a \in A, \qquad u \in N.$$

### 4.5 Assembling the factorization

Set $k = Q$. Then $k \in K$, $a \in A$, and $u \in N$.

Recall that $R = Q^T g$ and $Q Q^T = I$. Therefore

$$
\begin{aligned}
Q \cdot R
&= Q \cdot (Q^T g) \\
&= (Q Q^T) \cdot g \\
&= I \cdot g = g.
\end{aligned}
$$

Combining with the splitting $R = a \cdot u$ from Section 4.4,

$$g = Q \cdot R = Q \cdot (a \cdot u) = k \cdot a \cdot u.$$

This is the required factorization. Existence is proved.
$\blacksquare$

---

## 5. Uniqueness

Suppose that the matrix $g \in M_n(\mathbb{R})$ admits two
factorizations of the required form:

$$g = k_1 \cdot a_1 \cdot u_1 = k_2 \cdot a_2 \cdot u_2,$$

with $k_1, k_2 \in K$, $a_1, a_2 \in A$, and $u_1, u_2 \in N$. We
will show that

$$k_1 = k_2, \qquad a_1 = a_2, \qquad u_1 = u_2.$$

The argument proceeds in five steps:

- 5.1: Define an auxiliary matrix $M$.
- 5.2: Show that $M$ is orthogonal.
- 5.3: Show that $M$ is upper triangular with strictly positive
  diagonal.
- 5.4: Apply the key lemma to deduce $k_1 = k_2$.
- 5.5: Cancel and compare shapes to deduce $a_1 = a_2$ and
  $u_1 = u_2$.

The whole argument is a reduction to the key lemma:

```mermaid
flowchart TD
    TWO["two factorizations:<br/>k1 a1 u1 = k2 a2 u2"]
    M["M = k2ᵀ k1 (§5.1)"]
    ORTH["M orthogonal (§5.2)"]
    UT["M upper triangular,<br/>positive diagonal (§5.3)"]
    KEY["Key lemma (§3)"]
    MI["M = I, hence k1 = k2 (§5.4)"]
    LAST["cancel k, compare shapes:<br/>a1 = a2 and u1 = u2 (§5.5)"]
    TWO --> M
    M --> ORTH
    M --> UT
    ORTH --> KEY
    UT --> KEY
    KEY --> MI
    MI --> LAST
```

### 5.1 The auxiliary matrix $M$

Define

$$M := k_2^T k_1.$$

The strategy is to verify that $M$ satisfies the three hypotheses of
the key lemma in Section 3, and then conclude $M = I$.

### 5.2 $M$ is orthogonal

Compute the product $M M^T$ directly:

$$
\begin{aligned}
M M^T
&= (k_2^T k_1) \cdot (k_2^T k_1)^T \\
&= k_2^T k_1 k_1^T k_2 \\
&= k_2^T (k_1 k_1^T) k_2.
\end{aligned}
$$

Since $k_1 \in K$, we have $k_1 k_1^T = I$. Substituting,

$$M M^T = k_2^T \cdot I \cdot k_2 = k_2^T k_2.$$

Since $k_2 \in K$, we have $k_2 k_2^T = I$, and for square matrices
this implies $k_2^T k_2 = I$ as well. Therefore

$$M M^T = I,$$

so $M$ is orthogonal.

### 5.3 $M$ is upper triangular with strictly positive diagonal

Multiply the factorization equation

$$k_1 \cdot a_1 \cdot u_1 = k_2 \cdot a_2 \cdot u_2$$

on the left by $k_2^T$ and on the right by

$$(a_1 \cdot u_1)^{-1} = u_1^{-1} \cdot a_1^{-1}.$$

The left-hand side simplifies, using $u_1 \cdot u_1^{-1} = I$ and $a_1 \cdot a_1^{-1} = I$:

$$k_2^T \cdot k_1 \cdot a_1 \cdot u_1 \cdot u_1^{-1} \cdot a_1^{-1} = k_2^T \cdot k_1 = M.$$

The right-hand side simplifies, using $k_2^T \cdot k_2 = I$:

$$k_2^T \cdot k_2 \cdot a_2 \cdot u_2 \cdot u_1^{-1} \cdot a_1^{-1} = a_2 \cdot u_2 \cdot u_1^{-1} \cdot a_1^{-1}.$$

Hence

$$M = a_2 \cdot u_2 \cdot u_1^{-1} \cdot a_1^{-1}.$$

We now check that each of the four factors on the right is upper
triangular:

- $a_2$ is positive diagonal, hence upper triangular.
- $u_2$ is upper unipotent, hence upper triangular.
- $u_1^{-1}$ is upper unipotent (the inverse of an upper unipotent
  matrix is upper unipotent), hence upper triangular.
- $a_1^{-1}$ is positive diagonal (the inverse of a positive diagonal
  matrix is positive diagonal), hence upper triangular.

The product of upper-triangular matrices is upper triangular, so $M$
is upper triangular.

To compute the diagonal of $M$, recall that the $(i, i)$-entry of a
product of upper-triangular matrices equals the product of the
$(i, i)$-entries of the factors. Therefore

$$M_{ii} = (a_2)_{ii} \cdot (u_2)_{ii} \cdot (u_1^{-1})_{ii} \cdot (a_1^{-1})_{ii}.$$

The diagonal entries of $u_2$ and $u_1^{-1}$ are both $1$, since
both matrices are upper unipotent. The diagonal entry of $a_1^{-1}$
at position $(i, i)$ is the reciprocal of the diagonal entry of $a_1$:

$$(a_1^{-1})_{ii} = \frac{1}{(a_1)_{ii}}.$$

Hence

$$
\begin{aligned}
M_{ii}
&= (a_2)_{ii} \cdot 1 \cdot 1 \cdot \frac{ 1 }{ (a_1)_{ii} } \\
&= \frac{ (a_2)_{ii} }{ (a_1)_{ii} }.
\end{aligned}
$$

Both diagonal entries are strictly positive, since $a_1, a_2 \in A$:

$$(a_1)_{ii} > 0, \qquad (a_2)_{ii} > 0.$$

Therefore $M_{ii} > 0$ for every $i$.

### 5.4 Applying the key lemma

The matrix $M$ is orthogonal (Section 5.2), upper triangular, and
has strictly positive diagonal (Section 5.3). By the key lemma of
Section 3,

$$M = I.$$

Recalling the definition $M = k_2^T k_1$, this gives

$$k_2^T k_1 = I.$$

Multiplying on the left by $k_2$ and using $k_2 k_2^T = I$ yields

$$k_1 = k_2 k_2^T k_1 = k_2 \cdot I = k_2.$$

So $k_1 = k_2$.

### 5.5 Equality of the diagonal and unipotent factors

Cancel the common factor $k_1 = k_2$ on the left of the equation
$k_1 \cdot a_1 \cdot u_1 = k_1 \cdot a_2 \cdot u_2$. Multiplying both
sides on the left by $k_1^T$ and using $k_1^T k_1 = I$,

$$a_1 \cdot u_1 = a_2 \cdot u_2.$$

Multiply both sides on the left by $a_2^{-1}$ and on the right by
$u_1^{-1}$:

$$a_2^{-1} \cdot a_1 = u_2 \cdot u_1^{-1}.$$

The two sides of this equation have very different structural shapes:

- The **left side**, $a_2^{-1} \cdot a_1$, is a product of two
  diagonal matrices. The product of diagonal matrices is diagonal,
  so every off-diagonal entry equals zero.
- The **right side**, $u_2 \cdot u_1^{-1}$, is a product of two
  upper unipotent matrices. The product of upper unipotent matrices
  is upper unipotent, so every diagonal entry equals $1$.

Now combine the two descriptions. The matrix on the left equals the
matrix on the right, so a single matrix is simultaneously:

- diagonal (off-diagonal entries are zero), and
- upper unipotent (diagonal entries are $1$).

A matrix that is simultaneously diagonal and upper unipotent has all
off-diagonal entries equal to zero (from the first description) and
all diagonal entries equal to $1$ (from the second description).
Such a matrix is necessarily the identity.

Therefore

$$a_2^{-1} \cdot a_1 = I, \qquad u_2 \cdot u_1^{-1} = I,$$

from which

$$a_1 = a_2, \qquad u_1 = u_2.$$

This completes the uniqueness proof. $\blacksquare$

---

## 6. Conclusion

Combining the existence proof of Section 4 and the uniqueness proof
of Section 5: for every matrix $g \in M_n(\mathbb{R})$ with
$\det g \neq 0$, there exists a unique triple
$(k, a, u) \in K \times A \times N$ such that

$$g = k \cdot a \cdot u.$$

The orthogonal factor $k$ is obtained by applying Gram–Schmidt
orthonormalization to the columns of $g$ and assembling the result
into a matrix; the positive diagonal factor $a$ records the norms of
the Gram–Schmidt vectors; and the upper unipotent factor $u$ records
the coefficients that express each column of $g$ in terms of the
preceding orthonormalized columns. Uniqueness follows from the
observation that the only matrix that is simultaneously orthogonal,
upper triangular, and has strictly positive diagonal is the identity.

This is the **Iwasawa decomposition** for $GL_n(\mathbb{R})$.

---

## Formalization in Lean

The proof above is fully formalized in Lean 4 (with Mathlib) in the
companion file [`Iwasawa.lean`](Iwasawa.lean). It compiles with no
`sorry`, and the main theorems depend only on Lean's three standard
foundational axioms (`propext`, `Classical.choice`, `Quot.sound`).

Each section of this document corresponds to declarations in that file:

| Document | Lean declaration(s) |
| --- | --- |
| §1 Three subgroups | `IsOrthogonal`, `IsPositiveDiagonal`, `IsUpperUnipotent` |
| §2 Statement | `IwasawaFactorization`, `iwasawaDecomposition` |
| §3 Key lemma | `orthogonal_upperTriangular_posDiag_eq_one` |
| §4 Existence | `qMat`, `dMat`, `uMat`, `exists_iwasawa` |
| §5 Uniqueness | `iwasawa_unique` |
| §6 Conclusion | `iwasawaDecomposition` |

### The declarations in code

The listings below show the central definitions and the statements of
the main results, lightly trimmed (proof bodies and field docstrings
live in the source file). They line up with the sections above.

**§1, the three subgroups.** Each is a predicate on matrices, matching
the set definitions in Section 1 one for one.

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

**§2, the factorization data and the theorem.** An
`IwasawaFactorization g` bundles the three factors together with their
defining properties and the equation `g = k * a * u`.

```lean
structure IwasawaFactorization (g : Matrix (Fin n) (Fin n) ℝ) where
  k : Matrix (Fin n) (Fin n) ℝ
  a : Matrix (Fin n) (Fin n) ℝ
  u : Matrix (Fin n) (Fin n) ℝ
  k_orthogonal : IsOrthogonal k
  a_positiveDiagonal : IsPositiveDiagonal a
  u_upperUnipotent : IsUpperUnipotent u
  factorization : g = k * a * u
```

The main theorem says that for invertible `g` this triple exists and is
unique, using Lean's unique existence quantifier `∃!`.

```lean
theorem iwasawaDecomposition (g : Matrix (Fin n) (Fin n) ℝ) (hg : g.det ≠ 0) :
    ∃! (kau : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ ×
              Matrix (Fin n) (Fin n) ℝ),
      IsOrthogonal kau.1 ∧ IsPositiveDiagonal kau.2.1 ∧ IsUpperUnipotent kau.2.2 ∧
      g = kau.1 * kau.2.1 * kau.2.2
```

**§3, the key lemma.** The single fact that makes the factorization
rigid.

```lean
lemma orthogonal_upperTriangular_posDiag_eq_one
    {M : Matrix (Fin n) (Fin n) ℝ}
    (hOrth : IsOrthogonal M)
    (hUT : IsUpperTriangular M)
    (hPos : ∀ i, 0 < M i i) :
    M = 1
```

**§4, the existence construction.** A column of `g` is read into
`EuclideanSpace`; the orthogonal factor `qMat` has the Gram-Schmidt
vectors as its columns; and `rMat` records the inner products
`⟨eᵢ, g⁽ʲ⁾⟩`, so that `rMat g = (qMat g)ᵀ * g`.

```lean
noncomputable def gCol (g : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j => g j i)

noncomputable def qMat (g : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun j i => gsCol g i j

noncomputable def rMat (g : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => @inner ℝ _ _ (gsCol g i) (gCol g j)
```

Splitting `R` into its diagonal `dMat` and the unipotent remainder
`uMat` yields the other two factors.

```lean
noncomputable def dMat (g : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = j then rMat g i i else 0

noncomputable def uMat (g : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  diagInv (dMat g) * rMat g
```

These assemble into a concrete `IwasawaFactorization`. The `where` block
is exactly the checklist from Section 4.5: each field discharges one
requirement, and `exists_iwasawa` simply asserts the result is inhabited.

```lean
noncomputable def iwasawa {g : Matrix (Fin n) (Fin n) ℝ} (hg : g.det ≠ 0) :
    IwasawaFactorization g where
  k := qMat g
  a := dMat g
  u := uMat g
  k_orthogonal := qMat_orthogonal hg
  a_positiveDiagonal := dMat_isPositiveDiagonal hg
  u_upperUnipotent := uMat_isUpperUnipotent hg
  factorization := by
    rw [Matrix.mul_assoc]
    rw [dMat_mul_uMat hg]
    exact g_eq_Q_mul_R hg

theorem exists_iwasawa (g : Matrix (Fin n) (Fin n) ℝ) (hg : g.det ≠ 0) :
    Nonempty (IwasawaFactorization g) :=
  ⟨iwasawa hg⟩
```

**§5, uniqueness.** Stated on the bundled structure: any two
factorizations of the same `g` have equal components.

```lean
theorem iwasawa_unique {g : Matrix (Fin n) (Fin n) ℝ}
    (F G : IwasawaFactorization g) :
    F.k = G.k ∧ F.a = G.a ∧ F.u = G.u
```

### Building and checking

The toolchain is pinned in `lean-toolchain` (Lean `v4.30.0-rc1`). From
the directory containing `lakefile.toml`:

```sh
lake exe cache get   # download the prebuilt Mathlib cache
lake build           # elaborate and check Iwasawa.lean
```

A successful `lake build` is a complete machine verification of every
claim made above.

### Notes on the formalization

The mathematics here is classical (it is Lang's proof), so the work of
this project is the formalization. A few choices and obstacles are worth
recording, since none of them appears in the textbook.

**Subgroups as predicates, not bundled structures.** Membership in $K$,
$A$, $N$ is expressed by plain predicates (`IsOrthogonal`,
`IsPositiveDiagonal`, `IsUpperUnipotent`) rather than Mathlib `Subgroup`
objects. This keeps the statements elementary and avoids carrying group
structure the proof never uses; the price is that the closure facts
(identity, products, inverses) are proved by hand.

**Columns live in `EuclideanSpace`.** Gram-Schmidt in Mathlib needs an
inner product space, and the bare type `Fin n → ℝ` does not carry the
$\ell^2$ inner product. Each column is therefore mapped into
`EuclideanSpace ℝ (Fin n)` (which is `PiLp 2`) by `gCol`, and linear
independence of the columns has to be transported across the
`WithLp.linearEquiv` (in `gCol_linearIndependent`). This step is
invisible on paper but unavoidable in Lean.

**A computable diagonal inverse.** Mathlib's `M⁻¹` is defined through the
adjugate and is awkward to compute with. Rather than fight it, the file
defines `diagInv M`, the diagonal matrix of reciprocals, proves it is a
genuine two sided inverse for positive diagonal matrices, and only later
identifies it with `M⁻¹` (`matInv_eq_diagInv`). The existence factor is
then the clean expression `uMat g = diagInv (dMat g) * rMat g`.

**Definitions are total, so degenerate cases must be dispatched.** The
normalized column `gsCol` divides by the norm of the unnormalized
Gram-Schmidt vector, so the proof that `rMat g i i` equals that norm
(`rMat_diag`) still has to handle the zero vector case, even though
linear independence later rules it out. The case cannot be skipped: the
definitional equation has to hold before `det g ≠ 0` is ever assumed.

**Upper triangularity via `BlockTriangular`.** `IsUpperTriangular` is
defined as `Matrix.BlockTriangular M id`, which buys the closure and
inverse lemmas (`Matrix.BlockTriangular.mul`,
`blockTriangular_inv_of_blockTriangular`) directly from Mathlib, at the
cost of a slightly indirect encoding that surfaces as the `id i < id i`
contradictions in a few proofs.

**Left inverse equals right inverse.** For square matrices a one sided
inverse is automatically two sided (`mul_eq_one_comm`). This small fact
is used repeatedly: to turn `Qᵀ Q = I` into `Q Qᵀ = I`, to obtain
`M⁻¹ = Mᵀ` in the key lemma, and in `IsOrthogonal.transpose`.

**Steps the paper asserts and Lean has to prove.** Several one line
claims in the informal argument expand into real work. "Since
`det g ≠ 0` the columns are independent" becomes `gCol_linearIndependent`;
"the diagonal entry of a product of upper triangular matrices is the
product of the diagonal entries" becomes the explicit `hdiag1`, `hdiag2`,
`hdiag3` peeling inside `iwasawa_unique`; and "the product sum collapses
to a single term" is the recurring `Finset.sum_eq_single` pattern.

The load bearing Mathlib results are the Gram-Schmidt API
(`gramSchmidtNormed_orthonormal`, `gramSchmidt_def'`,
`gramSchmidt_orthogonal`, `gramSchmidt_inv_triangular`,
`gramSchmidt_ne_zero`), `Matrix.linearIndependent_cols_of_det_ne_zero`,
the block triangular lemmas above together with
`Matrix.det_of_upperTriangular`, and `mul_eq_one_comm` with
`Matrix.inv_eq_left_inv`.

---

## Reference

S. Lang, *Linear Algebra*, 3rd edition. Springer Undergraduate Texts
in Mathematics, 1987. (Appendix II, "Iwasawa Decomposition and
Others.")
