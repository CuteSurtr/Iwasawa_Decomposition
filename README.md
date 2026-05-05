# The Iwasawa Decomposition of $GL_n(\mathbb{R})$

This document records a complete proof of the Iwasawa decomposition
for the real general linear group $GL_n(\mathbb{R})$: every invertible
$n \times n$ real matrix factors uniquely as the product of an
orthogonal matrix, a positive diagonal matrix, and an upper-triangular
matrix with ones on the diagonal. The proof follows the one given by
Lang in *Linear Algebra* (3rd edition, 1987, Appendix II).

The exposition is organized into six sections:

1. Notation and the three subgroups involved.
2. The statement of the theorem.
3. The key lemma on which the uniqueness argument turns.
4. The existence proof, by Gram–Schmidt orthonormalization of the
   columns of the matrix.
5. The uniqueness proof, by reduction to the key lemma.
6. A short conclusion summarizing the result.

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

## Reference

S. Lang, *Linear Algebra*, 3rd edition. Springer Undergraduate Texts
in Mathematics, 1987. (Appendix II, "Iwasawa Decomposition and
Others.")
