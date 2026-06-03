/-
Iwasawa decomposition of GLₙ(ℝ). Math 157 final project.

Author: Jiho Lee (CuteSurtr)

Sole author; all contributions are the author's own.
-/
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The Iwasawa Decomposition of GLₙ(ℝ)

A Lean formalization of the Iwasawa decomposition for the real general
linear group: every invertible `n × n` real matrix factors uniquely as
`g = k * a * u`, where `k` is orthogonal, `a` is positive diagonal, and
`u` is upper unipotent. The proof follows Lang, *Linear Algebra*
(3rd ed., 1987, Appendix II).

See `README.md` for the full mathematical exposition. Section numbers in
the comments below refer to that document.

## Main results

* `orthogonal_upperTriangular_posDiag_eq_one` (README §3): an orthogonal,
  upper triangular matrix with strictly positive diagonal is the identity.
* `exists_iwasawa` (README §4): existence of the factorization, by
  Gram-Schmidt on the columns of `g`.
* `iwasawa_unique` (README §5): uniqueness of the factorization.
* `iwasawaDecomposition` (README §6, stated in §2): combined existence and uniqueness,
  packaged as a unique existence statement.
-/

namespace Iwasawa

open Matrix

variable {n : ℕ}

/-! ### §1. The three subgroups K, A, N

The Iwasawa factorization splits `g ∈ GLₙ(ℝ)` into factors from three
distinguished subgroups: the orthogonal group `K`, the positive diagonal
group `A`, and the upper unipotent group `N`. We encode membership in
each subgroup as a predicate on matrices.
-/

/-- `M` is upper triangular: every entry strictly below the diagonal is
zero. Implemented via `Matrix.BlockTriangular` with the identity ordering
on `Fin n`. -/
def IsUpperTriangular (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Matrix.BlockTriangular M (id : Fin n → Fin n)

/-- `M` is upper unipotent (`M ∈ N` in the README): upper triangular and
every diagonal entry equals `1`. -/
def IsUpperUnipotent (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsUpperTriangular M ∧ ∀ i, M i i = 1

/-- `M` is positive diagonal (`M ∈ A` in the README): off diagonal entries
vanish and the diagonal entries are strictly positive. -/
def IsPositiveDiagonal (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, i ≠ j → M i j = 0) ∧ ∀ i, 0 < M i i

/-- `M` is orthogonal (`M ∈ K` in the README): `M * Mᵀ = I`. -/
def IsOrthogonal (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  M * Mᵀ = 1

/-- The identity matrix is upper triangular. -/
lemma IsUpperTriangular.one : IsUpperTriangular (1 : Matrix (Fin n) (Fin n) ℝ) := by
  -- A below-diagonal entry has `j < i`; the goal is `(1 : Matrix) i j = 0`.
  intro i j hij
  simp only [Matrix.one_apply]
  -- The identity vanishes off the diagonal, so it suffices to rule out `i = j`.
  rw [if_neg]
  intro h
  subst h
  -- `i = j` would contradict `j < i`.
  exact absurd hij (lt_irrefl _)

/-- The identity matrix is upper unipotent. -/
lemma IsUpperUnipotent.one : IsUpperUnipotent (1 : Matrix (Fin n) (Fin n) ℝ) :=
  ⟨IsUpperTriangular.one, fun _ => by simp⟩

/-- The identity matrix is positive diagonal. -/
lemma IsPositiveDiagonal.one : IsPositiveDiagonal (1 : Matrix (Fin n) (Fin n) ℝ) :=
  ⟨fun _ _ hij => by simp [hij], fun _ => by simp⟩

/-- The identity matrix is orthogonal. -/
lemma IsOrthogonal.one : IsOrthogonal (1 : Matrix (Fin n) (Fin n) ℝ) := by
  unfold IsOrthogonal; simp

/-- The product of two upper triangular matrices is upper triangular.
A direct application of `Matrix.BlockTriangular.mul`. -/
lemma IsUpperTriangular.mul {M N : Matrix (Fin n) (Fin n) ℝ}
    (hM : IsUpperTriangular M) (hN : IsUpperTriangular N) :
    IsUpperTriangular (M * N) :=
  Matrix.BlockTriangular.mul hM hN

/-- The product of two positive diagonal matrices is positive diagonal:
the off diagonal entries vanish because every summand carries a zero
factor, and the diagonal entries multiply to give a product of two
strictly positive reals. -/
lemma IsPositiveDiagonal.mul {M N : Matrix (Fin n) (Fin n) ℝ}
    (hM : IsPositiveDiagonal M) (hN : IsPositiveDiagonal N) :
    IsPositiveDiagonal (M * N) := by
  refine ⟨?_, ?_⟩
  -- Off-diagonal (`i ≠ j`): every term `M i k * N k j` of the product-sum
  -- vanishes, as either `M i k = 0` (when `k ≠ i`) or `N k j = 0` (when `k = i`,
  -- using `i ≠ j`).
  · intro i j hij
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hki : k = i
    · subst hki
      rw [hN.1 k j hij, mul_zero]
    · rw [hM.1 i k (Ne.symm hki), zero_mul]
  -- Diagonal: the sum collapses to the single term `M i i * N i i`, a product
  -- of two positive reals.
  · intro i
    rw [Matrix.mul_apply]
    rw [show (∑ k, M i k * N k i) = M i i * N i i from ?_]
    · exact mul_pos (hM.2 i) (hN.2 i)
    · rw [Finset.sum_eq_single i]
      · intro k _ hk
        rw [hM.1 i k (Ne.symm hk), zero_mul]
      · intro h; exact absurd (Finset.mem_univ i) h

/-- The product of two upper unipotent matrices is upper unipotent. Upper
triangularity comes from `IsUpperTriangular.mul`; the diagonal of the
product at `(i, i)` collapses to `M i i * N i i = 1 * 1 = 1`. -/
lemma IsUpperUnipotent.mul {M N : Matrix (Fin n) (Fin n) ℝ}
    (hM : IsUpperUnipotent M) (hN : IsUpperUnipotent N) :
    IsUpperUnipotent (M * N) := by
  -- Upper triangularity is inherited from the factors; only the unit diagonal
  -- needs a separate check.
  refine ⟨hM.1.mul hN.1, ?_⟩
  intro i
  rw [Matrix.mul_apply]
  -- The diagonal sum collapses to `M i i * N i i = 1 * 1 = 1`.
  rw [show (∑ k, M i k * N k i) = M i i * N i i from ?_]
  · rw [hM.2 i, hN.2 i, mul_one]
  -- Every off-diagonal term drops: `N k i = 0` above the diagonal (`i < k`),
  -- and `M i k = 0` below it (`k < i`, obtained from `¬ i < k` and `k ≠ i`).
  · rw [Finset.sum_eq_single i]
    · intro k _ hk
      by_cases h : i < k
      · rw [hN.1 h, mul_zero]
      · push Not at h
        have h_lt : k < i := lt_of_le_of_ne h hk
        rw [hM.1 h_lt, zero_mul]
    · intro habs; exact absurd (Finset.mem_univ i) habs

/-- The determinant of an orthogonal matrix squares to `1`, since
`(det M)² = det M * det Mᵀ = det (M * Mᵀ) = det I = 1`. -/
lemma IsOrthogonal.det_sq {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : IsOrthogonal M) : (M.det) ^ 2 = 1 := by
  have h := congrArg Matrix.det hM
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  rw [sq]; exact h

/-- An orthogonal matrix has nonzero determinant. In particular, every
orthogonal matrix lies in `GLₙ(ℝ)`. -/
lemma IsOrthogonal.det_ne_zero {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : IsOrthogonal M) : M.det ≠ 0 := by
  intro h
  have h2 := hM.det_sq
  rw [h] at h2
  norm_num at h2

/-! ### The naive diagonal inverse `diagInv`

`diagInv M` is the matrix that is diagonal and whose `(i, i)` entry is
`(M i i)⁻¹`. This is *not* the matrix inverse `M⁻¹` in general, but it
does coincide with `M⁻¹` whenever `M` is itself diagonal with nonzero
diagonal entries. We use this construction below to build the upper
unipotent factor `u = (diagInv (dMat g)) * (rMat g)`.
-/

/-- The naive diagonal inverse of a matrix `M`: the diagonal matrix whose
`(i, i)` entry is `(M i i)⁻¹`. -/
noncomputable def diagInv (M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = j then (M i i)⁻¹ else 0

/-- Diagonal entry of `diagInv M` at position `(i, i)`. -/
@[simp] lemma diagInv_diag (M : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    diagInv M i i = (M i i)⁻¹ := by simp [diagInv]

/-- Off diagonal entries of `diagInv M` are zero. -/
lemma diagInv_off_diag {M : Matrix (Fin n) (Fin n) ℝ} {i j : Fin n} (h : i ≠ j) :
    diagInv M i j = 0 := by simp [diagInv, h]

/-- For positive diagonal `M`, `diagInv M` is a left inverse of `M`:
`diagInv M * M = I`. -/
lemma IsPositiveDiagonal.diagInv_mul_self {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : IsPositiveDiagonal M) : diagInv M * M = 1 := by
  ext i j
  -- `diagInv M` is diagonal, so only the `k = i` term survives the product-sum,
  -- leaving `(M i i)⁻¹ * M i j`.
  rw [Matrix.mul_apply,
      Finset.sum_eq_single i
        (fun k _ hk => by rw [diagInv_off_diag (Ne.symm hk), zero_mul])
        (fun habs => absurd (Finset.mem_univ i) habs),
      diagInv_diag]
  -- On the diagonal: `(M i i)⁻¹ * M i i = 1`; off the diagonal: `M i j = 0`.
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq, inv_mul_cancel₀ (ne_of_gt (hM.2 i))]
  · rw [Matrix.one_apply_ne hij, hM.1 i j hij, mul_zero]

/-- For positive diagonal `M`, `diagInv M` is a right inverse of `M`:
`M * diagInv M = I`. -/
lemma IsPositiveDiagonal.self_mul_diagInv {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : IsPositiveDiagonal M) : M * diagInv M = 1 := by
  ext i j
  -- Symmetric to the previous lemma: only the `k = j` term survives, leaving
  -- `M i j * (M j j)⁻¹`.
  rw [Matrix.mul_apply,
      Finset.sum_eq_single j
        (fun k _ hk => by rw [diagInv_off_diag hk, mul_zero])
        (fun habs => absurd (Finset.mem_univ j) habs),
      diagInv_diag]
  -- On the diagonal: `M i i * (M i i)⁻¹ = 1`; off the diagonal: `M i j = 0`.
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq, mul_inv_cancel₀ (ne_of_gt (hM.2 i))]
  · rw [Matrix.one_apply_ne hij, hM.1 i j hij, zero_mul]

/-- `diagInv` preserves positive diagonality: if `M` is positive diagonal
then so is `diagInv M`, because the reciprocal of a positive real is
again positive. -/
lemma IsPositiveDiagonal.isPositiveDiagonal_diagInv {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : IsPositiveDiagonal M) : IsPositiveDiagonal (diagInv M) := by
  refine ⟨fun _ _ hij => diagInv_off_diag hij, fun i => ?_⟩
  rw [diagInv_diag]; exact inv_pos.mpr (hM.2 i)

/-! ### §2. The `IwasawaFactorization` structure

The data of an Iwasawa factorization of a matrix `g`: a triple
`(k, a, u)` with `k` orthogonal, `a` positive diagonal, and `u` upper
unipotent, together with a proof that `g = k * a * u`. The main theorems
below show that this structure is inhabited and that any two inhabitants
are equal whenever `det g ≠ 0`.
-/

/-- An Iwasawa factorization of a matrix `g`: a triple `(k, a, u)` such
that `k` is orthogonal, `a` is positive diagonal, `u` is upper unipotent,
and `g = k * a * u`. -/
structure IwasawaFactorization (g : Matrix (Fin n) (Fin n) ℝ) where
  /-- The orthogonal factor, `k ∈ K`. -/
  k : Matrix (Fin n) (Fin n) ℝ
  /-- The positive diagonal factor, `a ∈ A`. -/
  a : Matrix (Fin n) (Fin n) ℝ
  /-- The upper unipotent factor, `u ∈ N`. -/
  u : Matrix (Fin n) (Fin n) ℝ
  /-- `k` is orthogonal. -/
  k_orthogonal : IsOrthogonal k
  /-- `a` is positive diagonal. -/
  a_positiveDiagonal : IsPositiveDiagonal a
  /-- `u` is upper unipotent. -/
  u_upperUnipotent : IsUpperUnipotent u
  /-- The three factors multiply back to `g`. -/
  factorization : g = k * a * u

namespace IwasawaFactorization

variable {g : Matrix (Fin n) (Fin n) ℝ}

/-- The trivial Iwasawa factorization of the identity matrix: all three
factors `k`, `a`, `u` are equal to the identity. -/
def one : IwasawaFactorization (1 : Matrix (Fin n) (Fin n) ℝ) where
  k := 1
  a := 1
  u := 1
  k_orthogonal := IsOrthogonal.one
  a_positiveDiagonal := IsPositiveDiagonal.one
  u_upperUnipotent := IsUpperUnipotent.one
  factorization := by simp

end IwasawaFactorization

open scoped InnerProductSpace
open InnerProductSpace

/-! ### §4.1 and §4.2. Gram-Schmidt and the orthogonal factor `Q`

The existence argument starts by running Gram-Schmidt on the columns of
`g`. The orthonormal family produced is then assembled into the
orthogonal matrix `Q = qMat g`, and the change of basis matrix
`R = rMat g = Qᵀ * g` is shown to be upper triangular with strictly
positive diagonal.
-/

/-- Column `i` of the matrix `g`, viewed as a vector in
`EuclideanSpace ℝ (Fin n)` (so the standard `ℓ²` inner product applies). -/
noncomputable def gCol (g : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j => g j i)

/-- The Gram-Schmidt normalized column of `g` at index `i`. In the
notation of README §4.1, this is the vector `eᵢ`. -/
noncomputable def gsCol (g : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    EuclideanSpace ℝ (Fin n) :=
  gramSchmidtNormed ℝ (gCol g) i

/-- The orthogonal matrix `Q` of README §4.2: column `i` of `Q` is the
Gram-Schmidt normalized vector `gsCol g i = eᵢ`. -/
noncomputable def qMat (g : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun j i => gsCol g i j

/-- The matrix `R` of README §4.3, with entries
`R_{ij} = ⟨eᵢ, g^{(j)}⟩` (the inner product of Gram-Schmidt column `i`
with column `j` of `g`). -/
noncomputable def rMat (g : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => @inner ℝ _ _ (gsCol g i) (gCol g j)

/-- The inner product on `EuclideanSpace ℝ (Fin n)` unfolds to the
coordinatewise sum `⟨x, y⟩ = ∑ k, x k * y k`. -/
lemma inner_eq_sum (x y : EuclideanSpace ℝ (Fin n)) :
    @inner ℝ _ _ x y = ∑ k, x k * y k := by
  -- Unfold the `ℓ²` inner product; over `ℝ` conjugation is the identity, so
  -- each summand is simply `x k * y k`.
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  show y.ofLp k * (starRingEnd ℝ) (x.ofLp k) = x.ofLp k * y.ofLp k
  rw [RCLike.conj_to_real]; ring

/-- If `det g ≠ 0`, the columns of `g`, viewed in `EuclideanSpace ℝ (Fin n)`,
are linearly independent. This is the input to Gram-Schmidt. -/
lemma gCol_linearIndependent {g : Matrix (Fin n) (Fin n) ℝ} (hg : g.det ≠ 0) :
    LinearIndependent ℝ (gCol g) := by
  -- `det g ≠ 0` makes the columns independent in the plain function space.
  have h := Matrix.linearIndependent_cols_of_det_ne_zero hg
  -- Transport that independence along the linear equivalence to
  -- `EuclideanSpace`, which changes the norm but not the linear structure.
  let e : (Fin n → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) := (WithLp.linearEquiv 2 ℝ _).symm
  have h2 : LinearIndependent ℝ (fun i => e (g.col i)) :=
    h.map' e.toLinearMap (LinearEquiv.ker e)
  convert h2 using 1

/-- If `det g ≠ 0`, the Gram-Schmidt normalized columns of `g` form an
orthonormal family. -/
lemma gsCol_orthonormal {g : Matrix (Fin n) (Fin n) ℝ} (hg : g.det ≠ 0) :
    Orthonormal ℝ (gsCol g) :=
  gramSchmidtNormed_orthonormal (gCol_linearIndependent hg)

/-- `Q = qMat g` is orthogonal whenever `det g ≠ 0` (README §4.2). The
proof first establishes `Qᵀ Q = I` using orthonormality of the columns,
then flips to `Q Qᵀ = I` via `mul_eq_one_comm`. -/
lemma qMat_orthogonal {g : Matrix (Fin n) (Fin n) ℝ} (hg : g.det ≠ 0) :
    IsOrthogonal (qMat g) := by
  have hortho := gsCol_orthonormal hg
  -- First establish `Qᵀ Q = I`: its `(i, j)` entry is `⟨eᵢ, eⱼ⟩`, which is `1`
  -- on the diagonal and `0` off it, by orthonormality of the columns.
  have hTQ : (qMat g)ᵀ * qMat g = 1 := by
    ext i j
    rw [Matrix.mul_apply]
    -- Identify the matrix-product entry with the coordinate sum for `⟨eᵢ, eⱼ⟩`.
    have hsum : ∑ k, (qMat g)ᵀ i k * qMat g k j = ∑ k, gsCol g i k * gsCol g j k := by
      apply Finset.sum_congr rfl
      intros k _
      simp [qMat, Matrix.transpose_apply]
    rw [hsum]
    have hinner : @inner ℝ _ _ (gsCol g i) (gsCol g j) = ∑ k, gsCol g i k * gsCol g j k :=
      inner_eq_sum _ _
    rw [← hinner]
    rcases eq_or_ne i j with rfl | hne
    · -- Diagonal: `⟨eᵢ, eᵢ⟩ = ‖eᵢ‖ * ‖eᵢ‖ = 1`.
      rw [Matrix.one_apply_eq]
      have hii : ‖gsCol g i‖ = 1 := hortho.1 i
      rw [real_inner_self_eq_norm_mul_norm, hii, mul_one]
    · -- Off-diagonal: distinct orthonormal vectors are orthogonal.
      rw [Matrix.one_apply_ne hne]
      exact hortho.2 hne
  -- For a square matrix a left inverse is also a right inverse, so `Qᵀ Q = I`
  -- upgrades to `Q Qᵀ = I`, i.e. `Q` is orthogonal.
  unfold IsOrthogonal
  exact mul_eq_one_comm.mp hTQ

/-- The definitional identity `R = Qᵀ * g`: each entry of `Qᵀ * g`
unfolds to the inner product `⟨eᵢ, g^{(j)}⟩`. -/
lemma rMat_eq_QT_mul_g (g : Matrix (Fin n) (Fin n) ℝ) :
    rMat g = (qMat g)ᵀ * g := by
  ext i j
  rw [Matrix.mul_apply]
  -- The `(i, j)` entry of `Qᵀ g` is the coordinate sum defining `⟨eᵢ, g⁽ʲ⁾⟩`.
  rw [show (∑ k, (qMat g)ᵀ i k * g k j) = ∑ k, gsCol g i k * gCol g j k from ?_]
  · exact (inner_eq_sum (gsCol g i) (gCol g j))
  · apply Finset.sum_congr rfl
    intros k _
    simp [qMat, Matrix.transpose_apply, gCol]

/-- The recovery identity `g = Q * R`. Combined with the splitting
`R = a * u` below, this produces the existence factorization
`g = Q * a * u`. -/
lemma g_eq_Q_mul_R {g : Matrix (Fin n) (Fin n) ℝ} (hg : g.det ≠ 0) :
    g = qMat g * rMat g := by
  -- Rewrite `R = Qᵀ g`, then cancel `Q Qᵀ = I` on the left of `Q (Qᵀ g)`.
  rw [rMat_eq_QT_mul_g, ← Matrix.mul_assoc]
  rw [(qMat_orthogonal hg : qMat g * (qMat g)ᵀ = 1)]
  rw [Matrix.one_mul]

/-- Below the diagonal, `R = rMat g` vanishes: `R i j = 0` whenever
`j < i`. The vector `eᵢ` is orthogonal to all `eₖ` with `k < i` by
Gram-Schmidt, and `g^{(j)}` lies in the span of `e₁, …, e_j`; for
`j < i` this forces the inner product to vanish. -/
lemma rMat_lowerTriangular_zero (g : Matrix (Fin n) (Fin n) ℝ)
    {i j : Fin n} (hij : j < i) : rMat g i j = 0 := by
  -- `R i j = ⟨eᵢ, g⁽ʲ⁾⟩`; peel off the normalization scalar in `eᵢ`.
  unfold rMat gsCol gramSchmidtNormed
  rw [inner_smul_left]
  -- Gram-Schmidt orthogonalizes `ẽᵢ` against the earlier columns `g⁽ʲ⁾` (`j < i`).
  have h0 : @inner ℝ _ _ (gramSchmidt ℝ (gCol g) i) (gCol g j) = 0 :=
    gramSchmidt_inv_triangular ℝ (gCol g) hij
  rw [h0]
  simp

/-- The diagonal entry `R_{ii}` equals the norm
`‖gramSchmidt ℝ (gCol g) i‖` of the *unnormalized* Gram-Schmidt vector
`tilde eᵢ`. This is the explicit formula derived in README §4.3
(positivity step). -/
lemma rMat_diag (g : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    rMat g i i = ‖gramSchmidt ℝ (gCol g) i‖ := by
  unfold rMat gsCol gramSchmidtNormed
  rw [inner_smul_left]

  have hexpand : gCol g i = gramSchmidt ℝ (gCol g) i +
      ∑ k ∈ Finset.Iio i, (Submodule.starProjection (ℝ ∙ gramSchmidt ℝ (gCol g) k)) (gCol g i) := by
    exact gramSchmidt_def' ℝ (gCol g) i
  rw [hexpand]
  rw [inner_add_right]
  rw [inner_sum]

  rw [@real_inner_self_eq_norm_mul_norm]

  have hzero : ∀ k ∈ Finset.Iio i,
      @inner ℝ _ _ (gramSchmidt ℝ (gCol g) i)
        (Submodule.starProjection (ℝ ∙ gramSchmidt ℝ (gCol g) k) (gCol g i)) = 0 := by
    intros k hk
    rw [Submodule.starProjection_singleton]
    rw [inner_smul_right]
    have hki : k < i := Finset.mem_Iio.mp hk
    have : @inner ℝ _ _ (gramSchmidt ℝ (gCol g) i) (gramSchmidt ℝ (gCol g) k) = 0 :=
      gramSchmidt_orthogonal ℝ _ hki.ne'
    rw [this, mul_zero]
  rw [Finset.sum_eq_zero hzero, add_zero]

  show (‖gramSchmidt ℝ (gCol g) i‖ : ℝ)⁻¹ *
      (‖gramSchmidt ℝ (gCol g) i‖ * ‖gramSchmidt ℝ (gCol g) i‖) = _
  by_cases hzero : gramSchmidt ℝ (gCol g) i = 0
  · simp [hzero]
  · field_simp

/-- For `det g ≠ 0`, the diagonal entries of `R` are strictly positive.
Each unnormalized Gram-Schmidt vector `tilde eᵢ` is nonzero by linear
independence of the columns, so its norm is strictly positive. -/
lemma rMat_diag_pos {g : Matrix (Fin n) (Fin n) ℝ} (hg : g.det ≠ 0) (i : Fin n) :
    0 < rMat g i i := by
  rw [rMat_diag g]
  rw [norm_pos_iff]
  exact gramSchmidt_ne_zero i (gCol_linearIndependent hg)

/-- `R = rMat g` is upper triangular: every entry strictly below the
diagonal is zero. -/
lemma rMat_isUpperTriangular (g : Matrix (Fin n) (Fin n) ℝ) :
    IsUpperTriangular (rMat g) := by
  intros i j hij

  exact rMat_lowerTriangular_zero g hij

/-! ### §4.4. Splitting `R = a * u`

We split the upper triangular matrix `R = rMat g` into its diagonal part
`a = dMat g` and an upper unipotent residual `u = uMat g`, so that
`R = a * u`.
-/

/-- The diagonal matrix `a = dMat g` of README §4.4: same diagonal as
`R`, zero elsewhere. -/
noncomputable def dMat (g : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = j then rMat g i i else 0

/-- The upper unipotent factor `u = uMat g = a⁻¹ * R` of README §4.4. -/
noncomputable def uMat (g : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  diagInv (dMat g) * rMat g

/-- Diagonal entry of `dMat g`: equals `R_{ii}`. -/
lemma dMat_diag (g : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    dMat g i i = rMat g i i := by simp [dMat]

/-- Off diagonal entries of `dMat g` are zero. -/
lemma dMat_off_diag {g : Matrix (Fin n) (Fin n) ℝ} {i j : Fin n} (h : i ≠ j) :
    dMat g i j = 0 := by simp [dMat, h]

/-- For `det g ≠ 0`, the diagonal matrix `dMat g` is positive diagonal,
since the diagonal of `R` is strictly positive. -/
lemma dMat_isPositiveDiagonal {g : Matrix (Fin n) (Fin n) ℝ} (hg : g.det ≠ 0) :
    IsPositiveDiagonal (dMat g) :=
  ⟨fun _ _ hij => dMat_off_diag hij, fun i => by rw [dMat_diag]; exact rMat_diag_pos hg i⟩

/-- The splitting equation `a * u = R`: `dMat g * uMat g = rMat g`. -/
lemma dMat_mul_uMat {g : Matrix (Fin n) (Fin n) ℝ} (hg : g.det ≠ 0) :
    dMat g * uMat g = rMat g := by
  -- `u = (diagInv a) R`, so `a * u = (a * diagInv a) * R = I * R = R`.
  unfold uMat
  rw [← Matrix.mul_assoc]
  rw [(dMat_isPositiveDiagonal hg).self_mul_diagInv]
  rw [Matrix.one_mul]

/-- `uMat g` is upper triangular, being the product of a diagonal matrix
(hence upper triangular) and the upper triangular matrix `R`. -/
lemma uMat_isUpperTriangular (g : Matrix (Fin n) (Fin n) ℝ) :
    IsUpperTriangular (uMat g) := by
  -- `u = (diagInv a) R` is a product of two upper triangular matrices: the
  -- diagonal `diagInv a` and the already-upper-triangular `R`.
  unfold uMat
  refine IsUpperTriangular.mul ?_ (rMat_isUpperTriangular g)
  -- `diagInv a` is upper triangular since its off-diagonal entries vanish.
  intros i j hij
  apply diagInv_off_diag
  intro h
  exact absurd (h ▸ hij : id i < id i) (lt_irrefl _)

/-- The diagonal entries of `uMat g` are all `1`: the diagonal of
`diagInv a * R` at position `(i, i)` evaluates to
`(R_{ii})⁻¹ * R_{ii} = 1`. -/
lemma uMat_diag {g : Matrix (Fin n) (Fin n) ℝ} (hg : g.det ≠ 0) (i : Fin n) :
    uMat g i i = 1 := by
  unfold uMat
  rw [Matrix.mul_apply]
  -- `diagInv a` is diagonal, so the `(i, i)` entry of `(diagInv a) R` is the
  -- single term `(R i i)⁻¹ * R i i = 1`.
  rw [Finset.sum_eq_single i]
  · rw [diagInv_diag, dMat_diag]
    rw [inv_mul_cancel₀ (ne_of_gt (rMat_diag_pos hg i))]
  · intros k _ hk
    rw [diagInv_off_diag (Ne.symm hk), zero_mul]
  · intros habs
    exact absurd (Finset.mem_univ i) habs

/-- `uMat g` is upper unipotent: upper triangular with unit diagonal. -/
lemma uMat_isUpperUnipotent {g : Matrix (Fin n) (Fin n) ℝ} (hg : g.det ≠ 0) :
    IsUpperUnipotent (uMat g) :=
  ⟨uMat_isUpperTriangular g, uMat_diag hg⟩

/-! ### §4.5. Assembling the existence factorization -/

/-- The explicit Iwasawa factorization of an invertible `g`, bundling
`(k, a, u) = (qMat g, dMat g, uMat g)` together with the proofs that each
factor has the required form and that `g = k * a * u`. -/
noncomputable def iwasawa {g : Matrix (Fin n) (Fin n) ℝ} (hg : g.det ≠ 0) :
    IwasawaFactorization g where
  k := qMat g
  a := dMat g
  u := uMat g
  k_orthogonal := qMat_orthogonal hg
  a_positiveDiagonal := dMat_isPositiveDiagonal hg
  u_upperUnipotent := uMat_isUpperUnipotent hg
  factorization := by
    -- `Q * a * u = Q * (a * u) = Q * R = g`.
    rw [Matrix.mul_assoc]
    rw [dMat_mul_uMat hg]
    exact g_eq_Q_mul_R hg

/-- **Existence (README §4).** Every matrix `g` with `det g ≠ 0` admits
at least one Iwasawa factorization. -/
theorem exists_iwasawa (g : Matrix (Fin n) (Fin n) ℝ) (hg : g.det ≠ 0) :
    Nonempty (IwasawaFactorization g) :=
  ⟨iwasawa hg⟩

/-! ### Determinant and inverse properties

A small toolkit of additional facts about the three subgroups, used in
the uniqueness argument: determinants of `A` and `N`, inverses of `K`,
`A`, `N`, and the embedding of `A` into the upper triangular matrices.
-/

/-- The determinant of an upper unipotent matrix is `1`: it is the
product of the diagonal entries of an upper triangular matrix, and every
diagonal entry equals `1`. -/
lemma IsUpperUnipotent.det {U : Matrix (Fin n) (Fin n) ℝ} (hU : IsUpperUnipotent U) :
    U.det = 1 := by
  -- The determinant of an upper triangular matrix is the product of its
  -- diagonal, and here every diagonal entry is `1`.
  rw [Matrix.det_of_upperTriangular hU.1]
  apply Finset.prod_eq_one
  intros i _
  exact hU.2 i

/-- An upper unipotent matrix has nonzero determinant, hence is
invertible. -/
lemma IsUpperUnipotent.det_ne_zero {U : Matrix (Fin n) (Fin n) ℝ} (hU : IsUpperUnipotent U) :
    U.det ≠ 0 := by
  rw [hU.det]
  exact one_ne_zero

/-- A positive diagonal matrix is upper triangular: its only nonzero
entries lie on the diagonal. -/
lemma IsPositiveDiagonal.isUpperTriangular {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : IsPositiveDiagonal D) : IsUpperTriangular D := by
  -- A below-diagonal entry has `i ≠ j`, exactly where the diagonal matrix vanishes.
  intros i j hij
  apply hD.1
  intro h
  exact absurd (h ▸ hij : id j < id j) (lt_irrefl _)

/-- The determinant of a positive diagonal matrix is strictly positive,
being a product of strictly positive reals. -/
lemma IsPositiveDiagonal.det_pos {D : Matrix (Fin n) (Fin n) ℝ} (hD : IsPositiveDiagonal D) :
    0 < D.det := by
  -- The determinant is the product of the (strictly positive) diagonal entries.
  rw [Matrix.det_of_upperTriangular hD.isUpperTriangular]
  exact Finset.prod_pos (fun i _ => hD.2 i)

/-- The matrix inverse of an upper unipotent matrix is upper unipotent.
Upper triangularity is `blockTriangular_inv_of_blockTriangular`; the
diagonal entries of the inverse are forced to be `1` by examining the
diagonal of `U * U⁻¹ = I`. -/
lemma IsUpperUnipotent.inv {U : Matrix (Fin n) (Fin n) ℝ} (hU : IsUpperUnipotent U) :
    IsUpperUnipotent U⁻¹ := by
  -- `U` is invertible because its determinant is `1`.
  letI : Invertible U := U.invertibleOfIsUnitDet (Ne.isUnit hU.det_ne_zero)
  -- The inverse of an upper triangular matrix is upper triangular.
  have hUT : IsUpperTriangular U⁻¹ := blockTriangular_inv_of_blockTriangular hU.1
  refine ⟨hUT, ?_⟩
  -- It remains to show each diagonal entry of `U⁻¹` is `1`; read it off the
  -- `(i, i)` entry of `U * U⁻¹ = I`.
  intro i
  have hUUinv : U * U⁻¹ = 1 := Matrix.mul_inv_of_invertible U
  have hUUinv_ii : (U * U⁻¹) i i = 1 := by rw [hUUinv]; simp
  rw [Matrix.mul_apply] at hUUinv_ii
  -- Off the diagonal each term `U i k * U⁻¹ k i` vanishes: `U i k = 0` below the
  -- diagonal (`k < i`), and `U⁻¹ k i = 0` above it (`i < k`).
  have honly : ∀ k ∈ (Finset.univ : Finset (Fin n)) \ {i}, U i k * U⁻¹ k i = 0 := by
    intros k hk
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hk
    rcases lt_or_gt_of_ne hk.2 with hki | hki
    · rw [hU.1 hki, zero_mul]
    · rw [hUT hki, mul_zero]
  -- So the sum collapses to the lone diagonal term `U i i * U⁻¹ i i`.
  have hcontract : ∑ k, U i k * U⁻¹ k i = U i i * U⁻¹ i i := by
    rw [show (Finset.univ : Finset (Fin n)) = {i} ∪ (Finset.univ \ {i}) by
      ext x; simp]
    rw [Finset.sum_union (by simp)]
    rw [Finset.sum_singleton, Finset.sum_eq_zero honly, add_zero]
  -- Since `U i i = 1`, the identity `U i i * U⁻¹ i i = 1` forces `U⁻¹ i i = 1`.
  rw [hcontract, hU.2 i, one_mul] at hUUinv_ii
  exact hUUinv_ii

/-- The matrix inverse of a positive diagonal matrix coincides with the
naive `diagInv`. -/
lemma IsPositiveDiagonal.matInv_eq_diagInv {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : IsPositiveDiagonal D) : D⁻¹ = diagInv D := by
  apply Matrix.inv_eq_left_inv
  exact hD.diagInv_mul_self

/-- The matrix inverse of a positive diagonal matrix is positive
diagonal. -/
lemma IsPositiveDiagonal.matInv {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : IsPositiveDiagonal D) : IsPositiveDiagonal D⁻¹ := by
  rw [hD.matInv_eq_diagInv]
  exact hD.isPositiveDiagonal_diagInv

/-! ### §3. The key lemma -/

/-- **Key lemma (README §3).** A matrix that is simultaneously orthogonal,
upper triangular, and has strictly positive diagonal must be the identity.

Sketch: from `M Mᵀ = I` we have `M⁻¹ = Mᵀ`. The inverse of an upper
triangular matrix is upper triangular, so `Mᵀ` is upper triangular, i.e.
`M` is lower triangular. Combined with the hypothesis that `M` is upper
triangular, `M` is diagonal. Then `M_{ii}² = 1` together with `M_{ii} > 0`
forces `M_{ii} = 1`, so `M = I`. -/
lemma orthogonal_upperTriangular_posDiag_eq_one
    {M : Matrix (Fin n) (Fin n) ℝ}
    (hOrth : IsOrthogonal M)
    (hUT : IsUpperTriangular M)
    (hPos : ∀ i, 0 < M i i) :
    M = 1 := by

  -- `M` is invertible (orthogonal ⇒ nonzero determinant), with `M⁻¹ = Mᵀ`.
  have hdet : M.det ≠ 0 := hOrth.det_ne_zero
  letI : Invertible M := M.invertibleOfIsUnitDet (Ne.isUnit hdet)
  have hMinv : M⁻¹ = Mᵀ := by
    apply Matrix.inv_eq_left_inv
    exact mul_eq_one_comm.mpr hOrth
  -- The inverse of an upper triangular matrix is upper triangular, so `Mᵀ` is
  -- upper triangular too; equivalently `M` is *lower* triangular.
  have hMinv_UT : IsUpperTriangular M⁻¹ := blockTriangular_inv_of_blockTriangular hUT
  have hMt_UT : IsUpperTriangular Mᵀ := hMinv ▸ hMinv_UT
  have hM_LT : ∀ ⦃i j⦄, i < j → M i j = 0 := by
    intros i j hij
    have : Mᵀ j i = 0 := hMt_UT hij
    simpa using this
  -- Upper triangular together with lower triangular ⇒ `M` is diagonal.
  have hDiag : ∀ ⦃i j⦄, i ≠ j → M i j = 0 := by
    intros i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hM_LT h
    · exact hUT h
  -- Prove `M = 1` entrywise.
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · -- Diagonal: the `(i, i)` entry of `M Mᵀ = I` says `∑ₖ (M i k)² = 1`.
    have hii : (M * Mᵀ) i i = 1 := by rw [hOrth]; simp
    rw [Matrix.mul_apply] at hii
    have hsum : ∑ k, M i k * M i k = 1 := by
      have hh : ∑ k, M i k * Mᵀ k i = ∑ k, M i k * M i k := by
        apply Finset.sum_congr rfl
        intros k _
        rfl
      rw [hh] at hii
      exact hii
    -- `M` is diagonal, so the sum collapses to the single term `M i i * M i i`.
    have honly : ∀ k ∈ (Finset.univ : Finset (Fin n)) \ {i}, M i k * M i k = 0 := by
      intros k hk
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hk
      rw [hDiag (Ne.symm hk.2), zero_mul]
    have hcontract : ∑ k, M i k * M i k = M i i * M i i := by
      rw [show (Finset.univ : Finset (Fin n)) = {i} ∪ (Finset.univ \ {i}) by
        ext x; simp]
      rw [Finset.sum_union (by simp)]
      rw [Finset.sum_singleton, Finset.sum_eq_zero honly, add_zero]
    rw [hcontract] at hsum
    -- `(M i i)² = 1` with `M i i > 0` forces `M i i = 1`.
    have hMi := hPos i
    have : M i i = 1 := by nlinarith
    rw [this, Matrix.one_apply_eq]
  · -- Off the diagonal both `M i j` and `(1) i j` are `0`.
    rw [hDiag hij, Matrix.one_apply_ne hij]

/-! ### Auxiliary uniqueness lemmas -/

/-- If `a * u = a'` where `a, a'` are positive diagonal and `u` is upper
unipotent, then `a = a'` and `u = 1`. This is the structural step in
README §5.5: comparing entries of `a * u` against the diagonal `a'` pins
down both factors. -/
lemma posDiag_mul_upperUnip_eq_diag_iff
    {a a' u : Matrix (Fin n) (Fin n) ℝ}
    (ha : IsPositiveDiagonal a) (ha' : IsPositiveDiagonal a')
    (hu : IsUpperUnipotent u)
    (h : a * u = a') : a = a' ∧ u = 1 := by

  -- Step 1: `a = a'`. Compare entries of `a * u = a'` by trichotomy on `(i, j)`.
  have h_eq_diag : a = a' := by
    ext i j
    have h_ij := congrFun (congrFun h i) j
    rcases lt_trichotomy i j with hlt | heq | hgt
    · -- Above the diagonal both diagonal matrices `a, a'` vanish.
      rw [ha.1 i j (ne_of_lt hlt)]
      rw [ha'.1 i j (ne_of_lt hlt)]
    · -- On the diagonal `(a * u) i i = a i i * u i i = a i i`, equal to `a' i i`.
      subst heq
      rw [Matrix.mul_apply] at h_ij
      rw [Finset.sum_eq_single i] at h_ij
      · rw [hu.2 i, mul_one] at h_ij
        exact h_ij
      · intros k _ hk
        rw [ha.1 i k (Ne.symm hk), zero_mul]
      · intro h; exact absurd (Finset.mem_univ i) h
    · -- Below the diagonal both diagonal matrices vanish again.
      rw [ha.1 i j (ne_of_gt hgt), ha'.1 i j (ne_of_gt hgt)]
  refine ⟨h_eq_diag, ?_⟩
  -- Step 2: `u = 1`. Compare entries of `a * u = a'` once more.
  ext i j
  have h_ij := congrFun (congrFun h i) j
  rcases lt_trichotomy i j with hlt | heq | hgt
  · -- Above the diagonal `a' i j = 0`; the sum gives `a i i * u i j`, and since
    -- `a i i ≠ 0` this forces `u i j = 0 = (1) i j`.
    have h_aij : a' i j = 0 := ha'.1 i j (ne_of_lt hlt)
    rw [Matrix.mul_apply] at h_ij
    rw [Finset.sum_eq_single i] at h_ij
    · rw [h_aij] at h_ij
      have ha_pos : 0 < a i i := ha.2 i
      have h_aii_ne : a i i ≠ 0 := ne_of_gt ha_pos
      have huij_zero : u i j = 0 := by
        have h_ij_eq : a i i * u i j = 0 := h_ij
        rcases mul_eq_zero.mp h_ij_eq with h1 | h2
        · exact absurd h1 h_aii_ne
        · exact h2
      rw [huij_zero, Matrix.one_apply_ne (ne_of_lt hlt)]
    · intros k _ hk
      rw [ha.1 i k (Ne.symm hk), zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  · -- On the diagonal `u i i = 1` (upper unipotent).
    subst heq; rw [hu.2 i, Matrix.one_apply_eq]
  · -- Below the diagonal `u i j = 0` (upper triangular).
    rw [hu.1 hgt, Matrix.one_apply_ne (ne_of_gt hgt)]

/-! ### §5. Uniqueness of the factorization -/

/-- **Uniqueness (README §5).** Two Iwasawa factorizations of the same
matrix have equal components.

Proof outline (matching README §5.1 to §5.5):

* §5.1: introduce the auxiliary matrix `M := k₂ᵀ * k₁`.
* §5.2: show `M` is orthogonal.
* §5.3: show `M` is upper triangular with strictly positive diagonal,
  using the rewrite `M = a₂ * u₂ * u₁⁻¹ * a₁⁻¹` and closure of the
  upper triangular property under multiplication.
* §5.4: apply the key lemma to deduce `M = I`, hence `k₁ = k₂`.
* §5.5: cancel `k₁ = k₂` and apply `posDiag_mul_upperUnip_eq_diag_iff`
  to conclude `a₁ = a₂` and `u₁ = u₂`. -/
theorem iwasawa_unique {g : Matrix (Fin n) (Fin n) ℝ}
    (F G : IwasawaFactorization g) :
    F.k = G.k ∧ F.a = G.a ∧ F.u = G.u := by
  obtain ⟨k₁, a₁, u₁, hk₁, ha₁, hu₁, hf₁⟩ := F
  obtain ⟨k₂, a₂, u₂, hk₂, ha₂, hu₂, hf₂⟩ := G

  -- The two factorizations of `g` agree: `k₁ a₁ u₁ = k₂ a₂ u₂`.
  have heq : k₁ * a₁ * u₁ = k₂ * a₂ * u₂ := hf₁.symm.trans hf₂
  -- `u₁` and `a₁` are invertible (nonzero determinant); needed for the algebra.
  letI : Invertible u₁ := u₁.invertibleOfIsUnitDet (Ne.isUnit hu₁.det_ne_zero)
  letI : Invertible a₁ := a₁.invertibleOfIsUnitDet (Ne.isUnit (ne_of_gt ha₁.det_pos))
  -- §5.1: introduce the auxiliary matrix `M := k₂ᵀ k₁`.
  set M : Matrix (Fin n) (Fin n) ℝ := k₂ᵀ * k₁ with hM_def
  -- §5.2: `M Mᵀ = k₂ᵀ (k₁ k₁ᵀ) k₂ = k₂ᵀ k₂ = I`, so `M` is orthogonal.
  have hMorth : IsOrthogonal M := by
    unfold IsOrthogonal
    rw [hM_def, Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc k₁, hk₁, Matrix.one_mul]
    exact mul_eq_one_comm.mpr hk₂

  -- §5.3 (rewrite): right-multiply the factorization by `(a₁ u₁)⁻¹` and use
  -- `k₂ᵀ k₂ = I` to solve for `M = a₂ u₂ u₁⁻¹ a₁⁻¹`.
  have hM_eq : M = a₂ * u₂ * u₁⁻¹ * a₁⁻¹ := by

    have h3 : M * a₁ * u₁ = a₂ * u₂ := by
      rw [hM_def, Matrix.mul_assoc, Matrix.mul_assoc]
      have hheq2 : k₁ * (a₁ * u₁) = k₂ * (a₂ * u₂) := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, heq]
      rw [hheq2, ← Matrix.mul_assoc, mul_eq_one_comm.mpr hk₂, Matrix.one_mul]

    have h4 : M * a₁ = a₂ * u₂ * u₁⁻¹ := by
      have heq4 := congrArg (· * u₁⁻¹) h3
      simp only at heq4
      rw [Matrix.mul_assoc, Matrix.mul_inv_of_invertible, Matrix.mul_one] at heq4
      exact heq4

    have heq5 := congrArg (· * a₁⁻¹) h4
    simp only at heq5
    rw [Matrix.mul_assoc, Matrix.mul_inv_of_invertible, Matrix.mul_one] at heq5
    exact heq5

  -- §5.3 (shape): each factor of `a₂ u₂ u₁⁻¹ a₁⁻¹` is upper triangular, and that
  -- property is closed under products.
  have hM_UT : IsUpperTriangular M := by
    rw [hM_eq]
    apply IsUpperTriangular.mul
    apply IsUpperTriangular.mul
    apply IsUpperTriangular.mul
    · exact ha₂.isUpperTriangular
    · exact hu₂.1
    · exact hu₁.inv.1
    · exact ha₁.matInv.isUpperTriangular

  -- §5.3 (diagonal): `Mᵢᵢ = a₂ᵢᵢ · 1 · 1 · (a₁ᵢᵢ)⁻¹ > 0`.
  have hM_pos : ∀ i, 0 < M i i := by
    intro i
    rw [hM_eq]
    -- The diagonal of a product of upper triangular matrices is the product of
    -- the diagonal entries; peel the factors off one at a time.
    have h_diag : (a₂ * u₂ * u₁⁻¹ * a₁⁻¹) i i =
        a₂ i i * u₂ i i * u₁⁻¹ i i * a₁⁻¹ i i := by
      have h1 := hu₁.inv
      have h2 := ha₁.matInv

      have hdiag1 : (a₂ * u₂) i i = a₂ i i * u₂ i i := by
        rw [Matrix.mul_apply]
        rw [Finset.sum_eq_single i]
        · intros k _ hk
          rw [ha₂.1 i k (Ne.symm hk), zero_mul]
        · intro h; exact absurd (Finset.mem_univ i) h

      have ha₂u₂_UT : IsUpperTriangular (a₂ * u₂) :=
        IsUpperTriangular.mul ha₂.isUpperTriangular hu₂.1
      have hdiag2 : (a₂ * u₂ * u₁⁻¹) i i = (a₂ * u₂) i i * u₁⁻¹ i i := by
        rw [Matrix.mul_apply]
        rw [Finset.sum_eq_single i]
        · intros k _ hk
          rcases lt_or_gt_of_ne hk with h | h
          ·
            rw [ha₂u₂_UT h, zero_mul]
          ·
            rw [h1.1 h, mul_zero]
        · intro h; exact absurd (Finset.mem_univ i) h
      have ha₂u₂u₁_UT : IsUpperTriangular (a₂ * u₂ * u₁⁻¹) :=
        IsUpperTriangular.mul ha₂u₂_UT h1.1
      have hdiag3 : (a₂ * u₂ * u₁⁻¹ * a₁⁻¹) i i = (a₂ * u₂ * u₁⁻¹) i i * a₁⁻¹ i i := by
        rw [Matrix.mul_apply]
        rw [Finset.sum_eq_single i]
        · intros k _ hk
          rcases lt_or_gt_of_ne hk with hh | hh
          · rw [ha₂u₂u₁_UT hh, zero_mul]
          · rw [h2.isUpperTriangular hh, mul_zero]
        · intro h; exact absurd (Finset.mem_univ i) h
      rw [hdiag3, hdiag2, hdiag1]
    rw [h_diag]
    -- A product of positive numbers: `a₂ᵢᵢ > 0`, `(u₂)ᵢᵢ = (u₁⁻¹)ᵢᵢ = 1`, `(a₁⁻¹)ᵢᵢ > 0`.
    apply mul_pos
    apply mul_pos
    apply mul_pos
    · exact ha₂.2 i
    · rw [hu₂.2 i]; exact one_pos
    · rw [hu₁.inv.2 i]; exact one_pos
    · exact ha₁.matInv.2 i

  -- §5.4: the key lemma applies to `M`, forcing `M = I`.
  have hM_one : M = 1 := orthogonal_upperTriangular_posDiag_eq_one hMorth hM_UT hM_pos
  -- §5.4: `k₂ᵀ k₁ = I` left-multiplied by `k₂` (with `k₂ k₂ᵀ = I`) gives `k₁ = k₂`.
  have hk_eq : k₁ = k₂ := by
    have h : k₂ᵀ * k₁ = 1 := hM_one

    have hc := congrArg (k₂ * ·) h
    simp only at hc
    rw [← Matrix.mul_assoc, hk₂, Matrix.one_mul, Matrix.mul_one] at hc
    exact hc

  -- §5.5: cancel the common factor `k₁ = k₂` on the left to get `a₁ u₁ = a₂ u₂`.
  have hau_eq : a₁ * u₁ = a₂ * u₂ := by
    have h := heq
    rw [hk_eq] at h

    letI : Invertible k₂ := k₂.invertibleOfIsUnitDet (Ne.isUnit hk₂.det_ne_zero)
    have := congrArg (k₂⁻¹ * ·) h
    simp only at this
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc] at this
    rw [Matrix.inv_mul_of_invertible, Matrix.one_mul, Matrix.one_mul] at this
    exact this

  letI : Invertible a₂ := a₂.invertibleOfIsUnitDet (Ne.isUnit (ne_of_gt ha₂.det_pos))

  -- §5.5: set `U := u₂ u₁⁻¹` (upper unipotent); from `a₁ u₁ = a₂ u₂` we get `a₂ U = a₁`,
  -- a "positive diagonal = positive diagonal × unipotent" equation.
  set U : Matrix (Fin n) (Fin n) ℝ := u₂ * u₁⁻¹ with hU_def
  have hU_unip : IsUpperUnipotent U := IsUpperUnipotent.mul hu₂ hu₁.inv
  have ha₂U_eq_a₁ : a₂ * U = a₁ := by

    have := congrArg (· * u₁⁻¹) hau_eq
    simp only at this
    rw [Matrix.mul_assoc, Matrix.mul_inv_of_invertible, Matrix.mul_one] at this
    rw [hU_def, ← Matrix.mul_assoc]
    exact this.symm
  -- The structural lemma pins down both factors: `a₂ = a₁` and `U = 1`.
  obtain ⟨ha_eq, hU_one⟩ := posDiag_mul_upperUnip_eq_diag_iff ha₂ ha₁ hU_unip ha₂U_eq_a₁
  -- `U = u₂ u₁⁻¹ = 1` right-multiplied by `u₁` gives `u₁ = u₂`.
  have hu_eq : u₁ = u₂ := by
    have h := hU_one
    rw [hU_def] at h
    have := congrArg (· * u₁) h
    simp only at this
    rw [Matrix.mul_assoc, Matrix.inv_mul_of_invertible, Matrix.mul_one, Matrix.one_mul] at this
    exact this.symm
  exact ⟨hk_eq, ha_eq.symm, hu_eq⟩

/-! ### §6. The main decomposition theorem -/

/-- **Iwasawa decomposition (README §6).** For every matrix `g` with
`det g ≠ 0`, there is a *unique* triple `(k, a, u) ∈ K × A × N` such that
`g = k * a * u`. -/
theorem iwasawaDecomposition (g : Matrix (Fin n) (Fin n) ℝ) (hg : g.det ≠ 0) :
    ∃! (kau : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ ×
              Matrix (Fin n) (Fin n) ℝ),
      IsOrthogonal kau.1 ∧ IsPositiveDiagonal kau.2.1 ∧ IsUpperUnipotent kau.2.2 ∧
      g = kau.1 * kau.2.1 * kau.2.2 := by
  -- Existence: the explicit Gram-Schmidt triple `(Q, a, u)` is a witness.
  refine ⟨(qMat g, dMat g, uMat g), ?_, ?_⟩
  · refine ⟨qMat_orthogonal hg, dMat_isPositiveDiagonal hg, uMat_isUpperUnipotent hg, ?_⟩
    show g = qMat g * dMat g * uMat g
    rw [Matrix.mul_assoc, dMat_mul_uMat hg]
    exact g_eq_Q_mul_R hg
  -- Uniqueness: any other valid triple packages as an `IwasawaFactorization`,
  -- so `iwasawa_unique` identifies it with the explicit one.
  · intro ⟨k', a', u'⟩ ⟨hk', ha', hu', hg'⟩
    let G : IwasawaFactorization g := ⟨k', a', u', hk', ha', hu', hg'⟩
    let F : IwasawaFactorization g := iwasawa hg
    obtain ⟨hk_eq, ha_eq, hu_eq⟩ := iwasawa_unique F G
    exact Prod.ext hk_eq.symm (Prod.ext ha_eq.symm hu_eq.symm)

/-! ### Axiom audit

The four headline results reduce to Lean's three standard foundational
axioms only. The `#print axioms` commands below make `lake build` report
that dependency, so the claim in the README is checked by the build
rather than only asserted. -/
#print axioms iwasawaDecomposition
#print axioms exists_iwasawa
#print axioms iwasawa_unique
#print axioms orthogonal_upperTriangular_posDiag_eq_one

end Iwasawa
