import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Iwasawa

open Matrix

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {n : ℕ}

/-- A matrix is **upper triangular** iff entries below the diagonal vanish. -/
def IsUpperTriangular (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Matrix.BlockTriangular M (id : Fin n → Fin n)

/-- A matrix is **upper unipotent** iff it is upper triangular and has 1's
    on the diagonal. -/
def IsUpperUnipotent (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsUpperTriangular M ∧ ∀ i, M i i = 1

/-- A matrix is **positive diagonal** iff it is diagonal with strictly
    positive entries. -/
def IsPositiveDiagonal (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, i ≠ j → M i j = 0) ∧ ∀ i, 0 < M i i

/-- A matrix is **orthogonal** iff `M Mᵀ = 1`. (Mathlib's
    `Matrix.orthogonalGroup` is the corresponding group.) -/
def IsOrthogonal (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  M * Mᵀ = 1

lemma IsUpperTriangular.one : IsUpperTriangular (1 : Matrix (Fin n) (Fin n) ℝ) := sorry

lemma IsUpperUnipotent.one : IsUpperUnipotent (1 : Matrix (Fin n) (Fin n) ℝ) := sorry

lemma IsPositiveDiagonal.one : IsPositiveDiagonal (1 : Matrix (Fin n) (Fin n) ℝ) := sorry

lemma IsOrthogonal.one : IsOrthogonal (1 : Matrix (Fin n) (Fin n) ℝ) := sorry

lemma IsUpperTriangular.mul {M N : Matrix (Fin n) (Fin n) ℝ}
    (hM : IsUpperTriangular M) (hN : IsUpperTriangular N) :
    IsUpperTriangular (M * N) := sorry

lemma IsPositiveDiagonal.mul {M N : Matrix (Fin n) (Fin n) ℝ}
    (hM : IsPositiveDiagonal M) (hN : IsPositiveDiagonal N) :
    IsPositiveDiagonal (M * N) := sorry

lemma IsUpperUnipotent.mul {M N : Matrix (Fin n) (Fin n) ℝ}
    (hM : IsUpperUnipotent M) (hN : IsUpperUnipotent N) :
    IsUpperUnipotent (M * N) := sorry

lemma IsOrthogonal.transpose {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : IsOrthogonal M) : IsOrthogonal Mᵀ := sorry

lemma IsOrthogonal.det_sq {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : IsOrthogonal M) : (M.det) ^ 2 = 1 := sorry

lemma IsOrthogonal.det_ne_zero {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : IsOrthogonal M) : M.det ≠ 0 := sorry

/-- Inverse of a positive diagonal matrix (entrywise reciprocal). -/
noncomputable def diagInv (M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = j then (M i i)⁻¹ else 0

@[simp] lemma diagInv_diag (M : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    diagInv M i i = (M i i)⁻¹ := by simp [diagInv]

lemma diagInv_off_diag {M : Matrix (Fin n) (Fin n) ℝ} {i j : Fin n} (h : i ≠ j) :
    diagInv M i j = 0 := sorry

lemma IsPositiveDiagonal.diagInv_mul_self {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : IsPositiveDiagonal M) : diagInv M * M = 1 := sorry

lemma IsPositiveDiagonal.self_mul_diagInv {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : IsPositiveDiagonal M) : M * diagInv M = 1 := sorry

lemma IsPositiveDiagonal.isPositiveDiagonal_diagInv {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : IsPositiveDiagonal M) : IsPositiveDiagonal (diagInv M) := sorry

/-- An Iwasawa factorization of `g`: `g = k · a · u` with `k` orthogonal,
    `a` positive diagonal, and `u` upper unipotent. -/
structure IwasawaFactorization (g : Matrix (Fin n) (Fin n) ℝ) where
  /-- Orthogonal component. -/
  k : Matrix (Fin n) (Fin n) ℝ
  /-- Positive diagonal component. -/
  a : Matrix (Fin n) (Fin n) ℝ
  /-- Upper unipotent component (`n` in classical notation, `u` here to
      avoid collision with the dimension). -/
  u : Matrix (Fin n) (Fin n) ℝ
  k_orthogonal : IsOrthogonal k
  a_positiveDiagonal : IsPositiveDiagonal a
  u_upperUnipotent : IsUpperUnipotent u
  /-- The factorization equation `g = k a u`. -/
  factorization : g = k * a * u

namespace IwasawaFactorization

variable {g : Matrix (Fin n) (Fin n) ℝ}

/-- The trivial factorization of the identity. -/
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

/-- The columns of `g`, viewed as vectors in `EuclideanSpace ℝ (Fin n)`. -/
noncomputable def gCol (g : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j => g j i)

/-- The Gram–Schmidt orthonormalized columns. -/
noncomputable def gsCol (g : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    EuclideanSpace ℝ (Fin n) :=
  gramSchmidtNormed ℝ (gCol g) i

/-- The orthogonal matrix `Q`: column `i` is the `i`-th orthonormal vector. -/
noncomputable def qMat (g : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun j i => gsCol g i j

/-- The upper-triangular matrix `R = Qᵀ · g`. -/
noncomputable def rMat (g : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => @inner ℝ _ _ (gsCol g i) (gCol g j)

/-- Inner product on `EuclideanSpace ℝ (Fin n)` is the dot product. -/
lemma inner_eq_sum (x y : EuclideanSpace ℝ (Fin n)) :
    @inner ℝ _ _ x y = ∑ k, x k * y k := sorry

/-- Linear independence of columns from `det g ≠ 0`, transferred to `gCol`. -/
lemma gCol_linearIndependent {g : Matrix (Fin n) (Fin n) ℝ} (hg : g.det ≠ 0) :
    LinearIndependent ℝ (gCol g) := sorry

/-- The Gram-Schmidt-normalized columns are orthonormal. -/
lemma gsCol_orthonormal {g : Matrix (Fin n) (Fin n) ℝ} (hg : g.det ≠ 0) :
    Orthonormal ℝ (gsCol g) := sorry

/-- The matrix `Q` is orthogonal: `Q · Qᵀ = 1`. -/
lemma qMat_orthogonal {g : Matrix (Fin n) (Fin n) ℝ} (hg : g.det ≠ 0) :
    IsOrthogonal (qMat g) := sorry

/-- The matrix entry `R i j = Qᵀ g`. -/
lemma rMat_eq_QT_mul_g (g : Matrix (Fin n) (Fin n) ℝ) :
    rMat g = (qMat g)ᵀ * g := sorry

/-- `g = Q · R`. -/
lemma g_eq_Q_mul_R {g : Matrix (Fin n) (Fin n) ℝ} (hg : g.det ≠ 0) :
    g = qMat g * rMat g := sorry

/-- Off-diagonal upper-triangular property of `R`. -/
lemma rMat_lowerTriangular_zero (g : Matrix (Fin n) (Fin n) ℝ)
    {i j : Fin n} (hij : j < i) : rMat g i j = 0 := sorry

/-- Diagonal of `R` equals `‖gramSchmidt v i‖`. -/
lemma rMat_diag (g : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    rMat g i i = ‖gramSchmidt ℝ (gCol g) i‖ := sorry

/-- Diagonal of `R` is positive. -/
lemma rMat_diag_pos {g : Matrix (Fin n) (Fin n) ℝ} (hg : g.det ≠ 0) (i : Fin n) :
    0 < rMat g i i := sorry

/-- `R` is upper triangular. -/
lemma rMat_isUpperTriangular (g : Matrix (Fin n) (Fin n) ℝ) :
    IsUpperTriangular (rMat g) := sorry

/-- The positive diagonal matrix `D` extracted from `R`. -/
noncomputable def dMat (g : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = j then rMat g i i else 0

/-- The upper unipotent matrix `U = D⁻¹ · R`. -/
noncomputable def uMat (g : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  diagInv (dMat g) * rMat g

lemma dMat_diag (g : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    dMat g i i = rMat g i i := sorry

lemma dMat_off_diag {g : Matrix (Fin n) (Fin n) ℝ} {i j : Fin n} (h : i ≠ j) :
    dMat g i j = 0 := sorry

lemma dMat_isPositiveDiagonal {g : Matrix (Fin n) (Fin n) ℝ} (hg : g.det ≠ 0) :
    IsPositiveDiagonal (dMat g) := sorry

/-- `D · U = R`, i.e. multiplying `D` on the left of `D⁻¹R` recovers `R`. -/
lemma dMat_mul_uMat {g : Matrix (Fin n) (Fin n) ℝ} (hg : g.det ≠ 0) :
    dMat g * uMat g = rMat g := sorry

/-- `U` is upper triangular: it's the product of two upper-triangular matrices. -/
lemma uMat_isUpperTriangular (g : Matrix (Fin n) (Fin n) ℝ) :
    IsUpperTriangular (uMat g) := sorry

/-- `U` has 1's on the diagonal. -/
lemma uMat_diag {g : Matrix (Fin n) (Fin n) ℝ} (hg : g.det ≠ 0) (i : Fin n) :
    uMat g i i = 1 := sorry

/-- `U` is upper unipotent. -/
lemma uMat_isUpperUnipotent {g : Matrix (Fin n) (Fin n) ℝ} (hg : g.det ≠ 0) :
    IsUpperUnipotent (uMat g) := sorry

/-- The Iwasawa factorization. -/
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

/-- **Existence of the Iwasawa factorization**: every invertible real matrix factors as
    `g = k · a · u` with `k` orthogonal, `a` positive diagonal, `u` upper unipotent. -/
theorem exists_iwasawa (g : Matrix (Fin n) (Fin n) ℝ) (hg : g.det ≠ 0) :
    Nonempty (IwasawaFactorization g) := sorry

/-- The determinant of an upper unipotent matrix is 1. -/
lemma IsUpperUnipotent.det {U : Matrix (Fin n) (Fin n) ℝ} (hU : IsUpperUnipotent U) :
    U.det = 1 := sorry

/-- An upper unipotent matrix is invertible. -/
lemma IsUpperUnipotent.det_ne_zero {U : Matrix (Fin n) (Fin n) ℝ} (hU : IsUpperUnipotent U) :
    U.det ≠ 0 := sorry

/-- A positive diagonal matrix is upper triangular. -/
lemma IsPositiveDiagonal.isUpperTriangular {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : IsPositiveDiagonal D) : IsUpperTriangular D := sorry

/-- The determinant of a positive diagonal matrix is positive. -/
lemma IsPositiveDiagonal.det_pos {D : Matrix (Fin n) (Fin n) ℝ} (hD : IsPositiveDiagonal D) :
    0 < D.det := sorry

/-- The inverse of an upper unipotent matrix is upper unipotent. -/
lemma IsUpperUnipotent.inv {U : Matrix (Fin n) (Fin n) ℝ} (hU : IsUpperUnipotent U) :
    IsUpperUnipotent U⁻¹ := sorry

/-- The inverse of a positive diagonal matrix (in the Mathlib `Matrix` inverse sense)
    equals the entrywise reciprocal `diagInv`. -/
lemma IsPositiveDiagonal.matInv_eq_diagInv {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : IsPositiveDiagonal D) : D⁻¹ = diagInv D := sorry

/-- The inverse of a positive diagonal matrix is positive diagonal. -/
lemma IsPositiveDiagonal.matInv {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : IsPositiveDiagonal D) : IsPositiveDiagonal D⁻¹ := sorry

/-- The inverse of an orthogonal matrix equals its transpose. -/
lemma IsOrthogonal.matInv_eq_transpose {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : IsOrthogonal Q) : Q⁻¹ = Qᵀ := sorry

/-- Key uniqueness lemma: an orthogonal upper-triangular matrix with positive
    diagonal entries equals the identity matrix.
    Proof sketch: orthogonality gives `Mᵀ = M⁻¹` since `M Mᵀ = 1`. The inverse
    of an upper-triangular invertible matrix is upper-triangular, so `Mᵀ` is
    upper-triangular. But `Mᵀ` is also lower-triangular (transpose of upper).
    Hence `M` is diagonal. Combined with `M_{ii}² = 1` (orthogonality of rows)
    and positivity, `M = I`. -/
lemma orthogonal_upperTriangular_posDiag_eq_one
    {M : Matrix (Fin n) (Fin n) ℝ}
    (hOrth : IsOrthogonal M)
    (hUT : IsUpperTriangular M)
    (hPos : ∀ i, 0 < M i i) :
    M = 1 := sorry

/-- A matrix that is both upper unipotent and positive diagonal is the identity. -/
lemma upperUnipotent_inter_positiveDiagonal_eq_one
    {M : Matrix (Fin n) (Fin n) ℝ}
    (hUU : IsUpperUnipotent M) (hPD : IsPositiveDiagonal M) :
    M = 1 := sorry

/-- The product of a positive diagonal and an upper unipotent matrix equals
    a positive diagonal matrix iff the upper unipotent factor is the identity. -/
lemma posDiag_mul_upperUnip_eq_diag_iff
    {a a' u : Matrix (Fin n) (Fin n) ℝ}
    (ha : IsPositiveDiagonal a) (ha' : IsPositiveDiagonal a')
    (hu : IsUpperUnipotent u)
    (h : a * u = a') : a = a' ∧ u = 1 := sorry

/-- **Uniqueness of the Iwasawa factorization**: any two factorizations of the same matrix
    have equal components. -/
theorem iwasawa_unique {g : Matrix (Fin n) (Fin n) ℝ}
    (F G : IwasawaFactorization g) :
    F.k = G.k ∧ F.a = G.a ∧ F.u = G.u := sorry

/-- **The Iwasawa decomposition for `GL_n(ℝ)`**: every invertible real matrix admits a
    unique factorization `g = k · a · u` with `k` orthogonal, `a` positive diagonal,
    and `u` upper unipotent. -/
theorem iwasawaDecomposition (g : Matrix (Fin n) (Fin n) ℝ) (hg : g.det ≠ 0) :
    ∃! (kau : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ ×
              Matrix (Fin n) (Fin n) ℝ),
      IsOrthogonal kau.1 ∧ IsPositiveDiagonal kau.2.1 ∧ IsUpperUnipotent kau.2.2 ∧
      g = kau.1 * kau.2.1 * kau.2.2 := sorry

end Iwasawa
