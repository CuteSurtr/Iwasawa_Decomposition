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

def IsUpperTriangular (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Matrix.BlockTriangular M (id : Fin n → Fin n)

def IsUpperUnipotent (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsUpperTriangular M ∧ ∀ i, M i i = 1

def IsPositiveDiagonal (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, i ≠ j → M i j = 0) ∧ ∀ i, 0 < M i i

def IsOrthogonal (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  M * Mᵀ = 1

lemma IsUpperTriangular.one : IsUpperTriangular (1 : Matrix (Fin n) (Fin n) ℝ) := by
  intro i j hij
  simp only [Matrix.one_apply]
  rw [if_neg]
  intro h
  subst h
  exact absurd hij (lt_irrefl _)

lemma IsUpperUnipotent.one : IsUpperUnipotent (1 : Matrix (Fin n) (Fin n) ℝ) :=
  ⟨IsUpperTriangular.one, fun _ => by simp⟩

lemma IsPositiveDiagonal.one : IsPositiveDiagonal (1 : Matrix (Fin n) (Fin n) ℝ) :=
  ⟨fun _ _ hij => by simp [hij], fun _ => by simp⟩

lemma IsOrthogonal.one : IsOrthogonal (1 : Matrix (Fin n) (Fin n) ℝ) := by
  unfold IsOrthogonal; simp

lemma IsUpperTriangular.mul {M N : Matrix (Fin n) (Fin n) ℝ}
    (hM : IsUpperTriangular M) (hN : IsUpperTriangular N) :
    IsUpperTriangular (M * N) :=
  Matrix.BlockTriangular.mul hM hN

lemma IsPositiveDiagonal.mul {M N : Matrix (Fin n) (Fin n) ℝ}
    (hM : IsPositiveDiagonal M) (hN : IsPositiveDiagonal N) :
    IsPositiveDiagonal (M * N) := by
  refine ⟨?_, ?_⟩
  · intro i j hij
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hki : k = i
    · subst hki
      rw [hN.1 k j hij, mul_zero]
    · rw [hM.1 i k (Ne.symm hki), zero_mul]
  · intro i
    rw [Matrix.mul_apply]
    rw [show (∑ k, M i k * N k i) = M i i * N i i from ?_]
    · exact mul_pos (hM.2 i) (hN.2 i)
    · rw [Finset.sum_eq_single i]
      · intro k _ hk
        rw [hM.1 i k (Ne.symm hk), zero_mul]
      · intro h; exact absurd (Finset.mem_univ i) h

lemma IsUpperUnipotent.mul {M N : Matrix (Fin n) (Fin n) ℝ}
    (hM : IsUpperUnipotent M) (hN : IsUpperUnipotent N) :
    IsUpperUnipotent (M * N) := by
  refine ⟨hM.1.mul hN.1, ?_⟩
  intro i
  rw [Matrix.mul_apply]
  rw [show (∑ k, M i k * N k i) = M i i * N i i from ?_]
  · rw [hM.2 i, hN.2 i, mul_one]
  · rw [Finset.sum_eq_single i]
    · intro k _ hk
      by_cases h : i < k
      · rw [hN.1 h, mul_zero]
      · push Not at h
        have h_lt : k < i := lt_of_le_of_ne h hk
        rw [hM.1 h_lt, zero_mul]
    · intro habs; exact absurd (Finset.mem_univ i) habs

lemma IsOrthogonal.transpose {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : IsOrthogonal M) : IsOrthogonal Mᵀ := by
  unfold IsOrthogonal at hM ⊢
  rw [Matrix.transpose_transpose]
  exact (mul_eq_one_comm.mp hM)

lemma IsOrthogonal.det_sq {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : IsOrthogonal M) : (M.det) ^ 2 = 1 := by
  have h := congrArg Matrix.det hM
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  rw [sq]; exact h

lemma IsOrthogonal.det_ne_zero {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : IsOrthogonal M) : M.det ≠ 0 := by
  intro h
  have h2 := hM.det_sq
  rw [h] at h2
  norm_num at h2

noncomputable def diagInv (M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = j then (M i i)⁻¹ else 0

@[simp] lemma diagInv_diag (M : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    diagInv M i i = (M i i)⁻¹ := by simp [diagInv]

lemma diagInv_off_diag {M : Matrix (Fin n) (Fin n) ℝ} {i j : Fin n} (h : i ≠ j) :
    diagInv M i j = 0 := by simp [diagInv, h]

lemma IsPositiveDiagonal.diagInv_mul_self {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : IsPositiveDiagonal M) : diagInv M * M = 1 := by
  ext i j
  rw [Matrix.mul_apply,
      Finset.sum_eq_single i
        (fun k _ hk => by rw [diagInv_off_diag (Ne.symm hk), zero_mul])
        (fun habs => absurd (Finset.mem_univ i) habs),
      diagInv_diag]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq, inv_mul_cancel₀ (ne_of_gt (hM.2 i))]
  · rw [Matrix.one_apply_ne hij, hM.1 i j hij, mul_zero]

lemma IsPositiveDiagonal.self_mul_diagInv {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : IsPositiveDiagonal M) : M * diagInv M = 1 := by
  ext i j
  rw [Matrix.mul_apply,
      Finset.sum_eq_single j
        (fun k _ hk => by rw [diagInv_off_diag hk, mul_zero])
        (fun habs => absurd (Finset.mem_univ j) habs),
      diagInv_diag]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq, mul_inv_cancel₀ (ne_of_gt (hM.2 i))]
  · rw [Matrix.one_apply_ne hij, hM.1 i j hij, zero_mul]

lemma IsPositiveDiagonal.isPositiveDiagonal_diagInv {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : IsPositiveDiagonal M) : IsPositiveDiagonal (diagInv M) := by
  refine ⟨fun _ _ hij => diagInv_off_diag hij, fun i => ?_⟩
  rw [diagInv_diag]; exact inv_pos.mpr (hM.2 i)

structure IwasawaFactorization (g : Matrix (Fin n) (Fin n) ℝ) where

  k : Matrix (Fin n) (Fin n) ℝ

  a : Matrix (Fin n) (Fin n) ℝ

  u : Matrix (Fin n) (Fin n) ℝ
  k_orthogonal : IsOrthogonal k
  a_positiveDiagonal : IsPositiveDiagonal a
  u_upperUnipotent : IsUpperUnipotent u

  factorization : g = k * a * u

namespace IwasawaFactorization

variable {g : Matrix (Fin n) (Fin n) ℝ}

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

noncomputable def gCol (g : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j => g j i)

noncomputable def gsCol (g : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    EuclideanSpace ℝ (Fin n) :=
  gramSchmidtNormed ℝ (gCol g) i

noncomputable def qMat (g : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun j i => gsCol g i j

noncomputable def rMat (g : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => @inner ℝ _ _ (gsCol g i) (gCol g j)

lemma inner_eq_sum (x y : EuclideanSpace ℝ (Fin n)) :
    @inner ℝ _ _ x y = ∑ k, x k * y k := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  show y.ofLp k * (starRingEnd ℝ) (x.ofLp k) = x.ofLp k * y.ofLp k
  rw [RCLike.conj_to_real]; ring

lemma gCol_linearIndependent {g : Matrix (Fin n) (Fin n) ℝ} (hg : g.det ≠ 0) :
    LinearIndependent ℝ (gCol g) := by
  have h := Matrix.linearIndependent_cols_of_det_ne_zero hg

  let e : (Fin n → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) := (WithLp.linearEquiv 2 ℝ _).symm
  have h2 : LinearIndependent ℝ (fun i => e (g.col i)) :=
    h.map' e.toLinearMap (LinearEquiv.ker e)
  convert h2 using 1

lemma gsCol_orthonormal {g : Matrix (Fin n) (Fin n) ℝ} (hg : g.det ≠ 0) :
    Orthonormal ℝ (gsCol g) :=
  gramSchmidtNormed_orthonormal (gCol_linearIndependent hg)

lemma qMat_orthogonal {g : Matrix (Fin n) (Fin n) ℝ} (hg : g.det ≠ 0) :
    IsOrthogonal (qMat g) := by
  have hortho := gsCol_orthonormal hg

  have hTQ : (qMat g)ᵀ * qMat g = 1 := by
    ext i j
    rw [Matrix.mul_apply]
    have hsum : ∑ k, (qMat g)ᵀ i k * qMat g k j = ∑ k, gsCol g i k * gsCol g j k := by
      apply Finset.sum_congr rfl
      intros k _
      simp [qMat, Matrix.transpose_apply]
    rw [hsum]
    have hinner : @inner ℝ _ _ (gsCol g i) (gsCol g j) = ∑ k, gsCol g i k * gsCol g j k :=
      inner_eq_sum _ _
    rw [← hinner]
    rcases eq_or_ne i j with rfl | hne
    · rw [Matrix.one_apply_eq]
      have hii : ‖gsCol g i‖ = 1 := hortho.1 i
      rw [real_inner_self_eq_norm_mul_norm, hii, mul_one]
    · rw [Matrix.one_apply_ne hne]
      exact hortho.2 hne

  unfold IsOrthogonal
  exact mul_eq_one_comm.mp hTQ

lemma rMat_eq_QT_mul_g (g : Matrix (Fin n) (Fin n) ℝ) :
    rMat g = (qMat g)ᵀ * g := by
  ext i j
  rw [Matrix.mul_apply]
  rw [show (∑ k, (qMat g)ᵀ i k * g k j) = ∑ k, gsCol g i k * gCol g j k from ?_]
  · exact (inner_eq_sum (gsCol g i) (gCol g j))
  · apply Finset.sum_congr rfl
    intros k _
    simp [qMat, Matrix.transpose_apply, gCol]

lemma g_eq_Q_mul_R {g : Matrix (Fin n) (Fin n) ℝ} (hg : g.det ≠ 0) :
    g = qMat g * rMat g := by
  rw [rMat_eq_QT_mul_g, ← Matrix.mul_assoc]

  rw [(qMat_orthogonal hg : qMat g * (qMat g)ᵀ = 1)]
  rw [Matrix.one_mul]

lemma rMat_lowerTriangular_zero (g : Matrix (Fin n) (Fin n) ℝ)
    {i j : Fin n} (hij : j < i) : rMat g i j = 0 := by

  unfold rMat gsCol gramSchmidtNormed
  rw [inner_smul_left]

  have h0 : @inner ℝ _ _ (gramSchmidt ℝ (gCol g) i) (gCol g j) = 0 :=
    gramSchmidt_inv_triangular ℝ (gCol g) hij
  rw [h0]
  simp

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

lemma rMat_diag_pos {g : Matrix (Fin n) (Fin n) ℝ} (hg : g.det ≠ 0) (i : Fin n) :
    0 < rMat g i i := by
  rw [rMat_diag g]
  rw [norm_pos_iff]
  exact gramSchmidt_ne_zero i (gCol_linearIndependent hg)

lemma rMat_isUpperTriangular (g : Matrix (Fin n) (Fin n) ℝ) :
    IsUpperTriangular (rMat g) := by
  intros i j hij

  exact rMat_lowerTriangular_zero g hij

noncomputable def dMat (g : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = j then rMat g i i else 0

noncomputable def uMat (g : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  diagInv (dMat g) * rMat g

lemma dMat_diag (g : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    dMat g i i = rMat g i i := by simp [dMat]

lemma dMat_off_diag {g : Matrix (Fin n) (Fin n) ℝ} {i j : Fin n} (h : i ≠ j) :
    dMat g i j = 0 := by simp [dMat, h]

lemma dMat_isPositiveDiagonal {g : Matrix (Fin n) (Fin n) ℝ} (hg : g.det ≠ 0) :
    IsPositiveDiagonal (dMat g) :=
  ⟨fun _ _ hij => dMat_off_diag hij, fun i => by rw [dMat_diag]; exact rMat_diag_pos hg i⟩

lemma dMat_mul_uMat {g : Matrix (Fin n) (Fin n) ℝ} (hg : g.det ≠ 0) :
    dMat g * uMat g = rMat g := by
  unfold uMat
  rw [← Matrix.mul_assoc]
  rw [(dMat_isPositiveDiagonal hg).self_mul_diagInv]
  rw [Matrix.one_mul]

lemma uMat_isUpperTriangular (g : Matrix (Fin n) (Fin n) ℝ) :
    IsUpperTriangular (uMat g) := by
  unfold uMat
  refine IsUpperTriangular.mul ?_ (rMat_isUpperTriangular g)

  intros i j hij

  apply diagInv_off_diag

  intro h
  exact absurd (h ▸ hij : id i < id i) (lt_irrefl _)

lemma uMat_diag {g : Matrix (Fin n) (Fin n) ℝ} (hg : g.det ≠ 0) (i : Fin n) :
    uMat g i i = 1 := by
  unfold uMat
  rw [Matrix.mul_apply]

  rw [Finset.sum_eq_single i]
  · rw [diagInv_diag, dMat_diag]
    rw [inv_mul_cancel₀ (ne_of_gt (rMat_diag_pos hg i))]
  · intros k _ hk
    rw [diagInv_off_diag (Ne.symm hk), zero_mul]
  · intros habs
    exact absurd (Finset.mem_univ i) habs

lemma uMat_isUpperUnipotent {g : Matrix (Fin n) (Fin n) ℝ} (hg : g.det ≠ 0) :
    IsUpperUnipotent (uMat g) :=
  ⟨uMat_isUpperTriangular g, uMat_diag hg⟩

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

lemma IsUpperUnipotent.det {U : Matrix (Fin n) (Fin n) ℝ} (hU : IsUpperUnipotent U) :
    U.det = 1 := by
  rw [Matrix.det_of_upperTriangular hU.1]
  apply Finset.prod_eq_one
  intros i _
  exact hU.2 i

lemma IsUpperUnipotent.det_ne_zero {U : Matrix (Fin n) (Fin n) ℝ} (hU : IsUpperUnipotent U) :
    U.det ≠ 0 := by
  rw [hU.det]
  exact one_ne_zero

lemma IsPositiveDiagonal.isUpperTriangular {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : IsPositiveDiagonal D) : IsUpperTriangular D := by
  intros i j hij

  apply hD.1
  intro h
  exact absurd (h ▸ hij : id j < id j) (lt_irrefl _)

lemma IsPositiveDiagonal.det_pos {D : Matrix (Fin n) (Fin n) ℝ} (hD : IsPositiveDiagonal D) :
    0 < D.det := by
  rw [Matrix.det_of_upperTriangular hD.isUpperTriangular]
  exact Finset.prod_pos (fun i _ => hD.2 i)

lemma IsUpperUnipotent.inv {U : Matrix (Fin n) (Fin n) ℝ} (hU : IsUpperUnipotent U) :
    IsUpperUnipotent U⁻¹ := by
  letI : Invertible U := U.invertibleOfIsUnitDet (Ne.isUnit hU.det_ne_zero)

  have hUT : IsUpperTriangular U⁻¹ := blockTriangular_inv_of_blockTriangular hU.1
  refine ⟨hUT, ?_⟩

  intro i
  have hUUinv : U * U⁻¹ = 1 := Matrix.mul_inv_of_invertible U
  have hUUinv_ii : (U * U⁻¹) i i = 1 := by rw [hUUinv]; simp
  rw [Matrix.mul_apply] at hUUinv_ii

  have honly : ∀ k ∈ (Finset.univ : Finset (Fin n)) \ {i}, U i k * U⁻¹ k i = 0 := by
    intros k hk
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hk
    rcases lt_or_gt_of_ne hk.2 with hki | hki
    ·
      rw [hU.1 hki, zero_mul]
    ·
      rw [hUT hki, mul_zero]
  have hcontract : ∑ k, U i k * U⁻¹ k i = U i i * U⁻¹ i i := by
    rw [show (Finset.univ : Finset (Fin n)) = {i} ∪ (Finset.univ \ {i}) by
      ext x; simp [or_iff_not_imp_left]]
    rw [Finset.sum_union (by simp [Finset.disjoint_sdiff])]
    rw [Finset.sum_singleton, Finset.sum_eq_zero honly, add_zero]
  rw [hcontract, hU.2 i, one_mul] at hUUinv_ii
  exact hUUinv_ii

lemma IsPositiveDiagonal.matInv_eq_diagInv {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : IsPositiveDiagonal D) : D⁻¹ = diagInv D := by
  apply Matrix.inv_eq_left_inv
  exact hD.diagInv_mul_self

lemma IsPositiveDiagonal.matInv {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : IsPositiveDiagonal D) : IsPositiveDiagonal D⁻¹ := by
  rw [hD.matInv_eq_diagInv]
  exact hD.isPositiveDiagonal_diagInv

lemma IsOrthogonal.matInv_eq_transpose {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : IsOrthogonal Q) : Q⁻¹ = Qᵀ := by
  apply Matrix.inv_eq_left_inv
  exact mul_eq_one_comm.mpr hQ

lemma orthogonal_upperTriangular_posDiag_eq_one
    {M : Matrix (Fin n) (Fin n) ℝ}
    (hOrth : IsOrthogonal M)
    (hUT : IsUpperTriangular M)
    (hPos : ∀ i, 0 < M i i) :
    M = 1 := by

  have hdet : M.det ≠ 0 := hOrth.det_ne_zero
  letI : Invertible M := M.invertibleOfIsUnitDet (Ne.isUnit hdet)

  have hMinv : M⁻¹ = Mᵀ := by
    apply Matrix.inv_eq_left_inv
    exact mul_eq_one_comm.mpr hOrth

  have hMinv_UT : IsUpperTriangular M⁻¹ := blockTriangular_inv_of_blockTriangular hUT

  have hMt_UT : IsUpperTriangular Mᵀ := hMinv ▸ hMinv_UT

  have hM_LT : ∀ ⦃i j⦄, i < j → M i j = 0 := by
    intros i j hij
    have : Mᵀ j i = 0 := hMt_UT hij
    simpa using this

  have hDiag : ∀ ⦃i j⦄, i ≠ j → M i j = 0 := by
    intros i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hM_LT h
    · exact hUT h

  ext i j
  rcases eq_or_ne i j with rfl | hij
  ·
    have hii : (M * Mᵀ) i i = 1 := by rw [hOrth]; simp
    rw [Matrix.mul_apply] at hii
    have hsum : ∑ k, M i k * M i k = 1 := by
      have hh : ∑ k, M i k * Mᵀ k i = ∑ k, M i k * M i k := by
        apply Finset.sum_congr rfl
        intros k _
        rfl
      rw [hh] at hii
      exact hii
    have honly : ∀ k ∈ (Finset.univ : Finset (Fin n)) \ {i}, M i k * M i k = 0 := by
      intros k hk
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hk
      rw [hDiag (Ne.symm hk.2), zero_mul]
    have hcontract : ∑ k, M i k * M i k = M i i * M i i := by
      rw [show (Finset.univ : Finset (Fin n)) = {i} ∪ (Finset.univ \ {i}) by
        ext x; simp [or_iff_not_imp_left]]
      rw [Finset.sum_union (by simp [Finset.disjoint_sdiff])]
      rw [Finset.sum_singleton, Finset.sum_eq_zero honly, add_zero]
    rw [hcontract] at hsum

    have hMi := hPos i
    have : M i i = 1 := by nlinarith
    rw [this, Matrix.one_apply_eq]
  · rw [hDiag hij, Matrix.one_apply_ne hij]

lemma upperUnipotent_inter_positiveDiagonal_eq_one
    {M : Matrix (Fin n) (Fin n) ℝ}
    (hUU : IsUpperUnipotent M) (hPD : IsPositiveDiagonal M) :
    M = 1 := by
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · rw [hUU.2 i, Matrix.one_apply_eq]
  · rw [hPD.1 i j hij, Matrix.one_apply_ne hij]

lemma posDiag_mul_upperUnip_eq_diag_iff
    {a a' u : Matrix (Fin n) (Fin n) ℝ}
    (ha : IsPositiveDiagonal a) (ha' : IsPositiveDiagonal a')
    (hu : IsUpperUnipotent u)
    (h : a * u = a') : a = a' ∧ u = 1 := by

  have h_eq_diag : a = a' := by
    ext i j
    have h_ij := congrFun (congrFun h i) j
    rcases lt_trichotomy i j with hlt | heq | hgt
    ·
      rw [ha.1 i j (ne_of_lt hlt)]
      rw [ha'.1 i j (ne_of_lt hlt)]
    · subst heq

      rw [Matrix.mul_apply] at h_ij
      rw [Finset.sum_eq_single i] at h_ij
      · rw [hu.2 i, mul_one] at h_ij
        exact h_ij
      · intros k _ hk
        rw [ha.1 i k (Ne.symm hk), zero_mul]
      · intro h; exact absurd (Finset.mem_univ i) h
    ·
      rw [ha.1 i j (ne_of_gt hgt), ha'.1 i j (ne_of_gt hgt)]
  refine ⟨h_eq_diag, ?_⟩

  ext i j
  have h_ij := congrFun (congrFun h i) j
  rcases lt_trichotomy i j with hlt | heq | hgt
  ·
    have h_aij : a' i j = 0 := ha'.1 i j (ne_of_lt hlt)
    rw [Matrix.mul_apply] at h_ij
    rw [Finset.sum_eq_single i] at h_ij
    ·
      rw [h_aij] at h_ij
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
  · subst heq; rw [hu.2 i, Matrix.one_apply_eq]
  ·
    rw [hu.1 hgt, Matrix.one_apply_ne (ne_of_gt hgt)]

theorem iwasawa_unique {g : Matrix (Fin n) (Fin n) ℝ}
    (F G : IwasawaFactorization g) :
    F.k = G.k ∧ F.a = G.a ∧ F.u = G.u := by
  obtain ⟨k₁, a₁, u₁, hk₁, ha₁, hu₁, hf₁⟩ := F
  obtain ⟨k₂, a₂, u₂, hk₂, ha₂, hu₂, hf₂⟩ := G

  have heq : k₁ * a₁ * u₁ = k₂ * a₂ * u₂ := hf₁.symm.trans hf₂

  letI : Invertible u₁ := u₁.invertibleOfIsUnitDet (Ne.isUnit hu₁.det_ne_zero)
  letI : Invertible a₁ := a₁.invertibleOfIsUnitDet (Ne.isUnit (ne_of_gt ha₁.det_pos))

  set M : Matrix (Fin n) (Fin n) ℝ := k₂ᵀ * k₁ with hM_def

  have hMorth : IsOrthogonal M := by
    unfold IsOrthogonal
    rw [hM_def, Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc k₁, hk₁, Matrix.one_mul]
    exact mul_eq_one_comm.mpr hk₂

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

  have hM_UT : IsUpperTriangular M := by
    rw [hM_eq]
    apply IsUpperTriangular.mul
    apply IsUpperTriangular.mul
    apply IsUpperTriangular.mul
    · exact ha₂.isUpperTriangular
    · exact hu₂.1
    · exact hu₁.inv.1
    · exact ha₁.matInv.isUpperTriangular

  have hM_pos : ∀ i, 0 < M i i := by
    intro i
    rw [hM_eq]

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
    apply mul_pos
    apply mul_pos
    apply mul_pos
    · exact ha₂.2 i
    · rw [hu₂.2 i]; exact one_pos
    · rw [hu₁.inv.2 i]; exact one_pos
    · exact ha₁.matInv.2 i

  have hM_one : M = 1 := orthogonal_upperTriangular_posDiag_eq_one hMorth hM_UT hM_pos

  have hk_eq : k₁ = k₂ := by
    have h : k₂ᵀ * k₁ = 1 := hM_one

    have hc := congrArg (k₂ * ·) h
    simp only at hc
    rw [← Matrix.mul_assoc, hk₂, Matrix.one_mul, Matrix.mul_one] at hc
    exact hc

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

  set U : Matrix (Fin n) (Fin n) ℝ := u₂ * u₁⁻¹ with hU_def
  have hU_unip : IsUpperUnipotent U := IsUpperUnipotent.mul hu₂ hu₁.inv
  have ha₂U_eq_a₁ : a₂ * U = a₁ := by

    have := congrArg (· * u₁⁻¹) hau_eq
    simp only at this
    rw [Matrix.mul_assoc, Matrix.mul_inv_of_invertible, Matrix.mul_one] at this
    rw [hU_def, ← Matrix.mul_assoc]
    exact this.symm
  obtain ⟨ha_eq, hU_one⟩ := posDiag_mul_upperUnip_eq_diag_iff ha₂ ha₁ hU_unip ha₂U_eq_a₁

  have hu_eq : u₁ = u₂ := by
    have h := hU_one
    rw [hU_def] at h
    have := congrArg (· * u₁) h
    simp only at this
    rw [Matrix.mul_assoc, Matrix.inv_mul_of_invertible, Matrix.mul_one, Matrix.one_mul] at this
    exact this.symm
  exact ⟨hk_eq, ha_eq.symm, hu_eq⟩

theorem iwasawaDecomposition (g : Matrix (Fin n) (Fin n) ℝ) (hg : g.det ≠ 0) :
    ∃! (kau : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ ×
              Matrix (Fin n) (Fin n) ℝ),
      IsOrthogonal kau.1 ∧ IsPositiveDiagonal kau.2.1 ∧ IsUpperUnipotent kau.2.2 ∧
      g = kau.1 * kau.2.1 * kau.2.2 := by
  refine ⟨(qMat g, dMat g, uMat g), ?_, ?_⟩
  · refine ⟨qMat_orthogonal hg, dMat_isPositiveDiagonal hg, uMat_isUpperUnipotent hg, ?_⟩
    show g = qMat g * dMat g * uMat g
    rw [Matrix.mul_assoc, dMat_mul_uMat hg]
    exact g_eq_Q_mul_R hg
  · intro ⟨k', a', u'⟩ ⟨hk', ha', hu', hg'⟩

    let G : IwasawaFactorization g := ⟨k', a', u', hk', ha', hu', hg'⟩
    let F : IwasawaFactorization g := iwasawa hg
    obtain ⟨hk_eq, ha_eq, hu_eq⟩ := iwasawa_unique F G
    exact Prod.ext hk_eq.symm (Prod.ext ha_eq.symm hu_eq.symm)

end Iwasawa
