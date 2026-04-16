/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.RFP.Defs
import TNLean.MPS.Symmetry.Defs
import TNLean.MPS.Examples.ZMod2

/-!
# AKLT state as a Matrix Product State

This module defines the AKLT (Affleck-Kennedy-Lieb-Tasaki) state as a concrete
MPS tensor with physical dimension `d = 3` (spin-1) and bond dimension `D = 2`,
and proves its key properties.

## Main definitions

* `akltTensor` : the AKLT MPS tensor with `A⁰ = (1/√3) σz`,
  `A¹ = (√2/√3) σ⁺`, `A² = -(√2/√3) σ⁻`
* `akltZ2Action` : the Z₂ on-site representation via spin-1 Rx(π) rotation

## Main results

* `aklt_not_isInjective` : the AKLT tensor is not 1-block injective (the 3
  matrices span only the traceless subspace of M₂(ℂ))
* `aklt_isNormal` : the AKLT tensor is normal (2-block injective)
* `aklt_transferMap_one` : the identity is a fixed point of the transfer map
* `aklt_isOnSiteSymmetric_Z2` : the AKLT tensor is on-site symmetric under Z₂

## References

* Affleck, Kennedy, Lieb, Tasaki (1987) — original AKLT construction
* RMP review (arXiv:2011.12127) Section III.A
-/

open scoped Matrix BigOperators
open Matrix Finset MPSTensor

noncomputable section

namespace MPSTensor

/-! ### Definition -/

/-- The AKLT MPS tensor: a spin-1 chain (d=3) with bond dimension D=2.

* `A⁰ = (1/√3) σz = (1/√3) · !![1, 0; 0, -1]`
* `A¹ = (√2/√3) σ⁺ = (√2/√3) · !![0, 1; 0, 0]`
* `A² = -(√2/√3) σ⁻ = -(√2/√3) · !![0, 0; 1, 0]` -/
def akltTensor : MPSTensor 3 2 := fun i =>
  match i with
  | 0 => (↑(1 / Real.sqrt 3) : ℂ) • !![1, 0; 0, -1]
  | 1 => (↑(Real.sqrt 2 / Real.sqrt 3) : ℂ) • !![0, 1; 0, 0]
  | 2 => -(↑(Real.sqrt 2 / Real.sqrt 3) : ℂ) • !![0, 0; 1, 0]

@[simp]
lemma akltTensor_zero :
    akltTensor 0 = (↑(1 / Real.sqrt 3) : ℂ) • !![1, 0; 0, -1] := rfl

@[simp]
lemma akltTensor_one :
    akltTensor 1 = (↑(Real.sqrt 2 / Real.sqrt 3) : ℂ) • !![0, 1; 0, 0] := rfl

@[simp]
lemma akltTensor_two :
    akltTensor 2 = -(↑(Real.sqrt 2 / Real.sqrt 3) : ℂ) • !![0, 0; 1, 0] := rfl

/-! ### Scalar arithmetic helpers -/

private lemma ofReal_sqrt3_mul_self :
    (↑(Real.sqrt 3) : ℂ) * (↑(Real.sqrt 3) : ℂ) = 3 := by
  rw [← Complex.ofReal_mul, ← sq, Real.sq_sqrt (by positivity), Complex.ofReal_ofNat]

private lemma ofReal_sqrt2_mul_self :
    (↑(Real.sqrt 2) : ℂ) * (↑(Real.sqrt 2) : ℂ) = 2 := by
  rw [← Complex.ofReal_mul, ← sq, Real.sq_sqrt (by positivity), Complex.ofReal_ofNat]

/-! ### Non-injectivity -/

/-- The AKLT tensor is **not** injective: the span of {A⁰, A¹, A²} is the 3-dimensional
space of traceless matrices, not the full 4-dimensional matrix algebra M₂(ℂ). -/
theorem aklt_not_isInjective : ¬ IsInjective akltTensor := by
  intro h
  have hmem : (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈
      Submodule.span ℂ (Set.range akltTensor) := h ▸ Submodule.mem_top
  suffices hzero : ∀ M ∈ Submodule.span ℂ (Set.range akltTensor), M 0 0 + M 1 1 = 0 by
    have h1 := hzero _ hmem
    norm_num at h1
  intro M hM
  induction hM using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    fin_cases k <;> simp [akltTensor, Matrix.smul_apply]
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Matrix.add_apply]
    linear_combination hx + hy
  | smul c x _ hx =>
    simp only [Matrix.smul_apply, smul_eq_mul]
    linear_combination c * hx

/-! ### Transfer map -/

/-- The conjTranspose of each AKLT matrix. Pre-computing avoids a `simp` loop
between `conjTranspose_apply`, `star`, and `Complex.conj_ofReal`. -/
@[simp]
lemma akltTensor_conjTranspose (k : Fin 3) :
    (akltTensor k)ᴴ = match k with
    | 0 => (↑(1 / Real.sqrt 3) : ℂ) • !![1, 0; 0, -1]
    | 1 => (↑(Real.sqrt 2 / Real.sqrt 3) : ℂ) • !![0, 0; 1, 0]
    | 2 => -(↑(Real.sqrt 2 / Real.sqrt 3) : ℂ) • !![0, 1; 0, 0] := by
  fin_cases k <;> simp only [akltTensor] <;>
    rw [show ∀ (c : ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ), (c • M)ᴴ = star c • Mᴴ from
      fun c M => conjTranspose_smul c M] <;>
    simp only [Complex.star_def, Complex.conj_ofReal, map_neg] <;>
    congr 1 <;>
    ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [Matrix.conjTranspose_apply, star_one, star_zero, star_neg]

/-- The identity is a fixed point of the AKLT transfer map: `E(I) = I`. -/
theorem aklt_transferMap_one :
    transferMap akltTensor 1 = 1 := by
  ext i j
  simp only [transferMap_apply, Fin.sum_univ_three, Matrix.add_apply,
    akltTensor_conjTranspose]
  fin_cases i <;> fin_cases j <;>
    simp only [akltTensor, one_div, Complex.ofReal_inv, smul_of, smul_cons,
      smul_eq_mul, mul_one, mul_zero, Matrix.smul_empty, mul_neg,
      Fin.zero_eta, Fin.isValue, Fin.mk_one, mul_apply, of_apply, cons_val',
      cons_val_fin_one, cons_val_zero, cons_val_one, Fin.sum_univ_two,
      zero_mul, add_zero, zero_add, Complex.ofReal_div, neg_smul, neg_of,
      neg_cons, neg_zero, Matrix.neg_empty, ne_eq, zero_ne_one, one_ne_zero,
      not_false_eq_true, one_apply_eq, one_apply_ne, neg_mul, neg_neg] <;> (
      rw [div_mul_div_comm, ← _root_.mul_inv_rev, ofReal_sqrt3_mul_self,
        ofReal_sqrt2_mul_self]
      norm_num)

/-! ### Normality (2-block injectivity) -/

private abbrev wordSpan :=
  Submodule.span ℂ (Set.range fun σ : Fin 2 → Fin 3 => evalWord akltTensor (List.ofFn σ))

private lemma product_in_wordSpan (i j : Fin 3) :
    akltTensor i * akltTensor j ∈ wordSpan := by
  rw [show akltTensor i * akltTensor j = evalWord akltTensor [i, j] from by simp [evalWord]]
  have : [i, j] = List.ofFn (![i, j] : Fin 2 → Fin 3) := by
    simp [List.ofFn_succ, List.ofFn_zero]
  rw [this]
  exact Submodule.subset_span ⟨_, rfl⟩

/-- Helper: nonzero coefficient for the off-diagonal products. -/
private lemma aklt_coeff_ne_zero :
    (↑(1 / Real.sqrt 3) : ℂ) * ↑(Real.sqrt 2 / Real.sqrt 3) ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity))
    (Complex.ofReal_ne_zero.mpr (by positivity))

private lemma single_00_in_wordSpan :
    Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ) ∈ wordSpan := by
  -- A¹ * A² = -(c₁²) e₀₀ for c₁ = √2/√3
  have hne : (↑(Real.sqrt 2 / Real.sqrt 3) : ℂ) * ↑(Real.sqrt 2 / Real.sqrt 3) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity))
      (Complex.ofReal_ne_zero.mpr (by positivity))
  have h : akltTensor 1 * akltTensor 2 =
      -(↑(Real.sqrt 2 / Real.sqrt 3) * ↑(Real.sqrt 2 / Real.sqrt 3) : ℂ) •
        Matrix.single 0 0 1 := by
    ext a b; fin_cases a <;> fin_cases b <;>
      simp [akltTensor, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul, Matrix.single]
  have hmem := product_in_wordSpan 1 2
  rw [h] at hmem
  have hmem' := Submodule.smul_mem wordSpan
    (-(↑(Real.sqrt 2 / Real.sqrt 3) * ↑(Real.sqrt 2 / Real.sqrt 3) : ℂ))⁻¹ hmem
  rwa [smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr hne), one_smul] at hmem'

private lemma single_11_in_wordSpan :
    Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ) ∈ wordSpan := by
  -- A² * A¹ = -(c₁²) e₁₁
  have hne : (↑(Real.sqrt 2 / Real.sqrt 3) : ℂ) * ↑(Real.sqrt 2 / Real.sqrt 3) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity))
      (Complex.ofReal_ne_zero.mpr (by positivity))
  have h : akltTensor 2 * akltTensor 1 =
      -(↑(Real.sqrt 2 / Real.sqrt 3) * ↑(Real.sqrt 2 / Real.sqrt 3) : ℂ) •
        Matrix.single 1 1 1 := by
    ext a b; fin_cases a <;> fin_cases b <;>
      simp [akltTensor, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul, Matrix.single]
  have hmem := product_in_wordSpan 2 1
  rw [h] at hmem
  have hmem' := Submodule.smul_mem wordSpan
    (-(↑(Real.sqrt 2 / Real.sqrt 3) * ↑(Real.sqrt 2 / Real.sqrt 3) : ℂ))⁻¹ hmem
  rwa [smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr hne), one_smul] at hmem'

private lemma single_01_in_wordSpan :
    Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ) ∈ wordSpan := by
  -- A⁰ * A¹ = (c₀ c₁) e₀₁
  suffices h : akltTensor 0 * akltTensor 1 =
      (↑(1 / Real.sqrt 3) * ↑(Real.sqrt 2 / Real.sqrt 3) : ℂ) •
        Matrix.single 0 1 1 by
    rw [show Matrix.single (0 : Fin 2) 1 (1 : ℂ) =
        (↑(1 / Real.sqrt 3) * ↑(Real.sqrt 2 / Real.sqrt 3) : ℂ)⁻¹ •
          (akltTensor 0 * akltTensor 1) from by
      rw [h, smul_smul, inv_mul_cancel₀ aklt_coeff_ne_zero, one_smul]]
    exact Submodule.smul_mem _ _ (product_in_wordSpan 0 1)
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [akltTensor, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul, Matrix.single]

private lemma single_10_in_wordSpan :
    Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ℂ) ∈ wordSpan := by
  -- A⁰ * A² = (c₀ c₁) e₁₀ (the double negation gives positive)
  suffices h : akltTensor 0 * akltTensor 2 =
      (↑(1 / Real.sqrt 3) * ↑(Real.sqrt 2 / Real.sqrt 3) : ℂ) •
        Matrix.single 1 0 1 by
    rw [show Matrix.single (1 : Fin 2) 0 (1 : ℂ) =
        (↑(1 / Real.sqrt 3) * ↑(Real.sqrt 2 / Real.sqrt 3) : ℂ)⁻¹ •
          (akltTensor 0 * akltTensor 2) from by
      rw [h, smul_smul, inv_mul_cancel₀ aklt_coeff_ne_zero, one_smul]]
    exact Submodule.smul_mem _ _ (product_in_wordSpan 0 2)
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [akltTensor, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul, Matrix.single]

/-- The AKLT tensor is 2-block injective: products of length 2 span M₂(ℂ). -/
theorem aklt_isNBlkInjective_two : IsNBlkInjective akltTensor 2 := by
  rw [IsNBlkInjective, eq_top_iff]
  intro M _
  have hM : M = M 0 0 • Matrix.single 0 0 1 + M 0 1 • Matrix.single 0 1 1 +
      M 1 0 • Matrix.single 1 0 1 + M 1 1 • Matrix.single 1 1 1 := by
    ext a b; fin_cases a <;> fin_cases b <;> simp [Matrix.single]
  rw [hM]
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.smul_mem _ _ single_00_in_wordSpan)
    (Submodule.smul_mem _ _ single_01_in_wordSpan))
    (Submodule.smul_mem _ _ single_10_in_wordSpan))
    (Submodule.smul_mem _ _ single_11_in_wordSpan)

/-- The AKLT tensor is normal (eventually block-injective). -/
theorem aklt_isNormal : IsNormal akltTensor := ⟨2, aklt_isNBlkInjective_two⟩

/-! ### Z₂ on-site symmetry -/

/-- The Z₂ physical action on the spin-1 basis `{|+1⟩, |0⟩, |−1⟩}`:
the generator `Rx(π)` acts as `diag(−1, 1, 1)` composed with the `|0⟩ ↔ |−1⟩` swap,
giving the matrix `!![−1, 0, 0; 0, 0, 1; 0, 1, 0]`. -/
def akltZ2Action :
    Multiplicative (ZMod 2) →* Matrix (Fin 3) (Fin 3) ℂ where
  toFun g := if Multiplicative.toAdd g = 0 then 1
    else Matrix.of !![(-1 : ℂ), 0, 0; 0, 0, 1; 0, 1, 0]
  map_one' := by simp [toAdd_one]
  map_mul' a b := by
    rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
      simp only [one_mul, mul_one, toAdd_one, toAdd_ofAdd, toAdd_mul,
        zmod2_one_add_one, one_ne_zero, ↓reduceIte]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one]

private def akltGaugeMat : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; -1, 0]

private lemma akltGaugeMat_det_ne_zero :
    akltGaugeMat.det ≠ 0 := by
  simp [akltGaugeMat, Matrix.det_fin_two]

private def akltGaugeGL : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero akltGaugeMat akltGaugeMat_det_ne_zero

@[simp] private lemma akltGaugeGL_val :
    (akltGaugeGL : Matrix (Fin 2) (Fin 2) ℂ) = akltGaugeMat :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

private lemma akltGaugeGL_inv_val :
    ((akltGaugeGL⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = !![0, -1; 1, 0] := by
  have : akltGaugeGL * (Matrix.GeneralLinearGroup.mkOfDetNeZero
      (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) (by
        simp [Matrix.det_fin_two])) = 1 := by
    apply Units.ext
    simp only [Units.val_mul, akltGaugeGL_val, akltGaugeMat, Units.val_one]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [show akltGaugeGL⁻¹ = Matrix.GeneralLinearGroup.mkOfDetNeZero
      (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) (by
        simp [Matrix.det_fin_two]) from
    inv_eq_of_mul_eq_one_right this]
  exact Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

private lemma aklt_twisted_generator_eq (i : Fin 3) :
    twistedTensor akltTensor akltZ2Action (Multiplicative.ofAdd 1) i =
      match i with
      | 0 => -akltTensor 0
      | 1 => akltTensor 2
      | 2 => akltTensor 1 := by
  simp only [twistedTensor, akltZ2Action, MonoidHom.coe_mk, OneHom.coe_mk,
    toAdd_ofAdd, Fin.sum_univ_three]
  fin_cases i <;>
    ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [akltTensor, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.smul_apply, Matrix.neg_apply, Matrix.add_apply, Matrix.zero_apply]

private lemma aklt_gaugeEquiv_twisted :
    GaugeEquiv akltTensor
      (twistedTensor akltTensor akltZ2Action (Multiplicative.ofAdd 1)) := by
  refine ⟨akltGaugeGL, fun i => ?_⟩
  rw [aklt_twisted_generator_eq]
  rw [akltGaugeGL_inv_val, akltGaugeGL_val, akltGaugeMat]
  fin_cases i <;>
    (ext a b; fin_cases a <;> fin_cases b <;>
    simp [akltTensor, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
      Matrix.neg_apply])

/-- The AKLT tensor is on-site symmetric under Z₂ = {1, Rx(π)}. -/
theorem aklt_isOnSiteSymmetric_Z2 :
    IsOnSiteSymmetric akltTensor akltZ2Action := by
  intro g
  rcases zmod2_cases g with rfl | rfl
  · rw [twistedTensor_one]; exact fun _ _ => rfl
  · exact aklt_gaugeEquiv_twisted.sameMPV

end MPSTensor

end
