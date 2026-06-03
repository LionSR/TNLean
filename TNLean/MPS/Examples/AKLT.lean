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
* `akltZ2Z2Action` : the Z₂ × Z₂ on-site representation via the commuting spin-1
  rotations Rx(π) and Rz(π)

## Main results

* `aklt_not_isInjective` : the AKLT tensor is not 1-block injective
* `aklt_isNormal` : the AKLT tensor is normal (2-block injective)
* `aklt_transferMap_one` : the identity is a fixed point of the transfer map
* `aklt_isOnSiteSymmetric_Z2` : the AKLT tensor is on-site symmetric under Z₂
* `aklt_isOnSiteSymmetric_Z2Z2` : the AKLT tensor is on-site symmetric under
  Z₂ × Z₂, with anticommuting virtual gauges σz and iσy

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

/-! ### Scalar arithmetic lemmas -/

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

/-- The conjugate transpose of each AKLT matrix. -/
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

/-- Nonzero coefficient for the off-diagonal products. -/
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

/-- The Z₂ physical action on the spin-1 basis ${|+1\rangle, |0\rangle, |-1\rangle}$:
the generator acts as the matrix
$\begin{pmatrix} -1 & 0 & 0 \\ 0 & 0 & 1 \\ 0 & 1 & 0 \end{pmatrix}$. -/
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

/-! ### Z₂ × Z₂ on-site symmetry

The single Z₂ above is generated by a spin-1 `π`-rotation.  Adjoining a second,
commuting spin-1 `π`-rotation about an orthogonal axis extends the symmetry to a
`Z₂ × Z₂` subgroup of `SO(3)`.  (In the basis used here the two generators are
the matrices below; each is real orthogonal with determinant `1` and eigenvalues
`{1, -1, -1}`, hence a `π`-rotation, but they are not the literal `Rx(π)`,
`Rz(π)` of the standard `|m⟩` basis.)  On the bond space the two rotations are
implemented by the anticommuting virtual gauges `iσy = !![0, 1; -1, 0]` and
`σz = !![1, 0; 0, -1]`, exhibiting the nontrivial class in `H²(Z₂ × Z₂, U(1))`
that protects the AKLT phase. -/

/-- The first physical generator, a spin-1 `π`-rotation
$\begin{pmatrix} -1 & 0 & 0 \\ 0 & 0 & 1 \\ 0 & 1 & 0 \end{pmatrix}$. -/
private def akltPhysP1 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(-1 : ℂ), 0, 0; 0, 0, 1; 0, 1, 0]

/-- The second physical generator, a commuting spin-1 `π`-rotation
`diag(1, -1, -1)` about an orthogonal axis. -/
private def akltPhysP2 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(1 : ℂ), 0, 0; 0, -1, 0; 0, 0, -1]

private lemma akltPhysP1_sq : akltPhysP1 * akltPhysP1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [akltPhysP1, Matrix.mul_apply, Fin.sum_univ_three]

private lemma akltPhysP2_sq : akltPhysP2 * akltPhysP2 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [akltPhysP2, Matrix.mul_apply, Fin.sum_univ_three]

private lemma akltPhysP1P2_comm : akltPhysP1 * akltPhysP2 = akltPhysP2 * akltPhysP1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [akltPhysP1, akltPhysP2, Matrix.mul_apply, Fin.sum_univ_three]

/-- The `Z₂ × Z₂` on-site representation on the spin-1 physical space.  The two
generators act by two commuting spin-1 `π`-rotations about orthogonal axes. -/
def akltZ2Z2Action :
    Multiplicative (ZMod 2 × ZMod 2) →* Matrix (Fin 3) (Fin 3) ℂ where
  toFun g :=
    (if (Multiplicative.toAdd g).1 = 0 then 1 else akltPhysP1) *
      (if (Multiplicative.toAdd g).2 = 0 then 1 else akltPhysP2)
  map_one' := by simp [toAdd_one]
  map_mul' a b := by
    have key : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add]
    obtain (h1 | h1) := key (Multiplicative.toAdd a).1 <;>
      obtain (h2 | h2) := key (Multiplicative.toAdd a).2 <;>
        obtain (h3 | h3) := key (Multiplicative.toAdd b).1 <;>
          obtain (h4 | h4) := key (Multiplicative.toAdd b).2 <;>
            simp only [h1, h2, h3, h4, show (1 : ZMod 2) + 1 = 0 from by decide, add_zero,
              zero_add, one_ne_zero, ↓reduceIte, mul_one, one_mul] <;>
            first
              | rfl
              | (ext i j; fin_cases i <;> fin_cases j <;>
                  simp [akltPhysP1, akltPhysP2, Matrix.mul_apply, Fin.sum_univ_three])

@[simp] private lemma akltZ2Z2Action_10 :
    akltZ2Z2Action (Multiplicative.ofAdd ((1, 0) : ZMod 2 × ZMod 2)) = akltPhysP1 := by
  simp only [akltZ2Z2Action, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd,
    show (1 : ZMod 2) ≠ 0 from by decide, ↓reduceIte, mul_one]

@[simp] private lemma akltZ2Z2Action_01 :
    akltZ2Z2Action (Multiplicative.ofAdd ((0, 1) : ZMod 2 × ZMod 2)) = akltPhysP2 := by
  simp only [akltZ2Z2Action, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd,
    show (1 : ZMod 2) ≠ 0 from by decide, ↓reduceIte, one_mul]

@[simp] private lemma akltZ2Z2Action_11 :
    akltZ2Z2Action (Multiplicative.ofAdd ((1, 1) : ZMod 2 × ZMod 2)) =
      akltPhysP1 * akltPhysP2 := by
  simp only [akltZ2Z2Action, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd,
    show (1 : ZMod 2) ≠ 0 from by decide, ↓reduceIte]

/-! #### Virtual gauges `σz` and `iσy σz` -/

/-- The virtual gauge `σz = !![1, 0; 0, -1]` implementing the `Rz(π)` rotation. -/
private def akltGaugeZ : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; 0, -1] (by norm_num [Matrix.det_fin_two])

@[simp] private lemma akltGaugeZ_val :
    (akltGaugeZ : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 0; 0, -1] :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

private lemma akltGaugeZ_inv_val :
    ((akltGaugeZ⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 0; 0, -1] := by
  have hsq : akltGaugeZ * akltGaugeZ = 1 := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_one, akltGaugeZ_val]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [show akltGaugeZ⁻¹ = akltGaugeZ from inv_eq_of_mul_eq_one_right hsq, akltGaugeZ_val]

/-- The virtual gauge for the combined element, `iσy σz = !![0, -1; -1, 0]`. -/
private def akltGaugeYZ : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, -1; -1, 0] (by norm_num [Matrix.det_fin_two])

@[simp] private lemma akltGaugeYZ_val :
    (akltGaugeYZ : Matrix (Fin 2) (Fin 2) ℂ) = !![0, -1; -1, 0] :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

private lemma akltGaugeYZ_inv_val :
    ((akltGaugeYZ⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = !![0, -1; -1, 0] := by
  have hsq : akltGaugeYZ * akltGaugeYZ = 1 := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_one, akltGaugeYZ_val]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [show akltGaugeYZ⁻¹ = akltGaugeYZ from inv_eq_of_mul_eq_one_right hsq, akltGaugeYZ_val]

/-- The two virtual gauges `iσy = !![0, 1; -1, 0]` and `σz = !![1, 0; 0, -1]`
implementing the `Z₂ × Z₂` symmetry anticommute.  This is the projective phase
witnessing the non-trivial SPT order: the physical generators commute, but their
virtual representatives do not. -/
lemma aklt_gauge_anticomm :
    (!![(0 : ℂ), 1; -1, 0]) * !![(1 : ℂ), 0; 0, -1] =
      -(!![(1 : ℂ), 0; 0, -1] * !![(0 : ℂ), 1; -1, 0]) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply]

/-! #### Twists by the second and combined generators -/

private lemma aklt_twisted_P2_eq (i : Fin 3) :
    twistedTensor akltTensor akltZ2Z2Action (Multiplicative.ofAdd ((0, 1) : ZMod 2 × ZMod 2)) i =
      match i with
      | 0 => akltTensor 0
      | 1 => -akltTensor 1
      | 2 => -akltTensor 2 := by
  simp only [twistedTensor, akltZ2Z2Action_01, akltPhysP2, Fin.sum_univ_three]
  fin_cases i <;>
    ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [akltTensor, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.smul_apply, Matrix.neg_apply, Matrix.add_apply, Matrix.zero_apply]

private lemma aklt_twisted_P1P2_eq (i : Fin 3) :
    twistedTensor akltTensor akltZ2Z2Action (Multiplicative.ofAdd ((1, 1) : ZMod 2 × ZMod 2)) i =
      match i with
      | 0 => -akltTensor 0
      | 1 => -akltTensor 2
      | 2 => -akltTensor 1 := by
  simp only [twistedTensor, akltZ2Z2Action_11, akltPhysP1, akltPhysP2, Matrix.mul_apply,
    Fin.sum_univ_three]
  fin_cases i <;>
    ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [akltTensor, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.neg_apply, Matrix.add_apply, Matrix.zero_apply]

private lemma aklt_gaugeEquiv_P1 :
    GaugeEquiv akltTensor
      (twistedTensor akltTensor akltZ2Z2Action
        (Multiplicative.ofAdd ((1, 0) : ZMod 2 × ZMod 2))) := by
  refine ⟨akltGaugeGL, fun i => ?_⟩
  simp only [twistedTensor, akltZ2Z2Action_10, akltPhysP1, Fin.sum_univ_three]
  rw [akltGaugeGL_inv_val, akltGaugeGL_val, akltGaugeMat]
  fin_cases i <;>
    (ext a b; fin_cases a <;> fin_cases b <;>
    simp [akltTensor, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply, Matrix.zero_apply])

private lemma aklt_gaugeEquiv_P2 :
    GaugeEquiv akltTensor
      (twistedTensor akltTensor akltZ2Z2Action
        (Multiplicative.ofAdd ((0, 1) : ZMod 2 × ZMod 2))) := by
  refine ⟨akltGaugeZ, fun i => ?_⟩
  rw [aklt_twisted_P2_eq, akltGaugeZ_inv_val, akltGaugeZ_val]
  fin_cases i <;>
    (ext a b; fin_cases a <;> fin_cases b <;>
    simp [akltTensor, Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply])

private lemma aklt_gaugeEquiv_P1P2 :
    GaugeEquiv akltTensor
      (twistedTensor akltTensor akltZ2Z2Action
        (Multiplicative.ofAdd ((1, 1) : ZMod 2 × ZMod 2))) := by
  refine ⟨akltGaugeYZ, fun i => ?_⟩
  rw [aklt_twisted_P1P2_eq, akltGaugeYZ_inv_val, akltGaugeYZ_val]
  fin_cases i <;>
    (ext a b; fin_cases a <;> fin_cases b <;>
    simp [akltTensor, Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply])

/-- Every element of `Multiplicative (ZMod 2 × ZMod 2)` is one of the four group
elements. -/
private lemma aklt_zmod2sq_cases (g : Multiplicative (ZMod 2 × ZMod 2)) :
    g = 1 ∨ g = Multiplicative.ofAdd (1, 0) ∨ g = Multiplicative.ofAdd (0, 1) ∨
      g = Multiplicative.ofAdd (1, 1) := by
  revert g
  decide

/-- The AKLT tensor is on-site symmetric under a `Z₂ × Z₂ ⊂ SO(3)` subgroup
generated by two commuting spin-1 `π`-rotations about orthogonal axes.  This is
the smallest subgroup of `SO(3)` carrying a nontrivial `2`-cocycle (arXiv:2011.12127,
line 1159): the virtual gauges `σz = !![1, 0; 0, -1]` and `iσy = !![0, 1; -1, 0]`
anticommute, so the projective bond representation is nontrivial and protects the
AKLT phase.  The full continuous `SO(3)` symmetry is not formalized here
(documented in `docs/paper-gaps/rmp_aklt_continuous_rotation_gap.tex`). -/
theorem aklt_isOnSiteSymmetric_Z2Z2 :
    IsOnSiteSymmetric akltTensor akltZ2Z2Action := by
  intro g
  rcases aklt_zmod2sq_cases g with rfl | rfl | rfl | rfl
  · rw [twistedTensor_one]; exact fun _ _ => rfl
  · exact aklt_gaugeEquiv_P1.sameMPV
  · exact aklt_gaugeEquiv_P2.sameMPV
  · exact aklt_gaugeEquiv_P1P2.sameMPV

end MPSTensor

end
