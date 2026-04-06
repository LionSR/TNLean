/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.RFP.Defs
import TNLean.MPS.Symmetry.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# GHZ state as a Matrix Product State

This module defines the GHZ (Greenberger-Horne-Zeilinger) state as a concrete
MPS tensor with physical dimension `d = 2` and bond dimension `D = 2`, and
proves its key properties.

## Main definitions

* `ghzTensor` : the GHZ MPS tensor with `A⁰ = |0⟩⟨0|` and `A¹ = |1⟩⟨1|`
* `z2PhysicalAction` : the Z₂ on-site representation via Pauli X

## Main results

* `ghz_isRFP` : the GHZ tensor is a renormalization fixed point
* `ghz_not_isInjective` : the GHZ tensor is not injective
* `ghz_isOnSiteSymmetric_Z2` : the GHZ tensor is on-site symmetric under Z₂

## References

* RMP review (arXiv:2011.12127) Example III.1
* Perez-Garcia et al. (arXiv:quant-ph/0608197) Section 4.1
-/

open scoped Matrix BigOperators
open Matrix Finset MPSTensor

namespace MPSTensor

/-! ### Definition -/

/-- The GHZ MPS tensor: `A i = diagonal (Pi.single i 1)`, i.e.
`A⁰ = |0⟩⟨0|` and `A¹ = |1⟩⟨1|`. -/
def ghzTensor : MPSTensor 2 2 := fun i => Matrix.diagonal (Pi.single i 1)

@[simp] lemma ghzTensor_apply (i : Fin 2) :
    ghzTensor i = Matrix.diagonal (Pi.single i 1) := rfl

/-! ### Transfer map and RFP -/

/-- The transfer map of the GHZ tensor extracts the diagonal:
`E(X)ᵢⱼ = if i = j then Xᵢⱼ else 0`. -/
private lemma ghz_transferMap_entry (X : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    (transferMap ghzTensor X) i j = if i = j then X i j else 0 := by
  simp only [transferMap_apply, Fin.sum_univ_two, ghzTensor_apply, Matrix.add_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply, Pi.single_apply,
    Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp

/-- The transfer map of the GHZ tensor is idempotent: `E² = E`. -/
theorem ghz_transferMap_idempotent :
    transferMap ghzTensor ∘ₗ transferMap ghzTensor = transferMap ghzTensor := by
  ext X i j : 3
  simp only [LinearMap.comp_apply]
  rw [ghz_transferMap_entry, ghz_transferMap_entry]
  split <;> simp [*]

/-- The GHZ tensor is a renormalization fixed point. -/
theorem ghz_isRFP : IsRFP ghzTensor := ghz_transferMap_idempotent

/-! ### Non-injectivity -/

/-- The GHZ tensor is **not** injective: span({A⁰, A¹}) is the 2-dimensional space
of diagonal matrices, not the full 4-dimensional matrix algebra. -/
theorem ghz_not_isInjective : ¬ IsInjective ghzTensor := by
  intro h
  -- Every element of the span has zero off-diagonal entries.
  suffices hzero : ∀ M ∈ Submodule.span ℂ (Set.range ghzTensor), M 0 1 = 0 by
    have hmem : (Matrix.of fun _ _ : Fin 2 => (1 : ℂ)) ∈
        Submodule.span ℂ (Set.range ghzTensor) := h ▸ Submodule.mem_top
    exact absurd (hzero _ hmem) one_ne_zero
  intro M hM
  induction hM using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    simp [ghzTensor]
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

/-! ### Z₂ on-site symmetry -/

private lemma zmod2_cases (g : Multiplicative (ZMod 2)) :
    g = 1 ∨ g = Multiplicative.ofAdd 1 := by
  fin_cases g <;> simp [Multiplicative.ext_iff] <;> tauto

private lemma zmod2_one_add_one : (1 : ZMod 2) + 1 = 0 := by decide

/-- The swap (Pauli X) matrix. -/
private def swapMat : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j => if i.val + j.val = 1 then 1 else 0

private lemma swapMat_sq : swapMat * swapMat = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [swapMat, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_two]

/-- The Z₂ on-site representation via Pauli X. We use `Multiplicative (ZMod 2)` as the
group: the identity corresponds to `ofAdd 0` and the generator to `ofAdd 1`.
`U(0) = 1` (identity), `U(1) = σx` (Pauli X swap). -/
noncomputable def z2PhysicalAction :
    Multiplicative (ZMod 2) →* Matrix (Fin 2) (Fin 2) ℂ where
  toFun g := if Multiplicative.toAdd g = 0 then 1 else swapMat
  map_one' := by simp [toAdd_one]
  map_mul' a b := by
    rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
      simp [toAdd_ofAdd, zmod2_one_add_one, swapMat_sq]

/-- σx as an element of GL(2,ℂ). -/
private noncomputable def swapGL : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero swapMat (by
    simp only [Matrix.det_fin_two, swapMat, Matrix.of_apply]; norm_num)

@[simp] private lemma swapGL_val :
    (swapGL : Matrix (Fin 2) (Fin 2) ℂ) = swapMat :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

private lemma swapGL_inv_val :
    ((swapGL⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = swapMat := by
  have hsq : swapGL * swapGL = 1 := by
    apply Units.ext; simp only [Units.val_mul, Units.val_one, swapGL_val, swapMat_sq]
  rw [show swapGL⁻¹ = swapGL from inv_eq_of_mul_eq_one_right hsq, swapGL_val]

/-- The Z₂ twist at the generator swaps A⁰ ↔ A¹. -/
private lemma ghz_twisted_generator_eq (i : Fin 2) :
    twistedTensor ghzTensor z2PhysicalAction (Multiplicative.ofAdd 1) i =
      ghzTensor (Fin.rev i) := by
  simp only [twistedTensor, z2PhysicalAction, MonoidHom.coe_mk, OneHom.coe_mk,
    toAdd_ofAdd, Fin.sum_univ_two]
  fin_cases i <;>
    ext a b <;> simp [swapMat, Matrix.of_apply, ghzTensor, Matrix.diagonal_apply,
      Pi.single_apply, Fin.rev]

/-- The swapped GHZ tensor is gauge equivalent to the original via σx. -/
private lemma ghz_gaugeEquiv_twisted :
    GaugeEquiv ghzTensor
      (twistedTensor ghzTensor z2PhysicalAction (Multiplicative.ofAdd 1)) := by
  refine ⟨swapGL, fun i => ?_⟩
  rw [ghz_twisted_generator_eq]
  rw [swapGL_inv_val, swapGL_val]
  ext a b
  simp only [ghzTensor, Matrix.diagonal_apply, Pi.single_apply, Fin.rev]
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [swapMat, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_two]

/-- The GHZ tensor is on-site symmetric under Z₂ = {1, σx}. -/
theorem ghz_isOnSiteSymmetric_Z2 :
    IsOnSiteSymmetric ghzTensor z2PhysicalAction := by
  intro g
  rcases zmod2_cases g with rfl | rfl
  · rw [twistedTensor_one]; exact fun _ _ => rfl
  · exact ghz_gaugeEquiv_twisted.sameMPV

end MPSTensor
