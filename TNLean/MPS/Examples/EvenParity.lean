/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.RFP.Defs
import TNLean.MPS.Symmetry.Defs
import TNLean.MPS.Examples.GHZ

/-!
# Even-parity (Z₂ group-algebra) MPS tensor

This module defines the even-parity MPS tensor with physical dimension `d = 2`
and bond dimension `D = 2`, and proves its key properties.

The tensor uses `A⁰ = (1/√2) I` and `A¹ = (1/√2) σx`, which generates the
abelian group algebra `ℂ[Z₂] = span{I, σx}` inside `M₂(ℂ)`. On a periodic
chain of `N` sites, it produces the equal superposition of all even-parity
bit strings: `∑_{|s| ≡ 0 mod 2} |s⟩`.

**Note**: This is *not* the 1D cluster state. The cluster state MPS uses
`A⁰ = |0⟩⟨+|` and `A¹ = |1⟩⟨-|` (arXiv:2011.12127, Section III.B), which
lies in a non-trivial SPT phase.

## Main definitions

* `evenParityTensor` : the even-parity MPS tensor with `A⁰ = (1/√2) I`,
  `A¹ = (1/√2) σx`
* `evenParityZ2Action` : the Z₂ on-site representation via Pauli Z (σz)

## Main results

* `evenParity_isRFP` : the tensor is a renormalization fixed point
* `evenParity_not_isInjective` : the tensor is not injective
* `evenParity_isOnSiteSymmetric_Z2` : the tensor is on-site symmetric under Z₂
-/

open scoped Matrix BigOperators
open Matrix Finset MPSTensor

namespace MPSTensor

/-! ### Definition -/

/-- The even-parity MPS tensor: `A⁰ = (1/√2) I` and `A¹ = (1/√2) σx`.

This generates the abelian group algebra `span{I, σx} ≅ ℂ[Z₂]` inside `M₂(ℂ)`.
On a periodic chain of `N` sites, `Tr(A^{s₁} ⋯ A^{sN}) ∝ δ(∑sᵢ ≡ 0 mod 2)`,
giving the equal superposition of even-parity bit strings. -/
noncomputable def evenParityTensor : MPSTensor 2 2 := fun i =>
  (1 / Real.sqrt 2 : ℂ) • (if i = 0 then 1 else pauliX)

@[simp] lemma evenParityTensor_zero :
    evenParityTensor 0 = (1 / Real.sqrt 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp [evenParityTensor]

@[simp] lemma evenParityTensor_one :
    evenParityTensor 1 = (1 / Real.sqrt 2 : ℂ) • pauliX := by
  simp [evenParityTensor]

/-! ### Transfer map and RFP -/

private lemma inv_sqrt2_mul_self :
    (1 / (↑(Real.sqrt 2) : ℂ)) * (1 / ↑(Real.sqrt 2)) = 1 / 2 := by
  rw [div_mul_div_comm, one_mul]
  congr 1
  push_cast [← Complex.ofReal_mul]
  exact_mod_cast Real.mul_self_sqrt (show (2 : ℝ) ≥ 0 by norm_num)

/-- The transfer map of the even-parity tensor symmetrises diagonal and off-diagonal:
`E(X)ᵢⱼ = c²(Xᵢⱼ + X₍₁₋ᵢ₎₍₁₋ⱼ₎)` where `c = 1/√2`. -/
private lemma evenParity_transferMap_entry (X : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    let c := 1 / (↑(Real.sqrt 2) : ℂ)
    (transferMap evenParityTensor X) i j =
      c * c * (X i j + X (Fin.rev i) (Fin.rev j)) := by
  simp only [transferMap_apply, Fin.sum_univ_two, evenParityTensor_zero, evenParityTensor_one]
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Fin.rev, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul] <;>
    ring

/-- The transfer map of the even-parity tensor is idempotent: `E² = E`. -/
theorem evenParity_transferMap_idempotent :
    transferMap evenParityTensor ∘ₗ transferMap evenParityTensor =
      transferMap evenParityTensor := by
  ext X i j : 3
  simp only [LinearMap.comp_apply]
  rw [evenParity_transferMap_entry, evenParity_transferMap_entry,
    evenParity_transferMap_entry]
  simp only [Fin.rev_rev, inv_sqrt2_mul_self]
  ring

/-- The even-parity tensor is a renormalization fixed point. -/
theorem evenParity_isRFP : IsRFP evenParityTensor := evenParity_transferMap_idempotent

/-! ### Non-injectivity -/

/-- Every element of `span{A⁰, A¹}` satisfies `M 0 0 = M 1 1`, since both
`I` and `σx` have equal diagonal entries. -/
private lemma evenParity_span_diag_eq :
    ∀ M ∈ Submodule.span ℂ (Set.range evenParityTensor), M 0 0 = M 1 1 := by
  intro M hM
  induction hM using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    fin_cases k <;> simp [evenParityTensor, pauliX, Matrix.of_apply]
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

/-- The even-parity tensor is **not** injective: `span{(1/√2)I, (1/√2)σx}` is the
2-dimensional commutative subalgebra `{aI + bσx}`, not the full 4-dimensional
matrix algebra `M₂(ℂ)`. -/
theorem evenParity_not_isInjective : ¬ IsInjective evenParityTensor := by
  intro h
  have hmem : Matrix.diagonal (Pi.single (0 : Fin 2) (1 : ℂ)) ∈
      Submodule.span ℂ (Set.range evenParityTensor) := h ▸ Submodule.mem_top
  have heq := evenParity_span_diag_eq _ hmem
  simp at heq

/-! ### Z₂ on-site symmetry via σz -/

/-- The Pauli Z matrix `σz = !![1, 0; 0, -1]`. -/
private def pauliZ : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j => if i = j then (if i = 0 then 1 else -1) else 0

private lemma pauliZ_sq : pauliZ * pauliZ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliZ, Matrix.of_apply, Matrix.mul_apply]

/-- The Z₂ on-site representation via Pauli Z. We use `Multiplicative (ZMod 2)` as the
group: the identity corresponds to `ofAdd 0` and the generator to `ofAdd 1`.
`U(0) = 1` (identity), `U(1) = σz` (Pauli Z). -/
noncomputable def evenParityZ2Action :
    Multiplicative (ZMod 2) →* Matrix (Fin 2) (Fin 2) ℂ where
  toFun g := if Multiplicative.toAdd g = 0 then 1 else pauliZ
  map_one' := by simp [toAdd_one]
  map_mul' a b := by
    rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
      simp [toAdd_ofAdd, zmod2_one_add_one, pauliZ_sq]

/-- σz as an element of GL(2,ℂ). -/
private noncomputable def pauliZGL : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero pauliZ (by
    simp only [Matrix.det_fin_two, pauliZ, Matrix.of_apply]; norm_num)

@[simp] private lemma pauliZGL_val :
    (pauliZGL : Matrix (Fin 2) (Fin 2) ℂ) = pauliZ :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

private lemma pauliZGL_inv_val :
    ((pauliZGL⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = pauliZ := by
  have hsq : pauliZGL * pauliZGL = 1 := by
    apply Units.ext; simp only [Units.val_mul, Units.val_one, pauliZGL_val, pauliZ_sq]
  rw [show pauliZGL⁻¹ = pauliZGL from inv_eq_of_mul_eq_one_right hsq, pauliZGL_val]

/-- σz conjugation flips the sign of σx: `σz σx σz = -σx`. -/
private lemma pauliZ_pauliX_pauliZ : pauliZ * pauliX * pauliZ = -pauliX := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliZ, pauliX, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.neg_apply]

/-- The Z₂ twist at the generator maps `A⁰ ↦ A⁰` and `A¹ ↦ -A¹`. -/
private lemma evenParity_twisted_generator_eq (i : Fin 2) :
    twistedTensor evenParityTensor evenParityZ2Action (Multiplicative.ofAdd 1) i =
      (1 / Real.sqrt 2 : ℂ) •
        (if i = 0 then (1 : Matrix (Fin 2) (Fin 2) ℂ) else -pauliX) := by
  simp only [twistedTensor, evenParityZ2Action, MonoidHom.coe_mk, OneHom.coe_mk,
    toAdd_ofAdd, Fin.sum_univ_two]
  fin_cases i
  · simp [pauliZ, evenParityTensor, pauliX, Matrix.of_apply]
  · ext a b; fin_cases a <;> fin_cases b <;>
      simp [pauliZ, evenParityTensor, pauliX, Matrix.of_apply]

/-- The twisted even-parity tensor at the generator is gauge equivalent to the
original via σz. -/
private lemma evenParity_gaugeEquiv_twisted :
    GaugeEquiv evenParityTensor
      (twistedTensor evenParityTensor evenParityZ2Action
        (Multiplicative.ofAdd 1)) := by
  refine ⟨pauliZGL, fun i => ?_⟩
  rw [evenParity_twisted_generator_eq]
  rw [pauliZGL_inv_val, pauliZGL_val]
  fin_cases i <;> simp [pauliZ_sq, pauliZ_pauliX_pauliZ]

/-- The even-parity tensor is on-site symmetric under Z₂ = {1, σz}, where σz acts
on the physical index by flipping the relative phase of `A¹`. -/
theorem evenParity_isOnSiteSymmetric_Z2 :
    IsOnSiteSymmetric evenParityTensor evenParityZ2Action := by
  intro g
  rcases zmod2_cases g with rfl | rfl
  · rw [twistedTensor_one]; exact fun _ _ => rfl
  · exact evenParity_gaugeEquiv_twisted.sameMPV

end MPSTensor
