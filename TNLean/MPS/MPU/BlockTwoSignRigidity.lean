/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.CommonNormalBlocking
import TNLean.MPS.Core.PairProductSignRigidity
import TNLean.MPS.MPU.CanonicalForm

/-!
# Equal two-site blocks determine an MPU tensor up to sign

Let `𝒰` be in canonical form II. Its normalized flattening is a normal tensor,
so its words of length `D⁴` span the full matrix algebra. If another tensor
`𝒲` has the same two-site block, `blockTwo 𝒲 = blockTwo 𝒰`, then the
flattenings have equal products of two letters, and sign rigidity gives
`𝒲 = σ 𝒰` with `σ = ±1`.

This is the step from equality of the standard-form chains, which see only
the two-site block (arXiv:1703.09188, Definition `SF`, lines 603--622, read as
in `docs/paper-gaps/mpu_standard_form_canonical_convention.tex`), back to the
one-site tensor. The sign is genuine: the tensors `1` and `-1` of
`docs/paper-gaps/mpu_standard_form_parity_gap.tex` have equal two-site blocks.

## Main results

* `MPOTensor.IsMPUCanonicalFormII.exists_sign_eq_smul_of_blockTwo_eq`.
-/

open scoped Matrix

namespace MPOTensor

variable {d D : ℕ}

/-- **Sign rigidity for two-site blocks.** If `𝒰` is in canonical form II and
`blockTwo 𝒲 = blockTwo 𝒰`, then `𝒲 = σ 𝒰` with `σ = 1` or `σ = -1`.
This is the one-site recovery needed to read the conjugation hypothesis of
arXiv:1703.09188, `prop1conj` (lines 1008--1027), on the two-spin chain. -/
theorem IsMPUCanonicalFormII.exists_sign_eq_smul_of_blockTwo_eq {U W : MPOTensor d D}
    (hU : IsMPUCanonicalFormII U) (h : blockTwo W = blockTwo U) :
    ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧ W = σ • U := by
  let : NeZero d := hU.neZero_phys
  let : NeZero D := hU.neZero_bond
  have hnormal := hU.isNormalTensor_normalizedFlattening
  have hA := hnormal.isNBlkInjective_pow_four
  set c : ℂ := ((Real.sqrt d : ℂ)⁻¹) with hc
  have hc0 : c ≠ 0 := by
    have : (Real.sqrt d : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (by exact_mod_cast NeZero.pos d)).ne'
    exact inv_ne_zero this
  -- Equal products of two letters of the flattenings.
  have hletter : ∀ i j k l : Fin d, W i j * W k l = U i j * U k l := by
    intro i j k l
    have := congrFun (congrFun h (finProdFinEquiv (i, k))) (finProdFinEquiv (j, l))
    simpa [blockTwo] using this
  have hpair : ∀ a b : Fin (d * d),
      W.normalizedFlattening a * W.normalizedFlattening b =
        U.normalizedFlattening a * U.normalizedFlattening b := by
    intro a b
    simp only [normalizedFlattening, toMPSTensor, Matrix.smul_mul, Matrix.mul_smul,
      hletter]
  obtain ⟨σ, hσ, hCA⟩ := MPSTensor.exists_sign_eq_smul_of_pair_mul_eq hpair
    (Nat.pow_pos (NeZero.pos D)) hA
  refine ⟨σ, hσ, ?_⟩
  funext i j
  have := congrFun hCA (finProdFinEquiv (i, j))
  simp only [normalizedFlattening, toMPSTensor, Pi.smul_apply] at this
  have hdiv : (finProdFinEquiv (i, j)).divNat = i := by simp
  have hmod : (finProdFinEquiv (i, j)).modNat = j := by simp
  rw [hdiv, hmod, smul_comm σ] at this
  simpa only [Pi.smul_apply] using smul_right_injective _ hc0 this

end MPOTensor
