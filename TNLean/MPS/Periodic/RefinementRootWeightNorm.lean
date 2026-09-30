/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.GroupedWeightNormalization
import TNLean.MPS.Periodic.BlockedFamilyPhaseTwist

/-!
# Normalization of the periodic refinement root

An arbitrary positive blocking raises the outer block weights to powers.
Comparison with a unit-weight periodic target forces each of these powered
weights to have modulus one. Since the blocking length is positive, the
original weights have modulus one and their direct-sum root is trace preserving.

Source: arXiv:1708.00029, Theorem 4.1, lines 752--765.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-- The weights of a periodic root are normalized by equality of its blocked
vectors with those of a unit-weight periodic target. No canonical
normalization of the root weights is assumed.
Source: arXiv:1708.00029, Theorem 4.1, lines 752--765. -/
theorem weight_norm_eq_one_of_blocked_periodic_sameMPV₂Pos
    {d r s : ℕ} {dim : Fin r → ℕ} {dim' : Fin s → ℕ}
    (A : (j : Fin r) → MPSTensor d (dim j)) (μ : Fin r → ℂ) (hμ : ∀ j, μ j ≠ 0)
    (periodA : Fin r → ℕ) (hPerA : ∀ j, IsPeriodic (periodA j) (A j))
    {p : ℕ} (hp : 0 < p)
    (B : (k : Fin s) → MPSTensor (blockPhysDim d p) (dim' k))
    (ν : Fin s → ℂ) (hν : ∀ k, ‖ν k‖ = 1)
    (periodB : Fin s → ℕ) (hPerB : ∀ k, IsPeriodic (periodB k) (B k))
    (hSame : SameMPV₂Pos (blockTensor (toTensorFromBlocks μ A) p)
      (toTensorFromBlocks ν B)) :
    (∀ j, ‖μ j‖ = 1) ∧ IsLeftCanonical (toTensorFromBlocks μ A) := by
  classical
  let count := fun j => Nat.gcd (periodA j) p
  obtain ⟨innerDim, C, Y, _, hPerC, _, hY, hbase, _⟩ :=
    exists_unitary_phaseTwisted_block_family A μ periodA hPerA hp
  let F := nestedBlockFlatTensor count innerDim C
  let weight : Fin (∑ j, count j) → ℂ := fun x => μ (finSigmaFinEquiv.symm x).1 ^ p
  let per : Fin (∑ j, count j) → ℕ := fun x =>
    periodA (finSigmaFinEquiv.symm x).1 / count (finSigmaFinEquiv.symm x).1
  have hBaseSame : SameMPV₂Pos (blockTensor (toTensorFromBlocks μ A) p)
      (toTensorFromBlocks weight F) := by
    apply sameMPV₂Pos_of_coisometry_reconstruction _ _ Yᴴ
      (by simpa only [Matrix.conjTranspose_conjTranspose] using hY)
    intro I
    simpa only [Matrix.conjTranspose_conjTranspose] using hbase I
  have hweight := weight_norm_eq_one_of_periodic_block_families_sameMPV₂Pos
    F weight (fun x => pow_ne_zero p (hμ _)) B ν hν per periodB
    (fun x => hPerC (finSigmaFinEquiv.symm x).1 (finSigmaFinEquiv.symm x).2)
    hPerB (hBaseSame.symm.trans hSame)
  have hnorm : ∀ j, ‖μ j‖ = 1 := by
    intro j
    have hcount : 0 < count j := Nat.gcd_pos_of_pos_left p (hPerA j).period_pos
    let a : Fin (count j) := ⟨0, hcount⟩
    have hpow : ‖μ j‖ ^ p = 1 := by
      have h := hweight (finSigmaFinEquiv ⟨j, a⟩)
      simpa only [weight, Equiv.symm_apply_apply, norm_pow] using h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hp.ne').mp hpow
  exact ⟨hnorm, leftCanonical_toTensorFromBlocks_of_weight_norm_one A μ
    (fun j => (hPerA j).leftCanonical) hnorm⟩

end MPSTensor
