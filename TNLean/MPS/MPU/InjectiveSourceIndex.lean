/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.InjectiveCanonicalRepresentative
import TNLean.MPS.MPU.RepresentativeIndex
import TNLean.MPS.MPU.SimpleSupportCompression

/-!
# Source-cut ranks and the index of simple injective tensors

For a simple injective matrix product unitary of physical dimension \(d\), the
two source-cut ranks satisfy \(r\ell=d^2\), and the index is
\(\frac12(\log_2 r-\log_2\ell)\). No canonical form is assumed for the original
tensor: injectivity forces its reduced canonical representative to have the
same bond dimension, and the resulting invertible bond similarity preserves
both source ranks and simplicity.

Source: arXiv:1703.09188, Theorem `ThmFund1` and Definition `def:index`,
lines 520--573 and 681--704; arXiv:2502.20257, lines 1403--1407 and 1547.
-/

namespace MPOTensor

variable {d D : ℕ}

private theorem blockTensor_one_eq_reindexPhysical (U : MPOTensor d D) :
    blockTensor U 1 = reindexPhysical (Kraus.singleBlockEquiv d) U := by
  ext i j
  simp [blockTensor, reindexPhysical, MPSTensor.wordOfBlock, Kraus.wordOfBlock_one]

private theorem canonical_index_eq_logb_of_isMPUSimple {U : MPOTensor d D}
    (hU : IsMPUCanonicalFormII U) (hS : IsMPUSimple U) :
    hU.index = (1 / 2 : ℝ) * (Real.logb 2 r[U] - Real.logb 2 ℓ[U]) := by
  have hS₁ : IsMPUSimple (blockTensor U 1) := by
    rw [blockTensor_one_eq_reindexPhysical]
    exact hS.reindexPhysical (Kraus.singleBlockEquiv d)
  rw [hU.index_eq_logb_of_isMPUSimple_blockTensor (by omega) hS₁,
    blockTensor_one_eq_reindexPhysical, rightRank_reindexPhysical,
    leftRank_reindexPhysical]

private theorem exists_cfii_simple_same_sourceRanks [NeZero d]
    {U : MPOTensor d D} (hU : IsMPU U)
    (hI : Kraus.IsInjective U.toMPSTensor) (hS : IsMPUSimple U) :
    ∃ V : MPOTensor d D, ∃ _hV : IsMPUCanonicalFormII V,
      IsMPUSimple V ∧ r[V] = r[U] ∧ ℓ[V] = ℓ[U] ∧
        ∀ N : ℕ, 0 < N → mpo V N = mpo U N := by
  obtain ⟨V, hV, X, hX, hMpo⟩ := hU.exists_cfii_representative_of_isInjective hI
  have hVeq : V = virtualSandwich (X : Matrix (Fin D) (Fin D) ℂ) U
      ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) :=
    funext fun i => funext fun j => hX i j
  have hS' : IsMPUSimple V := by
    rw [hVeq]
    exact hS.rectangularSandwich _ _ (by simp)
  have hR : r[V] = r[U] := by
    rw [hVeq]
    exact rightRank_virtualSandwich _ U _ ⟨X, rfl⟩ ⟨X⁻¹, rfl⟩
  have hL : ℓ[V] = ℓ[U] := by
    rw [hVeq]
    exact leftRank_virtualSandwich _ U _ ⟨X, rfl⟩ ⟨X⁻¹, rfl⟩
  exact ⟨V, hV, hS', hR, hL, hMpo⟩

/-- The two source ranks of a simple injective matrix product unitary have
product equal to the square of the physical dimension. Canonical form is
obtained by an invertible bond similarity, rather than assumed for the given
tensor. Source: CPSV17, Theorem `ThmFund1`, lines 562--573; FBC25,
arXiv:2502.20257, lines 1403--1407 and 1547. -/
theorem IsMPU.rightRank_mul_leftRank_of_isInjective_of_isMPUSimple [NeZero d]
    {U : MPOTensor d D} (hU : IsMPU U)
    (hI : Kraus.IsInjective U.toMPSTensor) (hS : IsMPUSimple U) :
    r[U] * ℓ[U] = d ^ 2 := by
  obtain ⟨V, hV, hS', hR, hL, _⟩ := exists_cfii_simple_same_sourceRanks hU hI hS
  have hprod := (hV.isMPUSimple_tfae.out 1 2).mp hS'
  simpa only [hR, hL, pow_two] using hprod

/-- For a simple injective tensor, the representative-defined index is the
half-difference of the logarithms of its original source-cut ranks. No
canonical-form presentation of the original tensor is supplied. Source:
CPSV17, Definition `def:index` and Proposition `index-well-defined`,
lines 681--704; FBC25, arXiv:2502.20257, line 1547. -/
theorem IsMPU.index_eq_logb_of_isInjective_of_isMPUSimple [NeZero d] [NeZero D]
    {U : MPOTensor d D} (hU : IsMPU U)
    (hI : Kraus.IsInjective U.toMPSTensor) (hS : IsMPUSimple U) :
    hU.index = (1 / 2 : ℝ) * (Real.logb 2 r[U] - Real.logb 2 ℓ[U]) := by
  obtain ⟨V, hV, hS', hR, hL, hMpo⟩ := exists_cfii_simple_same_sourceRanks hU hI hS
  rw [hU.index_eq_canonical_representative hV hMpo,
    canonical_index_eq_logb_of_isMPUSimple hV hS', hR, hL]

end MPOTensor
