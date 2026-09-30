/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.UnitaryPhaseClassGrouping
import TNLean.MPS.Periodic.EqualCaseWeightNorm

/-!
# Weight normalization before grouping repeated periodic blocks

Equal-case matching determines the moduli of weights in an arbitrary
periodic block family, even when its blocks are repeated. Unitary grouping
preserves the modulus of every copy weight and its positive-length vectors.

Source: arXiv:1708.00029, Theorem 4.1, lines 752--765.
-/

open scoped Matrix

namespace MPSTensor

/-- Equality with a unit-weight periodic family forces unit modulus of every
weight in the other periodic family. Repeated blocks are allowed on both
sides. Source: arXiv:1708.00029, Theorem 4.1, lines 752--765. -/
theorem weight_norm_eq_one_of_periodic_block_families_sameMPV₂Pos
    {d r s : ℕ} {dim : Fin r → ℕ} {dim' : Fin s → ℕ}
    (A : (j : Fin r) → MPSTensor d (dim j)) (μ : Fin r → ℂ) (hμ : ∀ j, μ j ≠ 0)
    (B : (k : Fin s) → MPSTensor d (dim' k)) (ν : Fin s → ℂ) (hν : ∀ k, ‖ν k‖ = 1)
    (periodA : Fin r → ℕ) (periodB : Fin s → ℕ)
    (hPerA : ∀ j, IsPeriodic (periodA j) (A j))
    (hPerB : ∀ k, IsPeriodic (periodB k) (B k))
    (hSame : SameMPV₂Pos (toTensorFromBlocks μ A) (toTensorFromBlocks ν B)) :
    ∀ j, ‖μ j‖ = 1 := by
  classical
  obtain ⟨P, eP, perP, hPerP, hNonRepP, _, _, hNormP, hGroupP⟩ :=
    exists_unitary_phaseClass_grouping A μ hμ periodA hPerA
  obtain ⟨Q, eQ, perQ, hPerQ, hNonRepQ, _, _, hNormQ, hGroupQ⟩ :=
    exists_unitary_phaseClass_grouping B ν
      (fun k => Complex.ne_zero_of_norm_eq_one (hν k)) periodB hPerB
  obtain ⟨U, _, hU, hP⟩ := hGroupP (fun _ => 1)
  obtain ⟨V, _, hV, hQ⟩ := hGroupQ (fun _ => 1)
  have hSameP : SameMPV₂Pos P.toTensor (toTensorFromBlocks μ A) := by
    apply sameMPV₂Pos_of_coisometry_reconstruction _ _ Uᴴ
      (by simpa only [Matrix.conjTranspose_conjTranspose] using hU)
    intro i
    simpa only [SectorDecomposition.toTensor, one_mul,
      Matrix.conjTranspose_conjTranspose] using hP i
  have hSameQ : SameMPV₂Pos Q.toTensor (toTensorFromBlocks ν B) := by
    apply sameMPV₂Pos_of_coisometry_reconstruction _ _ Vᴴ
      (by simpa only [Matrix.conjTranspose_conjTranspose] using hV)
    intro i
    simpa only [SectorDecomposition.toTensor, one_mul,
      Matrix.conjTranspose_conjTranspose] using hQ i
  have hQunit : ∀ j q, ‖Q.weight j q‖ = 1 := by
    intro j q
    have h := (hNormQ (Q.flatIndexEquiv ⟨j, q⟩)).trans
      (hν (eQ (Q.flatIndexEquiv ⟨j, q⟩)))
    simpa only [SectorDecomposition.flatWeight_flatIndexEquiv] using h
  have hPunit := P.weight_norm_eq_one_of_periodic_sameMPV₂Pos Q perP perQ
    hPerP hPerQ hNonRepP hNonRepQ (hSameP.trans (hSame.trans hSameQ.symm)) hQunit
  intro j
  calc ‖μ j‖ = ‖P.flatWeight (eP.symm j)‖ := by
        simpa only [Equiv.apply_symm_apply] using (hNormP (eP.symm j)).symm
    _ = 1 := hPunit _ _

end MPSTensor
