/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularTwoSiteChargeDetector
import TNLean.PEPS.RegularChargeDetectorMatrix
import TNLean.Algebra.PermutationMatrixUnitary
import TNLean.PEPS.RegularTorusGramExpansion

import TNLean.Algebra.PermutationMatrixCommutation

/-!
# Two local averages commute with the shared charge projector

The actual group-pair detector kernel is invariant under independent endpoint
translations. Extending it by the identity preserves this invariance and gives
commutation with both local regular averaging projectors.

Source: SCP10, arXiv:1001.3807, charge detection, lines 2470–2486.
This is an auxiliary finite-leg coefficient statement; no supplied physical
measurement, nonvanishing or parent-Hamiltonian claim enters the calculation.
-/

noncomputable section
open scoped BigOperators Matrix Kronecker
namespace TNLean.PEPS
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Independent vertex translations preserve the lifted charge projector kernel.
Source: SCP10, lines 2470–2486. -/
theorem regularTwoSiteChargeDetector_translate_entries (i : ι) (j : κ)
    (χ : G → ℂ) (x y : G) (α β : (ι → G) × (κ → G)) :
    regularTwoSiteChargeDetector i j χ (x • α.1, y • α.2) (x • β.1, y • β.2) =
      regularTwoSiteChargeDetector i j χ α β := by
  simp only [regularTwoSiteChargeDetector, Matrix.submatrix_apply, regularSharedLegEquiv,
    Equiv.trans_apply, Equiv.prodCongr_apply,
    Equiv.prodProdProdComm_apply, Matrix.kronecker, Matrix.kroneckerMap]
  change regularChargeDetectorMatrix χ (x * α.1 i, y * α.2 j) (x * β.1 i, y * β.2 j) *
    (1 : Matrix _ _ ℂ) (x • (fun e : {e : ι // e ≠ i} => α.1 e),
      y • (fun e : {e : κ // e ≠ j} => α.2 e))
      (x • (fun e : {e : ι // e ≠ i} => β.1 e),
        y • (fun e : {e : κ // e ≠ j} => β.2 e)) = _
  rw [regularChargeDetectorMatrix_translate_entries]
  simp [Matrix.one_apply, Prod.mk.injEq, smul_left_cancel_iff]

private def twoSiteTranslation (x y : G) : Equiv.Perm ((ι → G) × (κ → G)) :=
  (MulAction.toPermHom G (ι → G) x).prodCongr (MulAction.toPermHom G (κ → G) y)

private theorem twoSite_projector_average :
    (regularLegProjector (G := G) ι) ⊗ₖ regularLegProjector κ =
      (Fintype.card G : ℂ)⁻¹ ^ 2 • ∑ x : G, ∑ y : G,
        Matrix.permMatrixHom (R := ℂ) (twoSiteTranslation (ι := ι) (κ := κ) x y) := by
  ext ⟨α₁, α₂⟩ ⟨β₁, β₂⟩
  simp only [Matrix.kroneckerMap, Matrix.of_apply, regularLegProjector_apply, Matrix.smul_apply,
    Matrix.sum_apply, smul_eq_mul, permMatrixHom_apply_eq_ite, twoSiteTranslation,
    Equiv.prodCongr_apply, MulAction.toPermHom_apply, Prod.map_apply, Prod.mk.injEq]
  simp only [Finset.sum_mul, Finset.mul_sum]
  simp only [pow_two, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  split_ifs <;> simp_all

/-- The actual shared charge detector commutes with both local regular averages.
Source: SCP10, lines 2470–2486. -/
theorem regularTwoSiteChargeDetector_commute_projector (i : ι) (j : κ) (χ : G → ℂ) :
    Commute (regularTwoSiteChargeDetector i j χ)
      ((regularLegProjector (G := G) ι) ⊗ₖ regularLegProjector κ) := by
  rw [twoSite_projector_average]
  apply Commute.smul_right
  apply Commute.sum_right
  intro x _
  apply Commute.sum_right
  intro y _
  let e := twoSiteTranslation (ι := ι) (κ := κ) x y
  change Commute (regularTwoSiteChargeDetector i j χ) (Equiv.Perm.permMatrix ℂ e.symm)
  apply Matrix.commute_permMatrix_of_entry_invariant
  intro α β
  have h := regularTwoSiteChargeDetector_translate_entries i j χ x y (e.symm α) (e.symm β)
  change regularTwoSiteChargeDetector i j χ (e (e.symm α)) (e (e.symm β)) = _ at h
  simpa only [e.apply_symm_apply] using h.symm

end TNLean.PEPS
