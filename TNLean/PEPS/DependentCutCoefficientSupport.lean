/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.DependentCutBondSupport

/-!
# Extracted labels obey the constraints on every uncut edge

A trace-dual coefficient of an actual canonical cut vector can be nonzero
only if one vertex group labeling realizes its relative edge labels on all
uncut edges simultaneously. The cut boundary is arbitrary and correlated.
This isolates the graph-independent coefficient step of SCP10 Theorem 5.5;
any further flatness consequence is a property of the chosen cut geometry.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS.DependentBondNetwork

variable {Vertex Edge G : Type*} [Group G] [Fintype G]
variable [Fintype Vertex] [Fintype Edge] [DecidableEq Vertex] [DecidableEq Edge]
variable (tail head : Edge → Vertex) (D : Edge → Type*)
variable [∀ e, Fintype (D e)] [∀ e, DecidableEq (D e)]

/-- If no vertex labeling realizes all uncut relative labels, the extracted
coefficient vanishes for arbitrary insertions on the cut edges. -/
theorem bondCoefficientExtraction_network_eq_zero_of_incompatible
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (hU : ∀ e, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)))
    (C : Finset Edge) (B : (e : Edge) → Matrix (D e) (D e) ℂ)
    (hB : ∀ e, e ∉ C → B e = 1) (p : Edge → G)
    (hincompat : ¬ ∃ q : Vertex → G, ∀ e, e ∉ C → p e = q (head e) * (q (tail e))⁻¹) :
    bondCoefficientExtraction tail head D U p
      (network tail head D (averagingSite tail head D U) B) = 0 := by
  classical
  rw [bondCoefficientExtraction_network_averagingSite]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro q _
  obtain ⟨e, he, hne⟩ : ∃ e, e ∉ C ∧ p e ≠ q (head e) * (q (tail e))⁻¹ := by
    by_contra h
    apply hincompat
    refine ⟨q, fun e he => ?_⟩
    by_contra hne
    exact h ⟨e, he, hne⟩
  apply Finset.prod_eq_zero (Finset.mem_univ e)
  rw [hB e he, Matrix.mul_one, ← map_mul, torusDeltaPairing_apply_rep _ (hU e)]
  exact ite_eq_right hne

/-- A nonrealizable off-cut label has zero coefficient in every actual cut
vector, including vectors from arbitrary joint boundary tensors. -/
theorem bondCoefficientExtraction_eq_zero_of_mem_cutSpace_of_incompatible
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (hU : ∀ e, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)))
    (C : Finset Edge) (p : Edge → G)
    {ψ : ((v : Vertex) → LocalConfig tail head D v) → ℂ}
    (hψ : ψ ∈ cutSpace tail head D (averagingSite tail head D U) C)
    (hincompat : ¬ ∃ q : Vertex → G, ∀ e, e ∉ C → p e = q (head e) * (q (tail e))⁻¹) :
    bondCoefficientExtraction tail head D U p ψ = 0 := by
  classical
  obtain ⟨M, rfl⟩ := hψ
  rw [cutMap_eq_sum_single, map_sum]
  apply Finset.sum_eq_zero
  intro η _
  rw [map_smul]
  have hnet := funext (cutMap_single_eq_network tail head D (averagingSite tail head D U) C η)
  rw [hnet, bondCoefficientExtraction_network_eq_zero_of_incompatible
    tail head D U hU C (cutBondUnits D C η) (by intro e he; simp [cutBondUnits, he]) p hincompat,
    smul_zero]

/-- Every nonzero extracted cut coefficient has a simultaneous vertex-label
realization on all uncut edges. No factorization of the boundary is assumed. -/
theorem exists_vertexLabels_of_bondCoefficientExtraction_ne_zero
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (hU : ∀ e, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)))
    (C : Finset Edge) (p : Edge → G)
    {ψ : ((v : Vertex) → LocalConfig tail head D v) → ℂ}
    (hψ : ψ ∈ cutSpace tail head D (averagingSite tail head D U) C)
    (hne : bondCoefficientExtraction tail head D U p ψ ≠ 0) :
    ∃ q : Vertex → G, ∀ e, e ∉ C → p e = q (head e) * (q (tail e))⁻¹ := by
  classical
  by_contra h
  exact hne (bondCoefficientExtraction_eq_zero_of_mem_cutSpace_of_incompatible
    tail head D U hU C p hψ h)

end TNLean.PEPS.DependentBondNetwork
