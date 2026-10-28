/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.GluingCoordinates
import TNLean.MPS.AreaLaw.ViableSet.LeftColumns
import QICLean.Channel.BoundaryDensitySelection

/-!
# A finite family of minimizing boundary states

For every feasible point in a prescribed finite boundary set, choose a density matrix that
globally minimizes the left energy and a unit eigenvector for its largest eigenvalue. The
left columns of these vectors form an explicit finite set contained in the prescribed left
span. The choices use only that span, the left Hamiltonian, the bond dimension and the
boundary set; no ground vector or physical extension of the right bond is supplied.

This is an auxiliary construction for Landau, Vazirani and Vidick, arXiv:1307.5143v1,
`References/1307.5143/algo53.tex`, equation `eq:conv`, lines 472–476, the column extraction,
lines 477–478, and Claim `c:2`, lines 520–527. Only feasible boundary points are retained.
The theorem concerns a fixed actual bond dimension and asserts neither viability nor the
source's quantitative AKLV bound. It asserts no matrix product state bond budget; the
positive-budget convention of `IsLeftOpenMPS` remains in that definition.
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace TNLean.MPS.AreaLaw

variable {L q k : ℕ}

/-- Choose global minimizers and top unit eigenvectors at exactly the feasible points of a
finite boundary set, and retain all their left columns. This is the fixed-bond construction
in LVV13, `algo53.tex`, equation `eq:conv`, lines 472–478, and Claim `c:2`, lines 520–527. -/
theorem exists_finite_boundary_minimizer_family (S : Set (LeftBlockVector L q k))
    (HL : Matrix (CutLeft L q k × CutSite L q k) (CutLeft L q k × CutSite L q k) ℂ)
    (m : ℕ) (η : ℝ)
    (N : Finset (Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ)) :
    let P := reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection S)
    let feasible := fun X : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ ↦
      {ρ : Matrix ((CutLeft L q k × CutSite L q k) × Fin m)
          ((CutLeft L q k × CutSite L q k) × Fin m) ℂ |
        ρ.PosSemidef ∧ ρ.trace = 1 ∧ (P ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * ρ = ρ ∧
        rectangularTraceNorm (partialTraceFirst ρ - X) ≤ η}
    ∃ (F : Finset (Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ))
      (σ : F → Matrix ((CutLeft L q k × CutSite L q k) × Fin m)
        ((CutLeft L q k × CutSite L q k) × Fin m) ℂ)
      (u : F → EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m))
      (μ : F → ℝ) (T : Finset (LeftBlockVector L q k)),
      (∀ X, X ∈ F ↔ X ∈ N ∧ (feasible X).Nonempty) ∧
      T = leftColumns (Finset.univ : Finset F)
        (fun X ↦ gluingLeftCoordinates L q k m (u X)) ∧
      T.card ≤ m * N.card ∧ (T : Set (LeftBlockVector L q k)) ⊆ Submodule.span ℂ S ∧
      ∀ X : F, σ X ∈ feasible X ∧
        (∀ ρ ∈ feasible X,
          (σ X * (HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re ≤
            (ρ * (HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re) ∧
        ‖u X‖ = 1 ∧ 0 < μ X ∧
        σ X *ᵥ WithLp.ofLp (u X) = (μ X : ℂ) • WithLp.ofLp (u X) ∧
        (P ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) *ᵥ WithLp.ofLp (u X) = WithLp.ofLp (u X) ∧
        ∀ (ν : ℝ) (w : EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m)),
          w ≠ 0 → σ X *ᵥ WithLp.ofLp w = (ν : ℂ) • WithLp.ofLp w → ν ≤ μ X := by
  classical
  intro P feasible
  let F := N.filter fun X ↦ (feasible X).Nonempty
  have hF (X : F) : (feasible X).Nonempty := (Finset.mem_filter.mp X.property).2
  choose σ u μ hspec using
    fun X : F ↦ exists_boundary_density_minimizer_max_eigenvector
      (a := CutLeft L q k) (s := CutSite L q k) (b := Fin m) P HL X η (hF X)
  refine ⟨F, σ, u, μ, leftColumns Finset.univ
    (fun X ↦ gluingLeftCoordinates L q k m (u X)), ?_, rfl, ?_, ?_, ?_⟩
  · exact fun X ↦ Finset.mem_filter
  · calc
      _ ≤ F.card * m := by
        simpa only [Finset.card_univ, Fintype.card_coe] using
          card_leftColumns_le (Finset.univ : Finset F)
            (fun X ↦ gluingLeftCoordinates L q k m (u X))
      _ ≤ N.card * m := Nat.mul_le_mul_right m (Finset.card_filter_le _ _)
      _ = m * N.card := Nat.mul_comm _ _
  · exact leftColumns_subset_span S _ _ (fun X _ ↦
      (gluingLeftCoordinates_spanProjection_eq_iff S (u X)).mp
        (hspec X).2.2.2.2.2.2.2.2.1)
  · simpa only [feasible, Set.mem_ofPred_eq, and_imp, and_assoc] using hspec

end TNLean.MPS.AreaLaw
