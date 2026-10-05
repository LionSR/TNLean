/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularWeightedOpenContraction
import TNLean.PEPS.RegularEdgeChargeContraction

/-!
# A literal weighted contraction is the actual charge-inserted tensor network

Source: SCP10, arXiv:1001.3807, diagonal charge insertion, lines 2432–2453,
and `eq:anyons:chargeon-move-setting`, lines 2489–2507.
-/
noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}

/-- A weight on one actual internal bond equals the original open contraction
with the literal diagonal insertion on its ordered tail site.
Source: SCP10, `eq:anyons:chargeon-def`, lines 2432–2453. -/
theorem regularWeightedOpenRegionWeight_eq_openRegionWeight_regularEdgeCharacterSite
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (R : Finset V) (e : {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R})
    (χ : G → ℂ) (p : G) (θ : {b : Edge Γ // IsRegionBoundaryEdge R b} → G) :
    regularWeightedOpenRegionWeight a R (fun _ => 1)
        (fun η => χ (p * η ⟨e.1, Or.inl e.2.1⟩)) θ =
      openRegionWeight (groupBondTensor (regularEdgeCharacterSite a e.1 χ p)) R
        (fun b => Fintype.equivFin G (θ b)) := by
  classical
  have hsite (v : V) (α : IncidentEdge Γ v → G) :
      regularTwistedLabels (fun _ => (1 : G)) v α = α := by
    funext i
    simp only [regularTwistedLabels, one_mul, ite_self]
  have hone : regularTwistedSite (regularEdgeCharacterSite a e.1 χ p)
      (fun _ => 1) = regularEdgeCharacterSite a e.1 χ p := by
    funext v α s
    simp only [regularTwistedSite, hsite]
  rw [← hone, ← regularWeightedOpenRegionWeight_one]
  funext σ
  unfold regularWeightedOpenRegionWeight
  apply Finset.sum_congr rfl
  intro η _
  split_ifs
  · simp only [one_mul, hsite]
    have he (w : {v : V // v ∈ R}) :
        regularEdgeCharacterSite a e.1 χ p w.1
            (fun i => η ⟨i.1, isRegionIncidentEdge_of_regionVertex R w i⟩) (σ w) =
          (if w = ⟨e.1.1.1,e.2.1⟩ then χ (p * η ⟨e.1,Or.inl e.2.1⟩) else 1) *
            a w.1 (fun i => η ⟨i.1, isRegionIncidentEdge_of_regionVertex R w i⟩) (σ w) := by
      by_cases hw : w.1 = e.1.1.1
      · have hsub : w = ⟨e.1.1.1,e.2.1⟩ := Subtype.ext hw
        subst w
        simp only [regularEdgeCharacterSite, dite_true, ite_true]
      · have hsub : w ≠ ⟨e.1.1.1,e.2.1⟩ := fun h => hw (congrArg Subtype.val h)
        simp only [regularEdgeCharacterSite, dite_eq_right hw, ite_eq_right hsub, one_mul]
    simp_rw [he]
    rw [Finset.prod_mul_distrib]
    simp only [Fintype.prod_ite_eq']
  · rfl
end TNLean.PEPS
