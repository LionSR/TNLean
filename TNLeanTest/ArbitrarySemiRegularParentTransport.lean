/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.SemiRegularGInjectiveParentTransport

/-! # Actual two-site and empty-graph arbitrary-representation regressions -/
noncomputable section
open TNLean.PEPS

private abbrev Γ : SimpleGraph (Fin 2) := ⊤
private theorem incidence_one (v : Fin 2) : Fintype.card (IncidentEdge Γ v) = 1 := by
  fin_cases v <;> decide

-- This invokes the derived block factory and arbitrary-multiplicity capstone, not
-- a supplied Fourier or decomposition hypothesis.
example {G : Type*} [Group G] [Fintype G] [DecidableEq G] :
    Nonempty (regionParentGroundSpace (numberedGraphDressedAveragingTensor
      (leftRegularMatrix G) 1 (countedIncidentEnumeration G 1 incidence_one))
        (fun _ : Unit => Finset.univ) ≃ₗ[ℂ]
      regionParentGroundSpace (numberedGraphDressedAveragingTensor
      (leftRegularMatrix G) 1 (countedIncidentEnumeration G 1 incidence_one))
        (fun _ : Unit => Finset.univ)) := by
  have hU : ∀ g, leftRegularMatrix G g ∈ Matrix.unitaryGroup G ℂ := by
    intro g
    change Matrix.permMatrixHom (MulAction.toPermHom G G g) ∈ _
    rw [Matrix.permMatrixHom_apply]
    exact ((MulAction.toPermHom G G g)⁻¹).permMatrix_mem_unitaryGroup
  exact nonempty_canonicalSemiRegularParentEquiv (leftRegularMatrix G) hU
    isSemiRegular_leftRegularMatrix 1 incidence_one _ _
    (fun _ => ⟨(), Finset.mem_univ _, Finset.mem_univ _⟩)

-- Empty graphs and zero-dimensional physical tensors need no unmentioned nonempty premise.
example {G X : Type*} [Group G] [Fintype G] [DecidableEq G]
    [Fintype X] [DecidableEq X]
    (U : G →* Matrix X X ℂ) (hU : ∀ g, U g ∈ Matrix.unitaryGroup X ℂ)
    (hSemi : Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp U)) :
    Nonempty (regionParentGroundSpace
      (groupBondTensor (Γ := (⊥ : SimpleGraph Empty))
        (fun v => nomatch v : (v : Empty) → (IncidentEdge ⊥ v → X) → Fin 0 → ℂ))
        (fun i : Empty => nomatch i) ≃ₗ[ℂ]
      regionParentGroundSpace (numberedGraphDressedAveragingTensor (leftRegularMatrix G) 1
        (countedIncidentEnumeration (Γ := (⊥ : SimpleGraph Empty)) G 0
          (fun v : Empty => nomatch v)))
        (fun i : Empty => nomatch i)) := by
  exact nonempty_semiRegularGInjectiveParentEquiv U hU hSemi _ (fun v => nomatch v)
    0 (fun v => nomatch v) _ (fun v => nomatch v) (fun f => nomatch f.1.1)

set_option linter.hashCommand false

/--
info: 'TNLean.PEPS.nonempty_ker_regionParentHamiltonian_semiRegularGInjective_equiv'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.nonempty_ker_regionParentHamiltonian_semiRegularGInjective_equiv
