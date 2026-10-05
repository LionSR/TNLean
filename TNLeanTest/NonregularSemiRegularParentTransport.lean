/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.SemiRegularGInjectiveParentTransport

/-! # Concrete nonregular full-parent transport regression -/

noncomputable section
open TNLean.PEPS

private abbrev Γ : SimpleGraph (Fin 2) := ⊤
private theorem incidence_one (v : Fin 2) : Fintype.card (IncidentEdge Γ v) = 1 := by
  fin_cases v <;> decide
private def U : Unit →* Matrix (Fin 2) (Fin 2) ℂ := 1
private theorem hU (g : Unit) : U g ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  simp [U]
private theorem hSemi : Representation.IsSemiRegular
    (Matrix.toLinAlgEquiv'.toMonoidHom.comp U) := by
  apply Representation.isSemiRegular_of_linearIndependent
  rw [Fintype.linearIndependent_iff]
  intro c hc g
  have h := congrArg (fun L : Module.End ℂ (Fin 2 → ℂ) => L (fun _ => 1) 0) hc
  simpa [U] using h

-- Unit's regular representation has dimension one, while U has multiplicity two.
-- This drives the complete derived factory with genuinely nonregular input.
example : Nonempty (regionParentGroundSpace
    (numberedGraphDressedAveragingTensor U 1
      (countedIncidentEnumeration (Fin 2) 1 incidence_one))
    (fun _ : Unit => Finset.univ) ≃ₗ[ℂ]
    regionParentGroundSpace (numberedGraphDressedAveragingTensor
      (leftRegularMatrix Unit) 1 (countedIncidentEnumeration Unit 1 incidence_one))
    (fun _ : Unit => Finset.univ)) :=
  nonempty_canonicalSemiRegularParentEquiv U hU hSemi 1 incidence_one _ _
    (fun _ => ⟨(), Finset.mem_univ _, Finset.mem_univ _⟩)
