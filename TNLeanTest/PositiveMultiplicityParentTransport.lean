/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.PositiveMultiplicityParentTransport

/-! # Unequal multiplicity regression for the full canonical parent comparison -/
noncomputable section
open TNLean.PEPS

private abbrev Γ : SimpleGraph (Fin 2) := ⊤
private abbrev d : Fin 1 → ℕ := fun _ => 2
private abbrev m : Fin 1 → ℕ := fun _ => 3
private abbrev n : Fin 1 → ℕ := fun _ => 1
private def eX (v : Fin 2) : (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin 2 :=
  (Fintype.equivFin _).trans (finCongr (by fin_cases v <;> decide))
private def eM (v : Fin 2) : (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (m i)) ≃ Fin 6 :=
  (Fintype.equivFin _).trans (finCongr (by fin_cases v <;> decide))
private def eN (v : Fin 2) : (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (n i)) ≃ Fin 2 :=
  (Fintype.equivFin _).trans (finCongr (by fin_cases v <;> decide))
private def D : (i : Fin 1) → Unit →* Matrix (Fin (d i)) (Fin (d i)) ℂ := fun _ => 1

-- Copies 3 and 1 differ from block dimension 2; actual two-site ranges are compared.
example : Nonempty (regionParentGroundSpace
    (numberedGraphDressedAveragingTensor (blockMultiplicityRepresentation d m D) 1 eM)
      (fun _ : Unit => Finset.univ) ≃ₗ[ℂ]
    regionParentGroundSpace
    (numberedGraphDressedAveragingTensor (blockMultiplicityRepresentation d n D) 1 eN)
      (fun _ : Unit => Finset.univ)) :=
  ⟨canonicalMultiplicityChangeParentEquiv d m n D
    (fun _ => by change 0 < 3; decide) (fun _ => by change 0 < 1; decide)
    eX eM eN (fun _ : Unit => Finset.univ)
    (fun _ => ⟨(), Finset.mem_univ _, Finset.mem_univ _⟩)⟩
