/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.SemiRegularCanonicalParentTransport

/-! # Regression checks for canonical multiplicity parent transport -/

noncomputable section
open scoped Matrix
open TNLean.PEPS

private abbrev Γ : SimpleGraph (Fin 2) := ⊤
private abbrev dims : Fin 1 → ℕ := fun _ => 2
private abbrev X := Σ i : Fin 1, Fin (dims i)
private abbrev Y := Σ i : Fin 1, Fin (dims i) × Fin (dims i)

private def sourceEnumeration (v : Fin 2) : (IncidentEdge Γ v → X) ≃ Fin 2 :=
  (Fintype.equivFin _).trans (finCongr (by fin_cases v <;> decide))

private def targetEnumeration (v : Fin 2) : (IncidentEdge Γ v → Y) ≃ Fin 4 :=
  (Fintype.equivFin _).trans (finCongr (by fin_cases v <;> decide))

private def blocks : (i : Fin 1) → Unit →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ :=
  fun _ => 1

-- This checks an actual dimension-changing two-vertex canonical parent comparison.
example :
    Nonempty (regionParentGroundSpace
      (numberedGraphDressedAveragingTensor (blockMatrixRepresentation dims blocks)
        (blockFourthRootWeight dims) sourceEnumeration) (fun _ : Unit => Finset.univ) ≃ₗ[ℂ]
      regionParentGroundSpace
        (numberedGraphDressedAveragingTensor (multiplicityRestoredRepresentation dims blocks)
          1 targetEnumeration) (fun _ : Unit => Finset.univ)) := by
  exact ⟨canonicalMultiplicityParentEquiv dims blocks (fun _ => by change 0 < 2; decide)
    sourceEnumeration targetEnumeration (fun _ : Unit => Finset.univ)
    (fun f => ⟨(), Finset.mem_univ _, Finset.mem_univ _⟩)⟩

-- Unequal copy registers are annihilated by the actual supported bond map.
example :
    fullMultiplicityBondMap (fun i : Fin 1 => Fin (dims i)) (fun i : Fin 1 => Fin (dims i))
      (⟨0, 0, 0⟩, ⟨0, 1, 1⟩) (⟨0, 0⟩, ⟨0, 1⟩) = 0 := by
  simp [fullMultiplicityBondMap_apply, multiplicityBondAmplitude,
    multiplicityEndpointBase, multiplicityEndpointCopy]

-- With no edges or vertices, even zero physical alphabets cause no hidden nonempty premise.
example {G I : Type*} [Group G] [Fintype G] [Fintype I] [DecidableEq I]
    (d : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hd : ∀ i, 0 < d i) :
    Nonempty (regionParentGroundSpace
      (numberedGraphDressedAveragingTensor (Γ := (⊥ : SimpleGraph Empty))
        (blockMatrixRepresentation d D) (blockFourthRootWeight d)
        (fun v => nomatch v : (v : Empty) → (IncidentEdge ⊥ v → Σ i, Fin (d i)) ≃ Fin 0))
        (fun v : Empty => nomatch v) ≃ₗ[ℂ]
      regionParentGroundSpace
        (numberedGraphDressedAveragingTensor (Γ := (⊥ : SimpleGraph Empty))
          (multiplicityRestoredRepresentation d D) 1
          (fun v => nomatch v : (v : Empty) →
            (IncidentEdge ⊥ v → Σ i, Fin (d i) × Fin (d i)) ≃ Fin 2))
        (fun v : Empty => nomatch v)) := by
  exact ⟨canonicalMultiplicityParentEquiv d D hd _ _ _ (fun f => nomatch f.1.1)⟩
