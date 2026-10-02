/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GraphInsertedSemiRegularEquivalence

/-!
# Group-derived physical equivalence for all closed bond insertions

The finite group determines a multiplicity-one semi-regular representation and
one product of physical bond isometries before any insertion labels are chosen.
The representation is of smallest dimension among all finite-dimensional
complex semi-regular representations. The same isometry carries every actual
closed inserted contraction to the corresponding regular contraction.

Source: SCP10, arXiv:1001.3807, Section 7, lines 2947–3019. This is an auxiliary
inserted-state consequence for finite simple graphs. Open virtual boundaries,
arbitrary matrices mixing sectors, and parent-Hamiltonian claims are excluded.
The representation data are reused from the existing closed-state existence
result, without constructing a second Fourier decomposition.
-/

noncomputable section
open scoped Matrix BigOperators
namespace TNLean.PEPS
universe v
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The group determines one minimal multiplicity-one semi-regular representation
and one full-domain physical isometry for every closed group-inserted state.
Source: SCP10, Section 7, lines 2947–3019; auxiliary inserted-state consequence. -/
theorem exists_isometric_minimalSemiRegular_graphInsertedStates :
    ∃ (K : ℕ) (d : Fin K → ℕ)
      (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
      (Q : Matrix G (Σ i, Fin (d i) × Fin (d i)) ℂ)
      (T : Matrix
        ((Σ i, Fin (d i) × Fin (d i)) × (Σ i, Fin (d i) × Fin (d i)))
        ((Σ i, Fin (d i)) × (Σ i, Fin (d i))) ℂ),
      let U := blockMatrixRepresentation d D
      let W := blockFourthRootWeight d
      let 𝒯 := physicalProductMap (Edge Γ) (bondCoordinateMatrix Q) ∘ₗ
        physicalProductMap (Edge Γ) T
      (∀ g, U g ∈ Matrix.unitaryGroup (Σ i, Fin (d i)) ℂ) ∧
      Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp U) ∧
      (∀ i, Representation.characterMultiplicity (Matrix.toLinAlgEquiv'.toMonoidHom.comp U)
        (Representation.character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D i))) = 1) ∧
      (∀ (Z : Type v) [AddCommGroup Z] [Module ℂ Z] [FiniteDimensional ℂ Z]
        (σ : Representation ℂ G Z), σ.IsSemiRegular →
        (∑ i, d i) ≤ Module.finrank ℂ Z) ∧
      T.IsIsometry ∧
      (∀ u : Edge Γ → G,
        𝒯 (graphBondRegrouping (graphInsertedBondNetwork (fun e => U (u e))
          (graphDressedAveragingSite U W))) =
        graphBondRegrouping (graphInsertedBondNetwork
          (fun e => leftRegularMatrix G (u e))
          (graphAveragingSite (leftRegularMatrix G)))) ∧
      ∀ ψ φ, star (𝒯 ψ) ⬝ᵥ 𝒯 φ = star ψ ⬝ᵥ φ := by
  obtain ⟨K, d, D, Q, _, hd, _, _, _, hU, hSemi, hmult, hQ, hreg,
      _, _, _, _, _, _, _, _, hmin, _⟩ :=
    exists_isometric_minimalSemiRegular_graphState (Γ := Γ) (G := G)
  obtain ⟨T, hT, hstate, hoverlap⟩ :=
    exists_isometric_graphInsertedSemiRegularBondMap (Γ := Γ) d D hd Q hQ hreg
  exact ⟨K, d, D, Q, T, hU, hSemi, hmult, hmin, hT, hstate, hoverlap⟩

end TNLean.PEPS
