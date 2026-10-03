/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GraphMultiplicityBondState
import TNLean.PEPS.GraphBondCoordinateTransport
import TNLean.PEPS.GraphRegularStateNonzero
import TNLean.PEPS.SemiRegularBondIsometryExtension
import TNLean.PEPS.RegularFourierMatrix
import TNLean.PEPS.RegularMinimalDimension
import TNLean.PEPS.RegularMatrixCommutativity

/-!
# Minimal semi-regular states on finite graphs

The actual fourth-root-weighted averaging contraction is carried to the actual
regular contraction by a product of isometries on physical bond pairs. The
representation, Fourier coordinates, and full-domain isometries are derived
from the finite group. The single-copy virtual dimension is minimal among all
finite-dimensional complex semi-regular representations, and the actual
weighted state is nonzero. No connectivity assumption is required.

Source: SCP10, arXiv:1001.3807, Section 7, lines 2938–3019.

**Scope restriction (closed finite simple graphs):** The contractions here
pair every virtual leg along an edge of a finite simple graph. The site has
one virtual and one physical coordinate for each incident edge. In degree
four this gives the four-leg construction of Section 7. Dangling virtual
boundaries, infinite graphs, self-loops, and multiple edges are not included in this
statement; see `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
open scoped Matrix BigOperators
namespace TNLean.PEPS
universe v
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G I : Type*} [Group G] [Fintype G] [DecidableEq G]
variable [Fintype I] [DecidableEq I]

/-- The actual weighted block graph state is related to the actual regular graph
state by a product of physical isometries on their full bond-pair spaces.
Source: SCP10, Section 7, lines 2977–3019. -/
theorem exists_isometric_graphSemiRegularBondMap
    (d : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hd : ∀ i, 0 < d i) (Q : Matrix G (Σ i, Fin (d i) × Fin (d i)) ℂ)
    (hQ : Q.IsIsometry)
    (hreg : ∀ g, leftRegularMatrix G g =
      Q * multiplicityRestoredRepresentation d D g * Q.conjTranspose) :
    let Ψ := graphBondRegrouping (Γ := Γ) (graphBondNetwork
      (graphDressedAveragingSite (blockMatrixRepresentation d D) (blockFourthRootWeight d)))
    ∃ T : Matrix
        ((Σ i, Fin (d i) × Fin (d i)) × (Σ i, Fin (d i) × Fin (d i)))
        ((Σ i, Fin (d i)) × (Σ i, Fin (d i))) ℂ,
      T.IsIsometry ∧
      let 𝒯 := physicalProductMap (Edge Γ) (bondCoordinateMatrix Q) ∘ₗ
        physicalProductMap (Edge Γ) T
      (𝒯 Ψ = graphBondRegrouping
        (graphBondNetwork (graphAveragingSite (leftRegularMatrix G)))) ∧
      ∀ ψ φ, star (𝒯 ψ) ⬝ᵥ 𝒯 φ = star ψ ⬝ᵥ φ := by
  classical
  let : ∀ i, Nonempty (Fin (d i)) := fun i => ⟨⟨0, hd i⟩⟩
  obtain ⟨hsupport, hrestore⟩ := graphBondRegrouping_blockFourthRootWeight (Γ := Γ) d D hd
  obtain ⟨T, hT, hTE, _, _⟩ := exists_isIsometry_fullMultiplicityBondMap_extension
    (fun i => Fin (d i)) (fun i => Fin (d i))
  refine ⟨T, hT, ?_⟩
  constructor
  · simp only [LinearMap.comp_apply]
    rw [physicalProductMap_eq_on_inclusion_range T
      (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (d i)))
      (blockBondInclusion (fun i => Fin (d i))) hTE _ hsupport, hrestore]
    exact physicalProductMap_bondCoordinateMatrix_graphAveragingSite Q
      (multiplicityRestoredRepresentation d D) (leftRegularMatrix G) hreg
  · intro ψ φ
    simp only [LinearMap.comp_apply]
    rw [physicalProductMap_dotProduct_of_isIsometry _
      (bondCoordinateMatrix_isIsometry Q hQ),
      physicalProductMap_dotProduct_of_isIsometry _ hT]

omit [Fintype I] [DecidableEq I] in
/-- Every finite group determines a smallest semi-regular graph state and a
physical bond isometry to the regular graph state. The same choices give
multiplicity one, exact bond dimensions, universal minimality, and nonvanishing.
Source: SCP10, Section 7, lines 2947–3019. -/
theorem exists_isometric_minimalSemiRegular_graphState :
    ∃ (K : ℕ) (d : Fin K → ℕ)
      (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
      (Q : Matrix G (Σ i, Fin (d i) × Fin (d i)) ℂ)
      (T : Matrix
        ((Σ i, Fin (d i) × Fin (d i)) × (Σ i, Fin (d i) × Fin (d i)))
        ((Σ i, Fin (d i)) × (Σ i, Fin (d i))) ℂ),
      let U := blockMatrixRepresentation d D
      let W := blockFourthRootWeight d
      let Ψ := graphBondRegrouping (Γ := Γ)
        (graphBondNetwork (graphDressedAveragingSite U W))
      let 𝒯 := physicalProductMap (Edge Γ) (bondCoordinateMatrix Q) ∘ₗ
        physicalProductMap (Edge Γ) T
      (∀ i, 0 < d i) ∧
      (∀ i g, D i g ∈ Matrix.unitaryGroup (Fin (d i)) ℂ) ∧
      (∀ i, Representation.IsIrreducible (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D i))) ∧
      (∀ i j, i ≠ j →
        Representation.character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D i)) ≠
          Representation.character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D j))) ∧
      (∀ g, U g ∈ Matrix.unitaryGroup (Σ i, Fin (d i)) ℂ) ∧
      Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp U) ∧
      (∀ i, Representation.characterMultiplicity (Matrix.toLinAlgEquiv'.toMonoidHom.comp U)
        (Representation.character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D i))) = 1) ∧
      Q.IsIsometry ∧
      (∀ g, leftRegularMatrix G g =
        Q * multiplicityRestoredRepresentation d D g * Q.conjTranspose) ∧
      T.IsIsometry ∧
      (𝒯 Ψ = graphBondRegrouping
        (graphBondNetwork (graphAveragingSite (leftRegularMatrix G)))) ∧
      (∀ ψ φ, star (𝒯 ψ) ⬝ᵥ 𝒯 φ = star ψ ⬝ᵥ φ) ∧
      Fintype.card G = ∑ i, d i ^ 2 ∧
      Fintype.card (Σ i, Fin (d i)) = ∑ i, d i ∧
      (∑ i, d i) ≤ Fintype.card G ∧
      ((∑ i, d i) < Fintype.card G ↔ ∃ i, 1 < d i) ∧
      ((∑ i, d i) < Fintype.card G ↔ ¬ IsMulCommutative G) ∧
      (∀ (Z : Type v) [AddCommGroup Z] [Module ℂ Z] [FiniteDimensional ℂ Z]
        (σ : Representation ℂ G Z), σ.IsSemiRegular →
        (∑ i, d i) ≤ Module.finrank ℂ Z) ∧ Ψ ≠ 0 := by
  obtain ⟨K, d, D, Q, hd, hunit, hirr, hcross, hQ, hreg, hUunit, hSemi, hmult⟩ :=
    exists_minimalSemiRegular_leftRegular_matrix (G := G)
  obtain ⟨T, hT, hstate, hoverlap⟩ :=
    exists_isometric_graphSemiRegularBondMap (Γ := Γ) d D hd Q hQ hreg
  have hdim := bondDimensions_of_regular_intertwiner d D hd Q hQ hreg
  have hstrict := sum_dimensions_lt_card_iff_not_isMulCommutative_of_regular_intertwiner
    d D hd hirr Q hQ hreg
  refine ⟨K, d, D, Q, T, hd, hunit, hirr, hcross, hUunit, hSemi, hmult,
    hQ, hreg, hT, hstate, hoverlap, hdim.1, hdim.2.1, hdim.2.2.1, hdim.2.2.2, hstrict, ?_, ?_⟩
  · intro Z _ _ _ σ hσ
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_sigma,
      Fintype.card_fin] using finrank_blockMatrixRepresentation_le_of_isSemiRegular
        d D hirr (fun i j h => by
          by_contra hne
          exact hcross i j hne h) σ hσ
  · intro hzero
    have hn := graphBondNetwork_regularAveragingSite_ne_zero (Γ := Γ) (G := G)
    have h := hstate
    rw [hzero, map_zero] at h
    exact hn ((graphBondRegrouping (Γ := Γ)).injective (h.symm.trans (map_zero _).symm))
end TNLean.PEPS
