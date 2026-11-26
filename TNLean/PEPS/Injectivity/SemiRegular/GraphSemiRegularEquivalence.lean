/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Injectivity.Multiplicity.TorusBlockMultiplicityState
import TNLean.PEPS.Injectivity.Multiplicity.GraphAveragingBondState
import TNLean.PEPS.Injectivity.Multiplicity.GraphRegularStateNonzero
import TNLean.PEPS.Injectivity.Multiplicity.SemiRegularBondSupport
import TNLean.PEPS.Injectivity.SemiRegular.RegularFourierMatrix
import TNLean.PEPS.Injectivity.SemiRegular.RegularMinimalRepresentation
import TNLean.PEPS.Injectivity.Multiplicity.GraphInsertedBondState
import TNLean.PEPS.Injectivity.Multiplicity.CoherentMultiplicityTransport

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

## A fixed physical isometry for closed graph states with group insertions

The same bond isometry carries every group-inserted fourth-root-weighted
closed graph state to the corresponding regular inserted state. The actual
contraction formula supplies the weighted blocks and their support.

Source: SCP10, arXiv:1001.3807, Section 7, lines 2977–3019.
**Scope restriction (chosen Fourier coordinates):** The theorem takes positive
block dimensions and an isometric coordinate change identifying their repeated
representation with the regular representation. It does not assert an
all-boundary open-state equivalence. See
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

## Group-derived physical equivalence for all closed bond insertions

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

section

open ManyBody (Edge)

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
end

end

section

open ManyBody (Edge)

noncomputable section
open scoped Matrix BigOperators Kronecker
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G I : Type*} [Group G] [Fintype G] [DecidableEq G]
variable [Fintype I] [DecidableEq I]

/-- One full-domain physical isometry, independent of all edge insertions, carries
actual closed weighted graph states to actual regular inserted states.
Source: SCP10, Section 7, lines 2977–3019; this is an auxiliary inserted-state extension. -/
theorem exists_isometric_graphInsertedSemiRegularBondMap
    (d : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hd : ∀ i, 0 < d i) (B : Matrix G (Σ i, Fin (d i) × Fin (d i)) ℂ)
    (hB : B.IsIsometry)
    (hreg : ∀ g, leftRegularMatrix G g =
      B * multiplicityRestoredRepresentation d D g * B.conjTranspose) :
    let U := blockMatrixRepresentation d D
    let W := blockFourthRootWeight d
    ∃ T : Matrix
        ((Σ i, Fin (d i) × Fin (d i)) × (Σ i, Fin (d i) × Fin (d i)))
        ((Σ i, Fin (d i)) × (Σ i, Fin (d i))) ℂ,
      T.IsIsometry ∧
      let 𝒯 := physicalProductMap (Edge Γ) (bondCoordinateMatrix B) ∘ₗ
        physicalProductMap (Edge Γ) T
      (∀ u : Edge Γ → G,
        𝒯 (graphBondRegrouping (graphInsertedBondNetwork (fun e => U (u e))
          (graphDressedAveragingSite U W))) =
        graphBondRegrouping (graphInsertedBondNetwork
          (fun e => leftRegularMatrix G (u e))
          (graphAveragingSite (leftRegularMatrix G)))) ∧
      ∀ ψ φ, star (𝒯 ψ) ⬝ᵥ 𝒯 φ = star ψ ⬝ᵥ φ := by
  classical
  let U := blockMatrixRepresentation d D
  let W := blockFourthRootWeight d
  obtain ⟨T, hT, hcoherent, hoverlap⟩ :=
    exists_isometric_coherentWeightedBlocks (E := Edge Γ) (Q := V → G)
      d (fun i g => D i g) (fun g => W ^ 2 * U g)
      (fun g => blockFourthRootWeight_sq_mul d D g) hd B hB (leftRegularMatrix G) hreg
  refine ⟨T, hT, ?_, hoverlap⟩
  intro u
  have hin : graphBondRegrouping (graphInsertedBondNetwork (fun e => U (u e))
      (graphDressedAveragingSite U W)) =
      fun β => ∑ q : V → G, (Fintype.card G : ℂ)⁻¹ ^ Fintype.card V *
        ∏ e : Edge Γ, (W ^ 2 * U (q e.1.2 * u e * (q e.1.1)⁻¹))
          (β e).1 (β e).2 := by
    funext β
    exact graphInsertedBondNetwork_dressedAveragingSite_group U W
      (blockFourthRootWeight_commute d D) u β
  have hout : graphBondRegrouping (graphInsertedBondNetwork
      (fun e => leftRegularMatrix G (u e))
      (graphAveragingSite (leftRegularMatrix G))) =
      fun β => ∑ q : V → G, (Fintype.card G : ℂ)⁻¹ ^ Fintype.card V *
        ∏ e : Edge Γ, leftRegularMatrix G (q e.1.2 * u e * (q e.1.1)⁻¹)
          (β e).1 (β e).2 := by
    funext β
    exact graphInsertedBondNetwork_averagingSite_group (leftRegularMatrix G) u β
  rw [hin, hout]
  exact hcoherent (fun _ => (Fintype.card G : ℂ)⁻¹ ^ Fintype.card V)
    (fun q e => q e.1.2 * u e * (q e.1.1)⁻¹)

end TNLean.PEPS
end

end

section

open ManyBody (Edge)

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
end

end
