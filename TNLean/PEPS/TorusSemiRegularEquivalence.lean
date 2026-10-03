/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusBlockMultiplicityState
import TNLean.PEPS.TorusBondCoordinateTransport
import TNLean.PEPS.SemiRegularBondProductIsometry
import TNLean.PEPS.RegularTorusSite
import TNLean.PEPS.SemiRegularBondIsometryExtension
import TNLean.PEPS.RegularFourierMatrix
import TNLean.PEPS.PhysicalCoherentTransport

/-!
# The physical transformation from weighted blocks to the regular torus state

Multiplicity restoration on each physical bond is followed by the two-endpoint
Fourier coordinate change. The composed map carries the actual fourth-root-
weighted block torus state to the actual regular torus state. It preserves all
overlaps on the product matching-sector support, which is derived for the
weighted state from its original contraction.

Source: SCP10, arXiv:1001.3807, Section 7, lines 2938–3019.

**Scope restriction (finite torus):** This module realizes the Section 7
construction on finite tori with positive periods. The source treats the lattice
geometry more generally; see
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

The intermediate transformation theorems take chosen matrix representations
and Fourier coordinates. The final existence theorem derives these data from
the finite group and constructs a semi-regular representation whose irreducible
sectors each have multiplicity one. No universal dimension-minimum claim is made.
-/

noncomputable section
open scoped Matrix BigOperators
namespace TNLean.PEPS

variable {G I : Type*} [Group G] [Fintype G] [DecidableEq G]
variable [Fintype I] [DecidableEq I]
variable (d : I → ℕ)
variable {width height : ℕ} [NeZero width] [NeZero height]

/-- Restore multiplicities on every actual physical bond, then return its two
endpoints to the regular group basis. Source: SCP10, Section 7, lines 3008–3019. -/
noncomputable def torusSemiRegularBondMap
    (Q : Matrix G (Σ i, Fin (d i) × Fin (d i)) ℂ) :
    (((TorusVertex width height × Bool) → ((Σ i, Fin (d i)) × (Σ i, Fin (d i)))) → ℂ)
      →ₗ[ℂ] (((TorusVertex width height × Bool) → (G × G)) → ℂ) :=
  physicalProductMap (TorusVertex width height × Bool) (bondCoordinateMatrix Q) ∘ₗ
    physicalProductMap (TorusVertex width height × Bool)
      (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (d i)))

omit [Group G] [DecidableEq G] in
/-- The composed bond operation preserves overlaps on the matching-sector
support. Only the second vector must be supported. Source: SCP10, Section 7,
lines 3008–3019. -/
theorem torusSemiRegularBondMap_dotProduct
    (hd : ∀ i, 0 < d i) (Q : Matrix G (Σ i, Fin (d i) × Fin (d i)) ℂ)
    (hQ : Q.IsIsometry)
    (ψ φ : ((TorusVertex width height × Bool) →
      ((Σ i, Fin (d i)) × (Σ i, Fin (d i)))) → ℂ)
    (hφ : φ ∈ LinearMap.range (physicalProductMap (TorusVertex width height × Bool)
      (blockBondInclusion (fun i => Fin (d i))))) :
    star (torusSemiRegularBondMap d Q ψ) ⬝ᵥ torusSemiRegularBondMap d Q φ =
      star ψ ⬝ᵥ φ := by
  let : ∀ i, Nonempty (Fin (d i)) := fun i => ⟨⟨0, hd i⟩⟩
  simp only [torusSemiRegularBondMap, LinearMap.comp_apply]
  rw [physicalProductMap_dotProduct_of_isIsometry _
    (bondCoordinateMatrix_isIsometry Q hQ)]
  exact physicalProductMap_fullMultiplicityBondMap_dotProduct
    (fun i => Fin (d i)) (fun i => Fin (d i)) ψ φ hφ

/-- The actual fourth-root-weighted block contraction is supported on matching
sectors and is sent to the actual regular torus contraction by the composed
physical bond operation. The Fourier hypothesis is matrix intertwining, not
an equality of states. Source: SCP10, Section 7, lines 2938–3019. -/
theorem torusSemiRegularBondMap_blockFourthRootWeight
    (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hd : ∀ i, 0 < d i) (Q : Matrix G (Σ i, Fin (d i) × Fin (d i)) ℂ)
    (hreg : ∀ g, leftRegularMatrix G g =
      Q * multiplicityRestoredRepresentation d D g * Q.conjTranspose) :
    let U := blockMatrixRepresentation d D
    let W := blockFourthRootWeight d
    let Ψ := torusBondRegrouping (width := width) (height := height)
      (fun σ => torusBondNetwork (fun v t => torusDress W W
        (fun a => averagingSite U a.1 a.2.1 a.2.2.1 a.2.2.2 (σ v)) t) 1 1)
    (Ψ ∈ LinearMap.range (physicalProductMap (TorusVertex width height × Bool)
      (blockBondInclusion (fun i => Fin (d i))))) ∧
    torusSemiRegularBondMap d Q Ψ =
      torusBondRegrouping (fun σ => torusBondNetwork
        (fun v t => averagingSite (leftRegularMatrix G)
          t.1 t.2.1 t.2.2.1 t.2.2.2 (σ v)) 1 1) := by
  obtain ⟨hsupport, hrestore⟩ := torusBondRegrouping_blockFourthRootWeight
    (width := width) (height := height) d D hd
  refine ⟨hsupport, ?_⟩
  simp only [torusSemiRegularBondMap, LinearMap.comp_apply]
  rw [hrestore]
  exact physicalProductMap_bondCoordinateMatrix_averagingSite Q
    (multiplicityRestoredRepresentation d D) (leftRegularMatrix G) hreg


/-- The supported multiplicity-restoring formula extends to an isometric local
physical transformation of the entire torus physical space, and this extension
sends the actual weighted block state to the regular state. Source: SCP10,
Section 7, lines 2977–3019. -/
theorem exists_isometric_torusSemiRegularBondMap
    (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hd : ∀ i, 0 < d i) (Q : Matrix G (Σ i, Fin (d i) × Fin (d i)) ℂ)
    (hQ : Q.IsIsometry)
    (hreg : ∀ g, leftRegularMatrix G g =
      Q * multiplicityRestoredRepresentation d D g * Q.conjTranspose) :
    let U := blockMatrixRepresentation d D
    let W := blockFourthRootWeight d
    let Ψ := torusBondRegrouping (width := width) (height := height)
      (fun σ => torusBondNetwork (fun v t => torusDress W W
        (fun a => averagingSite U a.1 a.2.1 a.2.2.1 a.2.2.2 (σ v)) t) 1 1)
    ∃ T : Matrix
        ((Σ i, Fin (d i) × Fin (d i)) × (Σ i, Fin (d i) × Fin (d i)))
        ((Σ i, Fin (d i)) × (Σ i, Fin (d i))) ℂ,
      T.IsIsometry ∧
      let 𝒯 := physicalProductMap (TorusVertex width height × Bool)
          (bondCoordinateMatrix Q) ∘ₗ
        physicalProductMap (TorusVertex width height × Bool) T
      (𝒯 Ψ = torusBondRegrouping (fun σ => torusBondNetwork
        (fun v t => averagingSite (leftRegularMatrix G)
          t.1 t.2.1 t.2.2.1 t.2.2.2 (σ v)) 1 1)) ∧
      ∀ ψ φ, star (𝒯 ψ) ⬝ᵥ 𝒯 φ = star ψ ⬝ᵥ φ := by
  let : ∀ i, Nonempty (Fin (d i)) := fun i => ⟨⟨0, hd i⟩⟩
  obtain ⟨hsupport, hstate⟩ := torusSemiRegularBondMap_blockFourthRootWeight
    (width := width) (height := height) d D hd Q hreg
  obtain ⟨T, hT, hTE, _, _⟩ :=
    exists_isIsometry_fullMultiplicityBondMap_extension
      (fun i => Fin (d i)) (fun i => Fin (d i))
  refine ⟨T, hT, ?_⟩
  constructor
  · simp only [LinearMap.comp_apply]
    rw [physicalProductMap_eq_on_inclusion_range T
      (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (d i)))
      (blockBondInclusion (fun i => Fin (d i))) hTE _ hsupport]
    exact hstate
  · intro ψ φ
    simp only [LinearMap.comp_apply]
    rw [physicalProductMap_dotProduct_of_isIsometry _
      (bondCoordinateMatrix_isIsometry Q hQ),
      physicalProductMap_dotProduct_of_isIsometry _ hT]

end TNLean.PEPS

namespace TNLean.PEPS
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable {width height : ℕ} [NeZero width] [NeZero height]

/-- There exists a multiplicity-one semi-regular representation whose fourth-root-
weighted native site is related to the actual regular torus state by a local
physical isometry. All representation and Fourier data are derived from the group.
Source: SCP10, Section 7, lines 2938–3019. -/
theorem exists_isometric_multiplicityOneSemiRegular_torusState :
    ∃ (K : ℕ) (d : Fin K → ℕ)
      (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
      (Q : Matrix G (Σ i, Fin (d i) × Fin (d i)) ℂ)
      (T : Matrix
        ((Σ i, Fin (d i) × Fin (d i)) × (Σ i, Fin (d i) × Fin (d i)))
        ((Σ i, Fin (d i)) × (Σ i, Fin (d i))) ℂ),
      let U := blockMatrixRepresentation d D
      let W := blockFourthRootWeight d
      let Ψ := torusBondRegrouping (width := width) (height := height)
        (fun σ => torusBondNetwork (fun v t => torusDress W W
          (fun a => averagingSite U a.1 a.2.1 a.2.2.1 a.2.2.2 (σ v)) t) 1 1)
      let 𝒯 := physicalProductMap (TorusVertex width height × Bool)
          (bondCoordinateMatrix Q) ∘ₗ
        physicalProductMap (TorusVertex width height × Bool) T
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
      (𝒯 Ψ = torusBondRegrouping (fun σ => torusBondNetwork
        (fun v t => averagingSite (leftRegularMatrix G)
          t.1 t.2.1 t.2.2.1 t.2.2.2 (σ v)) 1 1)) ∧
      ∀ ψ φ, star (𝒯 ψ) ⬝ᵥ 𝒯 φ = star ψ ⬝ᵥ φ := by
  obtain ⟨K, d, D, Q, hd, hunit, hirr, hcross, hQ, hreg, hUunit, hSemi, hmult⟩ :=
    exists_minimalSemiRegular_leftRegular_matrix (G := G)
  obtain ⟨T, hT, hstate, hoverlap⟩ :=
    exists_isometric_torusSemiRegularBondMap (width := width) (height := height)
      d D hd Q hQ hreg
  exact ⟨K, d, D, Q, T, hd, hunit, hirr, hcross, hUunit, hSemi, hmult,
    hQ, hreg, hT, hstate, hoverlap⟩
end TNLean.PEPS
