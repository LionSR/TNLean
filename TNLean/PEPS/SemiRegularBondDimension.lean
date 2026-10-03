/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusSemiRegularEquivalence
import TNLean.PEPS.RegularMinimalDimension
import TNLean.PEPS.TorusSemiRegularStateNorm

/-!
# Dimensions of the Fourier and single-copy virtual spaces

An orthonormal Fourier basis gives the exact regular dimension ∑ᵢ dᵢ² = |G|.
The single-copy virtual space has dimension ∑ᵢ dᵢ ≤ |G|, with strict inequality
exactly when one of the positive sector dimensions exceeds one. The same
single-copy space has smallest dimension among finite-dimensional complex
semi-regular representations.

Source: SCP10, arXiv:1001.3807, Section 7, lines 2947–2988.

**Scope restriction (finite-torus physical consumer):** The final existence
corollary gives the dimension formulas for the actual physical equivalence on
finite tori with positive periods. The source treats the lattice geometry more
generally; see `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
The Fourier cardinal identities themselves have no lattice hypothesis.
-/

open scoped BigOperators Matrix
namespace TNLean.PEPS
universe v

/-- Count the actual row and multiplicity labels of a Fourier orthonormal basis.
Source: SCP10, Section 7, lines 2947–2954. -/
theorem card_eq_sum_sq_of_fourierBasis {G I : Type*} [Fintype G] [Fintype I]
    (d : I → ℕ)
    (b : OrthonormalBasis (Σ i, Fin (d i) × Fin (d i)) ℂ (EuclideanSpace ℂ G)) :
    Fintype.card G = ∑ i, d i ^ 2 := by
  simpa only [finrank_euclideanSpace, Fintype.card_sigma, Fintype.card_prod,
    Fintype.card_fin, pow_two] using Module.finrank_eq_card_basis b.toBasis

/-- The positive Fourier dimensions describe the single-copy bond space, and
strict reduction occurs exactly when a sector has dimension greater than one.
Source: SCP10, Section 7, lines 2955–2988. -/
theorem bondDimensions_of_fourierBasis {G I : Type*} [Fintype G] [Fintype I]
    (d : I → ℕ) (hd : ∀ i, 0 < d i)
    (b : OrthonormalBasis (Σ i, Fin (d i) × Fin (d i)) ℂ (EuclideanSpace ℂ G)) :
    Fintype.card G = ∑ i, d i ^ 2 ∧
    Fintype.card (Σ i, Fin (d i)) = ∑ i, d i ∧
    (∑ i, d i) ≤ Fintype.card G ∧
    ((∑ i, d i) < Fintype.card G ↔ ∃ i, 1 < d i) := by
  have hcard := card_eq_sum_sq_of_fourierBasis d b
  rw [hcard]
  exact ⟨rfl, positive_dimension_bounds d hd⟩

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable {width height : ℕ} [NeZero width] [NeZero height]

/-- The internally derived physical equivalence can be chosen with its exact
regular and single-copy bond dimensions, and strict reduction is characterized
by a sector dimension greater than one. The same virtual space has no greater
dimension than any finite-dimensional complex semi-regular representation.
Its actual weighted state is nonzero and has squared norm |G|^(N+1).
Source: SCP10, Section 7, lines 2947–2988. -/
theorem exists_isometric_multiplicityOneSemiRegular_torusState_bondDimensions :
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
      (∀ ψ φ, star (𝒯 ψ) ⬝ᵥ 𝒯 φ = star ψ ⬝ᵥ φ) ∧
      Fintype.card G = ∑ i, d i ^ 2 ∧
      Fintype.card (Σ i, Fin (d i)) = ∑ i, d i ∧
      (∑ i, d i) ≤ Fintype.card G ∧
      ((∑ i, d i) < Fintype.card G ↔ ∃ i, 1 < d i) ∧
      (∀ (V : Type v) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
        (σ : Representation ℂ G V), σ.IsSemiRegular →
        (∑ i, d i) ≤ Module.finrank ℂ V) ∧
      star Ψ ⬝ᵥ Ψ = (Fintype.card G : ℂ) ^
        (Fintype.card (TorusVertex width height) + 1) ∧ Ψ ≠ 0 := by
  obtain ⟨K, d, D, Q, T, hd, hunit, hirr, hcross, hUunit, hSemi, hmult,
    hQ, hreg, hT, hstate, hoverlap⟩ :=
    exists_isometric_multiplicityOneSemiRegular_torusState
      (G := G) (width := width) (height := height)
  have hcard := card_eq_sum_sq_of_regular_intertwiner d D Q hQ hreg
  have hdim := positive_dimension_bounds d hd
  rw [← hcard] at hdim
  have hnorm := norm_ne_zero_of_isometry_to_regularTorus
    _ (fun ψ => hoverlap ψ ψ) _ hstate
  refine ⟨K, d, D, Q, T, hd, hunit, hirr, hcross, hUunit, hSemi, hmult,
    hQ, hreg, hT, hstate, hoverlap, hcard, hdim.1, hdim.2.1, hdim.2.2, ?_, hnorm⟩
  intro V _ _ _ σ hσ
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_sigma,
    Fintype.card_fin] using finrank_blockMatrixRepresentation_le_of_isSemiRegular
      d D hirr (fun i j h => by
        by_contra hne
        exact hcross i j hne h) σ hσ

end TNLean.PEPS
