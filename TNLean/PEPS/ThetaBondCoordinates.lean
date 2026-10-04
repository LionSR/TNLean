/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.BlockDiagonalGauge
import TNLean.PEPS.SemiRegularBondIsometry
import TNLean.Algebra.RepresentationThetaSquared

/-!
# Weighted bond coefficients in multiplicity-one sector coordinates

For an explicitly supplied internal decomposition into multiplicity-one
irreducible summands, a single coordinate equivalence gives both the
representation blocks Dᵢ(g) and the weighted blocks √dᵢ Dᵢ(g) of Θ²ρ(g).
Reading these actual weighted diagonal blocks and applying the normalized
multiplicity-restoring bond map gives Dᵢ(g) ⊗ I_{dᵢ}.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Section 7,
`Papers/1001.3807/paper_v3.tex`, lines 2992–3019. The theorem identifies the
occurring blocks in the supplied decomposition. It assumes neither that every
irreducible occurs nor that the supplied sector coordinates are orthonormal.
The resulting global coordinate equivalence is linear; the physical local
isometry between complete PEPS requires the corresponding Hilbert-space
identification and contraction argument.
-/

noncomputable section
open scoped Matrix Kronecker
open Module LinearMap
namespace TNLean.PEPS

open Representation

variable {G V I : Type*} [Group G] [Fintype G]
variable [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
variable [Fintype I] [DecidableEq I]

private theorem exists_thetaSquared_split (ρ : Representation ℂ G V) (S : I → Subrepresentation ρ)
    (hI : ∀ k, (S k).toRepresentation.IsIrreducible)
    (hS : DirectSum.IsInternal (fun k => (S k).toSubmodule))
    (hm : ∀ k, characterMultiplicity ρ (S k).toRepresentation.character = 1)
    (d : I → ℕ) (ψ : ∀ k, (S k).toSubmodule ≃ₗ[ℂ] (Fin (d k) → ℂ)) :
    ∃ e : V ≃ₗ[ℂ] ((Σ k, Fin (d k)) → ℂ),
      (∀ g, LinearMap.toMatrix' (e.conj (ρ g)) =
        Matrix.blockDiagonal' (fun k =>
          LinearMap.toMatrix' ((ψ k).conj ((S k).toRepresentation g)))) ∧
      (∀ g, LinearMap.toMatrix' (e.conj (thetaOperator ρ ^ 2 * ρ g)) =
        Matrix.blockDiagonal' (fun k =>
          (Real.sqrt (d k : ℝ) : ℂ) •
            LinearMap.toMatrix' ((ψ k).conj ((S k).toRepresentation g)))) := by
  let f : G ⊕ G → Module.End ℂ V :=
    Sum.elim (fun g => ρ g) (fun g => thetaOperator ρ ^ 2 * ρ g)
  have hf : ∀ (i : G ⊕ G) (k : I), Set.MapsTo (f i) (S k).toSubmodule (S k).toSubmodule := by
    intro i k v hv
    cases i with
    | inl g => exact (S k).apply_mem_toSubmodule g hv
    | inr g =>
      let := hI k
      change (thetaOperator ρ ^ 2) (ρ g v) ∈ (S k).toSubmodule
      rw [thetaOperator_sq_apply_of_multiplicity_one ρ (S k) (hm k)
        ((S k).apply_mem_toSubmodule g hv)]
      exact (S k).toSubmodule.smul_mem _ ((S k).apply_mem_toSubmodule g hv)
  obtain ⟨e, he⟩ := exists_linearEquiv_blockDiagonal_of_isInternal hS d ψ f hf
  refine ⟨e, ?_, ?_⟩
  · intro g
    exact he (.inl g)
  · intro g
    have hd (k) : finrank ℂ (S k).toSubmodule = d k := by
      simpa using (ψ k).finrank_eq
    have hr (k) : (f (.inr g)).restrict (hf (.inr g) k) =
        (Real.sqrt (d k : ℝ) : ℂ) • (S k).toRepresentation g := by
      let := hI k
      ext v
      change (thetaOperator ρ ^ 2) (ρ g v) = _
      rw [thetaOperator_sq_apply_of_multiplicity_one ρ (S k) (hm k)
        ((S k).apply_mem_toSubmodule g v.2), hd]
      rfl
    change LinearMap.toMatrix' (e.conj (f (.inr g))) = _
    rw [he (.inr g)]
    congr 1
    funext k
    rw [hr]
    simp only [map_smul]

/-- In a supplied multiplicity-one irreducible decomposition, the actual Θ²ρ(g)
blocks have weights √dᵢ, and the normalized bond map restores the dᵢ copies.
Source: SCP10, Section 7, lines 2992–3019. -/
theorem exists_thetaBond_blockCoordinates (ρ : Representation ℂ G V)
    (S : I → Subrepresentation ρ) (hI : ∀ k, (S k).toRepresentation.IsIrreducible)
    (hS : DirectSum.IsInternal (fun k => (S k).toSubmodule))
    (hm : ∀ k, characterMultiplicity ρ (S k).toRepresentation.character = 1)
    (d : I → ℕ) (ψ : ∀ k, (S k).toSubmodule ≃ₗ[ℂ] (Fin (d k) → ℂ)) :
    ∃ e : V ≃ₗ[ℂ] ((Σ k, Fin (d k)) → ℂ),
      (∀ g, LinearMap.toMatrix' (e.conj (ρ g)) =
        Matrix.blockDiagonal' (fun k =>
          LinearMap.toMatrix' ((ψ k).conj ((S k).toRepresentation g)))) ∧
      (∀ g, LinearMap.toMatrix' (e.conj (thetaOperator ρ ^ 2 * ρ g)) =
        Matrix.blockDiagonal' (fun k => (Real.sqrt (d k : ℝ) : ℂ) •
          LinearMap.toMatrix' ((ψ k).conj ((S k).toRepresentation g)))) ∧
      (∀ g, multiplicityBondFamilyMap (fun k => Fin (d k)) (fun k => Fin (d k))
        (fun k a b => LinearMap.toMatrix' (e.conj (thetaOperator ρ ^ 2 * ρ g))
          ⟨k, a⟩ ⟨k, b⟩) =
        fun k => LinearMap.toMatrix' ((ψ k).conj ((S k).toRepresentation g)) ⊗ₖ
          (1 : Matrix (Fin (d k)) (Fin (d k)) ℂ)) := by
  obtain ⟨e, he, hweight⟩ := exists_thetaSquared_split ρ S hI hS hm d ψ
  refine ⟨e, he, hweight, ?_⟩
  have hd (k) : finrank ℂ (S k).toSubmodule = d k := by
    simpa using (ψ k).finrank_eq
  have hpos (k) : 0 < d k := by
    let := hI k
    simpa only [hd] using finrank_pos_of_isIrreducible (S k).toRepresentation
  let : ∀ k, Nonempty (Fin (d k)) := fun k => ⟨⟨0, hpos k⟩⟩
  intro g
  have hb : (fun k a b => LinearMap.toMatrix' (e.conj (thetaOperator ρ ^ 2 * ρ g))
      ⟨k, a⟩ ⟨k, b⟩) =
      fun k => (Real.sqrt (d k : ℝ) : ℂ) •
        LinearMap.toMatrix' ((ψ k).conj ((S k).toRepresentation g)) := by
    funext k a b
    rw [hweight g, Matrix.blockDiagonal'_apply_eq]
  rw [hb]
  simpa only [Fintype.card_fin] using
    multiplicityBondFamilyMap_sqrt_smul (fun k => Fin (d k)) (fun k => Fin (d k))
      (fun k => LinearMap.toMatrix' ((ψ k).conj ((S k).toRepresentation g)))
end TNLean.PEPS
