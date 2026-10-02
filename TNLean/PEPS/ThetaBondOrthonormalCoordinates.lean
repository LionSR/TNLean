/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.BlockDiagonalGauge
import TNLean.PEPS.SemiRegularBondIsometry
import TNLean.Algebra.RepresentationThetaSquared
import Mathlib.Analysis.InnerProductSpace.PiL2
/-!
# Orthonormal coordinates for weighted bond coefficients

For a supplied orthogonal internal decomposition into irreducible sectors of
character multiplicity one, collect their orthonormal bases into one global
orthonormal basis. The matrices of ρ(g) and Θ²ρ(g) then have blocks Dᵢ(g) and
√dᵢ Dᵢ(g), respectively. The normalized multiplicity-restoring bond map sends
the latter blocks to Dᵢ(g) ⊗ I_{dᵢ}.

Source: SCP10, arXiv:1001.3807, Section 7, lines 2992–3019. This is an auxiliary
coefficient identity with a supplied orthogonal decomposition. It neither
constructs that decomposition nor asserts equivalence of complete PEPS.
-/

noncomputable section
open scoped Matrix Kronecker
open Module LinearMap
namespace TNLean.PEPS
open Representation
variable {G V I : Type*} [Group G] [Fintype G]
variable [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable [Fintype I] [DecidableEq I]
private theorem exists_thetaOrthonormal_split (ρ : Representation ℂ G V)
    (S : I → Subrepresentation ρ)
    (hI : ∀ k, (S k).toRepresentation.IsIrreducible)
    (hS : DirectSum.IsInternal (fun k => (S k).toSubmodule))
    (hOrth : OrthogonalFamily ℂ (fun k => (S k).toSubmodule)
      (fun k => (S k).toSubmodule.subtypeₗᵢ))
    (hm : ∀ k, characterMultiplicity ρ (S k).toRepresentation.character = 1)
    (d : I → ℕ) (b : ∀ k, OrthonormalBasis (Fin (d k)) ℂ (S k).toSubmodule) :
    ∃ c : OrthonormalBasis (Σ k, Fin (d k)) ℂ V,
      (∀ g, LinearMap.toMatrix c.toBasis c.toBasis (ρ g) =
        Matrix.blockDiagonal' (fun k =>
          LinearMap.toMatrix (b k).toBasis (b k).toBasis ((S k).toRepresentation g))) ∧
      (∀ g, LinearMap.toMatrix c.toBasis c.toBasis (thetaOperator ρ ^ 2 * ρ g) =
        Matrix.blockDiagonal' (fun k => (Real.sqrt (d k : ℝ) : ℂ) •
          LinearMap.toMatrix (b k).toBasis (b k).toBasis ((S k).toRepresentation g))) := by
  let c := hS.collectedOrthonormalBasis hOrth b
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
  have he (i : G ⊕ G) : LinearMap.toMatrix c.toBasis c.toBasis (f i) =
      Matrix.blockDiagonal' (fun k => LinearMap.toMatrix (b k).toBasis (b k).toBasis
        ((f i).restrict (hf i k))) := by
    exact LinearMap.toMatrix_directSum_collectedBasis_eq_blockDiagonal'
      hS hS (fun k => (b k).toBasis) (fun k => (b k).toBasis) (hf i)
  refine ⟨c, ?_, ?_⟩
  · intro g
    exact he (.inl g)
  · intro g
    have hd (k) : finrank ℂ (S k).toSubmodule = d k := by
      simpa using Module.finrank_eq_card_basis (b k).toBasis
    have hr (k) : (f (.inr g)).restrict (hf (.inr g) k) =
        (Real.sqrt (d k : ℝ) : ℂ) • (S k).toRepresentation g := by
      let := hI k
      ext v
      change (thetaOperator ρ ^ 2) (ρ g v) = _
      rw [thetaOperator_sq_apply_of_multiplicity_one ρ (S k) (hm k)
        ((S k).apply_mem_toSubmodule g v.2), hd]
      rfl
    change LinearMap.toMatrix c.toBasis c.toBasis (f (.inr g)) = _
    rw [he]
    congr 1
    funext k
    rw [hr]
    simp only [map_smul]
/-- In a supplied orthogonal multiplicity-one irreducible decomposition, the actual Θ²ρ(g)
blocks have weights √dᵢ, and the normalized bond map restores the dᵢ copies.
Source: SCP10, Section 7, lines 2992–3019. -/
theorem exists_thetaBond_orthonormalCoordinates (ρ : Representation ℂ G V)
    (S : I → Subrepresentation ρ) (hI : ∀ k, (S k).toRepresentation.IsIrreducible)
    (hS : DirectSum.IsInternal (fun k => (S k).toSubmodule))
    (hOrth : OrthogonalFamily ℂ (fun k => (S k).toSubmodule)
      (fun k => (S k).toSubmodule.subtypeₗᵢ))
    (hm : ∀ k, characterMultiplicity ρ (S k).toRepresentation.character = 1)
    (d : I → ℕ) (b : ∀ k, OrthonormalBasis (Fin (d k)) ℂ (S k).toSubmodule) :
    ∃ c : OrthonormalBasis (Σ k, Fin (d k)) ℂ V,
      (∀ g, LinearMap.toMatrix c.toBasis c.toBasis (ρ g) =
        Matrix.blockDiagonal' (fun k =>
          LinearMap.toMatrix (b k).toBasis (b k).toBasis ((S k).toRepresentation g))) ∧
      (∀ g, LinearMap.toMatrix c.toBasis c.toBasis (thetaOperator ρ ^ 2 * ρ g) =
        Matrix.blockDiagonal' (fun k => (Real.sqrt (d k : ℝ) : ℂ) •
          LinearMap.toMatrix (b k).toBasis (b k).toBasis ((S k).toRepresentation g))) ∧
      (∀ g, multiplicityBondFamilyMap (fun k => Fin (d k)) (fun k => Fin (d k))
        (fun k a b => LinearMap.toMatrix c.toBasis c.toBasis (thetaOperator ρ ^ 2 * ρ g)
          ⟨k, a⟩ ⟨k, b⟩) =
        fun k => LinearMap.toMatrix (b k).toBasis (b k).toBasis ((S k).toRepresentation g) ⊗ₖ
          (1 : Matrix (Fin (d k)) (Fin (d k)) ℂ)) := by
  obtain ⟨c, he, hweight⟩ := exists_thetaOrthonormal_split ρ S hI hS hOrth hm d b
  refine ⟨c, he, hweight, ?_⟩
  have hd (k) : finrank ℂ (S k).toSubmodule = d k := by
    simpa using Module.finrank_eq_card_basis (b k).toBasis
  have hpos (k) : 0 < d k := by
    let := hI k
    simpa only [hd] using finrank_pos_of_isIrreducible (S k).toRepresentation
  let : ∀ k, Nonempty (Fin (d k)) := fun k => ⟨⟨0, hpos k⟩⟩
  intro g
  have hb : (fun k a b => LinearMap.toMatrix c.toBasis c.toBasis (thetaOperator ρ ^ 2 * ρ g)
      ⟨k, a⟩ ⟨k, b⟩) =
      fun k => (Real.sqrt (d k : ℝ) : ℂ) •
        LinearMap.toMatrix (b k).toBasis (b k).toBasis ((S k).toRepresentation g) := by
    funext k a b
    rw [hweight g, Matrix.blockDiagonal'_apply_eq]
  rw [hb]
  simpa only [Fintype.card_fin] using
    multiplicityBondFamilyMap_sqrt_smul (fun k => Fin (d k)) (fun k => Fin (d k))
      (fun k => LinearMap.toMatrix (b k).toBasis (b k).toBasis ((S k).toRepresentation g))
end TNLean.PEPS

