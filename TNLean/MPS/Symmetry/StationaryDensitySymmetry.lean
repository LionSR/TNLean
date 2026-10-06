/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.KrausFreedom
import TNLean.MPS.Preparation.BlockedPolar
import TNLean.Algebra.ProjectiveRepresentation

/-!
# Symmetry of a unique stationary matrix

A unitary physical rotation preserves the adjoint transfer map. Exact virtual
covariance therefore carries every stationary matrix to another stationary
matrix by unitary conjugation. If the trace-one stationary matrix is unique,
this conjugation fixes it, so it commutes with the virtual action.

The results apply to uniqueness among all trace-one stationary matrices. In
particular, they apply to a density matrix when the trace-one fixed point of
the adjoint transfer map is unique. They also apply when the stationary density
matrix is singular.

Source context: Cirac, Pérez-García, Schuch and Verstraete, arXiv:2011.12127,
§III.A, paragraph "Entanglement spectrum and edge modes". The stationary
matrix inherits the virtual symmetry by uniqueness. The normalization used
here places the density matrix in the fixed space of the adjoint transfer map.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open scoped Matrix

namespace MPSTensor

/-- Unitary physical rotation leaves the adjoint transfer map unchanged. -/
theorem adjointMap_rotatePhysical_eq_of_unitary
    {d D : ℕ} (A : MPSTensor d D)
    (u : Matrix (Fin d) (Fin d) ℂ) (hu : uᴴ * u = 1)
    (Z : Matrix (Fin D) (Fin D) ℂ) :
    Kraus.adjointMap (rotatePhysical u A) Z = Kraus.adjointMap A Z := by
  apply kraus_dual_eq_of_map_eq (rotatePhysical u A) A
  intro Y
  have hRot : Kraus.transferMap (rotatePhysical u A) = Kraus.transferMap A :=
    transferMap_rotatePhysical_eq u A (by rw [hu, rotatePhysical_one])
  simpa only [Kraus.transferMap_apply] using congrArg (fun E => E Y) hRot

/-- Under exact unitary covariance, the adjoint transfer map intertwines
conjugation by the virtual unitary. -/
theorem adjointMap_conj_of_unitary_covariance
    {d D : ℕ} (A : MPSTensor d D)
    (u : Matrix (Fin d) (Fin d) ℂ) (hu : uᴴ * u = 1)
    (X : Matrix (Fin D) (Fin D) ℂ) (hX : Xᴴ * X = 1)
    (hCov : rotatePhysical u A = fun i => X * A i * Xᴴ)
    (Z : Matrix (Fin D) (Fin D) ℂ) :
    Kraus.adjointMap A (X * Z * Xᴴ) = X * Kraus.adjointMap A Z * Xᴴ := by
  rw [← adjointMap_rotatePhysical_eq_of_unitary A u hu, hCov]
  simp only [Kraus.adjointMap_apply, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_assoc, ← Matrix.mul_assoc Xᴴ X, hX, Matrix.one_mul]

/-- A unique trace-one stationary matrix of the adjoint transfer map
commutes with each virtual unitary implementing exact physical covariance.
Source context: arXiv:2011.12127, §III.A, "Entanglement spectrum and edge modes". -/
theorem commute_stationaryMatrix_of_unitary_covariance
    {d D : ℕ} (A : MPSTensor d D)
    (u : Matrix (Fin d) (Fin d) ℂ) (hu : uᴴ * u = 1)
    (X : Matrix (Fin D) (Fin D) ℂ) (hX : Xᴴ * X = 1)
    (hCov : rotatePhysical u A = fun i => X * A i * Xᴴ)
    (σ : Matrix (Fin D) (Fin D) ℂ)
    (hσ : Kraus.adjointMap A σ = σ) (htr : Matrix.trace σ = 1)
    (huniq : ∀ τ : Matrix (Fin D) (Fin D) ℂ,
      Kraus.adjointMap A τ = τ → Matrix.trace τ = 1 → τ = σ) :
    Commute X σ := by
  have hconj : X * σ * Xᴴ = σ := huniq _
    (by rw [adjointMap_conj_of_unitary_covariance A u hu X hX hCov, hσ])
    (by rw [Matrix.trace_mul_cycle, hX, Matrix.one_mul, htr])
  have h := congrArg (fun M => M * X) hconj
  change X * σ = σ * X
  simpa only [Matrix.mul_assoc, hX, Matrix.mul_one] using h

/-- The unique trace-one stationary matrix of the adjoint transfer map
commutes with every matrix of the virtual projective action. Physical
covariance is expressed using the inverse group element.
Source context: arXiv:2011.12127, §III.A, "Entanglement spectrum and edge modes". -/
theorem virtualAction_commute_stationaryMatrix_of_unique
    {G : Type} [Group G] {d D : ℕ}
    {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ : TNLean.Algebra.ProjectiveRepresentation (D := D) ω)
    (hρ : ∀ g, (ρ.X g : Matrix (Fin D) (Fin D) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ) (A : MPSTensor d D)
    (hCov : ∀ g, rotatePhysical (U g) A = fun i =>
      (ρ.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * A i *
        (ρ.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ)ᴴ)
    (σ : Matrix (Fin D) (Fin D) ℂ)
    (hσ : Kraus.adjointMap A σ = σ) (htr : Matrix.trace σ = 1)
    (huniq : ∀ τ : Matrix (Fin D) (Fin D) ℂ,
      Kraus.adjointMap A τ = τ → Matrix.trace τ = 1 → τ = σ) :
    ∀ g, Commute (ρ.X g : Matrix (Fin D) (Fin D) ℂ) σ := by
  intro g
  apply commute_stationaryMatrix_of_unitary_covariance A (U g⁻¹) _ (ρ.X g) _
    (by simpa only [inv_inv] using hCov g⁻¹) σ hσ htr huniq
  · simpa only [Matrix.star_eq_conjTranspose] using
      Matrix.mem_unitaryGroup_iff'.mp (SetLike.coe_mem (U g⁻¹))
  · simpa only [Matrix.star_eq_conjTranspose] using
      Matrix.mem_unitaryGroup_iff'.mp (hρ g)


end MPSTensor
