/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.PhysicalCoherentTransport
import TNLean.PEPS.CoherentMultiplicityTransport
import TNLean.PEPS.SemiRegularBondSupport
import TNLean.PEPS.TorusPhysicalBondRegrouping
import TNLean.PEPS.ThetaBondOrthonormalCoordinates

/-!
# Multiplicity restoration of the actual weighted-site torus state

The fourth-root-weighted averaging site is contracted on the native torus.
After regrouping its physical legs into oriented bonds, its state belongs to
the product of matching-sector bond spaces. Applying the multiplicity-restoring
bond maps to this actual state gives the averaging-site torus state of the
representation with each irreducible repeated by its dimension.

Source: SCP10, arXiv:1001.3807, Section 7, lines 2977–3019. The support and
state equality are derived from the actual contraction, not assumed.

**Scope restriction (supplied decomposition):** The theorem takes an orthogonal
internal irreducible decomposition with character multiplicity one and supplied
orthonormal sector bases. It does not construct the smallest semi-regular
representation or identify the restored representation with the left-regular
representation. Those representation-existence steps remain separate; see
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
open scoped Kronecker
variable {G I : Type*} [Group G] [Fintype I] [DecidableEq I]
variable (d : I → ℕ)

/-- Repeat each irreducible-sized matrix representation by its dimension.
Source: SCP10, the regular block form in Section 7, lines 2947–2954. -/
noncomputable def multiplicityRestoredRepresentation
    (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    G →* Matrix (Σ i, Fin (d i) × Fin (d i)) (Σ i, Fin (d i) × Fin (d i)) ℂ where
  toFun g := Matrix.blockDiagonal' (fun i => D i g ⊗ₖ (1 : Matrix (Fin (d i)) (Fin (d i)) ℂ))
  map_one' := by
    simp only [map_one, Matrix.one_kronecker_one]
    exact Matrix.blockDiagonal'_one
  map_mul' g h := by
    rw [← Matrix.blockDiagonal'_mul]
    congr 1
    funext i
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, map_mul]
end TNLean.PEPS

namespace TNLean.PEPS
open scoped Kronecker
variable {G I : Type*} [Group G] [Fintype G] [Fintype I] [DecidableEq I]
variable {width height : ℕ} [NeZero width] [NeZero height]

/-- A weighted block matrix identity gives matching-sector support and multiplicity
restoration for the actual dressed averaging-site torus contraction.
Source: SCP10, Section 7, lines 2977–3019. The hypotheses concern single-bond
matrices; neither a PEPS coefficient identity nor a global Gram identity is assumed. -/
theorem torusBondRegrouping_dressedAveragingSite_of_weightedBlocks
    (d : I → ℕ) (U : G →* Matrix (Σ i, Fin (d i)) (Σ i, Fin (d i)) ℂ)
    (W : Matrix (Σ i, Fin (d i)) (Σ i, Fin (d i)) ℂ)
    (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hd : ∀ i, 0 < d i) (hc : ∀ g, Commute W (U g))
    (hwm : ∀ g, W ^ 2 * U g =
      Matrix.blockDiagonal' (fun i => (Real.sqrt (d i : ℝ) : ℂ) • D i g)) :
    let Ψ := torusBondRegrouping (width := width) (height := height)
      (fun σ => torusBondNetwork (fun v t => torusDress W W
        (fun a => averagingSite U a.1 a.2.1 a.2.2.1 a.2.2.2 (σ v)) t) 1 1)
    (∃ χ, physicalProductMap (TorusVertex width height × Bool)
      (blockBondInclusion (fun i => Fin (d i))) χ = Ψ) ∧
    physicalProductMap (TorusVertex width height × Bool)
      (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (d i))) Ψ =
    torusBondRegrouping (fun σ => torusBondNetwork
      (fun v t => averagingSite (multiplicityRestoredRepresentation d D)
        t.1 t.2.1 t.2.2.1 t.2.2.2 (σ v)) 1 1) := by
  rw [torusBondRegrouping_dressedAveragingSite_coherent U W hc,
    torusBondRegrouping_averagingSite_coherent]
  exact coherentWeightedBlocks_support_restore d (fun i g => D i g)
    (fun g => W ^ 2 * U g) hwm hd
    (fun _ : TorusVertex width height → G =>
      (Fintype.card G : ℂ)⁻¹ ^ Fintype.card (TorusVertex width height))
    torusBondRelativeElement

end TNLean.PEPS

namespace TNLean.PEPS
open Representation Module LinearMap
open scoped Kronecker
variable {G V I : Type*} [Group G] [Fintype G] [Fintype I] [DecidableEq I]
variable [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable {width height : ℕ} [NeZero width] [NeZero height]
/-- The actual weighted-site state has matching-sector bond support, and the
product multiplicity-restoring map carries it to the actual repeated-block state.
Source: SCP10, Section 7, lines 2977–3019. -/
theorem exists_torusMultiplicityBondState_of_orthogonalSectors
    (ρ : Representation ℂ G V) (S : I → Subrepresentation ρ)
    (hI : ∀ i, (S i).toRepresentation.IsIrreducible)
    (hS : DirectSum.IsInternal (fun i => (S i).toSubmodule))
    (hOrth : OrthogonalFamily ℂ (fun i => (S i).toSubmodule)
      (fun i => (S i).toSubmodule.subtypeₗᵢ))
    (hm : ∀ i, characterMultiplicity ρ (S i).toRepresentation.character = 1)
    (d : I → ℕ) (b : ∀ i, OrthonormalBasis (Fin (d i)) ℂ (S i).toSubmodule) :
    ∃ c : OrthonormalBasis (Σ i, Fin (d i)) ℂ V,
      let U := (LinearMap.toMatrixAlgEquiv c.toBasis).toMonoidHom.comp ρ
      let W := LinearMap.toMatrix c.toBasis c.toBasis (thetaOperator ρ)
      let D := fun i => (LinearMap.toMatrixAlgEquiv (b i).toBasis).toMonoidHom.comp
        (S i).toRepresentation
      let Ψ := torusBondRegrouping (width := width) (height := height)
        (fun σ => torusBondNetwork (fun v t => torusDress W W
          (fun a => averagingSite U a.1 a.2.1 a.2.2.1 a.2.2.2 (σ v)) t) 1 1)
      (∃ χ, physicalProductMap (TorusVertex width height × Bool)
        (blockBondInclusion (fun i => Fin (d i))) χ = Ψ) ∧
      physicalProductMap (TorusVertex width height × Bool)
        (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (d i))) Ψ =
      torusBondRegrouping (fun σ => torusBondNetwork
        (fun v t => averagingSite (multiplicityRestoredRepresentation d D)
          t.1 t.2.1 t.2.2.1 t.2.2.2 (σ v)) 1 1) := by
  obtain ⟨c, _, hweight, _⟩ :=
    exists_thetaBond_orthonormalCoordinates ρ S hI hS hOrth hm d b
  let U := (LinearMap.toMatrixAlgEquiv c.toBasis).toMonoidHom.comp ρ
  let W := LinearMap.toMatrix c.toBasis c.toBasis (thetaOperator ρ)
  let D := fun i => (LinearMap.toMatrixAlgEquiv (b i).toBasis).toMonoidHom.comp
    (S i).toRepresentation
  have hd (i) : finrank ℂ (S i).toSubmodule = d i := by
    simpa using Module.finrank_eq_card_basis (b i).toBasis
  have hpos (i) : 0 < d i := by
    let := hI i
    simpa only [hd] using finrank_pos_of_isIrreducible (S i).toRepresentation
  have hc (g) : Commute W (U g) :=
    (thetaOperator_commute ρ g).map (LinearMap.toMatrixAlgEquiv c.toBasis)
  have hwm (g) : W ^ 2 * U g = Matrix.blockDiagonal' (fun i =>
      (Real.sqrt (d i : ℝ) : ℂ) • D i g) := by
    change (LinearMap.toMatrixAlgEquiv c.toBasis) (thetaOperator ρ) ^ 2 *
      (LinearMap.toMatrixAlgEquiv c.toBasis) (ρ g) = _
    rw [← map_pow, ← map_mul]
    exact hweight g
  exact ⟨c, torusBondRegrouping_dressedAveragingSite_of_weightedBlocks
    d U W D hpos hc hwm⟩
end TNLean.PEPS
