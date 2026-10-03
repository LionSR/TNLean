/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularTorusGram
import TNLean.PEPS.TorusSemiRegularEquivalence

/-!
# Exact normalization of the Section 7 torus states

The normalized averaging site preserves inner products on the invariant virtual
subspace with factor one. Its regular torus contraction has squared norm
|G|^(N+1), where N is the number of sites. The actual fourth-root-weighted block
state has the same squared norm under the physical isometry to the regular state.

These are auxiliary normalization consequences of SCP10, arXiv:1001.3807,
Definition 6.1 and Section 7, lines 1692–1702 and 2938–3019. The contractions
use the existing normalized averaging sites and unnormalized virtual bonds.

**Scope restriction (finite torus):** The norm formulas concern finite tori
with positive periods and the chosen block construction with its Fourier
intertwiner. The broader lattice geometry of Section 7 is documented in
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

open scoped Matrix BigOperators
namespace TNLean.PEPS
variable {G : Type*} [Group G] [Fintype G]
attribute [local instance] Representation.invertibleFintypeCardComplex

/-- The averaging site has isometry factor one on invariant vectors.
Source: SCP10, Definition 6.1, lines 1692–1702. -/
theorem isGIsometric_averagingSite {V : Type*} [Fintype V] [DecidableEq V]
    (U : G →* Matrix V V ℂ) :
    IsGIsometric (torusLegRep U) (siteMap (averagingSite U)) := by
  refine ⟨isGInjective_averagingSite U, 1, zero_lt_one, ?_⟩
  intro x hx y hy
  rw [siteMap_averagingSite, (torusLegRep U).averageMap_id x hx,
    (torusLegRep U).averageMap_id y hy]
  simp

variable [DecidableEq G]

private theorem averagingSite_regular_gram (η θ : G × G × G × G) :
    (∑ s, star (averagingSite (leftRegularMatrix G)
      η.1 η.2.1 η.2.2.1 η.2.2.2 s) *
      averagingSite (leftRegularMatrix G) θ.1 θ.2.1 θ.2.2.1 θ.2.2.2 s) =
      (1 / (Fintype.card G : ℂ)) * ∑ g : G, if η = g • θ then 1 else 0 := by
  let ρ := torusLegRep (leftRegularMatrix G)
  have hAvg := averageMap_dotProduct_of_unitary ρ torusLegRep_leftRegularMatrix_unitary
  simp only [averagingSite, LinearMap.toMatrix'_apply]
  change star (ρ.averageMap (Pi.single η 1)) ⬝ᵥ
    ρ.averageMap (Pi.single θ 1) = _
  rw [hAvg, ρ.averageMap_id _ (ρ.averageMap_invariant _)]
  have hentry := toMatrix_averageMap_torusLegRep_leftRegularMatrix η θ
  simpa [LinearMap.toMatrix'_apply, ρ] using hentry

variable {width height : ℕ} [NeZero width] [NeZero height]

/-- The actual regular averaging-site torus state has squared norm |G|^(N+1).
Source: the regular Gram contraction of SCP10, Definition 6.1, and the native
regular state used in Section 7, lines 2938–2947. -/
theorem torusBondNetwork_regular_averagingSite_norm :
    let Ψ := fun σ : TorusVertex width height → G × G × G × G =>
      torusBondNetwork (fun v t => averagingSite (leftRegularMatrix G)
        t.1 t.2.1 t.2.2.1 t.2.2.2 (σ v)) 1 1
    star Ψ ⬝ᵥ Ψ = (Fintype.card G : ℂ) ^
      (Fintype.card (TorusVertex width height) + 1) := by
  have h := sum_star_torusGClosure_regular_mul (width := width) (height := height)
    (averagingSite (leftRegularMatrix G))
    1 averagingSite_regular_gram (1 : G) 1 1 1
  have hH : torusHorizontalClosure (leftRegularMatrix G) (1 : G)
      (width := width) (height := height) = 1 := by
    funext v
    simp [torusHorizontalClosure]
  have hV : torusVerticalClosure (leftRegularMatrix G) (1 : G)
      (width := width) (height := height) = 1 := by
    funext v
    simp [torusVerticalClosure]
  simpa [torusGClosure, hH, hV, dotProduct, pow_succ] using h


private theorem ne_zero_of_squared_norm {X : Type*} [Fintype X]
    (ψ : X → ℂ) (c : ℂ) (hnorm : star ψ ⬝ᵥ ψ = c) (hc : c ≠ 0) : ψ ≠ 0 := by
  intro hzero
  apply hc
  simpa only [hzero, star_zero, zero_dotProduct] using hnorm.symm

/-- The actual regular averaging-site torus state is nonzero at all positive periods.
Source: the exact auxiliary norm of the regular state in SCP10, Section 7. -/
theorem torusBondNetwork_regular_averagingSite_ne_zero :
    (fun σ : TorusVertex width height → G × G × G × G =>
      torusBondNetwork (fun v t => averagingSite (leftRegularMatrix G)
        t.1 t.2.1 t.2.2.1 t.2.2.2 (σ v)) 1 1) ≠ 0 :=
  ne_zero_of_squared_norm _ _ (torusBondNetwork_regular_averagingSite_norm
    (width := width) (height := height))
    (pow_ne_zero _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))

/-- A norm-preserving physical map to the actual regular torus state transfers its
exact normalization and nonvanishing. Source: the local isometry in SCP10,
Section 7, lines 2977–3019. This is a reusable normalization consequence. -/
theorem norm_ne_zero_of_isometry_to_regularTorus {X : Type*} [Fintype X]
    (F : (X → ℂ) →ₗ[ℂ] (((TorusVertex width height × Bool) → G × G) → ℂ))
    (hF : ∀ ψ, star (F ψ) ⬝ᵥ F ψ = star ψ ⬝ᵥ ψ)
    (ψ : X → ℂ)
    (hstate : F ψ = torusBondRegrouping (fun σ => torusBondNetwork
      (fun v t => averagingSite (leftRegularMatrix G)
        t.1 t.2.1 t.2.2.1 t.2.2.2 (σ v)) 1 1)) :
    star ψ ⬝ᵥ ψ = (Fintype.card G : ℂ) ^
      (Fintype.card (TorusVertex width height) + 1) ∧ ψ ≠ 0 := by
  have hnorm := hF ψ
  rw [hstate, torusBondRegrouping_dotProduct,
    torusBondNetwork_regular_averagingSite_norm] at hnorm
  exact ⟨hnorm.symm, ne_zero_of_squared_norm ψ _ hnorm.symm
    (pow_ne_zero _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))⟩

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The actual fourth-root-weighted block torus state has the exact regular-state
norm and is nonzero in the chosen Fourier construction. The norm is derived from
the physical state isometry. Source: SCP10, Section 7, lines 2977–3019. -/
theorem torusBondNetwork_blockFourthRootWeight_norm_ne_zero
    (d : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hd : ∀ i, 0 < d i) (Q : Matrix G (Σ i, Fin (d i) × Fin (d i)) ℂ)
    (hQ : Q.IsIsometry)
    (hreg : ∀ g, leftRegularMatrix G g =
      Q * multiplicityRestoredRepresentation d D g * Q.conjTranspose) :
    let U := blockMatrixRepresentation d D
    let W := blockFourthRootWeight d
    let H := fun σ : TorusVertex width height →
        (Σ i, Fin (d i)) × (Σ i, Fin (d i)) × (Σ i, Fin (d i)) × (Σ i, Fin (d i)) =>
      torusBondNetwork (fun v t => torusDress W W
        (fun a => averagingSite U a.1 a.2.1 a.2.2.1 a.2.2.2 (σ v)) t) 1 1
    star H ⬝ᵥ H = (Fintype.card G : ℂ) ^
      (Fintype.card (TorusVertex width height) + 1) ∧ H ≠ 0 := by
  obtain ⟨T, _, hstate, hinner⟩ := exists_isometric_torusSemiRegularBondMap
    (width := width) (height := height) d D hd Q hQ hreg
  have hresult := norm_ne_zero_of_isometry_to_regularTorus
    _ (fun ψ => hinner ψ ψ) _ hstate
  constructor
  · simpa only [torusBondRegrouping_dotProduct] using hresult.1
  · intro hzero
    apply hresult.2
    simp only [hzero, map_zero]

end TNLean.PEPS
