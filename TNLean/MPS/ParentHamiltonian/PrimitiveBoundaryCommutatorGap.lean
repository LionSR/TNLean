/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BoundaryObservableCompression
import TNLean.MPS.ParentHamiltonian.BulkObservableAlgebra
import TNLean.MPS.ParentHamiltonian.Martingale.GroundExpectationGap

/-!
# Commutator gap reduction for a primitive boundary state

For one normalized primitive tensor, interior observable expectations have a
boundary-independent limit. A centered observable has vanishing projection
onto the full finite-chain MPS space. A uniform positive finite-volume gap
therefore bounds the limiting commutator energy by the limiting excitation
norm, without assuming finite-volume uniqueness.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2, lines 933--947,
and Section 6, lines 2649--2675.

**Scope restriction (one primitive sector and explicit energy limit):**
The commutator limit is supplied explicitly. Identification with the
infinite-volume state and stabilization of the local commutator remain
separate steps; see
docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.
-/

open Filter
open scoped Matrix Topology ComplexOrder InnerProductSpace

namespace MPSTensor

variable {d D : ℕ}

/-- The squared norm of an interior excitation converges to the expectation
of the squared observable, for every varying unit boundary ground vector.
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 6, lines 2649--2675. -/
theorem IsPrimitiveMPS.bulkObservable_groundState_norm_sq_tendsto
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) (hρ : ρ.PosDef) {k : ℕ}
    (X : Matrix (Cfg d k) (Cfg d k) ℂ)
    {ι : Type*} {f : Filter ι} {ℓ r : ι → ℕ}
    (hℓ : Tendsto ℓ f atTop) (hr : Tendsto r f atTop)
    (ψ : (n : ι) → EuclideanSpace ℂ (Cfg d ((ℓ n + k) + r n)))
    (hψ : ∀ᶠ n in f, ψ n ∈ groundSpaceES A ((ℓ n + k) + r n))
    (hunit : ∀ᶠ n in f, ‖ψ n‖ = 1) :
    Tendsto (fun n =>
      ‖((Matrix.toEuclideanCLM (n := Cfg d ((ℓ n + k) + r n)) (𝕜 := ℂ))
        (bulkObservable X (ℓ n) (r n))) (ψ n)‖ ^ 2) f
      (nhds (observableInsertionExpectation A ρ (Xᴴ * X)).re) := by
  have heq (n : ι) :
      Matrix.toEuclideanCLM (n := Cfg d ((ℓ n + k) + r n)) (𝕜 := ℂ)
        (bulkObservable (Xᴴ * X) (ℓ n) (r n)) =
      (Matrix.toEuclideanCLM (n := Cfg d ((ℓ n + k) + r n)) (𝕜 := ℂ)
        (bulkObservable X (ℓ n) (r n))).adjoint *
      Matrix.toEuclideanCLM (n := Cfg d ((ℓ n + k) + r n)) (𝕜 := ℂ)
        (bulkObservable X (ℓ n) (r n)) := by
    rw [bulkObservable_mul, bulkObservable_conjTranspose, map_mul,
      ← Matrix.star_eq_conjTranspose, map_star, ContinuousLinearMap.star_eq_adjoint]
  have h := (Complex.continuous_re.tendsto _).comp
    (hP.bulkObservable_groundState_expectation_tendsto hρ (Xᴴ * X)
      hℓ hr ψ hψ hunit)
  simpa only [Function.comp_def, heq, mul_apply_eq_comp,
    ContinuousLinearMap.adjoint_inner_right, ← RCLike.re_eq_complex_re,
    inner_self_eq_norm_sq] using h

/-- A uniform finite-volume gap gives the limiting commutator bound in one
primitive sector. Both the excitation norm limit and the vanishing full
ground-space projection are derived from the tensor, rather than assumed.
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 6, lines 2649--2675. -/
theorem IsPrimitiveMPS.commutator_gap_of_bulkObservable_energy_limit
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) (hρ : ρ.PosDef) {k : ℕ}
    (X : Matrix (Cfg d k) (Cfg d k) ℂ)
    (hcenter : observableInsertionExpectation A ρ X = 0)
    {ℓ r : ℕ → ℕ} (hℓ : Tendsto ℓ atTop atTop) (hr : Tendsto r atTop atTop)
    (H : (n : ℕ) → EuclideanSpace ℂ (Cfg d ((ℓ n + k) + r n)) →ₗ[ℂ]
      EuclideanSpace ℂ (Cfg d ((ℓ n + k) + r n)))
    (ψ : (n : ℕ) → EuclideanSpace ℂ (Cfg d ((ℓ n + k) + r n)))
    {γ e : ℝ} (hγ : 0 ≤ γ)
    (hPos : ∀ᶠ n in atTop, (H n).IsPositive)
    (hGap : ∀ᶠ n in atTop, ∀ v ∈ (LinearMap.ker (H n))ᗮ,
      γ * ‖v‖ ≤ ‖H n v‖)
    (hKernel : ∀ᶠ n in atTop,
      LinearMap.ker (H n) = groundSpaceES A ((ℓ n + k) + r n))
    (hGround : ∀ᶠ n in atTop, ψ n ∈ groundSpaceES A ((ℓ n + k) + r n))
    (hUnit : ∀ᶠ n in atTop, ‖ψ n‖ = 1)
    (hEnergy :
      let B (n : ℕ) := ((Matrix.toEuclideanCLM
        (n := Cfg d ((ℓ n + k) + r n)) (𝕜 := ℂ))
          (bulkObservable X (ℓ n) (r n))).toLinearMap
      Tendsto (fun n =>
        (⟪((B n).adjoint.comp ((H n).comp (B n) - (B n).comp (H n))) (ψ n),
          ψ n⟫_ℂ).re) atTop (nhds e)) :
    γ * (observableInsertionExpectation A ρ (Xᴴ * X)).re ≤ e := by
  let B (n : ℕ) := ((Matrix.toEuclideanCLM
    (n := Cfg d ((ℓ n + k) + r n)) (𝕜 := ℂ))
      (bulkObservable X (ℓ n) (r n))).toLinearMap
  have hGround' : ∀ᶠ n in atTop, ψ n ∈ LinearMap.ker (H n) := by
    filter_upwards [hKernel, hGround] with n hk hg
    simpa only [hk] using hg
  have hNorm : Tendsto (fun n => ‖B n (ψ n)‖ ^ 2) atTop
      (nhds (observableInsertionExpectation A ρ (Xᴴ * X)).re) :=
    hP.bulkObservable_groundState_norm_sq_tendsto hρ X hℓ hr ψ hGround hUnit
  have hProjection : Tendsto (fun n =>
      ‖(LinearMap.ker (H n)).starProjection (B n (ψ n))‖ ^ 2) atTop (nhds 0) := by
    apply (hP.bulkObservable_groundSpace_projection_norm_sq_tendsto_zero hρ X
      hcenter hℓ hr ψ hGround (hUnit.mono fun _ hn => hn.le)).congr'
    filter_upwards [hKernel] with n hn
    simp only [hn, B, ContinuousLinearMap.coe_coe]
  exact FrustrationFree.commutator_gap_of_tendsto_ground_projection_zero
    H B ψ hγ hPos hGap hGround' hNorm hProjection hEnergy

end MPSTensor
