/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.NeumannInverse
import TNLean.MPS.ParentHamiltonian.GramConvergence
import TNLean.MPS.ParentHamiltonian.LimitingGramMetric

/-!
# Convergence of inverse MPS Gram operators

For a primitive MPS tensor with a positive-definite transfer fixed point, the
finite-volume ground-space Gram operators are eventually invertible. Their
ring inverses satisfy the arbitrary-base Neumann perturbation estimate and
converge to the inverse of the nonidentity limiting Gram operator
`Matrix.gramReshuffle (fixedPointProj ρ _)`.

The same eventual invertibility makes the Hilbert-space boundary maps
injective. Consequently, their `ContinuousLinearMap.inverseGram` operators
agree with the ring inverses and obey the same estimate.

## Main results

* `MPSTensor.IsPrimitiveMPS.eventually_groundSpaceGram_isUnit_and_inverse_bound`
* `MPSTensor.IsPrimitiveMPS.groundSpaceGram_ringInverse_tendsto`
* `MPSTensor.IsPrimitiveMPS.eventually_groundSpaceMapES_injective_and_inverseGram_bound`
-/

open scoped ComplexOrder Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- For every relative tolerance `a` strictly between zero and one, the
finite-volume Gram operator of a primitive MPS tensor is eventually a unit.
Its ring inverse differs from the inverse of the reshuffled fixed-point
projection by at most
\((1-a)^{-1}a\lVert K_\infty^{-1}\rVert\), where
`Kinf` is `Matrix.gramReshuffle (fixedPointProj ρ _)`.

Positive definiteness of `ρ` is explicit: primitivity alone only supplies a
positive-semidefinite fixed point and does not justify invertibility of the
limiting Gram operator. -/
theorem IsPrimitiveMPS.eventually_groundSpaceGram_isUnit_and_inverse_bound
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) (hρ : ρ.PosDef) {a : ℝ} (ha_pos : 0 < a)
    (ha_lt_one : a < 1) :
    ∀ᶠ n in Filter.atTop,
      IsUnit (groundSpaceGram A n) ∧
        ‖Ring.inverse (groundSpaceGram A n) -
            Ring.inverse (Matrix.gramReshuffle
              (fixedPointProj ρ (ne_of_gt hρ.trace_pos)))‖ ≤
          (1 - a)⁻¹ * a *
            ‖Ring.inverse (Matrix.gramReshuffle
              (fixedPointProj ρ (ne_of_gt hρ.trace_pos)))‖ := by
  let Kinf := Matrix.gramReshuffle (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
  have hKinf : IsUnit Kinf := Matrix.gramReshuffle_fixedPointProj_isUnit hρ
  have hconv : Filter.Tendsto (fun n => groundSpaceGram A n) Filter.atTop (nhds Kinf) := by
    simpa only [Kinf] using hP.groundSpaceGram_tendsto_gramReshuffle_fixedPointProj
  have hpert_tendsto : Filter.Tendsto
      (fun n => ‖Ring.inverse Kinf‖ * ‖groundSpaceGram A n - Kinf‖)
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul (tendsto_iff_norm_sub_tendsto_zero.mp hconv))
  filter_upwards [(tendsto_order.1 hpert_tendsto).2 a ha_pos] with n hn
  have hunit := NormedRing.isUnit_and_norm_inverse_le_of_norm_mul_norm_sub_le
    Kinf (groundSpaceGram A n) hKinf hn.le ha_lt_one
  refine ⟨hunit.1, ?_⟩
  simpa only [Kinf] using
    NormedRing.norm_inverse_sub_inverse_le_of_norm_mul_norm_sub_le
      Kinf (groundSpaceGram A n) hKinf hn.le ha_lt_one

/-- The ring inverses of the finite-volume Gram operators of a primitive MPS
tensor converge to the inverse of the nonidentity limiting Gram operator.
Positive definiteness of the fixed point is required to place the limit in the
open set of units. -/
theorem IsPrimitiveMPS.groundSpaceGram_ringInverse_tendsto
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) (hρ : ρ.PosDef) :
    Filter.Tendsto (fun n => Ring.inverse (groundSpaceGram A n)) Filter.atTop
      (nhds (Ring.inverse (Matrix.gramReshuffle
        (fixedPointProj ρ (ne_of_gt hρ.trace_pos))))) := by
  let Kinf := Matrix.gramReshuffle (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
  have hKinf : IsUnit Kinf := Matrix.gramReshuffle_fixedPointProj_isUnit hρ
  have hconv : Filter.Tendsto (fun n => groundSpaceGram A n) Filter.atTop (nhds Kinf) := by
    simpa only [Kinf] using hP.groundSpaceGram_tendsto_gramReshuffle_fixedPointProj
  change Filter.Tendsto (fun n => Ring.inverse (groundSpaceGram A n)) Filter.atTop
    (nhds (Ring.inverse Kinf))
  rw [← hKinf.unit_spec, Ring.inverse_unit]
  have hinv := (NormedRing.inverse_continuousAt hKinf.unit).tendsto.comp hconv
  change Filter.Tendsto (fun n => Ring.inverse (groundSpaceGram A n)) Filter.atTop
    (nhds (Ring.inverse (hKinf.unit :
      EuclideanSpace ℂ (Fin D × Fin D) →L[ℂ] EuclideanSpace ℂ (Fin D × Fin D)))) at hinv
  simpa only [Ring.inverse_unit] using hinv

/-- Eventually the Hilbert-space boundary map is injective. For any relative
tolerance `a` in `(0, 1)`, one may choose an injectivity proof so that its
inverse-Gram operator is exactly the ring inverse of the finite-volume Gram
operator and satisfies the same arbitrary-base Neumann estimate around the
reshuffled fixed-point projection.

The equality is independent of the chosen injectivity proof by proof
irrelevance. -/
theorem IsPrimitiveMPS.eventually_groundSpaceMapES_injective_and_inverseGram_bound
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) (hρ : ρ.PosDef) {a : ℝ} (ha_pos : 0 < a)
    (ha_lt_one : a < 1) :
    ∀ᶠ n in Filter.atTop,
      ∃ hInj : Function.Injective (groundSpaceMapES A n),
        ContinuousLinearMap.inverseGram (groundSpaceMapES A n) hInj =
            Ring.inverse (groundSpaceGram A n) ∧
          ‖ContinuousLinearMap.inverseGram (groundSpaceMapES A n) hInj -
              Ring.inverse (Matrix.gramReshuffle
                (fixedPointProj ρ (ne_of_gt hρ.trace_pos)))‖ ≤
            (1 - a)⁻¹ * a *
              ‖Ring.inverse (Matrix.gramReshuffle
                (fixedPointProj ρ (ne_of_gt hρ.trace_pos)))‖ := by
  filter_upwards [hP.eventually_groundSpaceGram_isUnit_and_inverse_bound
    hρ ha_pos ha_lt_one] with n hn
  have hGramInj : Function.Injective (groundSpaceGram A n) :=
    (ContinuousLinearMap.isUnit_iff_bijective.mp hn.1).1
  have hInj : Function.Injective (groundSpaceMapES A n) := by
    apply (groundSpaceMapES A n).adjoint_comp_self_injective_iff.mp
    intro x y hxy
    apply hGramInj
    change (groundSpaceMapES A n).adjoint (groundSpaceMapES A n x) =
      (groundSpaceMapES A n).adjoint (groundSpaceMapES A n y)
    exact hxy
  refine ⟨hInj, ?_, ?_⟩
  · simpa only [groundSpaceGram] using
      ContinuousLinearMap.inverseGram_eq_ringInverse (groundSpaceMapES A n) hInj
  · rw [ContinuousLinearMap.inverseGram_eq_ringInverse]
    simpa only [groundSpaceGram] using hn.2

end MPSTensor
