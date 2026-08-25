/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.NeumannInverse
import TNLean.MPS.ParentHamiltonian.GramConvergence
import QICLean.Channel.FixedPoint.LimitingGramMetric

/-!
# Convergence of inverse MPS Gram operators

For a primitive MPS tensor with a positive-definite transfer fixed point, the
finite-volume ground-space Gram operators converge geometrically to the
nonidentity limiting Gram operator
`Matrix.gramReshuffle (fixedPointProj ρ _)`. Pointwise Neumann estimates give
invertibility, inverse-norm control, and inverse displacement whenever the
geometric relative error is less than one. The same estimates apply uniformly
at the three C3 correction lengths once they hold at the base length.

The corresponding Hilbert-space boundary maps are injective under the same
pointwise condition. Their `ContinuousLinearMap.inverseGram` operators agree
with the ring inverses and obey the same bounds. Eventual invertibility and
convergence of the ring inverses are also recorded.

## Main results

* `MPSTensor.groundSpaceMapES_injective_of_isUnit_groundSpaceGram`
* `MPSTensor.IsPrimitiveMPS.groundSpaceGram_geometric_inverse_bounds`
* `MPSTensor.IsPrimitiveMPS.groundSpaceMapES_geometric_inverseGram_bounds`
* `MPSTensor.geometric_smallness_at_c3_lengths`
* `MPSTensor.IsPrimitiveMPS.eventually_groundSpaceGram_isUnit_and_inverse_bound`
* `MPSTensor.IsPrimitiveMPS.groundSpaceGram_ringInverse_tendsto`
* `MPSTensor.IsPrimitiveMPS.eventually_groundSpaceMapES_injective_and_inverseGram_bound`
-/

open scoped ComplexOrder Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- A unit finite-volume Gram operator implies injectivity of the corresponding
Hilbert-space boundary map. -/
theorem groundSpaceMapES_injective_of_isUnit_groundSpaceGram {A : MPSTensor d D} {n : ℕ}
    (hGramUnit : IsUnit (groundSpaceGram A n)) :
    Function.Injective (groundSpaceMapES A n) := by
  have hGramInj : Function.Injective (groundSpaceGram A n) :=
    (ContinuousLinearMap.isUnit_iff_bijective.mp hGramUnit).1
  apply (groundSpaceMapES A n).adjoint_comp_self_injective_iff.mp
  intro x y hxy
  apply hGramInj
  change (groundSpaceMapES A n).adjoint (groundSpaceMapES A n x) =
    (groundSpaceMapES A n).adjoint (groundSpaceMapES A n y)
  exact hxy

/-- Pointwise geometric control of the finite Gram operators and their ring inverses.

Writing \(K_\infty\) for the reshuffled fixed-point projection and
\(I_\infty=K_\infty^{-1}\), this theorem produces positive constants
\(g,c,r\), with \(r<1\) and \(c=\lVert I_\infty\rVert g\), such that
\(\lVert K_n-K_\infty\rVert\le g r^n\). Whenever \(c r^n<1\), the Gram
operator is a unit and both its inverse norm and its displacement from
\(I_\infty\) obey the corresponding Neumann bounds with denominator
\(1-c r^n\).

The direct choice \(g=\sqrt{D^3} C_G\) is obtained by taking square roots
of the available squared Gram estimate, without an additional dimension loss. -/
theorem IsPrimitiveMPS.groundSpaceGram_geometric_inverse_bounds
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) (hρ : ρ.PosDef) :
    let Kinf := Matrix.gramReshuffle (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
    let Iinf := Ring.inverse Kinf
    ∃ g c r : ℝ, 0 < g ∧ 0 < c ∧ 0 < r ∧ r < 1 ∧
      c = ‖Iinf‖ * g ∧ ∀ n : ℕ, 1 ≤ n →
        ‖groundSpaceGram A n - Kinf‖ ≤ g * r ^ n ∧
        (c * r ^ n < 1 →
          IsUnit (groundSpaceGram A n) ∧
          ‖Ring.inverse (groundSpaceGram A n)‖ ≤
            (1 - c * r ^ n)⁻¹ * ‖Iinf‖ ∧
          ‖Ring.inverse (groundSpaceGram A n) - Iinf‖ ≤
            (1 - c * r ^ n)⁻¹ * (c * r ^ n) * ‖Iinf‖) := by
  let Kinf := Matrix.gramReshuffle (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
  let Iinf := Ring.inverse Kinf
  obtain ⟨C_G, r, hC_G, hr_pos, hr_lt_one, hGramSq⟩ :=
    hP.groundSpaceGram_sub_fixedPointProj_norm_sq_le_geometric
  let g := Real.sqrt ((D : ℝ) ^ 3) * C_G
  let c := ‖Iinf‖ * g
  have hD_pos : 0 < (D : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne D)
  have hD : 0 < (D : ℝ) ^ 3 := pow_pos hD_pos 3
  have hg : 0 < g := mul_pos (Real.sqrt_pos.2 hD) hC_G
  have hKinf : IsUnit Kinf := by
    simpa only [Kinf] using Matrix.gramReshuffle_fixedPointProj_isUnit hρ
  have hIinf : IsUnit Iinf := by
    simpa only [Iinf] using hKinf.ringInverse
  have hIinf_norm : 0 < ‖Iinf‖ := norm_pos_iff.mpr hIinf.ne_zero
  refine ⟨g, c, r, hg, mul_pos hIinf_norm hg, hr_pos, hr_lt_one, rfl, ?_⟩
  intro n hn
  have hGramSq' : ‖groundSpaceGram A n - Kinf‖ ^ 2 ≤
      (D : ℝ) ^ 3 * (C_G * r ^ n) ^ 2 := by
    simpa only [Kinf] using hGramSq n hn
  have hgr_nonneg : 0 ≤ g * r ^ n := by positivity
  have hGram : ‖groundSpaceGram A n - Kinf‖ ≤ g * r ^ n := by
    apply (sq_le_sq₀ (norm_nonneg _) hgr_nonneg).1
    calc
      ‖groundSpaceGram A n - Kinf‖ ^ 2 ≤
          (D : ℝ) ^ 3 * (C_G * r ^ n) ^ 2 := hGramSq'
      _ = Real.sqrt ((D : ℝ) ^ 3) ^ 2 * (C_G * r ^ n) ^ 2 := by
        rw [Real.sq_sqrt hD.le]
      _ = (Real.sqrt ((D : ℝ) ^ 3) * (C_G * r ^ n)) ^ 2 := by ring
      _ = (g * r ^ n) ^ 2 := by simp only [g]; ring
  refine ⟨hGram, fun hsmall => ?_⟩
  have hrelative : ‖Iinf‖ * ‖groundSpaceGram A n - Kinf‖ ≤ c * r ^ n := by
    calc
      ‖Iinf‖ * ‖groundSpaceGram A n - Kinf‖ ≤ ‖Iinf‖ * (g * r ^ n) :=
        mul_le_mul_of_nonneg_left hGram (norm_nonneg Iinf)
      _ = c * r ^ n := by simp only [c]; ring
  have hunit := NormedRing.isUnit_and_norm_inverse_le_of_norm_mul_norm_sub_le
    Kinf (groundSpaceGram A n) hKinf (by simpa only [Iinf] using hrelative) hsmall
  refine ⟨hunit.1, ?_, ?_⟩
  · simpa only [Iinf] using hunit.2
  · simpa only [Iinf] using
      NormedRing.norm_inverse_sub_inverse_le_of_norm_mul_norm_sub_le
        Kinf (groundSpaceGram A n) hKinf
          (by simpa only [Iinf] using hrelative) hsmall

/-- Pointwise inverse-Gram bounds for the finite-volume boundary maps.

With \(K_\infty\), \(I_\infty\), \(g\), \(c\), and \(r\) as in
`groundSpaceGram_geometric_inverse_bounds`, every length \(n\ge 1\) satisfying
\(c r^n<1\) has an injective boundary map. Its inverse Gram operator equals the
ring inverse of the finite Gram operator and satisfies the same inverse-norm
and inverse-displacement estimates. -/
theorem IsPrimitiveMPS.groundSpaceMapES_geometric_inverseGram_bounds
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) (hρ : ρ.PosDef) :
    let Kinf := Matrix.gramReshuffle (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
    let Iinf := Ring.inverse Kinf
    ∃ g c r : ℝ, 0 < g ∧ 0 < c ∧ 0 < r ∧ r < 1 ∧
      c = ‖Iinf‖ * g ∧ ∀ n : ℕ, 1 ≤ n →
        ‖groundSpaceGram A n - Kinf‖ ≤ g * r ^ n ∧
        (c * r ^ n < 1 →
          ∃ hInj : Function.Injective (groundSpaceMapES A n),
            ContinuousLinearMap.inverseGram (groundSpaceMapES A n) hInj =
                Ring.inverse (groundSpaceGram A n) ∧
            ‖ContinuousLinearMap.inverseGram (groundSpaceMapES A n) hInj‖ ≤
                (1 - c * r ^ n)⁻¹ * ‖Iinf‖ ∧
            ‖ContinuousLinearMap.inverseGram (groundSpaceMapES A n) hInj - Iinf‖ ≤
                (1 - c * r ^ n)⁻¹ * (c * r ^ n) * ‖Iinf‖) := by
  let Kinf := Matrix.gramReshuffle (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
  let Iinf := Ring.inverse Kinf
  obtain ⟨g, c, r, hg, hc, hr_pos, hr_lt_one, hc_def, hbounds⟩ :=
    hP.groundSpaceGram_geometric_inverse_bounds hρ
  refine ⟨g, c, r, hg, hc, hr_pos, hr_lt_one, hc_def, ?_⟩
  intro n hn
  obtain ⟨hGram, hpointwise⟩ := hbounds n hn
  refine ⟨hGram, fun hsmall => ?_⟩
  obtain ⟨hGramUnit, hInvNorm, hInvSub⟩ := hpointwise hsmall
  have hInj : Function.Injective (groundSpaceMapES A n) :=
    groundSpaceMapES_injective_of_isUnit_groundSpaceGram hGramUnit
  refine ⟨hInj, ?_, ?_, ?_⟩
  · simpa only [groundSpaceGram] using
      ContinuousLinearMap.inverseGram_eq_ringInverse (groundSpaceMapES A n) hInj
  · rw [ContinuousLinearMap.inverseGram_eq_ringInverse]
    simpa only [groundSpaceGram] using hInvNorm
  · rw [ContinuousLinearMap.inverseGram_eq_ringInverse]
    simpa only [groundSpaceGram] using hInvSub

/-- A geometric smallness condition at length \(l\) propagates uniformly in
\(K\) to the three C3 correction lengths \(l+1\), \(K+l\), and
\(K+l+1\). -/
theorem geometric_smallness_at_c3_lengths {c r : ℝ} (hc : 0 < c) (hr_pos : 0 < r)
    (hr_lt_one : r < 1) {l : ℕ} (hsmall : c * r ^ l < 1) (K : ℕ) :
    c * r ^ (l + 1) < 1 ∧ c * r ^ (K + l) < 1 ∧ c * r ^ (K + l + 1) < 1 := by
  have hpow {m : ℕ} (hlm : l ≤ m) : r ^ m ≤ r ^ l :=
    pow_le_pow_of_le_one hr_pos.le hr_lt_one.le hlm
  have hsmall_of_le {m : ℕ} (hlm : l ≤ m) : c * r ^ m < 1 :=
    (mul_le_mul_of_nonneg_left (hpow hlm) hc.le).trans_lt hsmall
  exact ⟨hsmall_of_le (by omega), hsmall_of_le (by omega), hsmall_of_le (by omega)⟩

/-- For every relative tolerance \(a\) strictly between zero and one, the
finite-volume Gram operator of a primitive MPS tensor is eventually a unit.
Its ring inverse differs from the inverse of the reshuffled fixed-point
projection by at most
\((1-a)^{-1}a\lVert K_\infty^{-1}\rVert\), where
\(K_\infty\) is `Matrix.gramReshuffle (fixedPointProj ρ _)`.

Positive definiteness of \(\rho\) is explicit: primitivity alone only supplies a
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
  exact NormedRing.inverse_tendsto_of_tendsto_of_isUnit hKinf hconv

/-- Eventually the Hilbert-space boundary map is injective. For any relative
tolerance \(a\in(0,1)\), one may choose an injectivity proof so that its
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
  have hInj : Function.Injective (groundSpaceMapES A n) :=
    groundSpaceMapES_injective_of_isUnit_groundSpaceGram hn.1
  refine ⟨hInj, ?_, ?_⟩
  · simpa only [groundSpaceGram] using
      ContinuousLinearMap.inverseGram_eq_ringInverse (groundSpaceMapES A n) hInj
  · rw [ContinuousLinearMap.inverseGram_eq_ringInverse]
    simpa only [groundSpaceGram] using hn.2

end MPSTensor
