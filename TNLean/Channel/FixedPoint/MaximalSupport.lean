/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.FixedPoint.MaximalSupportBasic
import TNLean.Channel.FixedPoint.WeightedCornerFixedPoints
import TNLean.Channel.KrausMap

/-!
# Maximal-support fixed points for Kraus maps

This file specializes the positive-map maximal-support theorem from
`TNLean.Channel.FixedPoint.MaximalSupportBasic` to trace-preserving Kraus maps
and relates the resulting fixed point to the weighted corner algebra.

## Main results

* `Kraus.exists_maximalSupport_fixedPoint` -- a positive semidefinite fixed
  point whose support carries every fixed point of a trace-preserving Kraus map.
* `Kraus.exists_maximalSupport_weightedCorner_sqrt_eq` -- conjugation by the
  square root identifies the weighted corner carrier with the full fixed-point set.

## References

* M. Wolf, *Quantum Channels & Operations: Guided Tour*, Proposition 6.9 and
  Corollary 6.7.
-/

open scoped Matrix Matrix.Norms.Frobenius ComplexOrder MatrixOrder BigOperators
open Matrix Finset Complex

namespace Kraus

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- **A fixed point of maximal support for a Kraus map.** The mean-ergodic image
of the identity is a positive semidefinite fixed point whose support carries every fixed
point of the trace-preserving Kraus map. This is the completely positive specialization
of Wolf, Proposition 6.9, formalized for arbitrary positive trace-preserving maps by
`IsPositiveMap.exists_maximalSupport_fixedPoint`. -/
theorem exists_maximalSupport_fixedPoint (K : Fin d → Mat) (h_tp : IsTP K) :
    ∃ (ρ₀ : Mat) (hρ₀ : ρ₀.PosSemidef), map K ρ₀ = ρ₀ ∧
      ∀ X : Mat, map K X = X → stationaryProj hρ₀ * X * stationaryProj hρ₀ = X := by
  let E : Mat →ₗ[ℂ] Mat := mapLM K
  have hE : IsChannel E := isChannel_mapLM K h_tp
  let hbounded := hE.cp.isPositiveMap.hasBoundedOrbits_of_tracePreserving hE.tp
  let ρ₀ : Mat := LinearMap.meanErgodicProjection (𝕜 := ℂ) (E := Mat)
    E hbounded 1
  have hgeneric : ∃ hρ₀ : ρ₀.PosSemidef, E ρ₀ = ρ₀ ∧
      ∀ X : Mat, E X = X → stationaryProj hρ₀ * X * stationaryProj hρ₀ = X := by
    simpa only [ρ₀, hbounded] using
      hE.cp.isPositiveMap.exists_maximalSupport_fixedPoint hE.tp
  obtain ⟨hρ₀, hfix, hmax⟩ := hgeneric
  refine ⟨ρ₀, hρ₀, ?_, ?_⟩
  · simpa [E] using hfix
  · intro X hX
    apply hmax X
    simpa [E] using hX

/-- **Conjugation by the square root at a fixed point of maximal support.** For a
trace-preserving Kraus map $T$ there is a positive semidefinite fixed point $\rho_0$ such
that every fixed point $X$ of $T$ arises as $X = \sqrt{\rho_0}\, Y \sqrt{\rho_0}$ for a
corner-supported $Y$ with $\sqrt{\rho_0}\, Y \sqrt{\rho_0}$ fixed by $T$: conjugation by
$\sqrt{\rho_0}$ maps the carrier of the weighted corner star-subalgebra
(`Kraus.weightedCornerFixedPointsStarSubalgebra`) onto the full fixed-point set, so that
set realizes, with the inverse square root taken on the support of $\rho_0$,
$$\rho_0^{-1/2}\,\{X \mid T(X) = X\}\,\rho_0^{-1/2}.$$ This is the conjugated
fixed-point set of Corollary 6.7 of *Quantum Channels & Operations* (Wolf 2012), at a
fixed point of maximal support. -/
theorem exists_maximalSupport_weightedCorner_sqrt_eq (K : Fin d → Mat) (h_tp : IsTP K) :
    ∃ (ρ₀ : Mat) (hρ₀ : ρ₀.PosSemidef), map K ρ₀ = ρ₀ ∧
      ∀ X : Mat, map K X = X →
        ∃ Y : Mat, stationaryProj hρ₀ * Y * stationaryProj hρ₀ = Y ∧
          map K (CFC.sqrt ρ₀ * Y * CFC.sqrt ρ₀) = CFC.sqrt ρ₀ * Y * CFC.sqrt ρ₀ ∧
          CFC.sqrt ρ₀ * Y * CFC.sqrt ρ₀ = X := by
  obtain ⟨ρ₀, hρ₀, hfix, hmax⟩ := exists_maximalSupport_fixedPoint K h_tp
  exact ⟨ρ₀, hρ₀, hfix, fun X hX =>
    exists_weightedCorner_sqrt_eq_of_fixedPoint K h_tp hρ₀ hfix hX (hmax X hX)⟩

end Kraus
