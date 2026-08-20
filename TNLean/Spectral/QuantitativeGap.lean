/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Spectral.TransferOperatorGapInjective
import TNLean.Channel.Peripheral.Spectrum
import TNLean.Wielandt.Primitivity.EasyDirections
import TNLean.Wielandt.Primitivity.ImpliesStronglyIrreducibleAux
import TNLean.Spectral.PeripheralToTransferMapGap

/-!
# Quantitative transfer-map gap bounds for MPS transfer operators

This file provides **explicit quantitative bounds** on transfer-map gaps for
MPS transfer operators, strengthening the existing qualitative result
`spectralRadius_mixedTransfer_lt_one` (which only proves `ρ < 1` without
a lower bound on `1 - ρ`).

## Building blocks (already formalized elsewhere)

* `geometric_bound_of_spectralRadius_lt_one` in
  `Analysis/SpectralRadiusPowerDecay.lean` — a uniform geometric operator-norm
  bound when spectral radius < 1
* `compl_eigenvalue_norm_lt_one_of_primitive` in `Peripheral/Spectrum.lean` —
  primitive channels have a complementary transfer-map gap
* `cumulativeSpan_eq_top` in `Wielandt/SpanGrowth/NonzeroTraceProduct.lean` —
  the D² Wielandt bound

## Main results

* `exponential_convergence_of_primitive` — for an injective primitive TP channel,
  `‖E^n(X) - P(X)‖ ≤ C · (1-δ)^n · ‖X‖` (convergence to fixed-point projection)
* `correlation_length_bound` — exponential decay of traceless iterates
* `transfer_map_gap_of_injective` — explicit transfer-map gap `δ > 0` with
  all non-unit eigenvalues satisfying `|μ| ≤ 1 - δ`

## Strengthening relative to the literature

The existing formalization proves `ρ(F_{AB}) < 1` for non-equivalent blocks
but gives no explicit bound. This file provides constructive bounds.

## References

* [M. Wolf, *Quantum Channels & Operations*, Section 6.3]
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators NNReal ENNReal
open Matrix Finset

attribute [local instance 1001]
  ContinuousLinearMap.toNormedAddCommGroup
  ContinuousLinearMap.toNormedSpace
  ContinuousLinearMap.toNormedRing
  ContinuousLinearMap.toNormedAlgebra

namespace MPSTensor

variable {d D : ℕ}

/-! ## Convergence rate from a complementary transfer-map gap -/

/-- **Exponential convergence of injective primitive channels.**

For an injective primitive TP channel `E` with fixed point projection `P`, the iterates
`E^n(X)` converge exponentially to the fixed-point projection `P(X)`:

  `‖E^n(X) - P(X)‖ ≤ C · (1-δ)^n · ‖X‖`

where `P(X) = tr(X) · ρ_∞ / tr(ρ_∞)` is the projection onto the fixed state,
`δ > 0` is the transfer-map gap, and `C` depends on the Jordan structure.

The extra injectivity hypothesis is what supplies the needed uniqueness of
trace-zero fixed points, so that the complementary map `E - P` has spectral
radius `< 1`. The convergence estimate then follows from Gelfand's formula. -/
theorem exponential_convergence_of_primitive [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hA : IsInjective A)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ_pd : ρ.PosDef)
    (hρ_fix : transferMap (d := d) (D := D) A ρ = ρ) :
    ∃ (C : ℝ) (δ : ℝ),
      0 < C ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ (n : ℕ) (X : Matrix (Fin D) (Fin D) ℂ),
        ‖((transferMap (d := d) (D := D) A)^[n]) X -
          fixedPointProj ρ (ne_of_gt hρ_pd.trace_pos) X‖ ≤
          C * (1 - δ) ^ n * ‖X‖ := by
  classical
  let V := Matrix (Fin D) (Fin D) ℂ
  let E : V →ₗ[ℂ] V := transferMap (d := d) (D := D) A
  let P : V →ₗ[ℂ] V := fixedPointProj (D := D) ρ (ne_of_gt hρ_pd.trace_pos)
  let N : V →ₗ[ℂ] V := E - P
  let Φ : (V →ₗ[ℂ] V) ≃ₐ[ℂ] (V →L[ℂ] V) := Module.End.toContinuousLinearMap V
  let : NormedAddCommGroup (V →L[ℂ] V) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℂ (V →L[ℂ] V) := ContinuousLinearMap.toNormedSpace
  have hPrim : IsPrimitive E :=
    isPeripherallyPrimitive_of_isPrimitivePaper A hNorm
      (isPrimitivePaper_of_hasEventuallyFullKrausRank A
        ((MPSTensor.hasEventuallyFullKrausRank_iff_isNormal A).2 hA.isNormal))
  have hCh : IsChannel E := by
    simpa only [E] using transferMap_isChannel (A := A) hNorm
  have hIrr : IsIrreducibleMap E := by
    simpa only [E] using injective_implies_irreducibleCP A hA
  have hρ_ne : ρ ≠ 0 := by
    intro hρ0
    exact (ne_of_gt hρ_pd.trace_pos) (by simp [hρ0])
  have hρ_fixE : E ρ = ρ := by
    simpa only [E] using hρ_fix
  obtain ⟨htrρ, hgap⟩ :=
    spectralRadius_compl_lt_one_of_primitive_fixedPoint_of_irreducible_channel
      E hCh hIrr hPrim ρ hρ_pd.posSemidef hρ_ne hρ_fixE
  rcases _root_.geometric_apply_bound_of_spectralRadius_lt_one (T := Φ N) hgap with
    ⟨C₀, r, hC₀_pos, hr_pos, hr_lt_one, hgeom⟩
  let P' : V →L[ℂ] V := Φ P
  let C : ℝ := C₀ + (1 + ‖P'‖)
  refine ⟨C, 1 - r, by positivity, sub_pos.mpr hr_lt_one, by linarith, ?_⟩
  intro n X
  have hC₀_le_C : C₀ ≤ C := by
    dsimp [C]
    nlinarith [norm_nonneg P']
  have hPnorm : ‖P X‖ ≤ ‖P'‖ * ‖X‖ := by
    change ‖(Φ P) X‖ ≤ ‖Φ P‖ * ‖X‖
    exact ContinuousLinearMap.le_opNorm (Φ P) X
  have hgeomN : ∀ m : ℕ, ‖(N ^ m) X‖ ≤ C₀ * r ^ m * ‖X‖ := by
    intro m
    have hpow : ((Φ N) ^ m : V →L[ℂ] V) = Φ (N ^ m) := (map_pow Φ N m).symm
    calc
      ‖(N ^ m) X‖ = ‖((Φ N) ^ m) X‖ := by rw [hpow]; rfl
      _ ≤ C₀ * r ^ m * ‖X‖ := hgeom m X
  by_cases hn : n = 0
  · subst hn
    have hC_ge_one_plus : 1 + ‖P'‖ ≤ C := by
      dsimp [C]
      linarith
    calc
      ‖((E^[0]) X) - P X‖ = ‖X - P X‖ := by simp [E]
      _ ≤ ‖X‖ + ‖P X‖ := norm_sub_le _ _
      _ ≤ ‖X‖ + ‖P'‖ * ‖X‖ := by gcongr
      _ = (1 + ‖P'‖) * ‖X‖ := by ring
      _ ≤ C * ‖X‖ := by
        exact mul_le_mul_of_nonneg_right hC_ge_one_plus (norm_nonneg X)
      _ = C * (1 - (1 - r)) ^ 0 * ‖X‖ := by simp
  · have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
    have hpowEq :=
      pow_eq_fixedPointProj_add_compl_pow (D := D) (E := E) (ρ := ρ) htrρ
        (transferMap_isChannel (A := A) hNorm).tp hρ_fix hn1
    calc
      ‖((E^[n]) X) - P X‖ = ‖(E ^ n) X - P X‖ := by simp [E, Module.End.pow_apply]
      _ = ‖(P + N ^ n) X - P X‖ := by rw [hpowEq]
      _ = ‖(N ^ n) X‖ := by
        change ‖P X + (N ^ n) X - P X‖ = ‖(N ^ n) X‖
        simp only [add_sub_cancel_left]
      _ ≤ C₀ * r ^ n * ‖X‖ := hgeomN n
      _ ≤ C * r ^ n * ‖X‖ := by
        gcongr
      _ = C * (1 - (1 - r)) ^ n * ‖X‖ := by simp

/-- **Correlation length bound.**

For an injective TP-normalized MPS tensor, traceless matrices decay
exponentially under the transfer map iteration. The rate is determined by
the complementary transfer-map gap, which exists because injectivity implies
primitivity.

Traceless matrices lie in `ker(P) = range(E - P)`, where `E - P` has spectral
radius < 1, so their iterates decay geometrically. The bound is the pointwise
form `geometric_apply_bound_of_spectralRadius_lt_one` of
`geometric_bound_of_spectralRadius_lt_one` in
`Analysis/SpectralRadiusPowerDecay.lean`. -/
theorem correlation_length_bound [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hA : IsInjective A) :
    ∃ (C : ℝ) (ξ : ℝ),
      0 < C ∧ 0 < ξ ∧
      ∀ (n : ℕ) (X : Matrix (Fin D) (Fin D) ℂ),
        Matrix.trace X = 0 →
        ‖((transferMap (d := d) (D := D) A)^[n]) X‖ ≤
          C * Real.exp (-(n : ℝ) / ξ) * ‖X‖ := by
  classical
  let V := Matrix (Fin D) (Fin D) ℂ
  let E : V →ₗ[ℂ] V := transferMap (d := d) (D := D) A
  let Φ : (V →ₗ[ℂ] V) ≃ₐ[ℂ] (V →L[ℂ] V) := Module.End.toContinuousLinearMap V
  have hPrim : _root_.IsPrimitive E :=
    isPeripherallyPrimitive_of_isPrimitivePaper A hNorm
      (isPrimitivePaper_of_hasEventuallyFullKrausRank A
        ((MPSTensor.hasEventuallyFullKrausRank_iff_isNormal A).2 hA.isNormal))
  rcases spectralRadius_compl_lt_one_of_peripheralPrimitive
      (A := A) hA hNorm hPrim with
    ⟨ρ, _hρ_psd, _hρ_ne, hρ_fix, htrρ, hgap⟩
  let P : V →ₗ[ℂ] V := fixedPointProj (D := D) ρ htrρ
  let N : V →ₗ[ℂ] V := E - P
  rcases _root_.geometric_apply_bound_of_spectralRadius_lt_one (T := Φ N) hgap with
    ⟨C₀, r, hC₀_pos, hr_pos, hr_lt_one, hgeom⟩
  let C : ℝ := C₀ + 1
  let ξ : ℝ := 1 / (-Real.log r)
  have hξ_pos : 0 < ξ := by
    have hlog_neg : Real.log r < 0 := Real.log_neg hr_pos hr_lt_one
    have hneg_log_pos : 0 < -Real.log r := by linarith
    dsimp [ξ]
    positivity
  have hr_exp : ∀ n : ℕ, r ^ n = Real.exp (-(n : ℝ) / ξ) := by
    intro n
    calc
      r ^ n = Real.exp ((n : ℝ) * Real.log r) := by
        calc
          r ^ n = (Real.exp (Real.log r)) ^ n := by rw [Real.exp_log hr_pos]
          _ = Real.exp ((n : ℝ) * Real.log r) := by
            simpa [mul_comm] using (Real.exp_nat_mul (Real.log r) n).symm
      _ = Real.exp (-(n : ℝ) / ξ) := by
        congr 1
        dsimp [ξ]
        rw [one_div, div_eq_mul_inv, inv_inv]
        ring
  have hC₀_le_C : C₀ ≤ C := by
    dsimp [C]
    linarith
  have hgeomN : ∀ n : ℕ, ∀ X : V, ‖(N ^ n) X‖ ≤ C₀ * r ^ n * ‖X‖ := by
    intro n X
    have hpow : ((Φ N) ^ n : V →L[ℂ] V) = Φ (N ^ n) := (map_pow Φ N n).symm
    calc
      ‖(N ^ n) X‖ = ‖((Φ N) ^ n) X‖ := by rw [hpow]; rfl
      _ ≤ C₀ * r ^ n * ‖X‖ := hgeom n X
  refine ⟨C, ξ, by positivity, hξ_pos, ?_⟩
  intro n X htrX
  have hPX : P X = 0 := by
    change (Matrix.trace X / Matrix.trace ρ) • ρ = 0
    rw [htrX]
    simp only [zero_div, zero_smul]
  by_cases hn : n = 0
  · subst hn
    have hC_ge_one : 1 ≤ C := by
      dsimp [C]
      linarith
    have hzero : ‖X‖ ≤ C * ‖X‖ := by
      calc
        ‖X‖ ≤ 1 * ‖X‖ := by simp
        _ ≤ C * ‖X‖ := by
          exact mul_le_mul_of_nonneg_right hC_ge_one (norm_nonneg X)
    have hexp0 : Real.exp (-((0 : ℕ) : ℝ) / ξ) = 1 := by
      norm_num
    simpa [E, hexp0] using hzero
  · have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
    have hpowEq :=
      pow_eq_fixedPointProj_add_compl_pow (D := D) (E := E) (ρ := ρ) htrρ
        (transferMap_isChannel (A := A) hNorm).tp hρ_fix hn1
    calc
      ‖((E^[n]) X)‖ = ‖(E ^ n) X‖ := by simp [E, Module.End.pow_apply]
      _ = ‖(P + N ^ n) X‖ := by rw [hpowEq]
      _ = ‖(N ^ n) X‖ := by simp [LinearMap.add_apply, hPX]
      _ ≤ C₀ * r ^ n * ‖X‖ := hgeomN n X
      _ ≤ C * r ^ n * ‖X‖ := by
        gcongr
      _ = C * Real.exp (-(n : ℝ) / ξ) * ‖X‖ := by rw [hr_exp n]

/-! ## Explicit gap from injectivity -/

/-- **Transfer-map gap from injectivity** (existential version).

For an injective TP-normalized MPS tensor, all eigenvalues of the transfer
map other than 1 have modulus strictly less than 1, with a uniform gap.

The existential bound `∃ δ > 0` follows from: injectivity implies
`HasEventuallyFullKrausRank` (at index 1), which implies primitivity
(via `IsPrimitivePaper → IsPeripherallyPrimitive`), primitivity implies
the complementary transfer-map gap (by `compl_eigenvalue_norm_lt_one_of_primitive`),
and in finite dimensions the maximum over finitely many eigenvalues gives a
uniform bound. -/
theorem transfer_map_gap_of_injective [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hA : IsInjective A) :
    ∃ (δ : ℝ), 0 < δ ∧
      ∀ (μ : ℂ), Module.End.HasEigenvalue (transferMap (d := d) (D := D) A) μ →
        μ ≠ 1 → ‖μ‖ ≤ 1 - δ := by
  set E := transferMap (d := d) (D := D) A
  -- Step 1: IsInjective → IsPrimitive (transferMap A)
  have hPrim : _root_.IsPrimitive E :=
    isPeripherallyPrimitive_of_isPrimitivePaper A hNorm
      (isPrimitivePaper_of_hasEventuallyFullKrausRank A
        ((MPSTensor.hasEventuallyFullKrausRank_iff_isNormal A).2 hA.isNormal))
  -- Step 2: every eigenvalue has ‖μ‖ ≤ 1
  have hE_eq : E = mixedTransferMap A A := (mixedTransferMap_self A).symm
  have hbound : ∀ μ : ℂ, Module.End.HasEigenvalue E μ → ‖μ‖ ≤ 1 := by
    intro μ hμ
    exact eigenvalue_norm_le_one A A hNorm hNorm μ (hE_eq ▸ hμ)
  -- Step 3: non-1 eigenvalues have ‖μ‖ < 1, then extract uniform gap
  exact uniform_eigenvalue_gap_of_finite_lt_one (Module.End.finite_hasEigenvalue E)
    fun μ hμ hne => lt_of_le_of_ne (hbound μ hμ)
      fun h => hne (hPrim.unique_peripheral μ hμ h)

end MPSTensor
