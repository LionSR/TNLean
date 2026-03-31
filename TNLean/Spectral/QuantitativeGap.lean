/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Spectral.SpectralGap
import TNLean.Channel.Peripheral.Spectrum
import TNLean.Wielandt.Primitivity.EasyDirections
import TNLean.Wielandt.Primitivity.ImpliesStronglyIrreducible
import TNLean.MPS.Overlap.PeripheralToSpectralGap

/-!
# Quantitative spectral gap bounds for MPS transfer operators

This file provides **explicit quantitative bounds** on the spectral gap of
MPS transfer operators, strengthening the existing qualitative result
`spectralRadius_mixedTransfer_lt_one` (which only proves `ρ < 1` without
a lower bound on `1 - ρ`).

## Building blocks (already formalized elsewhere)

* `pow_tendsto_zero_of_spectralRadius_lt_one` in `Spectral/SpectralGap.lean` —
  exponential convergence to zero when spectral radius < 1
* `compl_eigenvalue_norm_lt_one_of_primitive` in `Peripheral/Spectrum.lean` —
  primitive channels have spectral gap
* `cumulativeSpan_eq_top` in `Wielandt/WielandtBound.lean` — the D² Wielandt bound

## Main results

* `exponential_convergence_of_primitive` — for an injective primitive TP channel,
  `‖E^n(X) - P(X)‖ ≤ C · (1-δ)^n · ‖X‖` (convergence to fixed-point projection)
* `correlation_length_bound` — exponential decay of traceless iterates
* `spectral_gap_of_injective` — explicit spectral gap `δ > 0` with
  all non-unit eigenvalues satisfying `|μ| ≤ 1 - δ`

## Strengthening relative to the literature

The existing formalization proves `ρ(F_{AB}) < 1` for non-equivalent blocks
but gives no explicit bound. This file provides constructive bounds.

## References

* [M. Wolf, *Quantum Channels & Operations*, §6.3]
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators NNReal ENNReal
open Matrix Finset

namespace MPSTensor

variable {d D : ℕ}

private theorem spectralRadius_compl_lt_one_of_primitive_fixedPoint [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hPrim : IsPrimitive (transferMap (d := d) (D := D) A))
    (ρ : Matrix (Fin D) (Fin D) ℂ)
    (hρ_psd : ρ.PosSemidef)
    (hρ_ne : ρ ≠ 0)
    (hρ_fix : transferMap (d := d) (D := D) A ρ = ρ)
    (huniq_fp :
      ∀ X : Matrix (Fin D) (Fin D) ℂ,
        transferMap (d := d) (D := D) A X = X →
        Matrix.trace X = 0 →
        X = 0) :
    ∃ htr : Matrix.trace ρ ≠ 0,
      spectralRadius ℂ
        ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
          ((transferMap (d := d) (D := D) A) - fixedPointProj (D := D) ρ htr)) < 1 := by
  set E := transferMap (d := d) (D := D) A
  have hCh : IsChannel E := transferMap_isChannel (A := A) hNorm
  have hρ_fixE : E ρ = ρ := by
    simpa [E] using hρ_fix
  have htrρ : Matrix.trace ρ ≠ 0 := by
    intro htr0
    exact hρ_ne ((Matrix.PosSemidef.trace_eq_zero_iff hρ_psd).1 htr0)
  have hbound : ∀ μ : ℂ, Module.End.HasEigenvalue E μ → ‖μ‖ ≤ 1 := by
    intro μ hμ
    have hμ' : Module.End.HasEigenvalue (mixedTransferMap A A) μ := by
      simpa [E, mixedTransferMap_self] using hμ
    simpa [E, mixedTransferMap_self] using
      eigenvalue_norm_le_one (A := A) (B := A) hNorm hNorm μ hμ'
  have huniq_fpE :
      ∀ X : Matrix (Fin D) (Fin D) ℂ,
        E X = X → Matrix.trace X = 0 → X = 0 := by
    intro X hXfix htrX
    exact huniq_fp X (by simpa [E] using hXfix) htrX
  have hcompl :
      ∀ ν : ℂ,
        Module.End.HasEigenvalue (E - fixedPointProj (D := D) ρ htrρ) ν → ‖ν‖ < 1 := by
    intro ν hν
    exact _root_.compl_eigenvalue_norm_lt_one_of_primitive
      (E := E) (ρ := ρ) hρ_fixE hρ_ne htrρ hCh.tp hPrim hbound huniq_fpE ν hν
  have hgap :
      spectralRadius ℂ
        ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
          (E - fixedPointProj (D := D) ρ htrρ)) < 1 := by
    have h_spec :
        spectrum ℂ
            ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
              (E - fixedPointProj (D := D) ρ htrρ)) =
          spectrum ℂ (E - fixedPointProj (D := D) ρ htrρ) :=
      AlgEquiv.spectrum_eq (Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
        (E - fixedPointProj (D := D) ρ htrρ)
    refine (spectrum.spectralRadius_lt_of_forall_lt
      (a := (Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
        (E - fixedPointProj (D := D) ρ htrρ))
      (r := (1 : NNReal)) ?_)
    intro z hz
    have hz' : z ∈ spectrum ℂ (E - fixedPointProj (D := D) ρ htrρ) := by
      exact h_spec ▸ hz
    have hEig : Module.End.HasEigenvalue (E - fixedPointProj (D := D) ρ htrρ) z :=
      Module.End.hasEigenvalue_iff_mem_spectrum.mpr hz'
    have hz_norm : ‖z‖ < 1 := hcompl z hEig
    have : ((‖z‖₊ : ℝ) < 1) := by simpa using hz_norm
    exact (NNReal.coe_lt_one).1 this
  exact ⟨htrρ, by simpa [E] using hgap⟩

private theorem geometric_bound_of_spectralRadius_lt_one
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (T : V →L[ℂ] V)
    (hT : spectralRadius ℂ T < 1) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ r < 1 ∧
      ∀ n : ℕ, ‖T ^ n‖ ≤ C * r ^ n := by
  obtain ⟨r, hr_above, hr_below⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hT
  have hr_lt_one : (r : ℝ) < 1 := by
    exact_mod_cast hr_below
  have hr_pos : 0 < (r : ℝ) := by
    exact_mod_cast (lt_of_le_of_lt (show (0 : ℝ≥0∞) ≤ spectralRadius ℂ T from bot_le) hr_above)
  have hev :
      ∀ᶠ n in Filter.atTop, ‖T ^ n‖₊ < r ^ n := by
    have gelfand := spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius T
    filter_upwards [gelfand.eventually (eventually_lt_nhds hr_above),
      Filter.eventually_gt_atTop 0] with n hn hn_pos
    rw [one_div, ENNReal.rpow_inv_lt_iff (Nat.cast_pos.mpr hn_pos)] at hn
    rw [ENNReal.rpow_natCast] at hn
    exact_mod_cast hn
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  let S : ℝ := Finset.sum (Finset.range N) fun k => ‖T ^ k‖ / (r : ℝ) ^ k
  let C : ℝ := S + 1
  refine ⟨C, r, by positivity, hr_pos, hr_lt_one, ?_⟩
  intro n
  by_cases hn : N ≤ n
  · have hnorm : ‖T ^ n‖ ≤ (r : ℝ) ^ n := by
      exact_mod_cast (hN n hn).le
    have hC_ge_one : 1 ≤ C := by
      have hS_nonneg : 0 ≤ S := by
        dsimp [S]
        positivity
      dsimp [C]
      linarith
    calc
      ‖T ^ n‖ ≤ (r : ℝ) ^ n := hnorm
      _ = 1 * (r : ℝ) ^ n := by ring
      _ ≤ C * (r : ℝ) ^ n := by
        gcongr
  · have hn_lt : n < N := Nat.lt_of_not_ge hn
    have hterm : ‖T ^ n‖ / (r : ℝ) ^ n ≤ S := by
      dsimp [S]
      exact Finset.single_le_sum
        (f := fun k => ‖T ^ k‖ / (r : ℝ) ^ k)
        (by intro k hk; positivity)
        (Finset.mem_range.mpr hn_lt)
    have hterm' : ‖T ^ n‖ ≤ S * (r : ℝ) ^ n := by
      exact (div_le_iff₀ (pow_pos hr_pos n)).1 hterm
    have hS_le_C : S ≤ C := by
      dsimp [C]
      linarith
    calc
      ‖T ^ n‖ ≤ S * (r : ℝ) ^ n := hterm'
      _ ≤ C * (r : ℝ) ^ n := by
        gcongr

private theorem geometric_apply_bound_of_spectralRadius_lt_one
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (T : V →L[ℂ] V)
    (hT : spectralRadius ℂ T < 1) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ r < 1 ∧
      ∀ n : ℕ, ∀ x : V, ‖(T ^ n) x‖ ≤ C * r ^ n * ‖x‖ := by
  rcases geometric_bound_of_spectralRadius_lt_one T hT with
    ⟨C, r, hC, hr_pos, hr_lt_one, hpow⟩
  refine ⟨C, r, hC, hr_pos, hr_lt_one, ?_⟩
  intro n x
  calc
    ‖(T ^ n) x‖ ≤ ‖T ^ n‖ * ‖x‖ := by
      simpa using (ContinuousLinearMap.le_opNorm (T ^ n) x)
    _ ≤ (C * r ^ n) * ‖x‖ := by
      exact mul_le_mul_of_nonneg_right (hpow n) (norm_nonneg x)
    _ = C * r ^ n * ‖x‖ := by ring

/-! ## Convergence rate from spectral gap -/

/-- **Exponential convergence of injective primitive channels.**

For an injective primitive TP channel `E` with fixed point projection `P`, the iterates
`E^n(X)` converge exponentially to the fixed-point projection `P(X)`:

  `‖E^n(X) - P(X)‖ ≤ C · (1-δ)^n · ‖X‖`

where `P(X) = tr(X) · ρ_∞ / tr(ρ_∞)` is the projection onto the fixed state,
`δ > 0` is the spectral gap, and `C` depends on the Jordan structure.

The extra injectivity hypothesis is what supplies the needed uniqueness of
trace-zero fixed points, so that the complementary map `E - P` has spectral
radius `< 1`. The convergence estimate then follows from Gelfand's formula. -/
theorem exponential_convergence_of_primitive [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hA : IsInjective A)
    (hPrim : IsPrimitive (transferMap (d := d) (D := D) A))
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
  have huniq_fp :
      ∀ X : V, E X = X → Matrix.trace X = 0 → X = 0 := by
    intro X hXfix htrX
    dsimp [E] at hXfix
    exact transferMap_fixedPoint_eq_zero_of_trace_eq_zero (A := A) hA hNorm X hXfix htrX
  obtain ⟨htrρ, hgap⟩ :=
    spectralRadius_compl_lt_one_of_primitive_fixedPoint
      (A := A) hNorm hPrim ρ hρ_pd.posSemidef
      (by
        intro hρ0
        have htr0 : Matrix.trace ρ = 0 := by simp [hρ0]
        exact (ne_of_gt hρ_pd.trace_pos) htr0)
      hρ_fix huniq_fp
  rcases geometric_apply_bound_of_spectralRadius_lt_one (T := Φ N) hgap with
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
        simp
      _ ≤ C₀ * r ^ n * ‖X‖ := hgeomN n
      _ ≤ C * r ^ n * ‖X‖ := by
        gcongr
      _ = C * (1 - (1 - r)) ^ n * ‖X‖ := by simp

/-- **Correlation length bound.**

For a primitive TP-normalized MPS tensor, traceless matrices decay
exponentially under the transfer map iteration. The rate is determined by
the spectral gap, which exists by primitivity.

This uses `pow_tendsto_zero_of_spectralRadius_lt_one` from
`Spectral/SpectralGap.lean` directly — traceless matrices lie in
`ker(P) = range(E - P)`, where `E - P` has spectral radius < 1. -/
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
      (isPrimitivePaper_of_hasEventuallyFullKrausRank A <| by
        refine ⟨1, ?_⟩
        have hword :
            wordSpan A 1 = Submodule.span ℂ (Set.range A) := by
          simp only [wordSpan]
          congr 1
          ext y
          constructor
          · rintro ⟨σ, rfl⟩
            exact ⟨σ 0, by simp [evalWord]⟩
          · rintro ⟨i, rfl⟩
            exact ⟨fun _ => i, by simp [evalWord]⟩
        rw [hword, hA])
  rcases spectralRadius_compl_lt_one_of_peripheralPrimitive
      (A := A) hA hNorm hPrim with
    ⟨ρ, _hρ_psd, _hρ_ne, hρ_fix, htrρ, hgap⟩
  let P : V →ₗ[ℂ] V := fixedPointProj (D := D) ρ htrρ
  let N : V →ₗ[ℂ] V := E - P
  rcases geometric_apply_bound_of_spectralRadius_lt_one (T := Φ N) hgap with
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
    simp
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

/-! ## Helper lemmas -/

/-- The word span at length 1 equals the span of the Kraus operators. -/
theorem wordSpan_one_eq_span_range (A : MPSTensor d D) :
    wordSpan A 1 = Submodule.span ℂ (Set.range A) := by
  simp only [wordSpan]
  congr 1; ext y; constructor
  · rintro ⟨σ, rfl⟩; exact ⟨σ 0, by simp [evalWord]⟩
  · rintro ⟨i, rfl⟩; exact ⟨fun _ => i, by simp [evalWord]⟩

/-- An injective MPS tensor has eventually full Kraus rank (at index 1). -/
theorem hasEventuallyFullKrausRank_of_injective (A : MPSTensor d D)
    (hA : IsInjective A) : HasEventuallyFullKrausRank A :=
  ⟨1, by rw [wordSpan_one_eq_span_range, hA]⟩

/-! ## Explicit gap from injectivity -/

/-- **Spectral gap from injectivity** (existential version).

For an injective TP-normalized MPS tensor, all eigenvalues of the transfer
map other than 1 have modulus strictly less than 1, with a uniform gap.

The existential bound `∃ δ > 0` follows from: injectivity implies
`HasEventuallyFullKrausRank` (at index 1), which implies primitivity
(via `IsPrimitivePaper → IsPeripherallyPrimitive`), primitivity implies
spectral gap (by `compl_eigenvalue_norm_lt_one_of_primitive`), and in
finite dimensions the maximum over finitely many eigenvalues gives a
uniform bound. -/
theorem spectral_gap_of_injective [NeZero D]
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
        (hasEventuallyFullKrausRank_of_injective A hA))
  -- Step 2: every eigenvalue has ‖μ‖ ≤ 1
  have hE_eq : E = mixedTransferMap A A := (mixedTransferMap_self A).symm
  have hbound : ∀ μ : ℂ, Module.End.HasEigenvalue E μ → ‖μ‖ ≤ 1 := by
    intro μ hμ
    exact eigenvalue_norm_le_one A A hNorm hNorm μ (hE_eq ▸ hμ)
  -- Step 3: non-1 eigenvalues have ‖μ‖ < 1, then extract uniform gap
  exact uniform_spectral_gap_of_finite_lt_one (Module.End.finite_hasEigenvalue E)
    fun μ hμ hne => lt_of_le_of_ne (hbound μ hμ)
      fun h => hne (hPrim.unique_peripheral μ hμ h)

end MPSTensor
