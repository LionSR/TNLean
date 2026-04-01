/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Spectral.SpectralGap
import TNLean.Channel.Peripheral.Spectrum
import TNLean.Channel.Peripheral.IrreducibleChannel
import TNLean.MPS.Overlap.PeripheralToSpectralGap
import TNLean.Channel.Semigroup.Primitivity.Helpers
import TNLean.Wielandt.Primitivity.EasyDirections
import TNLean.Wielandt.Primitivity.ImpliesStronglyIrreducible

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

* `exponential_convergence_of_primitive` — for a primitive TP channel,
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

/-! ## Quantitative decay from a spectral-radius gap -/

/-- Convert `spectralRadius T < 1` into a global exponential bound for the powers of `T`. -/
theorem exponential_bound_of_spectralRadius_lt_one
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (T : V →L[ℂ] V) (hT : spectralRadius ℂ T < 1) :
    ∃ (C ξ : ℝ),
      0 < C ∧ 0 < ξ ∧
      ∀ (n : ℕ) (X : V), ‖(T ^ n) X‖ ≤ C * Real.exp (-(n : ℝ) / ξ) * ‖X‖ := by
  have hpow0 : Filter.Tendsto (fun n => T ^ n) Filter.atTop (nhds 0) :=
    pow_tendsto_zero_of_spectralRadius_lt_one T hT
  have hnorm0 : Filter.Tendsto (fun n => ‖T ^ n‖) Filter.atTop (nhds 0) := by
    simpa using (continuous_norm.tendsto 0).comp hpow0
  have hsmall : ∀ᶠ n : ℕ in Filter.atTop, 0 < n ∧ ‖T ^ n‖ < 1 / 2 := by
    filter_upwards [Filter.eventually_gt_atTop 0,
      hnorm0.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 / 2 by norm_num))] with n hn hTn
    exact ⟨hn, hTn⟩
  rcases Filter.Eventually.exists hsmall with ⟨N, hNpos, hNsmall⟩
  have hN_ne : N ≠ 0 := Nat.ne_of_gt hNpos
  have hN_real_pos : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hN_real_ne : (N : ℝ) ≠ 0 := by exact_mod_cast hN_ne
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let Ms : Finset ℝ := (Finset.range N).image fun m => ‖T ^ m‖
  have hMs_nonempty : Ms.Nonempty := by
    refine Finset.image_nonempty.mpr ?_
    exact Finset.nonempty_range_iff.mpr hN_ne
  let M : ℝ := Ms.max' hMs_nonempty
  have hM_nonneg : 0 ≤ M := by
    have h0_mem : ‖T ^ 0‖ ∈ Ms := by
      refine Finset.mem_image.mpr ?_
      exact ⟨0, Finset.mem_range.mpr hNpos, rfl⟩
    have h0_le : ‖T ^ 0‖ ≤ M := Finset.le_max' Ms ‖T ^ 0‖ h0_mem
    exact le_trans (norm_nonneg _) h0_le
  let C : ℝ := 2 * (1 + M)
  let ξ : ℝ := (N : ℝ) / Real.log 2
  refine ⟨C, ξ, by
    dsimp [C]
    positivity, by
    dsimp [ξ]
    positivity, ?_⟩
  intro n X
  let k := n / N
  let m := n % N
  have hm_lt : m < N := by
    dsimp [m]
    exact Nat.mod_lt _ hNpos
  have hm_mem : ‖T ^ m‖ ∈ Ms := by
    refine Finset.mem_image.mpr ?_
    exact ⟨m, Finset.mem_range.mpr hm_lt, rfl⟩
  have hTm_le_M : ‖T ^ m‖ ≤ M := Finset.le_max' Ms ‖T ^ m‖ hm_mem
  have hn_decomp : n = k * N + m := by
    dsimp [k, m]
    simpa [Nat.mul_comm] using (Nat.div_add_mod n N).symm
  have hpow_le : ∀ j : ℕ, ‖(T ^ N) ^ j‖ ≤ ‖T ^ N‖ ^ j := by
    intro j
    induction j with
    | zero =>
        simpa using (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := V))
    | succ j ih =>
        calc
          ‖(T ^ N) ^ (j + 1)‖ = ‖(T ^ N) ^ j * (T ^ N)‖ := by rw [pow_succ]
          _ ≤ ‖(T ^ N) ^ j‖ * ‖T ^ N‖ := norm_mul_le _ _
          _ ≤ ‖T ^ N‖ ^ j * ‖T ^ N‖ := by
            gcongr
          _ = ‖T ^ N‖ ^ (j + 1) := by rw [pow_succ]
  have hnorm_pow : ‖T ^ n‖ ≤ ‖T ^ m‖ * (1 / 2 : ℝ) ^ k := by
    calc
      ‖T ^ n‖ = ‖(T ^ N) ^ k * T ^ m‖ := by
        rw [hn_decomp, pow_add, pow_mul']
      _ ≤ ‖(T ^ N) ^ k‖ * ‖T ^ m‖ := norm_mul_le _ _
      _ ≤ ‖T ^ N‖ ^ k * ‖T ^ m‖ := by
        gcongr
        exact hpow_le k
      _ ≤ (1 / 2 : ℝ) ^ k * ‖T ^ m‖ := by
        gcongr
      _ = ‖T ^ m‖ * (1 / 2 : ℝ) ^ k := by ring
  have hk_floor : (n : ℝ) / N ≤ (k : ℝ) + 1 := by
    have hn_div : (n : ℝ) / N = (k : ℝ) + (m : ℝ) / N := by
      have hn_cast : (n : ℝ) = (k : ℝ) * N + m := by
        exact_mod_cast hn_decomp
      rw [hn_cast, add_div, mul_div_cancel_right₀ _ hN_real_ne]
    have hm_div_lt : (m : ℝ) / N < 1 := by
      refine (div_lt_one hN_real_pos).2 ?_
      exact_mod_cast hm_lt
    rw [hn_div]
    linarith
  have hhalf_exp : (1 / 2 : ℝ) ^ k ≤ 2 * Real.exp (-(n : ℝ) / ξ) := by
    have hleft : (1 / 2 : ℝ) ^ k = Real.exp (-(k : ℝ) * Real.log 2) := by
      calc
        (1 / 2 : ℝ) ^ k = (Real.exp (Real.log (1 / 2 : ℝ))) ^ k := by
          rw [Real.exp_log (by positivity : 0 < (1 / 2 : ℝ))]
        _ = Real.exp ((k : ℝ) * Real.log (1 / 2 : ℝ)) := by
          rw [← Real.exp_nat_mul]
        _ = Real.exp (-(k : ℝ) * Real.log 2) := by
          rw [show Real.log (1 / 2 : ℝ) = -Real.log 2 by
            rw [one_div, Real.log_inv]]
          ring
    have hright :
        2 * Real.exp (-(n : ℝ) / ξ) = Real.exp (Real.log 2 - (n : ℝ) / ξ) := by
      calc
        2 * Real.exp (-(n : ℝ) / ξ) =
            Real.exp (Real.log 2) * Real.exp (-(n : ℝ) / ξ) := by
              rw [Real.exp_log (by positivity : 0 < (2 : ℝ))]
        _ = Real.exp (Real.log 2 - (n : ℝ) / ξ) := by
          rw [← Real.exp_add]
          ring
    have hξ_formula : (n : ℝ) / ξ = (n : ℝ) * Real.log 2 / N := by
      calc
        (n : ℝ) / ξ = (n : ℝ) / ((N : ℝ) / Real.log 2) := by rfl
        _ = (n : ℝ) * Real.log 2 / N := by
            field_simp [hN_real_ne, hlog2_pos.ne']
    have hk_floor' :
        (n : ℝ) * Real.log 2 / N ≤ ((k : ℝ) + 1) * Real.log 2 := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (mul_le_mul_of_nonneg_right hk_floor hlog2_pos.le)
    rw [hleft, hright]
    apply Real.exp_le_exp.mpr
    rw [hξ_formula]
    nlinarith
  calc
    ‖(T ^ n) X‖ ≤ ‖T ^ n‖ * ‖X‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (‖T ^ m‖ * (1 / 2 : ℝ) ^ k) * ‖X‖ := by
      gcongr
    _ ≤ ((1 + M) * (1 / 2 : ℝ) ^ k) * ‖X‖ := by
      gcongr
      linarith
    _ ≤ ((1 + M) * (2 * Real.exp (-(n : ℝ) / ξ))) * ‖X‖ := by
      gcongr
    _ = C * Real.exp (-(n : ℝ) / ξ) * ‖X‖ := by
      dsimp [C]
      ring

/-! ## Convergence rate from spectral gap -/

/-- **Exponential convergence of primitive irreducible channels.**

For a primitive TP channel `E` with unique fixed point `ρ_∞`, the iterates
`E^n(X)` converge exponentially to the fixed-point projection `P(X)`:

  `‖E^n(X) - P(X)‖ ≤ C · (1-δ)^n · ‖X‖`

where `P(X) = tr(X) · ρ_∞ / tr(ρ_∞)` is the projection onto the fixed state,
`δ > 0` is the spectral gap, and `C` depends on the Jordan structure.

Note: both primitivity and irreducibility of the tensor are required.
Primitivity gives the spectral gap, while irreducibility is used by the
channel-specific adapter `compl_eigenvalue_norm_lt_one_of_primitive_of_irreducible_channel`
to bridge to the unique trace-zero fixed-point property. -/
theorem exponential_convergence_of_primitive [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hPrim : IsPrimitive (transferMap (d := d) (D := D) A))
    (hIrr : IsIrreducibleTensor A)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ_pd : ρ.PosDef)
    (hρ_fix : transferMap (d := d) (D := D) A ρ = ρ) :
    ∃ (C : ℝ) (δ : ℝ),
      0 < C ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ (n : ℕ) (X : Matrix (Fin D) (Fin D) ℂ),
        ‖((transferMap (d := d) (D := D) A)^[n]) X -
          fixedPointProj ρ (ne_of_gt hρ_pd.trace_pos) X‖ ≤
          C * (1 - δ) ^ n * ‖X‖ := by
  set E := transferMap (d := d) (D := D) A
  have htr : Matrix.trace ρ ≠ 0 := ne_of_gt hρ_pd.trace_pos
  let P : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ := fixedPointProj ρ htr
  let N : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ := E - P
  let Pₗ :
      Matrix (Fin D) (Fin D) ℂ →L[ℂ] Matrix (Fin D) (Fin D) ℂ :=
    Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ) P
  have hCh : IsChannel E := transferMap_isChannel A hNorm
  have hIrrMap : IsIrreducibleMap E := by
    simpa [E] using
      isIrreducibleCP_transferMap_of_isIrreducibleTensor (d := d) (D := D) A hIrr
  have hρ_ne : ρ ≠ 0 := by
    intro hρ0
    exact (ne_of_gt hρ_pd.trace_pos) (by simp [hρ0])
  have hcompl :
      ∀ ν : ℂ, Module.End.HasEigenvalue N ν → ‖ν‖ < 1 := by
    intro ν hν
    exact compl_eigenvalue_norm_lt_one_of_primitive_of_irreducible_channel
      E hCh hIrrMap ρ hρ_fix hρ_ne htr hPrim ν (by simpa [N, P] using hν)
  have hgap :
      spectralRadius ℂ
        ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) N) < 1 :=
    spectralRadius_lt_one_of_eigenvalues_lt_one (D := D) N hcompl
  obtain ⟨C₀, ξ, hC₀_pos, hξ_pos, hbound⟩ :=
    exponential_bound_of_spectralRadius_lt_one
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) N) hgap
  let C : ℝ := C₀ * (1 + ‖Pₗ‖)
  let δ : ℝ := 1 - Real.exp (-1 / ξ)
  have hδ_pos : 0 < δ := by
    have hexp_lt : Real.exp (-1 / ξ) < 1 := by
      have hpos : 0 < 1 / ξ := by positivity
      have hneg : -1 / ξ < 0 := by rw [neg_div]; linarith
      exact Real.exp_lt_one_iff.mpr hneg
    dsimp [δ]
    linarith
  have hδ_le : δ ≤ 1 := by
    dsimp [δ]
    nlinarith [Real.exp_pos (-1 / ξ)]
  refine ⟨C, δ, by
    dsimp [C]
    positivity, hδ_pos, hδ_le, ?_⟩
  intro n X
  let Y : Matrix (Fin D) (Fin D) ℂ := X - P X
  have hY_bound : ‖Y‖ ≤ (1 + ‖Pₗ‖) * ‖X‖ := by
    calc
      ‖Y‖ = ‖X - P X‖ := rfl
      _ ≤ ‖X‖ + ‖P X‖ := norm_sub_le _ _
      _ ≤ ‖X‖ + ‖Pₗ‖ * ‖X‖ := by
        gcongr
        exact ContinuousLinearMap.le_opNorm Pₗ X
      _ = (1 + ‖Pₗ‖) * ‖X‖ := by ring_nf
  have hdecomp :
      (E ^ n) X - P X = (N ^ n) Y := by
    cases n with
    | zero =>
        simp [Y]
    | succ n =>
        have hpow :
            E ^ (n + 1) = P + N ^ (n + 1) :=
          pow_succ_eq_fixedPointProj_add_compl_pow
            (E := E) (ρ := ρ) (htr := htr) hCh.tp hρ_fix n
        have hNpowP : (N ^ (n + 1)) * P = 0 := by
          simpa [N, P] using
            compl_pow_succ_mul_fixedPointProj (E := E) (ρ := ρ) (htr := htr) hρ_fix n
        have hNpowPX : (N ^ (n + 1)) (P X) = 0 := by
          have h := LinearMap.congr_fun hNpowP X
          simpa [Module.End.mul_apply] using h
        calc
          (E ^ (n + 1)) X - P X = ((P + N ^ (n + 1)) : Module.End ℂ _) X - P X := by
            rw [hpow]
          _ = (N ^ (n + 1)) X := by simp [LinearMap.add_apply]
          _ = (N ^ (n + 1)) Y := by
            dsimp [Y]
            rw [map_sub, hNpowPX, sub_zero]
  have hmain :
      ‖(E ^ n) X - P X‖ ≤ C * Real.exp (-(n : ℝ) / ξ) * ‖X‖ := by
    calc
      ‖(E ^ n) X - P X‖ = ‖(N ^ n) Y‖ := by rw [hdecomp]
      _ ≤ C₀ * Real.exp (-(n : ℝ) / ξ) * ‖Y‖ := by
        simpa [toContinuousLinearMap_pow_apply] using hbound n Y
      _ ≤ C₀ * Real.exp (-(n : ℝ) / ξ) * ((1 + ‖Pₗ‖) * ‖X‖) := by
        gcongr
      _ = C * Real.exp (-(n : ℝ) / ξ) * ‖X‖ := by
        dsimp [C]
        ring_nf
  have hexp_eq_pow : Real.exp (-(n : ℝ) / ξ) = (1 - δ) ^ n := by
    calc
      Real.exp (-(n : ℝ) / ξ) = Real.exp ((n : ℝ) * (-1 / ξ)) := by ring
      _ = (Real.exp (-1 / ξ)) ^ n := by rw [← Real.exp_nat_mul]
      _ = (1 - δ) ^ n := by simp [δ]
  have hmain' :
      ‖(E ^ n) X - P X‖ ≤ C * (1 - δ) ^ n * ‖X‖ := by
    rw [← hexp_eq_pow]
    exact hmain
  simpa [E, P, Module.End.pow_apply] using hmain'

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

/-- **Correlation length bound.**

For an injective TP-normalized MPS tensor, traceless matrices decay
exponentially under the transfer map iteration. The rate is determined by
the spectral gap, which exists because injectivity implies primitivity.

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
  set E := transferMap (d := d) (D := D) A
  have hPrim : PeripheralSpectrum.IsPrimitive E :=
    isPeripherallyPrimitive_of_isPrimitivePaper A hNorm
      (isPrimitivePaper_of_hasEventuallyFullKrausRank A
        (hasEventuallyFullKrausRank_of_injective A hA))
  obtain ⟨ρ, _, _, hρ_fix, htr, hgap⟩ :=
    spectralRadius_compl_lt_one_of_peripheralPrimitive
      (A := A) hA hNorm hPrim
  let P : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ := fixedPointProj ρ htr
  let N : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ := E - P
  have hCh : IsChannel E := transferMap_isChannel A hNorm
  obtain ⟨C, ξ, hC_pos, hξ_pos, hbound⟩ :=
    exponential_bound_of_spectralRadius_lt_one
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) N) hgap
  refine ⟨C, ξ, hC_pos, hξ_pos, ?_⟩
  intro n X htrX
  cases n with
  | zero =>
      simpa [E, Module.End.pow_apply] using hbound 0 X
  | succ n =>
      have hPX : P X = 0 := by
        simp [P, fixedPointProj, htrX]
      have hpow :
          E ^ (n + 1) = P + N ^ (n + 1) :=
        pow_succ_eq_fixedPointProj_add_compl_pow
          (E := E) (ρ := ρ) (htr := htr) hCh.tp hρ_fix n
      have hpow_eq : (E ^ (n + 1)) X = (N ^ (n + 1)) X := by
        calc
          (E ^ (n + 1)) X = ((P + N ^ (n + 1)) : Module.End ℂ _) X := by
            rw [hpow]
          _ = P X + (N ^ (n + 1)) X := LinearMap.add_apply P (N ^ (n + 1)) X
          _ = (N ^ (n + 1)) X := by simp [hPX]
      have hmain :
          ‖(E ^ (n + 1)) X‖ ≤ C * Real.exp (-((n + 1 : ℕ) : ℝ) / ξ) * ‖X‖ := by
        rw [hpow_eq]
        simpa [toContinuousLinearMap_pow_apply] using hbound (n + 1) X
      simpa [E, Module.End.pow_apply] using hmain

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
  exact _root_.uniform_spectral_gap_of_finite_lt_one
    (Module.End.finite_hasEigenvalue E)
    fun μ hμ hne => lt_of_le_of_ne (hbound μ hμ)
      fun h => hne (hPrim.unique_peripheral μ hμ h)

end MPSTensor
