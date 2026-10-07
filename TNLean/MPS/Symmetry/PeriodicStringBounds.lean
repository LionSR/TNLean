/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.PeriodicFullRingString

/-!
# Quantitative periodic normalization and fixed-support expectations

Canonical spectral purity provides one geometric rate for the normalization
of the periodic vector and for its fixed-support expectations. The prefactor
may depend on the fixed observable. On an eventual tail the periodic vector
is nonzero and its squared norm is bounded away from zero.

These are finite-size estimates for the thermodynamic interpretation of
arXiv:0802.0447, `MPS` and `SOPMP`, lines 137–181. They do not exchange the
ambient-ring limit with a growing-support string limit.
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder TNOperatorSpace InnerProductSpace
  NNReal ENNReal
open Filter

namespace MPSTensor

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- One canonical rate bounds both periodic normalization and every fixed-block
expectation. The common tail has nonzero vectors and denominator at least
`1/2` in norm; only the expectation prefactor depends on the block observable.
Source: arXiv:0802.0447, `MPS`, `SOPMP`, and the exponential convergence at
lines 241–255. No simultaneous support-length limit is asserted. -/
theorem pureCanonical_periodic_expectations_le_geometric
    [NeZero D] (A : MPSTensor d D)
    (Λ : Mat) (hΛpos : Λ.PosDef) (hΛtr : Matrix.trace Λ = 1)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (hNorm : Kraus.transferMap A 1 = 1)
    (hPure : ∀ (ev : ℂ) (X : Mat),
      X ≠ 0 → ‖ev‖ = 1 → Kraus.transferMap A X = ev • X →
      ev = 1 ∧ ∃ c : ℂ, X = c • 1) :
    ∃ C₀ r : ℝ, 0 < C₀ ∧ 0 < r ∧ r < 1 ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      (∀ L : ℕ, N₀ ≤ L → mpvState A L ≠ 0 ∧
        (1 / 2 : ℝ) ≤ ‖⟪mpvState A L, mpvState A L⟫_ℂ‖ ∧
        ‖⟪mpvState A L, mpvState A L⟫_ℂ - 1‖ ≤ C₀ * r ^ L) ∧
      ∀ (k : ℕ) (O : Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ),
        ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, N₀ ≤ n →
          ‖mpvExpectation A (k + n) (appendObservable O
              (1 : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ)) -
            Matrix.trace (Λ * physicalObservableTransfer A k O 1)‖ ≤ C * r ^ n := by
  obtain ⟨hIrr, hPrim⟩ := pureCanonical_isIrreducibleMap_and_isPrimitive
    A Λ hΛpos hΛfix hNorm hPure
  obtain ⟨r, hr, hr1, htrace⟩ := canonical_trace_mul_transfer_pow_le_geometric
    A hIrr hPrim Λ hΛpos hΛtr hΛfix hNorm
  obtain ⟨C₀, hC₀, hnorm⟩ := htrace (1 : Module.End ℂ Mat)
  have hnorm' (L : ℕ) (hL : 1 ≤ L) :
      ‖⟪mpvState A L, mpvState A L⟫_ℂ - 1‖ ≤ C₀ * r ^ L := by
    simpa only [one_mul, Module.End.one_apply, Matrix.mul_one, hΛtr,
      inner_mpvState_self_eq_trace] using hnorm L hL
  have hlim := (pureCanonical_mpvState_inner_self_tendsto_one
    A Λ hΛpos hΛtr hΛfix hNorm hPure).norm
  have htail : ∀ᶠ L : ℕ in atTop,
      (1 / 2 : ℝ) ≤ ‖⟪mpvState A L, mpvState A L⟫_ℂ‖ := by
    exact (hlim.eventually (eventually_gt_nhds (by norm_num))).mono fun L hL => hL.le
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    (htail.and (eventually_ge_atTop 1))
  have hN₀pos := (hN₀ N₀ le_rfl).2
  have hnonzero (L : ℕ) (hL : N₀ ≤ L) : mpvState A L ≠ 0 := by
    intro hz
    have h := (hN₀ L hL).1
    simp only [hz, inner_zero_left, norm_zero] at h
    norm_num at h
  refine ⟨C₀, r, hC₀, hr, hr1, N₀, hN₀pos, ?_, ?_⟩
  · exact fun L hL => ⟨hnonzero L hL, (hN₀ L hL).1, hnorm' L (hN₀ L hL).2⟩
  intro k O
  obtain ⟨C₁, hC₁, hnum⟩ := htrace (physicalObservableTransfer A k O)
  let s := Matrix.trace (Λ * physicalObservableTransfer A k O 1)
  refine ⟨2 * (C₁ + ‖s‖ * C₀), by positivity, fun n hn => ?_⟩
  let a := LinearMap.trace ℂ Mat
    (physicalObservableTransfer A k O * Kraus.transferMap A ^ n)
  let b := ⟪mpvState A (k + n), mpvState A (k + n)⟫_ℂ
  have hkn : N₀ ≤ k + n := by omega
  have hb : (1 / 2 : ℝ) ≤ ‖b‖ := (hN₀ (k + n) hkn).1
  have hbpos : 0 < ‖b‖ := lt_of_lt_of_le (by norm_num) hb
  have hbne : b ≠ 0 := norm_pos_iff.mp hbpos
  have ha : ‖a - s‖ ≤ C₁ * r ^ n := hnum n (by omega)
  have hpow : r ^ (k + n) ≤ r ^ n := by
    rw [pow_add]
    exact mul_le_of_le_one_left (pow_nonneg hr.le n) (pow_le_one₀ hr.le hr1.le)
  have hbErr : ‖b - 1‖ ≤ C₀ * r ^ n :=
    (hnorm' (k + n) (by omega)).trans (mul_le_mul_of_nonneg_left hpow hC₀.le)
  have hquot : a / b - s = ((a - s) + s * (1 - b)) / b := by
    field_simp
    ring
  have htop : ‖(a - s) + s * (1 - b)‖ ≤ (C₁ + ‖s‖ * C₀) * r ^ n := by
    calc
      _ ≤ ‖a - s‖ + ‖s * (1 - b)‖ := norm_add_le _ _
      _ = ‖a - s‖ + ‖s‖ * ‖b - 1‖ := by rw [norm_mul, norm_sub_rev (1 : ℂ) b]
      _ ≤ C₁ * r ^ n + ‖s‖ * (C₀ * r ^ n) :=
        add_le_add ha (mul_le_mul_of_nonneg_left hbErr (norm_nonneg _))
      _ = _ := by ring
  have hexpect : mpvExpectation A (k + n) (appendObservable O
      (1 : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ)) = a / b := by
    rw [mpvExpectation_eq_div, inner_mpvState_toEuclideanLin,
      physicalObservableTransfer_appendObservable, physicalObservableTransfer_one]
  change ‖mpvExpectation A (k + n) (appendObservable O 1) - s‖ ≤ _
  rw [hexpect, hquot, norm_div]
  apply (div_le_iff₀ hbpos).mpr
  calc
    _ ≤ (C₁ + ‖s‖ * C₀) * r ^ n := htop
    _ ≤ 2 * (C₁ + ‖s‖ * C₀) * r ^ n * ‖b‖ := by
      have hpos : 0 ≤ (C₁ + ‖s‖ * C₀) * r ^ n := by positivity
      nlinarith

/-- The actual normalized full-ring expectation has a geometric bound at
every prescribed rate above the twisted spectral radius. Taking the rate below
one gives exponential decay. The nonzero denominator tail is derived from
canonical purity.
Source: arXiv:0802.0447, lines 241–243 and display `RL`, lines 381–388. -/
theorem pureCanonical_mpvExpectation_fullRing_le_geometric
    [NeZero D] (A : MPSTensor d D)
    (Λ : Mat) (hΛpos : Λ.PosDef) (hΛtr : Matrix.trace Λ = 1)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (hNorm : Kraus.transferMap A 1 = 1)
    (hPure : ∀ (ev : ℂ) (X : Mat),
      X ≠ 0 → ‖ev‖ = 1 → Kraus.transferMap A X = ev • X →
      ev = 1 ∧ ∃ c : ℂ, X = c • 1)
    (u : Matrix (Fin d) (Fin d) ℂ) (rate : ℝ≥0)
    (hRate : spectralRadius ℂ
      (Module.End.toContinuousLinearMap Mat (twistedTransferMap A u)) <
        (rate : ℝ≥0∞)) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ L : ℕ, N₀ ≤ L →
      ‖mpvExpectation A L (Matrix.finKronecker fun _ : Fin L => u)‖ ≤
        C * (rate : ℝ) ^ L := by
  let : TopologicalSpace Mat :=
    (inferInstance : NormedAddCommGroup Mat).toUniformSpace.toTopologicalSpace
  obtain ⟨C, hC, hpow⟩ := geometric_bound_of_spectralRadius_lt
    (Module.End.toContinuousLinearMap Mat (twistedTransferMap A u)) rate hRate
  let ℓ : (Mat →L[ℂ] Mat) →L[ℂ] ℂ :=
    ((LinearMap.trace ℂ Mat).comp (ContinuousLinearMap.coeLM ℂ)).toContinuousLinearMap
  obtain ⟨M, hM, hℓ⟩ := ℓ.bound
  have hlim := (pureCanonical_mpvState_inner_self_tendsto_one
    A Λ hΛpos hΛtr hΛfix hNorm hPure).norm
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    (hlim.eventually (eventually_gt_nhds (show (1 / 2 : ℝ) < ‖(1 : ℂ)‖ by norm_num)))
  refine ⟨2 * (M * C), by positivity, N₀, fun L hL => ?_⟩
  have hnum : ‖LinearMap.trace ℂ Mat (twistedTransferIter A u L)‖ ≤
      M * C * (rate : ℝ) ^ L := by
    have h := hℓ ((Module.End.toContinuousLinearMap Mat (twistedTransferMap A u)) ^ L)
    rw [← map_pow] at h
    change ‖LinearMap.trace ℂ Mat (twistedTransferIter A u L)‖ ≤ _ at h
    exact h.trans (by simpa only [← map_pow, mul_assoc] using
      mul_le_mul_of_nonneg_left (hpow L) hM.le)
  rw [mpvExpectation_finKronecker_const_eq_trace_div, norm_div]
  have hden : (1 / 2 : ℝ) < ‖LinearMap.trace ℂ Mat (Kraus.transferMap A ^ L)‖ := by
    simpa only [inner_mpvState_self_eq_trace] using hN₀ L hL
  have hdenpos : 0 < ‖LinearMap.trace ℂ Mat (Kraus.transferMap A ^ L)‖ := by linarith
  apply (div_le_iff₀ hdenpos).mpr
  refine hnum.trans ?_
  have hnonneg : 0 ≤ M * C * (rate : ℝ) ^ L := by positivity
  nlinarith

end MPSTensor
