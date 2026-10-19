/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.InitialExponentGain
import TNLean.PEPS.AreaLaw.Scan.ExponentBootstrap

/-!
# An upper bound for the number of entropy bootstrap rounds

The initial exponent gain bounds the number of rounds needed to reach the
safe-box exponent. For the cyclic-color recurrence constants `p` and `M`,
`⌈400000 * log M * log 500000 / p⌉₊` rounds suffice. This is an auxiliary
quantitative consequence of the finite iteration, not the manuscript's
literal choice of numerical recurrence constants.

## References

OpenAI, *A two-dimensional area law from a global spectral gap*,
proof of Proposition 9.5, `08-scanner.tex`, lines 788–803, and proof of
Proposition 3.3, `02-initial.tex`, lines 651–667, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text reused.
-/

namespace TNLean.PEPS.AreaLaw.Scan

/-- A logarithmic upper bound on the finite iteration count, using
`-log (1 - ℓ) ≥ ℓ` and `e₀ ≤ 1`. This quantifies the iteration in the proof of
Proposition 9.5 (`08-scanner.tex`, lines 788–803). -/
theorem boxBootstrapRounds_le_ceil_log_div {e₀ ε ℓ : ℝ}
    (he₀ : 0 < e₀) (he₀₁ : e₀ ≤ 1) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hℓ : 0 < ℓ) (hℓ₁ : ℓ < 1) :
    boxBootstrapRounds e₀ ε ℓ ≤ ⌈Real.log (1 / ε) / ℓ⌉₊ := by
  have hθ : 0 < 1 - ℓ := sub_pos.mpr hℓ₁
  have hlog : Real.log (1 - ℓ) < 0 := Real.log_neg hθ (sub_lt_self 1 hℓ)
  have hlogBound : Real.log (1 - ℓ) ≤ -ℓ := by
    linarith [Real.log_le_sub_one_of_pos hθ]
  have hnonneg : 0 ≤ Real.log (1 / ε) :=
    Real.log_nonneg ((le_div_iff₀ hε).2 (by simpa using hε₁))
  apply Nat.ceil_mono
  apply (div_le_iff_of_neg hlog).2
  calc
    Real.log (1 / ε) / ℓ * Real.log (1 - ℓ) ≤
        Real.log (1 / ε) / ℓ * (-ℓ) :=
      mul_le_mul_of_nonneg_left hlogBound (div_nonneg hnonneg hℓ.le)
    _ = Real.log ε := by
      rw [one_div, Real.log_inv]
      field_simp [hℓ.ne']
    _ ≤ Real.log (ε / e₀) :=
      Real.log_le_log hε ((le_div_iff₀ he₀).2 (mul_le_of_le_one_right hε.le he₀₁))

/-- A round budget expressed directly in the probability and scale of the cyclic-color
initial recurrence. The physical parameters remain explicit. This is an auxiliary bound
for the iteration in Proposition 9.5 (`08-scanner.tex`, lines 788–803). -/
noncomputable def initialBoxBootstrapRoundBound (q R : ℕ) (J Δ : ℝ) : ℕ :=
  ⌈400000 * Real.log (initialBoxScale q R J Δ) * Real.log 500000 /
    initialBoxProb q R J Δ⌉₊

/-- The bootstrap count used by the physical safe-box constant is at most
`initialBoxBootstrapRoundBound q R J Δ`. Source: the iteration of Proposition 9.5,
`08-scanner.tex`, lines 788–803, with the initial exponent from Proposition 3.3. -/
theorem boxBootstrapRounds_initial_le (q R : ℕ) (J Δ : ℝ) :
    boxBootstrapRounds (initialBoxExponent q R J Δ) (Exponents.boxError : ℝ)
        (BootstrapParameters.ell (initialBoxExponent q R J Δ)) ≤
      initialBoxBootstrapRoundBound q R J Δ := by
  obtain ⟨he₀, he₀₁⟩ := initialBoxExponent_pos_and_lt_one q R J Δ
  obtain ⟨_, _, hℓ, hℓ₁, _⟩ := BootstrapParameters.parameter_bounds he₀ he₀₁
  have hp := (initialBoxProb_pos_and_le_half q R J Δ).1
  have hlog := Real.log_pos (one_lt_initialBoxScale q R J Δ)
  have hgain := (initialBoxExponent_gain_bounds q R J Δ).1
  have hell : initialBoxProb q R J Δ / (400000 * Real.log (initialBoxScale q R J Δ)) ≤
      BootstrapParameters.ell (initialBoxExponent q R J Δ) := by
    unfold BootstrapParameters.ell BootstrapParameters.nu BootstrapParameters.g0
    convert div_le_div_of_nonneg_right hgain (by norm_num : (0 : ℝ) ≤ 200000) using 1 <;>
      ring
  refine (boxBootstrapRounds_le_ceil_log_div he₀ he₀₁.le
    (by norm_num [Exponents.boxError]) (by norm_num [Exponents.boxError]) hℓ hℓ₁).trans ?_
  apply Nat.ceil_mono
  have hden : 0 < initialBoxProb q R J Δ /
      (400000 * Real.log (initialBoxScale q R J Δ)) := div_pos hp (by positivity)
  have h := div_le_div_of_nonneg_left
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 500000)) hden hell
  norm_num [Exponents.boxError]
  convert h using 1
  field_simp [hp.ne', hlog.ne']

/-- Contracting the initial exponent for the explicit round budget reaches the safe-box
exponent `2 · 10⁻⁶`. Source: the finite iteration in Proposition 9.5,
`08-scanner.tex`, lines 788–803. -/
theorem pow_initialBoxBootstrapRoundBound_mul_le (q R : ℕ) (J Δ : ℝ) :
    (1 - BootstrapParameters.ell (initialBoxExponent q R J Δ)) ^
        initialBoxBootstrapRoundBound q R J Δ * initialBoxExponent q R J Δ ≤
      (Exponents.boxError : ℝ) := by
  obtain ⟨he₀, he₀₁⟩ := initialBoxExponent_pos_and_lt_one q R J Δ
  obtain ⟨_, _, hℓ, hℓ₁, _⟩ := BootstrapParameters.parameter_bounds he₀ he₀₁
  exact (mul_le_mul_of_nonneg_right
    (pow_le_pow_of_le_one (sub_nonneg.mpr hℓ₁.le) (sub_le_self 1 hℓ.le)
      (boxBootstrapRounds_initial_le q R J Δ)) he₀.le).trans
    (pow_boxBootstrapRounds_mul_le he₀ (by norm_num [Exponents.boxError]) hℓ hℓ₁)

end TNLean.PEPS.AreaLaw.Scan
