/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SharpMomentScale

/-!
# Power decay of the selected charge energy bound

At the final source exponents, an entropy-defect density at most `n^(-8ν)`
and an interpolation parameter in `[n^(-ν), 2 n^(-ν)]` make the charge-energy
bracket at most `4 n^(-ν)`, provided `P ≥ ν`. The literal ceiling
`D = ceil(n^κ)` contributes a factor at most `4 n^(2κ)`.
Consequently the energy cap is at most
`16 C n^(-111/125000) (log n)^Cl`. Its exact power margin over
`n^(-1/2000)` is `97/250000`.

After fixing the coefficient, logarithmic power, positive gap and tail power,
one threshold works for every admissible scalar datum; it is given explicitly by
`finalSelectedEnergyThreshold`. An initial error at
most `n^(-1000)` is absorbed as well. An additional replica remainder is
retained additively after division by `g/2`; its decay is not assumed here.

The density and the energy
comparison at a common selected charge point are not constructed here.
The scalar theorem does not assert a physical defect bound, the remaining
sharp comparison, or the area law.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 492--511 (charge energy), lines 839--865
(`scanner:final-parameters`), revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The rate `8ν` is an explicit sufficient density hypothesis for this numerical
corollary. Independently formalized from the manuscript; no upstream Lean
proof text is reused.
-/

open Filter

namespace TNLean.PEPS.AreaLaw.Scan

/-- The final-scale charge-energy cap with the literal separation ceiling.
The argument `x` is the normalized entropy defect, not the unnormalized
charge defect. Source: `08-scanner.tex`, lines 492--511. -/
noncomputable def finalSelectedEnergyCap (C Cl P : ℝ) (n : ℕ) (W x p : ℝ) : ℝ :=
  C * W ^ 2 * (n : ℝ) ^ (Exponents.scannerEll : ℝ) *
    (Nat.ceil ((n : ℝ) ^ (Exponents.scannerKappa : ℝ)) : ℝ) ^ 2 *
      Real.log (n : ℝ) ^ Cl *
        ((1 - p) * x ^ (1 / 8 : ℝ) + (1 - p) * (n : ℝ) ^ (-P) + p)

/-- Exact power arithmetic for the final energy estimate. The first number
is the prefactor exponent; the second is its exponent after the charge
bracket; the third is the strict margin for the target decay. -/
theorem final_selectedEnergy_margins :
    2 * (Exponents.scannerOmega : ℝ) + (Exponents.scannerEll : ℝ) +
        2 * (Exponents.scannerKappa : ℝ) = (14 / 125000 : ℝ) ∧
    2 * (Exponents.scannerOmega : ℝ) + (Exponents.scannerEll : ℝ) +
        2 * (Exponents.scannerKappa : ℝ) - (Exponents.scannerNu : ℝ) =
      (-111 / 125000 : ℝ) ∧
    -(1 / 2000 : ℝ) -
        (2 * (Exponents.scannerOmega : ℝ) + (Exponents.scannerEll : ℝ) +
          2 * (Exponents.scannerKappa : ℝ) - (Exponents.scannerNu : ℝ)) =
      (97 / 250000 : ℝ) := by
  norm_num [Exponents.scannerOmega, Exponents.scannerEll,
    Exponents.scannerKappa, Exponents.scannerNu]

/-- The literal energy cap has a uniform explicit power bound. It uses the
matched density rate `8ν`, the full interpolation interval and `P ≥ ν`.
The ceiling is estimated by `D ≤ 2 n^κ` at every `n ≥ 1`.
No sign restriction on the fixed logarithmic exponent is needed. -/
theorem finalSelectedEnergyCap_le {C Cl P : ℝ} (hC : 0 ≤ C)
    (hP : (Exponents.scannerNu : ℝ) ≤ P) {n : ℕ} (hn : 1 ≤ n)
    {W x p : ℝ} (hW : 1 ≤ W)
    (hWupper : W ≤ (n : ℝ) ^ (Exponents.scannerOmega : ℝ))
    (hx : 0 ≤ x) (hxupper : x ≤ (n : ℝ) ^ (-(8 * (Exponents.scannerNu : ℝ))))
    (hp : p ∈ Set.Icc ((n : ℝ) ^ (-(Exponents.scannerNu : ℝ)))
      (2 * (n : ℝ) ^ (-(Exponents.scannerNu : ℝ)))) :
    finalSelectedEnergyCap C Cl P n W x p ≤
      (16 * C) * (n : ℝ) ^ (-111 / 125000 : ℝ) * Real.log (n : ℝ) ^ Cl := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := zero_lt_one.trans_le hn1
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hp0 : 0 ≤ p := (Real.rpow_nonneg (Nat.cast_nonneg n) _).trans hp.1
  have hroot0 : 0 ≤ x ^ (1 / 8 : ℝ) := Real.rpow_nonneg hx _
  have hroot : x ^ (1 / 8 : ℝ) ≤
      (n : ℝ) ^ (-(Exponents.scannerNu : ℝ)) := by
    calc
      x ^ (1 / 8 : ℝ) ≤
          ((n : ℝ) ^ (-(8 * (Exponents.scannerNu : ℝ)))) ^ (1 / 8 : ℝ) :=
        Real.rpow_le_rpow hx hxupper (by norm_num)
      _ = _ := by
        rw [← Real.rpow_mul hnpos.le]
        congr 1
        ring
  have hfirst : (1 - p) * x ^ (1 / 8 : ℝ) ≤
      (n : ℝ) ^ (-(Exponents.scannerNu : ℝ)) := by
    calc
      (1 - p) * x ^ (1 / 8 : ℝ) ≤ x ^ (1 / 8 : ℝ) := by
        nlinarith [mul_nonneg hp0 hroot0]
      _ ≤ _ := hroot
  have htail : (1 - p) * (n : ℝ) ^ (-P) ≤
      (n : ℝ) ^ (-(Exponents.scannerNu : ℝ)) := by
    calc
      (1 - p) * (n : ℝ) ^ (-P) ≤ (n : ℝ) ^ (-P) := by
        nlinarith [mul_nonneg hp0 (Real.rpow_nonneg (Nat.cast_nonneg n) (-P))]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hbracket : (1 - p) * x ^ (1 / 8 : ℝ) +
      (1 - p) * (n : ℝ) ^ (-P) + p ≤
        4 * (n : ℝ) ^ (-(Exponents.scannerNu : ℝ)) := by
    linarith [hp.2]
  have hκ : (1 : ℝ) ≤ (n : ℝ) ^ (Exponents.scannerKappa : ℝ) :=
    Real.one_le_rpow hn1 (by norm_num [Exponents.scannerKappa])
  have hD : (Nat.ceil ((n : ℝ) ^ (Exponents.scannerKappa : ℝ)) : ℝ) ≤
      2 * (n : ℝ) ^ (Exponents.scannerKappa : ℝ) := by
    have hceil := Nat.ceil_lt_add_one
      (Real.rpow_nonneg (Nat.cast_nonneg n) (Exponents.scannerKappa : ℝ))
    linarith
  have hWsq : W ^ 2 ≤ (n : ℝ) ^ (2 * (Exponents.scannerOmega : ℝ)) := by
    calc
      W ^ 2 ≤ ((n : ℝ) ^ (Exponents.scannerOmega : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (zero_le_one.trans hW) hWupper 2
      _ = _ := by
        rw [← Real.rpow_mul_natCast hnpos.le]
        congr 1
        ring
  have hDsq : (Nat.ceil ((n : ℝ) ^ (Exponents.scannerKappa : ℝ)) : ℝ) ^ 2 ≤
      4 * (n : ℝ) ^ (2 * (Exponents.scannerKappa : ℝ)) := by
    calc
      _ ≤ (2 * (n : ℝ) ^ (Exponents.scannerKappa : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hD 2
      _ = _ := by
        rw [mul_pow, ← Real.rpow_mul_natCast hnpos.le]
        norm_num [mul_comm]
  have hpowers :
      (n : ℝ) ^ (2 * (Exponents.scannerOmega : ℝ)) *
        (n : ℝ) ^ (Exponents.scannerEll : ℝ) *
        (n : ℝ) ^ (2 * (Exponents.scannerKappa : ℝ)) *
        (n : ℝ) ^ (-(Exponents.scannerNu : ℝ)) =
      (n : ℝ) ^ (-111 / 125000 : ℝ) := by
    rw [← Real.rpow_add hnpos, ← Real.rpow_add hnpos, ← Real.rpow_add hnpos]
    congr 1
    norm_num [Exponents.scannerOmega, Exponents.scannerEll,
      Exponents.scannerKappa, Exponents.scannerNu]
  unfold finalSelectedEnergyCap
  calc
    _ ≤ C * W ^ 2 * (n : ℝ) ^ (Exponents.scannerEll : ℝ) *
        (Nat.ceil ((n : ℝ) ^ (Exponents.scannerKappa : ℝ)) : ℝ) ^ 2 *
          Real.log (n : ℝ) ^ Cl *
            (4 * (n : ℝ) ^ (-(Exponents.scannerNu : ℝ))) :=
      mul_le_mul_of_nonneg_left hbracket (by positivity)
    _ ≤ C * (n : ℝ) ^ (2 * (Exponents.scannerOmega : ℝ)) *
        (n : ℝ) ^ (Exponents.scannerEll : ℝ) *
        (4 * (n : ℝ) ^ (2 * (Exponents.scannerKappa : ℝ))) *
          Real.log (n : ℝ) ^ Cl *
            (4 * (n : ℝ) ^ (-(Exponents.scannerNu : ℝ))) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hlog0 Cl)
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hWsq hC) (by positivity))
        hDsq (sq_nonneg _) (by positivity)
    _ = (16 * C) *
        ((n : ℝ) ^ (2 * (Exponents.scannerOmega : ℝ)) *
          (n : ℝ) ^ (Exponents.scannerEll : ℝ) *
          (n : ℝ) ^ (2 * (Exponents.scannerKappa : ℝ)) *
          (n : ℝ) ^ (-(Exponents.scannerNu : ℝ))) *
            Real.log (n : ℝ) ^ Cl := by ring
    _ = _ := by rw [hpowers]

/-- The explicit threshold of the final selected-energy bound: the thresholds for
`16 C n^(-111/125000) (log n)^Cl ≤ (g/4) n^(-1/2000)` and
`n^(-1000) ≤ (g/4) n^(-1/2000)` (`08-scanner.tex`, lines 492--511 and 839--865). -/
noncomputable def finalSelectedEnergyThreshold (C Cl g : ℝ) : ℕ :=
  max ⌈Real.logRpowThreshold (16 * C) (g / 4) (-111 / 125000) (-1 / 2000) Cl⌉₊
    ⌈Real.logRpowThreshold 1 (g / 4) (-1000) (-1 / 2000) 0⌉₊

/-- The initial error and literal final-scale energy cap together are at most `n^(-1/2000)`
after division by `g/2` at every `n` from the explicit threshold
`finalSelectedEnergyThreshold C Cl g` on, uniformly over every displayed scalar datum.
Source: `08-scanner.tex`, lines 492--511 and 839--865. -/
theorem final_selectedEnergy_le_rpow_of_finalSelectedEnergyThreshold_le {C Cl g P : ℝ}
    (hC : 0 ≤ C) (hg : 0 < g) (hP : (Exponents.scannerNu : ℝ) ≤ P) {n : ℕ}
    (hthr : finalSelectedEnergyThreshold C Cl g ≤ n) :
    2 ≤ n ∧
      ∀ W x p e : ℝ, 1 ≤ W → W ≤ (n : ℝ) ^ (Exponents.scannerOmega : ℝ) →
        0 ≤ x → x ≤ (n : ℝ) ^ (-(8 * (Exponents.scannerNu : ℝ))) →
        p ∈ Set.Icc ((n : ℝ) ^ (-(Exponents.scannerNu : ℝ)))
          (2 * (n : ℝ) ^ (-(Exponents.scannerNu : ℝ))) →
        e ≤ (n : ℝ) ^ (-1000 : ℝ) →
        (e + finalSelectedEnergyCap C Cl P n W x p) / (g / 2) ≤
          (n : ℝ) ^ (-(1 / 2000 : ℝ)) := by
  have hn := Real.two_le_of_ceil_logRpowThreshold_le ((le_max_left _ _).trans hthr)
  have hcap : (16 * C) * (n : ℝ) ^ (-111 / 125000 : ℝ) * Real.log (n : ℝ) ^ Cl ≤
      (g / 4) * (n : ℝ) ^ (-(1 / 2000 : ℝ)) := by
    simpa only [neg_div] using
      Real.mul_rpow_mul_log_rpow_le_mul_rpow_of_ceil_logRpowThreshold_le
        (by positivity) (by positivity) (by norm_num) ((le_max_left _ _).trans hthr)
  have he : (n : ℝ) ^ (-1000 : ℝ) ≤ (g / 4) * (n : ℝ) ^ (-(1 / 2000 : ℝ)) := by
    simpa only [Real.rpow_zero, mul_one, one_mul, neg_div] using
      Real.mul_rpow_mul_log_rpow_le_mul_rpow_of_ceil_logRpowThreshold_le
        (by norm_num) (by positivity) (by norm_num) ((le_max_right _ _).trans hthr)
  refine ⟨hn, ?_⟩
  intro W x p e hW hWupper hx hxupper hp heupper
  have hbound := finalSelectedEnergyCap_le (Cl := Cl) hC hP
    (show 1 ≤ n by omega) hW hWupper hx hxupper hp
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < g / 2)).2
  nlinarith [hbound.trans hcap, heupper.trans he]

/-- After fixing the coefficients and positive gap, the initial error and
literal final-scale energy cap together decay at least as `n^(-1/2000)`
after division by `g/2`, uniformly over every displayed scalar datum.
The upper bound `e ≤ n^(-1000)` suffices; the source's additional bounds
`0 ≤ e` and `e ≤ g/4` need not be used in this numerical upper bound. -/
theorem eventually_final_selectedEnergy_le_rpow {C Cl g P : ℝ}
    (hC : 0 ≤ C) (hg : 0 < g) (hP : (Exponents.scannerNu : ℝ) ≤ P) :
    ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧
      ∀ W x p e : ℝ, 1 ≤ W → W ≤ (n : ℝ) ^ (Exponents.scannerOmega : ℝ) →
        0 ≤ x → x ≤ (n : ℝ) ^ (-(8 * (Exponents.scannerNu : ℝ))) →
        p ∈ Set.Icc ((n : ℝ) ^ (-(Exponents.scannerNu : ℝ)))
          (2 * (n : ℝ) ^ (-(Exponents.scannerNu : ℝ))) →
        e ≤ (n : ℝ) ^ (-1000 : ℝ) →
        (e + finalSelectedEnergyCap C Cl P n W x p) / (g / 2) ≤
          (n : ℝ) ^ (-(1 / 2000 : ℝ)) :=
  eventually_atTop.2
    ⟨_, fun _ => final_selectedEnergy_le_rpow_of_finalSelectedEnergyThreshold_le hC hg hP⟩

/-- Explicit threshold form of the uniform numerical energy bound. The
threshold precedes the size, weight, density, interpolation parameter and
initial error. Source: the final parameter substitution in `08-scanner.tex`,
lines 839--865, applied to the charge-energy expression in lines 492--511. -/
theorem exists_final_selectedEnergy_le_rpow {C Cl g P : ℝ}
    (hC : 0 ≤ C) (hg : 0 < g) (hP : (Exponents.scannerNu : ℝ) ≤ P) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ W x p e : ℝ, 1 ≤ W → W ≤ (n : ℝ) ^ (Exponents.scannerOmega : ℝ) →
        0 ≤ x → x ≤ (n : ℝ) ^ (-(8 * (Exponents.scannerNu : ℝ))) →
        p ∈ Set.Icc ((n : ℝ) ^ (-(Exponents.scannerNu : ℝ)))
          (2 * (n : ℝ) ^ (-(Exponents.scannerNu : ℝ))) →
        e ≤ (n : ℝ) ^ (-1000 : ℝ) →
        (e + finalSelectedEnergyCap C Cl P n W x p) / (g / 2) ≤
          (n : ℝ) ^ (-(1 / 2000 : ℝ)) :=
  ⟨_, Real.two_le_of_ceil_logRpowThreshold_le (le_max_left _ _), fun _ hn =>
    (final_selectedEnergy_le_rpow_of_finalSelectedEnergyThreshold_le (Cl := Cl) hC hg hP hn).2⟩

/-- Adding a replica remainder preserves it exactly, after division by the
same gap. No estimate or sign assumption on that remainder is introduced. -/
theorem selectedEnergy_add_remainder_le {e cap rem g r : ℝ}
    (henergy : (e + cap) / (g / 2) ≤ r) :
    (e + cap + rem) / (g / 2) ≤ r + rem / (g / 2) := by
  rw [add_div]
  exact _root_.add_le_add henergy le_rfl

/-- The same uniform threshold controls the energy expression with an
arbitrary replica remainder, retained as `rem / (g/2)`. This does not assert
that the physical remainder has any rate in the system-size variable. -/
theorem exists_final_selectedEnergy_add_remainder_le_rpow {C Cl g P : ℝ}
    (hC : 0 ≤ C) (hg : 0 < g) (hP : (Exponents.scannerNu : ℝ) ≤ P) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ W x p e rem : ℝ,
        1 ≤ W → W ≤ (n : ℝ) ^ (Exponents.scannerOmega : ℝ) →
        0 ≤ x → x ≤ (n : ℝ) ^ (-(8 * (Exponents.scannerNu : ℝ))) →
        p ∈ Set.Icc ((n : ℝ) ^ (-(Exponents.scannerNu : ℝ)))
          (2 * (n : ℝ) ^ (-(Exponents.scannerNu : ℝ))) →
        e ≤ (n : ℝ) ^ (-1000 : ℝ) →
        (e + finalSelectedEnergyCap C Cl P n W x p + rem) / (g / 2) ≤
          (n : ℝ) ^ (-(1 / 2000 : ℝ)) + rem / (g / 2) := by
  obtain ⟨N, hN, hbound⟩ := exists_final_selectedEnergy_le_rpow (Cl := Cl) hC hg hP
  refine ⟨N, hN, ?_⟩
  intro n hn W x p e rem hW hWupper hx hxupper hp he
  exact selectedEnergy_add_remainder_le
    (hbound n hn W x p e hW hWupper hx hxupper hp he)

end TNLean.PEPS.AreaLaw.Scan
