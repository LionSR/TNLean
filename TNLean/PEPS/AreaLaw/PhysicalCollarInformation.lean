/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.CollarInformation
import TNLean.PEPS.AreaLaw.Scan.PhysicalBoxBootstrap
import TNLean.PEPS.AreaLaw.Scan.TemplateFinalInformation
import TNLean.PEPS.AreaLaw.Scan.BoxClearanceComparison

/-!
# The physical sublinear collar bound

For every real clearance greater than 2R+10, the physical safe-box entropy
estimate gives the sublinear mutual-information bound for the original ground
state. The same constant and scale threshold apply to every finite domain,
Hamiltonian, ground state, cut, and separated template. The collar cut and
volume estimates then give all assertions of Proposition 9.6.

The proof uses the integer clearance 2R+10 internally, after transferring the
physical safe-box estimate from clearance 2R+11 by subdivision. Separation at
the prescribed real clearance implies separation at this integer clearance.
No scanner or mutual-information estimate is assumed.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
Proposition 9.6, `08-scanner.tex`, lines 808–827 and 942–943; the real safety
parameter is specified in `02-initial.tex`, line 225,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw

/-- The sublinear collar bound for every real clearance allowed by the source.
Source: area-law Proposition 9.6, `08-scanner.tex`, lines 808–827 and 942–943,
with the real safety parameter of `02-initial.tex`, line 225, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The original-state information estimate follows from the physical safe-box
bootstrap and the proved integer-clearance comparison. -/
theorem sublinearCollarBound_real
    (q R : ℕ) (hq : 1 ≤ q) {J Δ D₀ Ctpl : ℝ}
    (hJ : 0 ≤ J) (hΔ : 0 < Δ) (hD₀ : 2 * (R : ℝ) + 10 < D₀)
    (hCtpl : 24 ≤ Ctpl) :
    SublinearCollarBound q R J Δ D₀ Ctpl := by
  obtain ⟨Cb, hCb, hbox⟩ := Scan.exists_boxEntropy_le_boxError q R hq hJ hΔ
  let d : ℕ := 2 * R + 10
  have hd : 3 ≤ d := by dsimp only [d]; omega
  have hp : 0 ≤ 1 + (Exponents.boxError : ℝ) := by
    norm_num [Exponents.boxError]
  have hweak := boxEntropy_power_le_of_succ_clearance
    (R := R) (D := d) (J := J) (Δ := Δ) (p := 1 + (Exponents.boxError : ℝ))
    hq hd hCb.le hp (hbox (d + 1) (by dsimp only [d]; omega))
  have hlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hCw : 0 ≤ 4 * Cb + 4 * Real.log q + 1 := by linarith
  obtain ⟨Cm, _, N, _, hinfo⟩ :=
    Scan.exists_template_final_mutualInformation_of_boxEntropy q R d hq (by omega)
      hJ hΔ hCtpl hCw hweak
  have hdreal : (d : ℝ) < D₀ := by
    simpa only [d, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hD₀
  refine sublinearCollarBound_of_mutualInformation_le hCtpl
    (show (1 : ℝ) ≤ D₀ by linarith [show (0 : ℝ) ≤ (R : ℝ) from Nat.cast_nonneg R]) ?_
  refine ⟨Cm / 2, N, ?_⟩
  intro n s₀ hn Λ h E₀ Ω hgs A T hsep hL
  have hsep' : T.IsSeparated (d : ℝ) (Geometry.boundaryEndpoints Λ A) := by
    intro t ht z hz
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hdreal.le (by norm_num : (0 : ℝ) ≤ 4))
        (Nat.cast_nonneg s₀)) (hsep t ht z hz)
  have hi := (hinfo n s₀ hn Λ h E₀ Ω hgs A T hsep' hL).2
  dsimp only [Exponents.scannerEll, Exponents.amplificationEpsilon] at hi ⊢
  nlinarith only [hi]

end TNLean.PEPS.AreaLaw
