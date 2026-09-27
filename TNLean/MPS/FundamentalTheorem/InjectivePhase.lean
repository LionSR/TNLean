/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.UnimodularPowerSum
import TNLean.MPS.Core.ScaledNormality
import TNLean.MPS.FundamentalTheorem.Basic
import TNLean.MPS.FundamentalTheorem.SectorBNT.UnblockedPowerSumCoefficients
import TNLean.MPS.ParentHamiltonian.Nonvanishing

/-!
# The fundamental theorem for injective tensors up to a phase

If the periodic vectors of a tensor `B` are, at every positive length `N`, a unimodular
multiple `c_N` of those of an injective tensor `A` with the same bond dimension, then
`B = λ X A X⁻¹` for an invertible `X` and a phase `λ`, and `c_N = λ^N`.

This is the single-block, injective case of the Fundamental Theorem of MPV,
arXiv:1606.00608, Theorem `thm1`, `Papers/1606.00608/MPDO-22-12-17-2.tex` lines 1167–1170,
with proportionality constants of unit modulus.  The proof first shows that the
length-dependent constants form a geometric sequence, as in the footnote to
`eq:UpsiA-eq-psiB` of arXiv:2405.00439 (`Papers/2405.00439/MPU-DW.tex` lines 571–574),
and then applies the equal-vector theorem `MPSTensor.fundamentalTheorem_singleBlock` to
`λ⁻¹ B`.

## Main results

* `MPSTensor.exists_mpv_ne_zero_of_isInjective`: an injective tensor of positive bond dimension
  has a nonzero periodic vector at every positive length.
* `MPSTensor.exists_eq_pow_of_mpv_eq_smul`: unimodular proportionality constants between an
  arbitrary tensor and an injective one are the powers of a phase.
* `MPSTensor.unitGaugePhaseEquiv_of_mpv_eq_smul_of_isInjective`: unimodular proportionality
  of the periodic vectors of an injective tensor gives gauge equivalence up to a phase.

## References

- [arXiv:1606.00608](https://arxiv.org/abs/1606.00608) -- Cirac, Pérez-García, Schuch,
  Verstraete, *Matrix product density operators: Renormalization fixed points and boundary
  theories*
- [arXiv:2405.00439](https://arxiv.org/abs/2405.00439) -- Garre-Rubio, Schuch,
  *Fractional domain wall statistics in spin chains with anomalous symmetries*
-/

open scoped Matrix

namespace MPSTensor

variable {d D DA : ℕ}

/-- Project result: an injective tensor of positive bond dimension has a nonzero periodic
vector at every positive length. At length one the traces of the letters cannot all vanish,
because the letters span the full matrix algebra; from length two on this is
`MPSTensor.mpv_ne_zero_of_isNBlkInjective`. -/
theorem exists_mpv_ne_zero_of_isInjective [NeZero D] {B : MPSTensor d D}
    (hB : Kraus.IsInjective B) {N : ℕ} (hN : 0 < N) :
    ∃ σ : Fin N → Fin d, mpv B σ ≠ 0 := by
  rcases Nat.lt_or_ge N 2 with hN2 | hN2
  · obtain rfl : N = 1 := by omega
    by_contra hall
    push Not at hall
    refine Kraus.not_isInjective_of_linearMap (Matrix.traceLinearMap (Fin D) ℂ ℂ)
      (fun i ↦ ?_) 1 ?_ hB
    · simpa [mpv, coeff] using hall (fun _ ↦ i)
    · simp [NeZero.ne D]
  · have hne := mpv_ne_zero_of_isNBlkInjective (Kraus.isNBlkInjective_one_of_isInjective hB)
      one_pos (N := N) hN2
    by_contra hall
    push Not at hall
    exact hne (funext hall)

/-- Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 571–574 (footnote to
`eq:UpsiA-eq-psiB`). **Unimodular proportionality constants are powers**: if
`|ψ_N(A)⟩ = c_N |ψ_N(B)⟩` with `|c_N| = 1` at every positive length `N` and `B` injective,
then `c_N = λ^N` for a phase `λ`.  The tensor `A` is arbitrary.  The proof expands `A` in
the single normal tensor `B` (`MPSTensor.exists_unblocked_powerSum_coeff`), so that
`c_N = ∑ₖ μₖ^N`, and then `Complex.exists_norm_eq_one_sum_pow_eq_pow` leaves one phase. -/
theorem exists_eq_pow_of_mpv_eq_smul [NeZero D] (A : MPSTensor d DA) {B : MPSTensor d D}
    (hB : Kraus.IsInjective B) (c : ℕ → ℂ)
    (hC : ∀ N, 0 < N → ∀ σ : Fin N → Fin d, mpv A σ = c N * mpv B σ)
    (hnorm : ∀ N, 0 < N → ‖c N‖ = 1) :
    ∃ lam : ℂ, ‖lam‖ = 1 ∧ ∀ N, 0 < N → c N = lam ^ N := by
  obtain ⟨n, μ, hμne, hexp, -, -⟩ :=
    exists_unblocked_powerSum_coeff A (Γ := Unit) (fun _ ↦ B)
      (fun _ ↦ hB.isNormal) (fun _ ↦ Nat.pos_of_ne_zero (NeZero.ne D))
      (fun γ δ hγδ ↦ absurd (Subsingleton.elim γ δ) hγδ)
      (fun N hN ↦ ⟨fun _ ↦ c N, fun σ ↦ by rw [hC N hN σ]; simp⟩)
  have hcoef : ∀ N, 0 < N → c N = ∑ k, μ () k ^ N := by
    intro N hN
    obtain ⟨σ, hσ⟩ := exists_mpv_ne_zero_of_isInjective hB hN
    have h := (hC N hN σ).symm.trans (hexp N hN σ)
    simp only [Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton] at h
    exact mul_right_cancel₀ hσ h
  obtain ⟨-, lam, hlam, hpow⟩ := Complex.exists_norm_eq_one_sum_pow_eq_pow (μ ()) (hμne ())
    (fun L hL ↦ by rw [← hcoef L hL]; exact hnorm L hL)
  exact ⟨lam, hlam, fun N hN ↦ (hcoef N hN).trans (hpow N)⟩

/-- **Fundamental theorem for injective tensors up to a phase.**
Source: arXiv:1606.00608, Theorem `thm1`, `Papers/1606.00608/MPDO-22-12-17-2.tex`
lines 1167–1170, in the single-block case: if `A` is injective and, for every positive
length `N`, `|ψ_N(B)⟩ = c_N |ψ_N(A)⟩` for a phase `c_N`, then `Bⁱ = e^{iφ} X Aⁱ X⁻¹` for an
invertible `X` and a phase `e^{iφ}`.  The source states the theorem for proportionality
constants without the modulus condition, for tensors in canonical form; here the tensors
have the same bond dimension and the constants have unit modulus. -/
theorem unitGaugePhaseEquiv_of_mpv_eq_smul_of_isInjective [NeZero D] {A B : MPSTensor d D}
    (hA : Kraus.IsInjective A)
    (hAB : ∀ N, 0 < N → ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ σ : Fin N → Fin d, mpv B σ = c * mpv A σ) :
    UnitGaugePhaseEquiv A B := by
  choose! c hc hBA using hAB
  obtain ⟨lam, hlam, hpow⟩ := exists_eq_pow_of_mpv_eq_smul B hA c hBA hc
  have hlam0 : lam ≠ 0 := by rintro rfl; simp at hlam
  obtain ⟨X, hX⟩ := fundamentalTheorem_singleBlock (B := fun i ↦ lam⁻¹ • B i) hA (by
    intro N σ
    rw [mpv_smul]
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp [mpv, coeff]
    · rw [hBA N hN σ, hpow N hN, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hlam0, one_pow,
        one_mul])
  refine ⟨X, lam, ?_, fun i ↦ ?_⟩
  · rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hlam]; simp
  · rw [← hX i, smul_smul, mul_inv_cancel₀ hlam0, one_smul]

end MPSTensor
