/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.UnimodularPowerSum
import TNLean.MPS.FundamentalTheorem.SectorBNT.UnblockedPowerSumCoefficients
import TNLean.MPS.MPDO.ActionTensor
import TNLean.MPS.ParentHamiltonian.Nonvanishing

/-!
# A unimodular length-dependent phase under a matrix product operator is a power

**Source.** Garre-Rubio, Schuch 2024 (arXiv:2405.00439), Section II.B, footnote to
`eq:UpsiA-eq-psiB`, `Papers/2405.00439/MPU-DW.tex` lines 571–574: if a matrix product unitary
`U` maps the injective matrix product state `|ψ_A⟩` to `c_N |ψ_B⟩` on `N` sites, with `B`
injective and `|c_N|² = 1` for every `N`, then `c_N = λ^N` for a phase `λ`.

**Formalized here.** The statement at every positive length `N`. The hypotheses are weaker than
the source's: `U` is an arbitrary matrix product operator and `A` an arbitrary tensor; only the
injectivity of `B` (with positive bond dimension, so that `|ψ_B⟩` is a state) and the modulus
condition are used. The source's proof expands the canonical form of `U|ψ_A⟩` into blocks
proportional to `B`, so that `c_N = ∑ᵢ λᵢ^N`, and then shows that one phase survives by
comparing `N` and `2N`. Here the first step is the unblocked power-sum expansion
`MPSTensor.exists_unblocked_powerSum_coeff` applied to the action tensor of `U` on `A` and the
single target `B`, and the second step is `Complex.exists_norm_eq_one_sum_pow_eq_pow`, which
uses uniqueness of power sums in place of the approximation argument.

## Main results

* `MPSTensor.exists_mpv_ne_zero_of_isInjective`: an injective tensor of positive bond dimension
  has a nonzero periodic vector at every positive length.
* `MPOTensor.exists_eq_pow_of_mpo_mulVec_mpv_eq_smul`: the phase is a power.

## References
- [arXiv:2405.00439](https://arxiv.org/abs/2405.00439) -- Garre-Rubio, Schuch,
  *Fractional domain wall statistics in spin chains with anomalous symmetries*
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

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

end MPSTensor

namespace MPOTensor

variable {d DU DA DB : ℕ}

/-- Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 571–574 (footnote to
`eq:UpsiA-eq-psiB`). **A unimodular length-dependent phase is a power**: if
`U_N |ψ_A⟩_N = c_N |ψ_B⟩_N` with `|c_N| = 1` at every positive length `N` and `B` injective,
then `c_N = λ^N` for a phase `λ`. The source's assumptions that `U` is a matrix product unitary
and that `A` is injective are not needed. -/
theorem exists_eq_pow_of_mpo_mulVec_mpv_eq_smul [NeZero DB] (U : MPOTensor d DU)
    (A : MPSTensor d DA) {B : MPSTensor d DB} (hB : Kraus.IsInjective B) (c : ℕ → ℂ)
    (hc : ∀ N, 0 < N → mpo U N *ᵥ (fun τ : Fin N → Fin d ↦ MPSTensor.mpv A τ) =
      c N • fun σ : Fin N → Fin d ↦ MPSTensor.mpv B σ)
    (hnorm : ∀ N, 0 < N → ‖c N‖ = 1) :
    ∃ lam : ℂ, ‖lam‖ = 1 ∧ ∀ N, 0 < N → c N = lam ^ N := by
  have hC : ∀ N, 0 < N → ∀ σ : Fin N → Fin d,
      MPSTensor.mpv (actTensor U A) σ = c N * MPSTensor.mpv B σ := by
    intro N hN σ
    have := congrFun ((mpo_mulVec_mpv U A N).symm.trans (hc N hN)) σ
    simpa using this
  obtain ⟨n, μ, hμne, hexp, -, -⟩ :=
    MPSTensor.exists_unblocked_powerSum_coeff (actTensor U A) (Γ := Unit) (fun _ ↦ B)
      (fun _ ↦ hB.isNormal) (fun _ ↦ Nat.pos_of_ne_zero (NeZero.ne DB))
      (fun γ δ hγδ ↦ absurd (Subsingleton.elim γ δ) hγδ)
      (fun N hN ↦ ⟨fun _ ↦ c N, fun σ ↦ by rw [hC N hN σ]; simp⟩)
  have hcoef : ∀ N, 0 < N → c N = ∑ k, μ () k ^ N := by
    intro N hN
    obtain ⟨σ, hσ⟩ := MPSTensor.exists_mpv_ne_zero_of_isInjective hB hN
    have h := (hC N hN σ).symm.trans (hexp N hN σ)
    simp only [Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton] at h
    exact mul_right_cancel₀ hσ h
  obtain ⟨-, lam, hlam, hpow⟩ := Complex.exists_norm_eq_one_sum_pow_eq_pow (μ ()) (hμne ())
    (fun L hL ↦ by rw [← hcoef L hL]; exact hnorm L hL)
  exact ⟨lam, hlam, fun N hN ↦ (hcoef N hN).trans (hpow N)⟩

end MPOTensor
