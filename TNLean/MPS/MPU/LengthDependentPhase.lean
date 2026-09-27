/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.InjectivePhase
import TNLean.MPS.MPDO.ActionTensor

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
comparing `N` and `2N`. Here the statement is `MPSTensor.exists_eq_pow_of_mpv_eq_smul`
applied to the action tensor of `U` on `A`; that lemma uses uniqueness of power sums in place
of the approximation argument.

## Main results

* `MPOTensor.exists_eq_pow_of_mpo_mulVec_mpv_eq_smul`: the phase is a power.

## References
- [arXiv:2405.00439](https://arxiv.org/abs/2405.00439) -- Garre-Rubio, Schuch,
  *Fractional domain wall statistics in spin chains with anomalous symmetries*
-/

open scoped Matrix

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
  exact MPSTensor.exists_eq_pow_of_mpv_eq_smul (actTensor U A) hB c hC hnorm

end MPOTensor
