/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.WState
import TNLean.MPS.Core.RepeatedWord
import QICLean.Algebra.NewtonGirard

/-!
# W state: periodic (trace) boundary conditions

**Source.** Cirac, Pérez-García, Schuch, Verstraete 2021 (arXiv:2011.12127), Appendix A,
"The W state", `Papers/2011.12127/TN-Review-main.tex` lines 2348–2362: the W state is an
open-boundary MPS with `D = 2`; the review notes that this is not a translationally
invariant representation because of the non-periodic boundary, and that a translationally
invariant representation needs a bond dimension growing with `N`, with a bound of the form
`D^3 log D = Ω(N)`.
Review: arXiv:2011.12127, Appendix A, "The W state".

**Formalized here.** The periodic closure of the printed tensor is not the W state: its
trace contraction is `2` on the vacuum and `0` on every configuration with an excitation,
in particular on every single-excitation configuration. No periodic tensor of bond
dimension `1` gives `W_N` for any `N ≥ 2`. A periodic tensor of bond dimension `D` that
gives `W_1, …, W_D` gives `W_N` for no `N > D`; consequently no single periodic tensor
gives `W_N` for all `N ≥ 1`, and among `W_1, …, W_{D+1}` one fails. The asymptotic bound
`D^3 log D = Ω(N)` for a single length is not formalized; it is recorded in
`docs/paper-gaps/rmp_w_state_ti_bound.tex`.

## Main definitions

* `IsPeriodicWState A N` — the trace contraction of `A` on `N` sites is `W_N`.

## Main results

* `mpv_wTensor` — the periodic closure of the printed tensor is `2 · |0⋯0⟩`.
* `mpv_wTensor_ne_wIndicator` — the periodic closure of the printed tensor is not `W_N`.
* `not_isPeriodicWState_of_bondDim_one` — bond dimension `1` fails for every `N ≥ 2`.
* `pow_eq_zero_of_isPeriodicWState` — representing `W_1, …, W_D` forces `(A^0)^D = 0`.
* `not_isPeriodicWState_of_lt` — representing `W_1, …, W_D` rules out every `W_N`, `N > D`.
* `exists_not_isPeriodicWState_le` — some `N ≤ D + 1` is not represented.

## References

- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- Cirac, Pérez-García, Schuch,
  Verstraete, *Matrix product states and projected entangled pair states: Concepts,
  symmetries, theorems*
-/

open scoped Matrix

namespace MPSTensor

variable {D : ℕ}

/-! ### The printed tensor with a trace boundary -/

/-- Project result, illustrating arXiv:2011.12127, line 2362 (the open-boundary
representation is "not a translationally invariant representation ... due to the
non-periodic boundary condition"; the review prints no trace-closure value). Closing the
printed W tensor with a trace instead of the boundary vectors `(0|` and `|1)` gives `2` on the
vacuum and `0` on every configuration containing an excitation: the trace of the single
raising operator vanishes. -/
theorem mpv_wTensor {N : ℕ} (σ : Cfg 2 N) :
    mpv wTensor σ = if (List.ofFn σ).count 1 = 0 then 2 else 0 := by
  rw [mpv_eq, coeff_eq, evalWord_wTensor]
  rcases (List.ofFn σ).count 1 with _ | _ | k
  · simp [Matrix.trace_one]
  · simp [wRaising, Matrix.trace_fin_two]
  · simp

/-- Project result, illustrating arXiv:2011.12127, line 2362. On every single-excitation
configuration,
where `W_N` has amplitude `1`, the periodic closure of the printed tensor vanishes. -/
theorem mpv_wTensor_eq_zero_of_wIndicator_eq_one {N : ℕ} {σ : Cfg 2 N}
    (hσ : wIndicator N σ = 1) : mpv wTensor σ = 0 := by
  rw [mpv_wTensor]
  rw [wIndicator_apply] at hσ
  split_ifs at hσ with h
  · simp [h]
  · exact absurd hσ zero_ne_one

/-- Project result, illustrating arXiv:2011.12127, line 2362. For `N ≥ 1` the periodic
closure of the printed tensor is not the W state. -/
theorem mpv_wTensor_ne_wIndicator {N : ℕ} (hN : 1 ≤ N) :
    (fun σ : Cfg 2 N => mpv wTensor σ) ≠ wIndicator N := by
  intro h
  have hw : wIndicator N (excitedAt N ⟨0, hN⟩) = 1 := by
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    have : excitedAt (M + 1) ⟨0, hN⟩ = Fin.cons 1 (fun _ : Fin M => 0) := by
      funext j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp [excitedAt]
      · simp [excitedAt, Fin.ext_iff]
    rw [wIndicator_apply, this, List.ofFn_succ]
    simp [List.count_replicate]
  have h0 := mpv_wTensor_eq_zero_of_wIndicator_eq_one hw
  rw [congrFun h, hw] at h0
  exact one_ne_zero h0

/-! ### Periodic representations of the W state -/

/-- Project result: the trace contraction of `A` on `N` sites equals the W state `W_N`,
that is, `A` is a translationally invariant periodic representation of `W_N` in the sense
of arXiv:2011.12127, line 2362. -/
def IsPeriodicWState (A : MPSTensor 2 D) (N : ℕ) : Prop :=
  ∀ σ : Cfg 2 N, mpv A σ = wIndicator N σ

/-- Project result: a periodic representation of `W_k` has vanishing vacuum amplitude
`tr((A^0)^k) = 0`. -/
theorem trace_pow_eq_zero_of_isPeriodicWState {A : MPSTensor 2 D} {k : ℕ}
    (h : IsPeriodicWState A k) : Matrix.trace (A 0 ^ k) = 0 := by
  have := h (fun _ => 0)
  rw [mpv_const_eq_trace_pow] at this
  rw [this, wIndicator_apply, List.ofFn_const]
  simp [List.count_replicate]

/-- Project result: if `(A^0)^M = 0` with `M ≥ 1`, then `A` does not represent
`W_{M+1}`: the configuration `|10⋯0⟩` has amplitude `tr(A^1 (A^0)^M) = 0`, while its
W-state amplitude is `1`. -/
theorem not_isPeriodicWState_of_pow_eq_zero {A : MPSTensor 2 D} {M : ℕ}
    (h0 : A 0 ^ M = 0) : ¬ IsPeriodicWState A (M + 1) := by
  intro h
  have := h (Fin.cons 1 (fun _ : Fin M => 0))
  rw [mpv_eq, coeff_eq, wIndicator_apply, List.ofFn_succ] at this
  simp only [Fin.cons_zero, Fin.cons_succ, List.ofFn_const, Kraus.evalWord_cons,
    evalWord_replicate, h0, mul_zero, Matrix.trace_zero] at this
  simp [List.count_replicate] at this

/-- Project result: no periodic tensor of bond dimension `1` represents `W_N` for any
`N ≥ 2`. The vacuum amplitude `(a_0)^N = 0` forces `A^0 = 0`, and then the configuration
`|10⋯0⟩` receives amplitude `0` instead of `1`. -/
theorem not_isPeriodicWState_of_bondDim_one (A : MPSTensor 2 1) {N : ℕ} (hN : 2 ≤ N) :
    ¬ IsPeriodicWState A N := by
  intro h
  have htr := trace_pow_eq_zero_of_isPeriodicWState h
  have hentry : ∀ n : ℕ, (A 0 ^ n) 0 0 = (A 0 0 0) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => simp [pow_succ, Matrix.mul_apply, ih]
  have hA0 : A 0 = 0 := by
    have : A 0 0 0 = 0 := by
      rw [Matrix.trace_fin_one, hentry] at htr
      exact pow_eq_zero_iff (by omega) |>.mp htr
    ext i j
    fin_cases i; fin_cases j
    simpa using this
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  exact not_isPeriodicWState_of_pow_eq_zero (by rw [hA0, zero_pow (by omega)]) h

/-- Project result: a periodic tensor of bond dimension `D` representing `W_1, …, W_D`
has nilpotent zeroth matrix with `(A^0)^D = 0`. The vacuum amplitudes give
`tr((A^0)^k) = 0` for `1 ≤ k ≤ D`, so by the Newton–Girard identities the characteristic
polynomial of `A^0` is `X^D`, and Cayley–Hamilton applies. -/
theorem pow_eq_zero_of_isPeriodicWState {A : MPSTensor 2 D}
    (h : ∀ k, 1 ≤ k → k ≤ D → IsPeriodicWState A k) : A 0 ^ D = 0 := by
  have hchar : (A 0).charpoly = (0 : Matrix (Fin D) (Fin D) ℂ).charpoly := by
    refine Matrix.charpoly_eq_of_trace_pow_eq_of_le_card (A 0) 0 (fun k hk hkD => ?_)
    rw [trace_pow_eq_zero_of_isPeriodicWState (h k hk (by simpa using hkD)),
      zero_pow hk.ne', Matrix.trace_zero]
  have hCH := (A 0).aeval_self_charpoly
  rw [hchar, Matrix.charpoly_zero] at hCH
  simpa using hCH

/-- Project result: multi-length analogue of arXiv:2011.12127, line 2362. The review's
bound constrains `D` at a single length `N`; this result assumes representation at every
length `1, …, D`, and the single-length bound is open, see
`docs/paper-gaps/rmp_w_state_ti_bound.tex`. A periodic tensor of bond dimension `D` that
represents `W_1, …, W_D` represents `W_N` for no `N > D`. -/
theorem not_isPeriodicWState_of_lt {A : MPSTensor 2 D}
    (h : ∀ k, 1 ≤ k → k ≤ D → IsPeriodicWState A k) {N : ℕ} (hN : D < N) :
    ¬ IsPeriodicWState A N := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  refine not_isPeriodicWState_of_pow_eq_zero ?_
  obtain ⟨j, rfl⟩ : ∃ j, M = D + j := ⟨M - D, by omega⟩
  rw [pow_add, pow_eq_zero_of_isPeriodicWState h, zero_mul]

/-- Project result: multi-length analogue of arXiv:2011.12127, line 2362. It constrains
one tensor across the lengths `1, …, D + 1`, not `D` at a single length as the review does;
the single-length bound is open, see `docs/paper-gaps/rmp_w_state_ti_bound.tex`. For every
periodic tensor of bond dimension `D` there is a length `1 ≤ N ≤ D + 1` at which
it does not represent `W_N`. -/
theorem exists_not_isPeriodicWState_le (A : MPSTensor 2 D) :
    ∃ N, 1 ≤ N ∧ N ≤ D + 1 ∧ ¬ IsPeriodicWState A N := by
  by_contra hcon
  have hall : ∀ k, 1 ≤ k → k ≤ D + 1 → IsPeriodicWState A k :=
    fun k hk hkD => by_contra fun hfail => hcon ⟨k, hk, hkD, hfail⟩
  exact not_isPeriodicWState_of_lt (fun k hk hkD => hall k hk (by omega)) (Nat.lt_succ_self D)
    (hall (D + 1) (by omega) le_rfl)

/-- Project result, illustrating arXiv:2011.12127, line 2362: no single periodic tensor of
fixed bond dimension represents the W state on every number of sites `N ≥ 1`. -/
theorem not_forall_isPeriodicWState (A : MPSTensor 2 D) :
    ¬ ∀ N, 1 ≤ N → IsPeriodicWState A N := by
  intro h
  obtain ⟨N, hN, -, hfail⟩ := exists_not_isPeriodicWState_le A
  exact hfail (h N hN)

end MPSTensor
