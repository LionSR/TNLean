/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.Basic
import TNLean.Wielandt.WielandtBound
import TNLean.Algebra.TracePairing

/-!
# Fundamental Theorem with finite-length MPV agreement

This file strengthens the single-block Fundamental Theorem of MPS by weakening
the hypothesis from `SameMPV` (agreement for **all** system sizes) to
`SameMPVFrom N₀` (agreement for system sizes `N ≥ N₀`).

## Main results

* `SameMPVFrom` — definition of finite-length MPV agreement
* `sameMPV_of_sameMPVFrom_of_injective` — finite-length agreement implies
  full agreement for injective tensors
* `fundamentalTheorem_singleBlock_finiteLength` — the strengthened FT

## Mathematical content

For an injective MPS tensor `A` with bond dimension `D`, injectivity means
word products of length 1 already span `M_D(ℂ)`. For any word `w` of length
`n`, the traces `tr(evalWord A (w ++ w'))` for all extensions `w'` of length 1
determine `evalWord A w` via the trace pairing:

  `tr(evalWord A w * A i) = tr(evalWord A (w ++ [i]))` = MPV coefficient

So if `B` agrees with `A` on all MPV coefficients for system sizes `≥ N₀`,
then for any word `w` of length `n ≥ N₀ - 1`:

  `tr(evalWord A w * A i) = tr(evalWord B w * A i)` for all `i`

Since `{A i}` spans `M_D(ℂ)`, the trace pairing gives `evalWord A w = evalWord B w`.
Iterating downward, agreement propagates to all word lengths.

## Strengthening relative to the literature

The standard formulation of the FT (Pérez-García et al. 2007, Cirac et al. 2021)
requires either all-length agreement or works in the thermodynamic limit.
This formalization shows that a finite threshold suffices, making the theorem
applicable to fixed-size quantum systems.

## References

* [Pérez-García, Verstraete, Wolf, Cirac, *Matrix Product State Representations*,
  arXiv:quant-ph/0608197]
* [Sanz, Pérez-García, Wolf, Cirac, *A quantum version of Wielandt's inequality*,
  arXiv:0909.5347]
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-! ## Definition: finite-length MPV agreement -/

/-- Two tensors generate the same MPV family **from system size `N₀` onwards**:
they produce the same coefficient for every basis configuration `σ` of length
`N ≥ N₀`.

This is strictly weaker than `SameMPV`, which requires agreement for all `N`. -/
def SameMPVFrom (N₀ : ℕ) (A B : MPSTensor d D) : Prop :=
  ∀ (N : ℕ), N₀ ≤ N → ∀ (σ : Fin N → Fin d), mpv A σ = mpv B σ

/-- `SameMPV` implies `SameMPVFrom N₀` for any `N₀`. -/
theorem SameMPV.sameMPVFrom {A B : MPSTensor d D} (h : SameMPV A B) (N₀ : ℕ) :
    SameMPVFrom N₀ A B :=
  fun N _ σ => h N σ

/-- `SameMPVFrom 0` is equivalent to `SameMPV`. -/
theorem sameMPVFrom_zero_iff {A B : MPSTensor d D} :
    SameMPVFrom 0 A B ↔ SameMPV A B :=
  ⟨fun h N σ => h N (Nat.zero_le N) σ, fun h => h.sameMPVFrom 0⟩

/-- Monotonicity: `SameMPVFrom N₀` implies `SameMPVFrom N₁` for `N₀ ≤ N₁`. -/
theorem SameMPVFrom.mono {A B : MPSTensor d D} {N₀ N₁ : ℕ}
    (h : SameMPVFrom N₀ A B) (hle : N₀ ≤ N₁) :
    SameMPVFrom N₁ A B :=
  fun N hN σ => h N (le_trans hle hN) σ

/-! ## Trace agreement on word extensions -/

/-- If `SameMPVFrom N₀ A B`, then traces of word evaluations agree for words
of length `≥ N₀`. -/
lemma SameMPVFrom.trace_evalWord_of_length_ge
    {A B : MPSTensor d D} {N₀ : ℕ}
    (h : SameMPVFrom N₀ A B) {w : List (Fin d)} (hw : N₀ ≤ w.length) :
    Matrix.trace (evalWord A w) = Matrix.trace (evalWord B w) := by
  simpa [mpv, coeff, List.ofFn_get] using h w.length hw w.get

/-- Key downward-propagation lemma: if traces of `(n+1)`-letter words agree for
both `A` and `B`, and `A` is injective, then `evalWord` at `n`-letter words
already agrees.

**Proof idea**: For a word `w` of length `n`, the function
`i ↦ tr(evalWord A (w ++ [i]))` determines `evalWord A w` via the
trace pairing against `{A i}`, which spans `M_D(ℂ)` by injectivity. -/
private lemma evalWord_eq_of_trace_ext_eq [NeZero D]
    {A B : MPSTensor d D}
    (hA : IsInjective A) (w : List (Fin d))
    (hext : ∀ i : Fin d,
      Matrix.trace (evalWord A (w ++ [i])) = Matrix.trace (evalWord B (w ++ [i]))) :
    evalWord A w = evalWord B w := by
  -- evalWord A (w ++ [i]) = evalWord A w * A i, so
  -- tr(evalWord A w * A i) = tr(evalWord B w * A i) for all i.
  have htrace : ∀ i : Fin d,
      Matrix.trace (evalWord A w * A i) = Matrix.trace (evalWord B w * A i) := by
    intro i
    rw [← evalWord_append]; rw [← evalWord_append (A := B)]
    exact hext i
  -- The difference M := evalWord A w - evalWord B w satisfies
  -- tr(M * A i) = 0 for all i.
  set M := evalWord A w - evalWord B w with hM_def
  suffices M = 0 by
    have := sub_eq_zero.mp this
    exact this
  apply trace_mul_right_eq_zero
  intro N
  -- N is in span of {A i}, so it suffices to check generators.
  have hspan := hA.span_eq_top
  rw [eq_top_iff] at hspan
  -- Use linearity: tr(M * ·) is a linear map that vanishes on generators.
  have hlin : ∀ X ∈ Set.range A, Matrix.trace (M * X) = 0 := by
    rintro _ ⟨i, rfl⟩
    simp [hM_def, Matrix.mul_sub, Matrix.trace_sub, htrace i, sub_self]
  have := Submodule.span_le.mpr hlin
  rw [hspan] at this
  exact this (Submodule.mem_top : N ∈ ⊤)

/-! ## Main results -/

/-- **Finite-length agreement implies full word evaluation agreement** for
injective tensors.

If `A` is injective and `A`, `B` agree on all MPV coefficients for system sizes
`N ≥ N₀`, then `evalWord A w = evalWord B w` for **every** word `w`. -/
theorem evalWord_eq_of_sameMPVFrom_of_injective [NeZero D]
    {A B : MPSTensor d D}
    (hA : IsInjective A)
    {N₀ : ℕ} (hFrom : SameMPVFrom N₀ A B) :
    ∀ w : List (Fin d), evalWord A w = evalWord B w := by
  -- We prove this by strong induction on (N₀ - w.length).
  -- For long words (length ≥ N₀), the agreement is given.
  -- For shorter words, we use evalWord_eq_of_trace_ext_eq to propagate downward.
  intro w
  -- Induction on how far below N₀ the word length is.
  -- Base case: if w.length ≥ N₀, then coeff agreement gives evalWord agreement.
  -- Step: from (n+1)-level agreement, derive n-level agreement.
  suffices ∀ n : ℕ, ∀ w : List (Fin d), w.length = n → evalWord A w = evalWord B w from
    this w.length w rfl
  intro n
  -- We do strong downward induction. More precisely, by strong induction on
  -- the "deficit" (N₀ - n) when n < N₀.
  induction n using Nat.strong_rec_on with
  | _ n ih => ?_
  intro w hw_len
  by_cases hn : N₀ ≤ n
  · -- Long word: agreement follows from SameMPVFrom via trace.
    -- Actually we need evalWord equality, not just trace equality.
    -- For words of length n ≥ N₀, we use the extension trick:
    -- tr(evalWord A (w ++ [i])) = tr(evalWord B (w ++ [i])) since |w ++ [i]| = n+1 ≥ N₀.
    -- This determines evalWord A w = evalWord B w by trace pairing (since A injective).
    exact evalWord_eq_of_trace_ext_eq hA w (fun i => by
      apply hFrom.trace_evalWord_of_length_ge
      simp [hw_len]; omega)
  · -- Short word: n < N₀.
    push_neg at hn
    -- Use the extension trick: for each i, w ++ [i] has length n + 1.
    -- By the induction hypothesis applied to n + 1 (which is closer to N₀),
    -- evalWord A (w ++ [i]) = evalWord B (w ++ [i]).
    -- Since evalWord A (w ++ [i]) = evalWord A w * A i, the trace pairing
    -- gives evalWord A w = evalWord B w.
    exact evalWord_eq_of_trace_ext_eq hA w (fun i => by
      have h_ext := ih (n + 1) (by omega) (w ++ [i]) (by simp [hw_len])
      simp [evalWord_append] at h_ext ⊢
      rw [h_ext])

/-- **Finite-length agreement implies full agreement** for injective tensors. -/
theorem sameMPV_of_sameMPVFrom_of_injective [NeZero D]
    {A B : MPSTensor d D}
    (hA : IsInjective A)
    {N₀ : ℕ} (hFrom : SameMPVFrom N₀ A B) :
    SameMPV A B := by
  intro N σ
  simp only [mpv, coeff]
  rw [evalWord_eq_of_sameMPVFrom_of_injective hA hFrom]

/-- **Strengthened single-block Fundamental Theorem (finite-length version).**

If `A` is injective and `A`, `B` agree on all MPV coefficients for system sizes
`N ≥ N₀` (for **any** threshold `N₀`), then they are gauge equivalent.

This strengthens `fundamentalTheorem_singleBlock` by weakening the hypothesis
from `SameMPV` (all-length agreement) to `SameMPVFrom N₀` (finite-length
agreement). The threshold `N₀` can be **any** natural number — there is no
lower bound required, because injectivity allows downward propagation via
the trace pairing.

**Literature comparison**: The standard FT requires all-length agreement.
This version shows that any finite threshold suffices for injective tensors. -/
theorem fundamentalTheorem_singleBlock_finiteLength [NeZero D]
    {A B : MPSTensor d D}
    (hA : IsInjective A)
    {N₀ : ℕ} (hFrom : SameMPVFrom N₀ A B) :
    GaugeEquiv A B :=
  fundamentalTheorem_singleBlock hA (sameMPV_of_sameMPVFrom_of_injective hA hFrom)

/-- For injective tensors, finite-length MPV agreement (from any threshold) is
equivalent to gauge equivalence. -/
theorem sameMPVFrom_iff_gaugeEquiv_of_injective [NeZero D]
    {A B : MPSTensor d D} (hA : IsInjective A) {N₀ : ℕ} :
    SameMPVFrom N₀ A B ↔ GaugeEquiv A B := by
  constructor
  · exact fundamentalTheorem_singleBlock_finiteLength hA
  · intro hGE
    exact (GaugeEquiv.sameMPV hGE).sameMPVFrom _

end MPSTensor
