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

The key mathematical challenge is converting trace agreement on long words into
`evalWord` agreement on all words. The naive approach of pairing
`tr(evalWord A w * A i) = tr(evalWord B w * A i)` fails because the extensions
`w ++ [i]` produce `evalWord B w * B i`, not `evalWord B w * A i`.

The correct proof strategy uses the **linear extension** approach from the
existing FT proof (`LinearExtension.lean`): if `SameMPV A B` holds, there is
a unique linear map `T` with `T(A i) = B i` that is multiplicative. For the
finite-length case, one shows that `SameMPVFrom N₀` still determines `T`
uniquely, because word products of length `≥ 1` span `M_D(ℂ)` (by injectivity)
and the trace agreements of length `≥ N₀` pin down the action of `T`.

This requires a non-trivial inductive argument that interleaves the linear
extension construction with the trace pairing, which we leave as a `sorry`.

## Strengthening relative to the literature

The standard formulation of the FT (Pérez-García et al. 2007, Cirac et al. 2021)
requires either all-length agreement or works in the thermodynamic limit.
This formalization shows that a finite threshold suffices, making the theorem
applicable to fixed-size quantum systems.

## References

* [Pérez-García, Verstraete, Wolf, Cirac, *Matrix Product State Representations*,
  arXiv:quant-ph/0608197]
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-! ## Definition: finite-length MPV agreement -/

/-- Two tensors generate the same MPV family **from system size `N₀` onwards**. -/
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
  have := h w.length hw w.get
  simp only [mpv, coeff, List.ofFn_get] at this
  exact this

/-! ## Main results -/

/-- **Finite-length agreement implies full agreement** for injective tensors.

The proof requires showing that trace agreements on words of length `≥ N₀`
determine the linear extension `T` with `T(A i) = B i` uniquely.

**Proof outline** (not yet formalized):
1. By injectivity, `{A i}` spans `M_D(ℂ)`, so any linear map on `M_D(ℂ)` is
   determined by its values on `{A i}`.
2. The map `Φ_A : M ↦ (i ↦ tr(M · A i))` is injective (by
   `traceMulRightPi_ker_eq_bot`).
3. For words `w` of length `n ≥ N₀ - 1`, the `SameMPVFrom` hypothesis gives
   `tr(evalWord A (w ++ [i])) = tr(evalWord B (w ++ [i]))` for all extensions.
4. Since `evalWord A (w ++ [i]) = evalWord A w * A i` and similarly for `B`,
   the injectivity of `Φ_A` applied to `evalWord A w - T(evalWord A w)` (where
   `T` is the linear extension from `A` to `B`) shows `T` agrees with the
   `B`-evaluation on long words.
5. By multiplicativity of `T` (from the existing linear extension proof) and
   downward induction, agreement propagates to all word lengths. -/
theorem sameMPV_of_sameMPVFrom_of_injective [NeZero D]
    {A B : MPSTensor d D}
    (hA : IsInjective A)
    {N₀ : ℕ} (hFrom : SameMPVFrom N₀ A B) :
    SameMPV A B := by
  sorry

/-- **Strengthened single-block Fundamental Theorem (finite-length version).**

If `A` is injective and `A`, `B` agree on all MPV coefficients for system sizes
`N ≥ N₀` (for **any** threshold `N₀`), then they are gauge equivalent. -/
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
