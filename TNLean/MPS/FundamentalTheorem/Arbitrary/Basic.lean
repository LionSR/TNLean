/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.Words.TracePairing
import TNLean.MPS.FundamentalTheorem.Compression.UniquenessBlocks
import TNLean.MPS.FundamentalTheorem.Compression.LabelledFlag
import TNLean.MPS.Tensor.Defs
import TNLean.MPS.Tensor.Words.ScaledNormality
import QICLean.Spectral.Eigenvalue.WordAlgebra

/-!
# Word modules and word traces for the fundamental theorem for arbitrary tensors

Small facts about word-algebra modules and word traces used by several files of the
`Arbitrary` folder: promoting a letterwise compatible linear equivalence to a module equivalence,
the reformulation of equal states through word traces, and the consequences of gauge equivalence for
word traces.

## Main results

* `WordAlgebra.linearEquivOfLetter`: a complex-linear equivalence commuting with every letter is
  an equivalence of word-algebra modules (it extends `WordAlgebra.linearMapOfLetter`).
* `MPSTensor.sameMPV₂Pos_iff_forall_trace_evalWord_eq`: equal states at positive lengths are
  equal traces on nonempty words.
* `MPSTensor.IsGaugeRelated.trace_evalWord_eq`, `MPSTensor.IsGaugeRelated.sameMPV₂Pos`: gauge
  equivalent tensors have equal word traces and the same states.

## Proportional states with one scalar

For tensors `A`, `B` of any bond dimensions and a scalar `c`, the states satisfy
`V_N(A) = c ^ N • V_N(B)` at every positive length exactly when `A` and `c • B` have the same
states. The fundamental theorem for arbitrary tensors and its uniqueness half therefore apply
verbatim to the pair `(A, c • B)`.

An `N`-dependent constant `c_N` in place of `c ^ N` is not covered: there is a pair
with `V_N(A) = c_N • V_N(B)` for which no rescaling of `B` has the states of `A`.

### Main results

* `MPSTensor.sameMPV₂Pos_smul_iff`.
-/

section

namespace MPSTensor

open WordAlgebra

variable {d : ℕ}

/-- Same states at every positive length means equal traces on every nonempty word. -/
theorem sameMPV₂Pos_iff_forall_trace_evalWord_eq {D₁ D₂ : ℕ} {A : MPSTensor d D₁}
    {A' : MPSTensor d D₂} :
    SameMPV₂Pos A A' ↔ ∀ w : List (Fin d), w ≠ [] →
      Matrix.trace (Kraus.evalWord A w) = Matrix.trace (Kraus.evalWord A' w) := by
  refine ⟨fun h w hw => h.trace_evalWord w hw, fun h N hN σ => ?_⟩
  simp only [mpv_eq, coeff_eq]
  refine h _ fun h0 => ?_
  have := congrArg List.length h0
  simp at this
  omega

/-- Gauge equivalent tensors have equal word traces. -/
theorem IsGaugeRelated.trace_evalWord_eq {D₁ D₂ : ℕ} {A : MPSTensor d D₁}
    {A' : MPSTensor d D₂} (h : IsGaugeRelated A A') (w : List (Fin d)) :
    Matrix.trace (Kraus.evalWord A w) = Matrix.trace (Kraus.evalWord A' w) := by
  obtain ⟨e⟩ := nonempty_linearEquiv_wordModule_of_isGaugeRelated h
  rw [← traceWord_wordModule, ← traceWord_wordModule, traceWord_congr e]

/-- Gauge equivalent tensors have the same states. -/
theorem IsGaugeRelated.sameMPV₂Pos {D₁ D₂ : ℕ} {A : MPSTensor d D₁} {A' : MPSTensor d D₂}
    (h : IsGaugeRelated A A') : SameMPV₂Pos A A' :=
  sameMPV₂Pos_iff_forall_trace_evalWord_eq.2 fun w _ => h.trace_evalWord_eq w

end MPSTensor

end

section

namespace MPSTensor

variable {d : ℕ}

/-- **Proportional states with one scalar.** `A` and `c • B` have the same states at every positive
length exactly when every coefficient of `A` of length `N` is `c ^ N` times the corresponding
coefficient of `B`. -/
theorem sameMPV₂Pos_smul_iff {D₁ D₂ : ℕ} {A : MPSTensor d D₁} {B : MPSTensor d D₂} {c : ℂ} :
    SameMPV₂Pos A (c • B) ↔
      ∀ N, 0 < N → ∀ σ : Fin N → Fin d, mpv A σ = c ^ N * mpv B σ := by
  refine forall_congr' fun N => forall_congr' fun _ => forall_congr' fun σ => ?_
  rw [← mpv_smul c B σ]
  rfl

end MPSTensor

end
