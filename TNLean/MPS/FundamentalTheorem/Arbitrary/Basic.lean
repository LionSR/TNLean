/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.TracePairing
import TNLean.MPS.FundamentalTheorem.Arbitrary.WordModuleGauge
import TNLean.MPS.FundamentalTheorem.Reduction.UniquenessFlag

/-!
# Word modules and word traces for the fundamental theorem for arbitrary tensors

Small facts about word-algebra modules and word traces used by several files of the
`Arbitrary` folder: promoting a letterwise compatible linear equivalence to a module equivalence,
the reformulation of equal states through word traces, vanishing of word traces on a module on
which every letter acts as zero, and the consequences of gauge equivalence for word traces.

## Main results

* `WordAlgebra.linearEquivOfLetter`: a complex-linear equivalence commuting with every letter is
  an equivalence of word-algebra modules (it extends `WordAlgebra.linearMapOfLetter`).
* `WordAlgebra.traceWord_eq_zero_of_forall_smul_eq_zero`: word traces vanish when every letter
  acts as zero.
* `MPSTensor.sameMPV₂Pos_iff_forall_trace_evalWord_eq`: equal states at positive lengths are
  equal traces on nonempty words.
* `MPSTensor.IsGaugeRelated.trace_evalWord_eq`, `MPSTensor.IsGaugeRelated.sameMPV₂Pos`: gauge
  equivalent tensors have equal word traces and the same states.
-/

namespace WordAlgebra

variable {d : ℕ} {M N : Type*} [AddCommGroup M] [Module ℂ M] [Module (WordAlgebra d) M]
  [IsScalarTower ℂ (WordAlgebra d) M] [AddCommGroup N] [Module ℂ N] [Module (WordAlgebra d) N]
  [IsScalarTower ℂ (WordAlgebra d) N]

/-- A complex-linear equivalence commuting with every letter is an equivalence of word-algebra
modules. -/
noncomputable def linearEquivOfLetter (e : M ≃ₗ[ℂ] N)
    (h : ∀ (i : Fin d) (x : M), e ((ofWord [i] : WordAlgebra d) • x) = (ofWord [i]) • e x) :
    M ≃ₗ[WordAlgebra d] N :=
  { linearMapOfLetter e.toLinearMap h with
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv }

@[simp]
theorem linearEquivOfLetter_apply (e : M ≃ₗ[ℂ] N)
    (h : ∀ (i : Fin d) (x : M), e ((ofWord [i] : WordAlgebra d) • x) = (ofWord [i]) • e x)
    (x : M) : linearEquivOfLetter e h x = e x :=
  rfl

/-- On a module on which every letter acts as zero, every nonempty word has trace zero. This is
the case of words of length one in `WordAlgebra.traceWord_eq_zero_of_forall_ofWord_smul_eq_zero`,
with a direct proof. -/
theorem traceWord_eq_zero_of_forall_smul_eq_zero
    (h : ∀ (i : Fin d) (x : N), (ofWord [i] : WordAlgebra d) • x = 0) {w : List (Fin d)}
    (hw : w ≠ []) : traceWord N w = 0 := by
  obtain ⟨i, w, rfl⟩ := List.exists_cons_of_ne_nil hw
  have : Algebra.lsmul ℂ ℂ N (ofWord (i :: w)) = 0 := by
    ext q
    rw [ofWord_cons, map_mul, Module.End.mul_apply, Algebra.lsmul_apply, Algebra.lsmul_apply, h,
      LinearMap.zero_apply]
  rw [traceWord_def, this, map_zero]

end WordAlgebra

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
