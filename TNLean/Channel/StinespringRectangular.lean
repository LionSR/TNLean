/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.KrausRectangular
import TNLean.Channel.Stinespring

/-!
# Stinespring representation for rectangular completely positive maps

This file proves the Stinespring representation theorem in the shape stated in
Wolf, *Quantum Channels & Operations*, Chapter 2,
`Notes/WolfNoteTexSource/ch02_representations.tex`, line 322:

> Let `T : M_d → M_{d'}` be a completely positive linear map. Then for every
> `r ≥ rank(τ)` there is a `V : ℂ^d → ℂ^{d'} ⊗ ℂ^r` such that
> `T*(A) = V†(A ⊗ 𝟙_r)V` for all `A ∈ M_{d'}`.
> `V` is an isometry (that is, `V†V = 𝟙_d`) if and only if `T` is trace
> preserving.

Here `τ` is the Choi matrix of `T` and `T*` is the dual map, characterized by
the trace pairing `tr[T*(A)X] = tr[A T(X)]` (Wolf, Equation (2.3)).

## Main results

* `ChoiRectangular.exists_stinespringV_of_isKrausCP` — Wolf's theorem: for every
  ancilla dimension `r` at least the Choi rank there is a single `V` realizing
  the Heisenberg identity `T*(A) = V†(A ⊗ 𝟙_r)V`, and this `V` is an isometry
  exactly when `T` is trace preserving.
* `ChoiRectangular.exists_stinespringV_traceAdjointMap_of_isKrausCP` — the same
  statement with `T*` the trace-pairing adjoint `Matrix.traceAdjointMap T`, so
  that nothing at all is assumed about `T*`.
* `ChoiRectangular.exists_stinespringV_choiRank_of_isKrausCP` and
  `ChoiRectangular.exists_stinespringV_traceAdjointMap_choiRank_of_isKrausCP` —
  the dilation at the Choi-rank ancilla dimension `r = rank(τ)`.

## Design notes

The dual map `T*` enters the statement as a linear map satisfying the trace
pairing that defines it; the pairing determines `T*` uniquely, so this is
Wolf's `T*` and not an additional assumption on `T`.

The dilation matrix is `V = Σⱼ Kⱼ ⊗ |j⟩` built by `stinespringV` from a Kraus
family of `T` with exactly `r` operators, obtained by zero-padding a minimal
family of `rank(τ)` operators. The square statements
`exists_stinespring_dilation` and `exists_stinespring_isometry_of_cptp` in
`TNLean/Channel/Stinespring.lean` remain separate and are weaker: their ancilla
dimension is existentially quantified, whereas the theorems here hold for an
arbitrary `r` at least the Choi rank.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 2,
  Theorem 2.2][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix Finset BigOperators

namespace ChoiRectangular

variable {d d' : ℕ}

/-- **Stinespring representation** (Wolf, Chapter 2, Theorem 2.2,
Equation (2.11); `Notes/WolfNoteTexSource/ch02_representations.tex`, line 322).

Let `T : M_d → M_{d'}` be completely positive with dual `T*`, characterized by
the trace pairing `tr[T*(A)X] = tr[A T(X)]`. Then for **every** ancilla
dimension `r ≥ rank(τ)`, where `τ` is the Choi matrix of `T`, there is a
`V : ℂ^d → ℂ^{d'} ⊗ ℂ^r` with

  `T*(A) = V†(A ⊗ 𝟙_r)V` for all `A ∈ M_{d'}`,

and `V` is an isometry, `V†V = 𝟙_d`, if and only if `T` is trace preserving.

The dilation matrix is `V = Σⱼ Kⱼ ⊗ |j⟩` for a Kraus family `{Kⱼ}` of `T` with
exactly `r` operators, and `π(A) = A ⊗ 𝟙_r` is `stinespringPi`. -/
theorem exists_stinespringV_of_isKrausCP
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ}
    {Tstar : Matrix (Fin d') (Fin d') ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ}
    (hT : IsKrausCP T)
    (hTstar : ∀ (A : Matrix (Fin d') (Fin d') ℂ) (X : Matrix (Fin d) (Fin d) ℂ),
      (Tstar A * X).trace = (A * T X).trace)
    {r : ℕ} (hr : Channel.choiRank T ≤ r) :
    ∃ V : Matrix (Fin d' × Fin r) (Fin d) ℂ,
      (∀ A : Matrix (Fin d') (Fin d') ℂ, Tstar A = Vᴴ * stinespringPi (r := r) A * V) ∧
      (Vᴴ * V = 1 ↔ ∀ X : Matrix (Fin d) (Fin d) ℂ, (T X).trace = X.trace) := by
  -- A minimal Kraus family has `rank(τ)` operators; zero-pad it to `r` operators.
  obtain ⟨K, hK⟩ := Channel.hasKrausCard_mono (Channel.hasKrausCard_choiRank_of_cp hT) hr
  refine ⟨stinespringV K, fun A => ?_, ?_⟩
  · -- The trace pairing identifies `T*(A)` with the Kraus form `Σⱼ Kⱼ†AKⱼ`.
    have hdual : Tstar A = ∑ j : Fin r, (K j)ᴴ * A * K j := by
      refine Matrix.ext_iff_trace_mul_right.2 fun X => ?_
      rw [hTstar A X, hK X, Finset.mul_sum, Finset.sum_mul, Matrix.trace_sum,
        Matrix.trace_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      calc (A * (K j * X * (K j)ᴴ)).trace
          = (A * K j * X * (K j)ᴴ).trace := by simp [Matrix.mul_assoc]
        _ = ((K j)ᴴ * (A * K j * X)).trace := Matrix.trace_mul_comm _ _
        _ = ((K j)ᴴ * A * K j * X).trace := by simp [Matrix.mul_assoc]
    rw [hdual, ← stinespring_dual_representation K A]
    rfl
  · -- `V†V = Σⱼ Kⱼ†Kⱼ`, which is `𝟙` exactly for trace-preserving `T`.
    rw [stinespringV_conjTranspose_mul]
    exact (kraus_tp_iff_sum_conjTranspose_mul K T hK).symm

/-- **Stinespring representation for the trace-pairing adjoint** (Wolf,
Chapter 2, Theorem 2.2; `Notes/WolfNoteTexSource/ch02_representations.tex`,
line 322).

The dual map is `Matrix.traceAdjointMap T`, the unique map satisfying the
trace pairing `tr[T*(A)X] = tr[A T(X)]`, so this form of the theorem carries
no hypothesis beyond complete positivity of `T` and `r ≥ rank(τ)`. -/
theorem exists_stinespringV_traceAdjointMap_of_isKrausCP
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ}
    (hT : IsKrausCP T) {r : ℕ} (hr : Channel.choiRank T ≤ r) :
    ∃ V : Matrix (Fin d' × Fin r) (Fin d) ℂ,
      (∀ A : Matrix (Fin d') (Fin d') ℂ,
        Matrix.traceAdjointMap T A = Vᴴ * stinespringPi (r := r) A * V) ∧
      (Vᴴ * V = 1 ↔ ∀ X : Matrix (Fin d) (Fin d) ℂ, (T X).trace = X.trace) :=
  exists_stinespringV_of_isKrausCP hT (Matrix.trace_traceAdjointMap_mul T) hr

/-- **Stinespring dilation at the Choi-rank ancilla dimension** (Wolf,
Chapter 2, Theorem 2.2): the case `r = rank(τ)` of
`exists_stinespringV_of_isKrausCP`. A dilation with this ancilla dimension is
called minimal.

That no ancilla dimension below `rank(τ)` admits a dilation is not asserted
here: it would need a Kraus family of `r` operators extracted from an arbitrary
`V`, and Wolf's Theorem 2.2 states only the existence for `r ≥ rank(τ)`. -/
theorem exists_stinespringV_choiRank_of_isKrausCP
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ}
    {Tstar : Matrix (Fin d') (Fin d') ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ}
    (hT : IsKrausCP T)
    (hTstar : ∀ (A : Matrix (Fin d') (Fin d') ℂ) (X : Matrix (Fin d) (Fin d) ℂ),
      (Tstar A * X).trace = (A * T X).trace) :
    ∃ V : Matrix (Fin d' × Fin (Channel.choiRank T)) (Fin d) ℂ,
      (∀ A : Matrix (Fin d') (Fin d') ℂ,
        Tstar A = Vᴴ * stinespringPi (r := Channel.choiRank T) A * V) ∧
      (Vᴴ * V = 1 ↔ ∀ X : Matrix (Fin d) (Fin d) ℂ, (T X).trace = X.trace) :=
  exists_stinespringV_of_isKrausCP hT hTstar le_rfl

/-- **Stinespring dilation at the Choi-rank ancilla dimension, trace-pairing
adjoint form** (Wolf, Chapter 2, Theorem 2.2): the case `r = rank(τ)` of
`exists_stinespringV_traceAdjointMap_of_isKrausCP`, so that complete positivity
of `T` is the only hypothesis. -/
theorem exists_stinespringV_traceAdjointMap_choiRank_of_isKrausCP
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ}
    (hT : IsKrausCP T) :
    ∃ V : Matrix (Fin d' × Fin (Channel.choiRank T)) (Fin d) ℂ,
      (∀ A : Matrix (Fin d') (Fin d') ℂ,
        Matrix.traceAdjointMap T A = Vᴴ * stinespringPi (r := Channel.choiRank T) A * V) ∧
      (Vᴴ * V = 1 ↔ ∀ X : Matrix (Fin d) (Fin d) ℂ, (T X).trace = X.trace) :=
  exists_stinespringV_traceAdjointMap_of_isKrausCP hT le_rfl

end ChoiRectangular
