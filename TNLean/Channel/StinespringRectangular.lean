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

> Let \(T : M_d \to M_{d'}\) be a completely positive linear map. Then for every
> \(r \ge \operatorname{rank}(\tau)\) there is a
> \(V : \mathbb C^d \to \mathbb C^{d'} \otimes \mathbb C^r\) such that
> \(T^*(A) = V^\dagger (A \otimes \mathbb 1_r) V\) for all \(A \in M_{d'}\).
> \(V\) is an isometry (that is, \(V^\dagger V = \mathbb 1_d\)) if and only if
> \(T\) is trace preserving.

Here \(\tau\) is the Choi matrix of \(T\), and the dual \(T^*\) is the
trace-pairing adjoint `Matrix.traceAdjointMap T`, characterized by the identity
\(\operatorname{tr}[T^*(A)X] = \operatorname{tr}[A\,T(X)]\) (Wolf, Equation
(2.3)); that identity is `Matrix.trace_traceAdjointMap_mul`, so the theorems
below carry no hypothesis on the dual beyond complete positivity of \(T\) and
the lower bound on the ancilla dimension.

## Main results

* `ChoiRectangular.exists_stinespringV_of_isKrausCP` — Wolf's theorem: for every
  ancilla dimension \(r\) at least the Choi rank there is a single \(V\)
  realizing the Heisenberg identity \(T^*(A) = V^\dagger(A \otimes \mathbb 1_r)V\)
  for every observable \(A\), and this \(V\) is an isometry exactly when \(T\)
  is trace preserving.
* `ChoiRectangular.exists_stinespringV_choiRank_of_isKrausCP` — the case
  \(r = \operatorname{rank}(\tau)\) of the same statement.
* `ChoiRectangular.exists_stinespringV_pairing_of_isKrausCP` and
  `ChoiRectangular.exists_stinespringV_pairing_choiRank_of_isKrausCP` — the
  same two statements for a dual map supplied through the trace pairing that
  characterizes it.
* `ChoiRectangular.choiRank_le_of_stinespring_dual_representation` — the
  converse bound: an ancilla dimension \(r\) that admits a dilation of \(T\)
  satisfies \(\operatorname{rank}(\tau) \le r\). Together with the case
  \(r = \operatorname{rank}(\tau)\) above, the Choi rank is the least
  admissible ancilla dimension; dilations with \(r = \operatorname{rank}(\tau)\)
  are minimal in the sense of the discussion following Wolf's Theorem 2.2
  (`Notes/WolfNoteTexSource/ch02_representations.tex`, lines 346–351).

## Design notes

The dual map is the canonical trace-pairing adjoint `Matrix.traceAdjointMap T`;
the theorems named `_pairing_` transport the same conclusion to any linear map
satisfying the trace pairing, which determines the dual uniquely.

The dilation matrix is \(V = \sum_j K_j \otimes |j\rangle\), built by
`stinespringV` from a Kraus family of \(T\) with exactly \(r\) operators,
obtained by zero-padding a minimal family of \(\operatorname{rank}(\tau)\)
operators. The square statements `exists_stinespring_dilation` and
`exists_stinespring_isometry_of_cptp` in `TNLean/Channel/Stinespring.lean`
remain separate and are weaker: their ancilla dimension is existentially
quantified, whereas the theorems here hold for an arbitrary \(r\) at least the
Choi rank.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 2,
  Theorem 2.2][Wolf2012QChannels]
-/

open scoped Matrix
open BigOperators

namespace ChoiRectangular

variable {d d' : ℕ}

/-- **Stinespring representation** (Wolf, Chapter 2, Theorem 2.2,
Equation (2.11); `Notes/WolfNoteTexSource/ch02_representations.tex`, line 322).

Let \(T : M_d \to M_{d'}\) be completely positive, with dual \(T^*\) the
trace-pairing adjoint of \(T\). Then for **every** ancilla dimension
\(r \ge \operatorname{rank}(\tau)\), where \(\tau\) is the Choi matrix of
\(T\), there is a \(V : \mathbb C^d \to \mathbb C^{d'} \otimes \mathbb C^r\)
with \(T^*(A) = V^\dagger(A \otimes \mathbb 1_r)V\) for every
\(A \in M_{d'}\), and \(V\) is an isometry, \(V^\dagger V = \mathbb 1_d\), if
and only if \(T\) is trace preserving.

The dilation matrix is \(V = \sum_j K_j \otimes |j\rangle\) for a Kraus family
\(\{K_j\}_{j=0}^{r-1}\) of \(T\) with exactly \(r\) operators, and
\(\pi(A) = A \otimes \mathbb 1_r\) is `stinespringPi`. -/
theorem exists_stinespringV_of_isKrausCP
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ}
    (hT : IsKrausCP T) {r : ℕ} (hr : Channel.choiRank T ≤ r) :
    ∃ V : Matrix (Fin d' × Fin r) (Fin d) ℂ,
      (∀ A : Matrix (Fin d') (Fin d') ℂ,
        Matrix.traceAdjointMap T A = Vᴴ * stinespringPi (r := r) A * V) ∧
      (Vᴴ * V = 1 ↔ ∀ X : Matrix (Fin d) (Fin d) ℂ, (T X).trace = X.trace) := by
  -- A minimal Kraus family has `rank(τ)` operators; zero-pad it to `r` operators.
  obtain ⟨K, hK⟩ := Channel.hasKrausCard_mono (Channel.hasKrausCard_choiRank_of_cp hT) hr
  refine ⟨stinespringV K, fun A => ?_, ?_⟩
  · -- The trace pairing identifies the adjoint `T*(A)` with the Kraus form
    -- `∑ⱼ Kⱼ†AKⱼ`.
    have hdual : Matrix.traceAdjointMap T A = ∑ j : Fin r, (K j)ᴴ * A * K j := by
      refine Matrix.ext_iff_trace_mul_right.2 fun X => ?_
      rw [Matrix.trace_traceAdjointMap_mul T A X, hK X, Finset.mul_sum, Finset.sum_mul,
        Matrix.trace_sum, Matrix.trace_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      calc (A * (K j * X * (K j)ᴴ)).trace
          = (A * K j * X * (K j)ᴴ).trace := by simp [Matrix.mul_assoc]
        _ = ((K j)ᴴ * (A * K j * X)).trace := Matrix.trace_mul_comm _ _
        _ = ((K j)ᴴ * A * K j * X).trace := by simp [Matrix.mul_assoc]
    rw [hdual, ← stinespring_dual_representation K A]
    rfl
  · -- `V†V = ∑ⱼ Kⱼ†Kⱼ`, which is `𝟙` exactly for trace-preserving `T`.
    rw [stinespringV_conjTranspose_mul]
    exact (kraus_tp_iff_sum_conjTranspose_mul K T hK).symm

/-- **Stinespring dilation at the Choi-rank ancilla dimension** (Wolf,
Chapter 2, Theorem 2.2): the case \(r = \operatorname{rank}(\tau)\) of
`exists_stinespringV_of_isKrausCP`, so that complete positivity of \(T\) is the
only hypothesis.

A dilation with this ancilla dimension is called minimal, and by
`choiRank_le_of_stinespring_dual_representation` the Choi rank is the least
admissible ancilla dimension. -/
theorem exists_stinespringV_choiRank_of_isKrausCP
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ}
    (hT : IsKrausCP T) :
    ∃ V : Matrix (Fin d' × Fin (Channel.choiRank T)) (Fin d) ℂ,
      (∀ A : Matrix (Fin d') (Fin d') ℂ,
        Matrix.traceAdjointMap T A =
          Vᴴ * stinespringPi (r := Channel.choiRank T) A * V) ∧
      (Vᴴ * V = 1 ↔ ∀ X : Matrix (Fin d) (Fin d) ℂ, (T X).trace = X.trace) :=
  exists_stinespringV_of_isKrausCP hT le_rfl

/-- **Least dilation dimension** (Wolf, Chapter 2, discussion after Theorem 2.2,
`Notes/WolfNoteTexSource/ch02_representations.tex`, lines 346–351): in the same
way in which \(V\) is assembled from Kraus operators, the operators
\(K_j = (\mathbb 1_{d'} \otimes \langle j|)V\) are recovered from the blocks of
\(V\). Any dilation with ancilla dimension \(r\) therefore exhibits an
\(r\)-operator Kraus family of \(T\), forcing
\(\operatorname{rank}(\tau) \le r\).

No complete positivity or trace-preservation hypothesis is needed: the
dilation identity itself produces the Kraus family, for the trace-pairing
adjoint of \(T\). -/
theorem choiRank_le_of_stinespring_dual_representation
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ} {r : ℕ}
    (V : Matrix (Fin d' × Fin r) (Fin d) ℂ)
    (hV : ∀ A : Matrix (Fin d') (Fin d') ℂ,
      Matrix.traceAdjointMap T A = Vᴴ * stinespringPi (r := r) A * V) :
    Channel.choiRank T ≤ r := by
  classical
  -- The blocks `K j = (𝟙 ⊗ ⟨j|) V` of the dilation form a Kraus family of `T`.
  obtain ⟨K, hstV⟩ : ∃ K : Fin r → Matrix (Fin d') (Fin d) ℂ, stinespringV K = V :=
    ⟨fun j i k => V (i, j) k, by ext p k; rcases p with ⟨i, j⟩; rfl⟩
  have hdual : ∀ A : Matrix (Fin d') (Fin d') ℂ,
      Matrix.traceAdjointMap T A = ∑ j : Fin r, (K j)ᴴ * A * K j := by
    intro A
    rw [hV A, ← hstV, ← stinespring_dual_representation K A]
    rfl
  refine Channel.choiRank_le_of_hasKrausCard ⟨K, fun X => ?_⟩
  -- Nondegeneracy of the trace pairing turns the dilation identity into the
  -- Schrödinger-form Kraus identity `T X = ∑ⱼ Kⱼ X Kⱼ†`.
  refine Matrix.ext_iff_trace_mul_right.2 fun A => ?_
  calc (T X * A).trace
      = (A * T X).trace := Matrix.trace_mul_comm _ _
    _ = (Matrix.traceAdjointMap T A * X).trace :=
        (Matrix.trace_traceAdjointMap_mul T A X).symm
    _ = ((∑ j : Fin r, (K j)ᴴ * A * K j) * X).trace := by rw [hdual A]
    _ = (A * ∑ j : Fin r, K j * X * (K j)ᴴ).trace := by
        rw [Finset.mul_sum, Finset.sum_mul, Matrix.trace_sum, Matrix.trace_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        calc ((K j)ᴴ * A * K j * X).trace
            = ((K j)ᴴ * (A * K j * X)).trace := by simp [Matrix.mul_assoc]
          _ = (A * K j * X * (K j)ᴴ).trace := Matrix.trace_mul_comm _ _
          _ = (A * (K j * X * (K j)ᴴ)).trace := by simp [Matrix.mul_assoc]
    _ = ((∑ j : Fin r, K j * X * (K j)ᴴ) * A).trace := Matrix.trace_mul_comm _ _

/-- **Stinespring representation for a dual supplied by the trace pairing**
(Wolf, Chapter 2, Theorem 2.2; `Notes/WolfNoteTexSource/ch02_representations.tex`,
line 322): the variant of `exists_stinespringV_of_isKrausCP` in which the dual
map is an arbitrary linear map satisfying the trace pairing
\(\operatorname{tr}[T^*(A)X] = \operatorname{tr}[A\,T(X)]\) that characterizes
the dual (Wolf, Equation (2.3)). The pairing determines the dual uniquely, so
this is the same theorem, made usable when a dual map is already in hand. -/
theorem exists_stinespringV_pairing_of_isKrausCP
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ}
    {Tstar : Matrix (Fin d') (Fin d') ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ}
    (hT : IsKrausCP T)
    (hTstar : ∀ (A : Matrix (Fin d') (Fin d') ℂ) (X : Matrix (Fin d) (Fin d) ℂ),
      (Tstar A * X).trace = (A * T X).trace)
    {r : ℕ} (hr : Channel.choiRank T ≤ r) :
    ∃ V : Matrix (Fin d' × Fin r) (Fin d) ℂ,
      (∀ A : Matrix (Fin d') (Fin d') ℂ, Tstar A = Vᴴ * stinespringPi (r := r) A * V) ∧
      (Vᴴ * V = 1 ↔ ∀ X : Matrix (Fin d) (Fin d) ℂ, (T X).trace = X.trace) := by
  obtain ⟨V, hV, hViso⟩ := exists_stinespringV_of_isKrausCP hT hr
  refine ⟨V, fun A => ?_, hViso⟩
  -- The trace pairing determines the dual map uniquely.
  have hdual : Tstar A = Matrix.traceAdjointMap T A :=
    Matrix.ext_iff_trace_mul_right.2 fun X => by
      rw [hTstar A X, Matrix.trace_traceAdjointMap_mul]
  rw [hdual]
  exact hV A

/-- **Stinespring dilation at the Choi-rank ancilla dimension for a dual
supplied by the trace pairing** (Wolf, Chapter 2, Theorem 2.2): the case
\(r = \operatorname{rank}(\tau)\) of `exists_stinespringV_pairing_of_isKrausCP`. -/
theorem exists_stinespringV_pairing_choiRank_of_isKrausCP
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ}
    {Tstar : Matrix (Fin d') (Fin d') ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ}
    (hT : IsKrausCP T)
    (hTstar : ∀ (A : Matrix (Fin d') (Fin d') ℂ) (X : Matrix (Fin d) (Fin d) ℂ),
      (Tstar A * X).trace = (A * T X).trace) :
    ∃ V : Matrix (Fin d' × Fin (Channel.choiRank T)) (Fin d) ℂ,
      (∀ A : Matrix (Fin d') (Fin d') ℂ,
        Tstar A = Vᴴ * stinespringPi (r := Channel.choiRank T) A * V) ∧
      (Vᴴ * V = 1 ↔ ∀ X : Matrix (Fin d) (Fin d) ℂ, (T X).trace = X.trace) :=
  exists_stinespringV_pairing_of_isKrausCP hT hTstar le_rfl

end ChoiRectangular
