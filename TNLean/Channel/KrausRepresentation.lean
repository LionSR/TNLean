/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Basic
import TNLean.Channel.ChoiJamiolkowski
import TNLean.Algebra.TracePairing

/-!
# Kraus representation theorem (Wolf Ch. 2, Thm 2.1)

This file states and (partially) proves the full Kraus representation theorem:
a linear map is completely positive if and only if it admits a Kraus
decomposition `T(A) = ∑ⱼ Kⱼ A Kⱼ†`.

## Main results

* `IsCPMap_iff_kraus`: CP ↔ Kraus (currently the ⟸ direction is the definition)
* `kraus_tp_iff`: Kraus normalization conditions for trace-preserving and
  unital maps
* `kraus_unitary_freedom`: two Kraus decompositions of the same map differ by
  a unitary matrix (stated)

## Design notes

In the current TNLean codebase, `IsCPMap` is *defined* as the existence of a
Kraus representation. This file documents the fact that the Choi–Jamiolkowski
isomorphism provides the equivalence with positivity of the Choi matrix,
and records additional properties of the Kraus representation.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Thm 2.1][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix Finset BigOperators

variable {D : ℕ}

/-! ### Kraus normalization conditions (Thm 2.1, item 1) -/

/-- **Thm 2.1, item 1 (trace-preserving ⟹ Kraus normalization)**:
If `T` is trace-preserving and has Kraus form `T(X) = ∑ᵢ Kᵢ X Kᵢ†`,
then `∑ᵢ Kᵢ† Kᵢ = 𝟙`. -/
theorem kraus_sum_conjTranspose_mul_of_tp
    {r : ℕ} (K : Fin r → Matrix (Fin D) (Fin D) ℂ)
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hK : ∀ X, T X = ∑ i : Fin r, K i * X * (K i)ᴴ)
    (htp : IsTracePreservingMap T) :
    ∑ i : Fin r, (K i)ᴴ * K i = 1 := by
  -- Strategy: show ∑ᵢ Kᵢ† Kᵢ - 1 = 0 via trace pairing nondegeneracy
  -- For any X: tr((∑ᵢ Kᵢ† Kᵢ) X) = ∑ᵢ tr(Kᵢ† Kᵢ X) = ∑ᵢ tr(Kᵢ X Kᵢ†)
  -- = tr(T(X)) = tr(X) = tr(1 * X)
  suffices h : ∀ N : Matrix (Fin D) (Fin D) ℂ,
      trace ((∑ i : Fin r, (K i)ᴴ * K i - 1) * N) = 0 by
    have := (Matrix.trace_mul_right_eq_zero_iff _).mp h
    exact sub_eq_zero.mp this
  intro N
  rw [sub_mul, Matrix.one_mul]
  rw [show ((∑ i, (K i)ᴴ * K i) * N - N).trace =
    ((∑ i, (K i)ᴴ * K i) * N).trace - N.trace from
    Matrix.trace_sub _ _]
  rw [Finset.sum_mul, Matrix.trace_sum]
  simp_rw [show ∀ i : Fin r,
    ((K i)ᴴ * K i * N).trace = (K i * N * (K i)ᴴ).trace from
    fun i => by
      rw [Matrix.mul_assoc ((K i)ᴴ)]
      rw [Matrix.trace_mul_comm, Matrix.mul_assoc]]
  rw [← Matrix.trace_sum]
  -- Now: tr(∑ Kᵢ N Kᵢ†) - tr(N) = tr(T(N)) - tr(N) = 0
  conv_lhs => rw [← hK N]
  rw [htp N, sub_self]

/-- **Thm 2.1, item 1 (Kraus normalization ⟹ trace-preserving)**:
If `∑ᵢ Kᵢ† Kᵢ = 𝟙`, then the Kraus map is trace-preserving. -/
theorem kraus_tp_of_sum_conjTranspose_mul
    {r : ℕ} (K : Fin r → Matrix (Fin D) (Fin D) ℂ)
    (hK_norm : ∑ i : Fin r, (K i)ᴴ * K i = 1) :
    ∀ X : Matrix (Fin D) (Fin D) ℂ,
      trace (∑ i : Fin r, K i * X * (K i)ᴴ) = trace X := by
  intro X
  rw [Matrix.trace_sum]
  -- Each term: tr(Kᵢ X Kᵢ†) = tr(Kᵢ† Kᵢ X) by cyclic property
  simp_rw [show ∀ i : Fin r,
    trace (K i * X * (K i)ᴴ) = trace ((K i)ᴴ * K i * X) from fun i => by
      rw [Matrix.trace_mul_cycle, Matrix.mul_assoc]]
  -- ∑ᵢ tr(Kᵢ† Kᵢ X) = tr((∑ᵢ Kᵢ† Kᵢ) X)
  rw [← Matrix.trace_sum, ← Finset.sum_mul]
  rw [hK_norm, Matrix.one_mul]

/-! ### Kraus normalization for unital maps (Thm 2.1, item 1) -/

/-- If `T(𝟙) = 𝟙` and `T(X) = ∑ᵢ Kᵢ X Kᵢ†`, then `∑ᵢ Kᵢ Kᵢ† = 𝟙`. -/
theorem kraus_sum_mul_conjTranspose_of_unital
    {r : ℕ} (K : Fin r → Matrix (Fin D) (Fin D) ℂ)
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hK : ∀ X, T X = ∑ i : Fin r, K i * X * (K i)ᴴ)
    (hunit : T 1 = 1) :
    ∑ i : Fin r, K i * (K i)ᴴ = 1 := by
  have := hK 1
  simp only [Matrix.mul_one] at this
  rw [hunit] at this
  exact this.symm

/-! ### Unitary freedom in Kraus operators (Thm 2.1, item 4) -/

/-- **Thm 2.1, item 4 (unitary freedom, sufficient direction)**:
If `U` is unitary and `Kⱼ = ∑ₗ Uⱼₗ K̃ₗ`, then `{Kⱼ}` and `{K̃ₗ}`
give the same Kraus map.

(This is the easier direction of the unitary freedom result.) -/
theorem kraus_same_map_of_unitary_combination
    {r : ℕ}
    (K : Fin r → Matrix (Fin D) (Fin D) ℂ)
    (K' : Fin r → Matrix (Fin D) (Fin D) ℂ)
    (U : Matrix (Fin r) (Fin r) ℂ)
    (hU : Uᴴ * U = 1)
    (hK : ∀ j, K j = ∑ l, U j l • K' l) :
    ∀ X : Matrix (Fin D) (Fin D) ℂ,
      ∑ j : Fin r, K j * X * (K j)ᴴ =
      ∑ l : Fin r, K' l * X * (K' l)ᴴ := by
  intro X
  have hU_entry : ∀ l l' : Fin r,
      ∑ j : Fin r, ((starRingEnd ℂ) (U j l)) * U j l' = if l = l' then 1 else 0 := by
    intro l l'
    have h := congrArg (fun M : Matrix (Fin r) (Fin r) ℂ => M l l') hU
    simpa [Matrix.mul_apply, Matrix.one_apply] using h
  calc
    ∑ j : Fin r, K j * X * (K j)ᴴ
        = ∑ j : Fin r, (∑ l : Fin r, U j l • K' l) * X * ((∑ l : Fin r, U j l • K' l)ᴴ) := by
            simp [hK]
    _ = ∑ j : Fin r, ∑ l : Fin r, ∑ l' : Fin r,
          (((starRingEnd ℂ) (U j l')) * U j l) • (K' l * X * (K' l')ᴴ) := by
          simp_rw [Matrix.sum_mul]
          simp_rw [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul]
          simp_rw [Matrix.mul_sum]
          simp_rw [smul_mul_assoc, mul_smul_comm, Matrix.mul_assoc, smul_smul]
          simp [mul_comm]
    _ = ∑ l : Fin r, ∑ l' : Fin r,
          (∑ j : Fin r, ((starRingEnd ℂ) (U j l')) * U j l) • (K' l * X * (K' l')ᴴ) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro l _
          rw [Finset.sum_comm]
          simp_rw [← Finset.sum_smul]
    _ = ∑ l : Fin r, ∑ l' : Fin r,
          (if l' = l then 1 else 0) • (K' l * X * (K' l')ᴴ) := by
          simp_rw [hU_entry]
          simp
    _ = ∑ l : Fin r, K' l * X * (K' l)ᴴ := by
          simp
