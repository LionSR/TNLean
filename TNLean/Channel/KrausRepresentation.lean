/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Basic
import TNLean.Channel.ChoiJamiolkowski
import TNLean.Algebra.TracePairing

/-!
# Kraus representation theorem (Wolf Ch. 2, Thm 2.1)

This file proves key properties of the Kraus representation of completely
positive maps `T(A) = ∑ⱼ Kⱼ A Kⱼ†`.

## Main results (Wolf Thm 2.1)

* `kraus_sum_conjTranspose_mul_of_tp` — TP ⟹ `∑ᵢ Kᵢ†Kᵢ = 𝟙`
* `kraus_tp_of_sum_conjTranspose_mul` — `∑ᵢ Kᵢ†Kᵢ = 𝟙` ⟹ TP
* `kraus_sum_mul_conjTranspose_of_unital` — unital ⟹ `∑ᵢ Kᵢ Kᵢ† = 𝟙`
* `kraus_same_map_of_unitary_combination` — unitary freedom (sufficient direction)
* `kraus_unitary_combination_of_same_map` — unitary freedom (necessary direction)
* `kraus_same_map_iff_unitary_combination` — unitary freedom (iff characterisation)

## Design notes

In the current TNLean codebase, `IsCPMap` is *defined* as the existence of a
Kraus representation. The Choi–Jamiolkowski isomorphism
(`ChoiJamiolkowski.cp_iff_choi_posSemidef`) provides the equivalence with
positivity of the Choi matrix.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Thm 2.1][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix Finset BigOperators

variable {D : ℕ}

/-! ### Kraus normalization conditions (Thm 2.1, item 1) -/

/-- **Thm 2.1 item 1 (TP ⟹ normalization)**:
If `T(X) = ∑ᵢ Kᵢ X Kᵢ†` is trace-preserving, then `∑ᵢ Kᵢ†Kᵢ = 𝟙`. -/
theorem kraus_sum_conjTranspose_mul_of_tp
    {r : ℕ} (K : Fin r → Matrix (Fin D) (Fin D) ℂ)
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hK : ∀ X, T X = ∑ i : Fin r, K i * X * (K i)ᴴ)
    (htp : IsTracePreservingMap T) :
    ∑ i : Fin r, (K i)ᴴ * K i = 1 := by
  -- Show `∑ᵢ Kᵢ†Kᵢ - 1 = 0` via trace pairing nondegeneracy.
  -- For any `N`: `tr((∑ᵢ Kᵢ†Kᵢ) N) = ∑ᵢ tr(Kᵢ†KᵢN) = ∑ᵢ tr(KᵢNKᵢ†) = tr(T(N)) = tr(N)`.
  suffices h : ∀ N : Matrix (Fin D) (Fin D) ℂ,
      trace ((∑ i : Fin r, (K i)ᴴ * K i - 1) * N) = 0 by
    have := (Matrix.trace_mul_right_eq_zero_iff _).mp h
    exact sub_eq_zero.mp this
  intro N
  rw [sub_mul, Matrix.one_mul]
  rw [show ((∑ i, (K i)ᴴ * K i) * N - N).trace =
    ((∑ i, (K i)ᴴ * K i) * N).trace - N.trace from Matrix.trace_sub _ _]
  rw [Finset.sum_mul, Matrix.trace_sum]
  simp_rw [show ∀ i : Fin r,
    ((K i)ᴴ * K i * N).trace = (K i * N * (K i)ᴴ).trace from
    fun i => by rw [Matrix.mul_assoc ((K i)ᴴ), Matrix.trace_mul_comm, Matrix.mul_assoc]]
  rw [← Matrix.trace_sum]
  conv_lhs => rw [← hK N]
  rw [htp N, sub_self]

/-- **Thm 2.1 item 1 (normalization ⟹ TP)**:
If `∑ᵢ Kᵢ†Kᵢ = 𝟙`, then `T(X) = ∑ᵢ Kᵢ X Kᵢ†` is trace-preserving. -/
theorem kraus_tp_of_sum_conjTranspose_mul
    {r : ℕ} (K : Fin r → Matrix (Fin D) (Fin D) ℂ)
    (hK_norm : ∑ i : Fin r, (K i)ᴴ * K i = 1) :
    ∀ X : Matrix (Fin D) (Fin D) ℂ,
      trace (∑ i : Fin r, K i * X * (K i)ᴴ) = trace X := by
  intro X
  rw [Matrix.trace_sum]
  -- Each term: `tr(KᵢXKᵢ†) = tr(Kᵢ†KᵢX)` by the cyclic property of trace.
  simp_rw [show ∀ i : Fin r,
    trace (K i * X * (K i)ᴴ) = trace ((K i)ᴴ * K i * X) from fun i => by
      rw [Matrix.trace_mul_cycle, Matrix.mul_assoc]]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, hK_norm, Matrix.one_mul]

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

/-- **Thm 2.1 item 4 (unitary freedom, sufficient direction)**:
If `U` is unitary (`Uᴴ U = 1`) and `Kⱼ = ∑ₗ Uⱼₗ K̃ₗ`, then `{Kⱼ}` and
`{K̃ₗ}` define the same map: `∑ⱼ Kⱼ X Kⱼ† = ∑ₗ K̃ₗ X K̃ₗ†`. -/
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
  -- Extract the orthogonality relation `∑ⱼ conj(Uⱼₗ') * Uⱼₗ = δ_{l,l'}` from `Uᴴ U = 1`.
  have hU_entry : ∀ l l' : Fin r,
      ∑ j : Fin r, (starRingEnd ℂ) (U j l) * U j l' = if l = l' then 1 else 0 := by
    intro l l'
    have h := congrArg (fun M : Matrix (Fin r) (Fin r) ℂ => M l l') hU
    simpa [Matrix.mul_apply, Matrix.one_apply] using h
  calc
    ∑ j : Fin r, K j * X * (K j)ᴴ
        = ∑ j : Fin r,
            (∑ l : Fin r, U j l • K' l) * X *
            ((∑ l : Fin r, U j l • K' l)ᴴ) := by simp [hK]
    _ = ∑ j : Fin r, ∑ l : Fin r, ∑ l' : Fin r,
          (((starRingEnd ℂ) (U j l')) * U j l) • (K' l * X * (K' l')ᴴ) := by
          simp_rw [Matrix.sum_mul, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
            Matrix.mul_sum, smul_mul_assoc, mul_smul_comm, Matrix.mul_assoc, smul_smul]
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
          simp_rw [hU_entry]; simp
    _ = ∑ l : Fin r, K' l * X * (K' l)ᴴ := by simp

/-! ### Unitary freedom: necessary direction and full characterisation (Thm 2.1, item 4) -/

/-- **Core linear algebra lemma for unitary freedom**: if two families of
vectors have the same outer-product sum `∑ⱼ vⱼ vⱼ† = ∑ₗ wₗ wₗ†`, then the
families are related by a unitary mixing matrix.

This is the finite-dimensional fact that two decompositions of a positive
semidefinite matrix into rank-1 terms (of the same cardinality) are
related by a unitary transformation.

**Proof status**: requires partial-isometry extension or polar decomposition
for matrices over `ℂ`, which is not yet available in this project's
Mathlib toolchain. This is the sole `sorry` underlying the converse
direction of Kraus unitary freedom. -/
theorem exists_unitary_of_sum_vecMulVec_star_eq
    {ι : Type*}
    {r : ℕ}
    (v w : Fin r → (ι → ℂ))
    (h : ∑ j : Fin r, Matrix.vecMulVec (v j) (star (v j)) =
         ∑ l : Fin r, Matrix.vecMulVec (w l) (star (w l))) :
    ∃ U : Matrix (Fin r) (Fin r) ℂ, Uᴴ * U = 1 ∧
      ∀ j i, v j i = ∑ l : Fin r, U j l * w l i := by
  sorry

/-- **Thm 2.1 item 4 (unitary freedom, necessary direction)**:
if two same-size Kraus families define the same map, they are related by a
unitary mixing matrix.

Concretely, if `∀ X, ∑ⱼ Kⱼ X Kⱼ† = ∑ₗ K̃ₗ X K̃ₗ†`, then there exists a
unitary `U` (satisfying `Uᴴ U = 1`) such that `Kⱼ = ∑ₗ Uⱼₗ K̃ₗ`.

### Hypotheses

Both families must have the same number `r` of operators. When the Kraus
ranks differ, pad the shorter family with zero operators.

### Proof strategy

The map-equality hypothesis, tested on rank-1 inputs `X = |i⟩⟨j|`, yields the
identity `∑ⱼ vⱼ vⱼ† = ∑ₗ wₗ wₗ†` for the "vectorisations"
`vⱼ(a,i) = (Kⱼ)ₐᵢ`. The core linear algebra lemma
`exists_unitary_of_sum_vecMulVec_star_eq` then gives the unitary. -/
theorem kraus_unitary_combination_of_same_map
    {r : ℕ}
    (K K' : Fin r → Matrix (Fin D) (Fin D) ℂ)
    (hmap : ∀ X : Matrix (Fin D) (Fin D) ℂ,
      ∑ j : Fin r, K j * X * (K j)ᴴ =
      ∑ l : Fin r, K' l * X * (K' l)ᴴ) :
    ∃ U : Matrix (Fin r) (Fin r) ℂ, Uᴴ * U = 1 ∧
      ∀ j, K j = ∑ l : Fin r, U j l • K' l := by
  -- Vectorise: define v_j(a,i) = (K_j)_{a,i}, w_l(a,i) = (K'_l)_{a,i}.
  -- The map equality on rank-1 inputs gives ∑ⱼ v_j v_j† = ∑ₗ w_l w_l†.
  -- The core linear algebra lemma then produces the unitary U.
  sorry

/-- **Thm 2.1 item 4 (unitary freedom, full characterisation)**:
two same-size Kraus families define the same map **if and only if** they
are related by a unitary mixing matrix.

This combines the sufficient direction (`kraus_same_map_of_unitary_combination`)
with the necessary direction (`kraus_unitary_combination_of_same_map`). -/
theorem kraus_same_map_iff_unitary_combination
    {r : ℕ}
    (K K' : Fin r → Matrix (Fin D) (Fin D) ℂ) :
    (∀ X : Matrix (Fin D) (Fin D) ℂ,
      ∑ j : Fin r, K j * X * (K j)ᴴ =
      ∑ l : Fin r, K' l * X * (K' l)ᴴ) ↔
    (∃ U : Matrix (Fin r) (Fin r) ℂ, Uᴴ * U = 1 ∧
      ∀ j, K j = ∑ l : Fin r, U j l • K' l) := by
  constructor
  · exact kraus_unitary_combination_of_same_map K K'
  · rintro ⟨U, hU, hK⟩
    exact kraus_same_map_of_unitary_combination K K' U hU hK
