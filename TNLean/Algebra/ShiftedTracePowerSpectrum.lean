/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.TracePowerCharPoly
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-!
# Trace Powers Above One Determine the Nonzero Spectrum

For a square complex matrix `A`, suppose `tr(A^k) = 1` for every `k > 1`.
Then the nonzero part of the spectrum is exactly `{1}`. This is the precise
power-sum consequence used in arXiv:1703.09188, Proposition
`prop:normal-tensor`, lines 349--354.

The proof applies the all-positive-moment characteristic-polynomial theorem
to `A ^ 2` and `A ^ 3`. Spectral mapping then gives, for each nonzero spectral
value `μ`, both `μ ^ 2 = 1` and `μ ^ 3 = 1`, hence `μ = 1`. Applying spectral
mapping in the reverse direction to the spectral value `1` of `A ^ 2` proves
that `1` itself occurs in the spectrum of `A`.

No positivity, normality, diagonalizability, or first-moment hypothesis is
used.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1703.09188,
  Proposition `prop:normal-tensor`, lines 349--354
* [Cirac--Perez-Garcia--Schuch--Verstraete 2016] arXiv:1606.00608,
  Lemma A.5, lines 1155--1163
-/

open scoped Matrix
open Polynomial

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A moment hypothesis for exponents above one becomes an all-positive-moment
hypothesis after replacing `A` by `A ^ m`, provided `m > 1`. -/
theorem forall_trace_pow_pow_eq_one_of_forall_trace_pow_eq_one_of_one_lt
    (A : Matrix n n ℂ)
    (h : ∀ k : ℕ, 1 < k → trace (A ^ k) = 1)
    (m : ℕ) (hm : 1 < m) :
    ∀ k : ℕ, 0 < k → trace ((A ^ m) ^ k) = 1 := by
  intro k hk
  rw [← pow_mul]
  exact h (m * k) (hm.trans_le (Nat.le_mul_of_pos_right m hk))

/-- If all traces `tr(A^k)` with `k > 1` equal one, every nonzero spectral
value of `A` equals one.

This is the set-spectrum part of arXiv:1703.09188, Proposition
`prop:normal-tensor`, lines 349--354.

**Scope restriction (set spectrum only):** the source proposition also states
that the sole nonzero eigenvalue has algebraic multiplicity one. This theorem
proves only that every nonzero spectral value equals one. See
`docs/paper-gaps/cpsv17_transfer_trace_power.tex`. -/
theorem eq_one_of_mem_spectrum_of_forall_trace_pow_eq_one_of_one_lt
    (A : Matrix n n ℂ)
    (h : ∀ k : ℕ, 1 < k → trace (A ^ k) = 1)
    {μ : ℂ} (hμ : μ ∈ spectrum ℂ A) (hμ0 : μ ≠ 0) :
    μ = 1 := by
  have hpow2 :=
    forall_trace_pow_pow_eq_one_of_forall_trace_pow_eq_one_of_one_lt A h 2 (by omega)
  have hpow3 :=
    forall_trace_pow_pow_eq_one_of_forall_trace_pow_eq_one_of_one_lt A h 3 (by omega)
  have hchar2 :=
    charpoly_eq_X_pow_pred_mul_X_sub_one_of_forall_trace_pow_eq_one (A ^ 2) hpow2
  have hchar3 :=
    charpoly_eq_X_pow_pred_mul_X_sub_one_of_forall_trace_pow_eq_one (A ^ 3) hpow3
  have hμ2root : IsRoot (A ^ 2).charpoly (μ ^ 2) :=
    mem_spectrum_iff_isRoot_charpoly.mp (spectrum.pow_mem_pow A 2 hμ)
  have hμ3root : IsRoot (A ^ 3).charpoly (μ ^ 3) :=
    mem_spectrum_iff_isRoot_charpoly.mp (spectrum.pow_mem_pow A 3 hμ)
  have hμ2sub : μ ^ 2 - 1 = 0 := by
    rw [hchar2] at hμ2root
    simpa [IsRoot, hμ0] using hμ2root
  have hμ2 : μ ^ 2 = 1 := sub_eq_zero.mp hμ2sub
  have hμ3sub : μ ^ 3 - 1 = 0 := by
    rw [hchar3] at hμ3root
    simpa [IsRoot, hμ0] using hμ3root
  have hμ3 : μ ^ 3 = 1 := sub_eq_zero.mp hμ3sub
  calc
    μ = μ ^ 3 / μ ^ 2 := by field_simp
    _ = 1 := by rw [hμ2, hμ3]; simp

/-- If all traces `tr(A^k)` with `k > 1` equal one, then one belongs to the
spectrum of `A`.

This is the existence part of the spectral conclusion in arXiv:1703.09188,
Proposition `prop:normal-tensor`, lines 349--354.

**Scope restriction (set spectrum only):** the source proposition also states
that the sole nonzero eigenvalue has algebraic multiplicity one. This theorem
proves only that `1` is a spectral value. See
`docs/paper-gaps/cpsv17_transfer_trace_power.tex`. -/
theorem one_mem_spectrum_of_forall_trace_pow_eq_one_of_one_lt
    (A : Matrix n n ℂ)
    (h : ∀ k : ℕ, 1 < k → trace (A ^ k) = 1) :
    (1 : ℂ) ∈ spectrum ℂ A := by
  have hpow2 :=
    forall_trace_pow_pow_eq_one_of_forall_trace_pow_eq_one_of_one_lt A h 2 (by omega)
  have hchar2 :=
    charpoly_eq_X_pow_pred_mul_X_sub_one_of_forall_trace_pow_eq_one (A ^ 2) hpow2
  have hone_sq : (1 : ℂ) ∈ spectrum ℂ (A ^ 2) := by
    apply mem_spectrum_of_isRoot_charpoly
    rw [hchar2]
    simp [IsRoot]
  rw [spectrum.map_pow_of_pos (𝕜 := ℂ) (a := A) (n := 2) (by omega)] at hone_sq
  rcases hone_sq with ⟨μ, hμ, hμ2⟩
  have hμ0 : μ ≠ 0 := by
    intro hμ0
    simp [hμ0] at hμ2
  have hμ1 := eq_one_of_mem_spectrum_of_forall_trace_pow_eq_one_of_one_lt A h hμ hμ0
  simpa [hμ1] using hμ

/-- If all traces `tr(A^k)` with `k > 1` equal one, the nonzero part of the
spectrum of `A` is the singleton `{1}`.

This is the set-spectrum consequence used in arXiv:1703.09188,
Proposition `prop:normal-tensor`, lines 349--354.

**Scope restriction (set spectrum only):** the source proposition also states
that the sole nonzero eigenvalue has algebraic multiplicity one. This theorem
proves only equality of the nonzero spectrum as a set. See
`docs/paper-gaps/cpsv17_transfer_trace_power.tex`. -/
theorem spectrum_diff_zero_eq_singleton_of_forall_trace_pow_eq_one_of_one_lt
    (A : Matrix n n ℂ)
    (h : ∀ k : ℕ, 1 < k → trace (A ^ k) = 1) :
    spectrum ℂ A \ {0} = {1} := by
  ext μ
  constructor
  · rintro ⟨hμ, hμ0⟩
    have hμ_ne : μ ≠ 0 := by simp at hμ0; exact hμ0
    simp [eq_one_of_mem_spectrum_of_forall_trace_pow_eq_one_of_one_lt A h hμ hμ_ne]
  · intro hμ
    have hμ1 : μ = 1 := by simpa using hμ
    subst μ
    exact ⟨one_mem_spectrum_of_forall_trace_pow_eq_one_of_one_lt A h, by simp⟩

end Matrix
