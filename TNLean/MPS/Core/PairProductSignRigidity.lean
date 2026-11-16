/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.Injectivity
import TNLean.Wielandt.SpanGrowth.CumulativeSpan

/-!
# Sign rigidity of tensors with equal products of two letters

Let `A` be block injective at some length: its words of that length span the
full matrix algebra. If a tensor `C` has the same products of two letters,
`C a * C b = A a * A b`, then `C = σ A` with `σ = ±1`.

All words of even length agree, so `C a * M * C b = A a * M * A b` for every
matrix `M`. On matrix units this gives `C a i p * C b q j = A a i p * A b q j`
for all entries. A single nonzero entry of `A` then fixes a common sign.

This is the rigidity step needed to pass from equality of the two-site blocks
of two matrix product unitaries to equality of the tensors up to a sign. The
parity counterexample `1, -1` of
`docs/paper-gaps/mpu_standard_form_parity_gap.tex` shows that the sign cannot
be removed.

## Main results

* `MPSTensor.evalWord_eq_of_pair_mul_eq`: equal even-length words.
* `MPSTensor.exists_sign_eq_smul_of_pair_mul_eq`: `C = σ A` with `σ = ±1`.
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- Two tensors with equal products of two letters have equal words of every
even length. -/
theorem evalWord_eq_of_pair_mul_eq {A C : Fin d → Matrix (Fin D) (Fin D) ℂ}
    (h : ∀ a b, C a * C b = A a * A b) :
    ∀ w : List (Fin d), Even w.length → Kraus.evalWord C w = Kraus.evalWord A w
  | [], _ => by simp
  | [a], hw => by simp at hw
  | a :: b :: w, hw => by
    have hw' : Even w.length := by
      simpa [Nat.even_add_one, parity_simps] using hw
    simp only [Kraus.evalWord_cons, ← Matrix.mul_assoc, h a b,
      evalWord_eq_of_pair_mul_eq h w hw']

/-- With equal products of two letters and block injectivity of `A` at an even
length, conjugating any matrix by a pair of letters gives the same result for
`C` and for `A`. -/
theorem mul_mul_eq_of_pair_mul_eq {A C : Fin d → Matrix (Fin D) (Fin D) ℂ}
    (h : ∀ a b, C a * C b = A a * A b) {L : ℕ} (hL : Even L)
    (hA : Kraus.IsNBlkInjective A L) (a b : Fin d) (M : Matrix (Fin D) (Fin D) ℂ) :
    C a * M * C b = A a * M * A b := by
  have hM : M ∈ Submodule.span ℂ
      (Set.range fun σ : Fin L → Fin d ↦ Kraus.evalWord A (List.ofFn σ)) := by
    rw [hA.span_eq_top]
    exact Submodule.mem_top
  induction hM using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨σ, rfl⟩ := hx
    have hσ : Kraus.evalWord C (List.ofFn σ) = Kraus.evalWord A (List.ofFn σ) :=
      evalWord_eq_of_pair_mul_eq h _ (by simpa using hL)
    have hlong := evalWord_eq_of_pair_mul_eq h (a :: (List.ofFn σ ++ [b]))
      (by simpa [Nat.even_add_one, parity_simps] using hL)
    simp only [Kraus.evalWord_cons, Kraus.evalWord_append, Kraus.evalWord_nil,
      Matrix.mul_one] at hlong
    change C a * Kraus.evalWord A (List.ofFn σ) * C b =
      A a * Kraus.evalWord A (List.ofFn σ) * A b
    rw [← hσ]
    simpa only [Matrix.mul_assoc, hσ] using hlong
  | zero => simp
  | add x y _ _ hx hy => simp only [Matrix.mul_add, Matrix.add_mul, hx, hy]
  | smul c x _ hx => simp only [Matrix.mul_smul, Matrix.smul_mul, hx]

/-- **Sign rigidity.** If `A` is block injective at some positive length and
`C a * C b = A a * A b` for all letters, then `C = σ A` with `σ = 1` or
`σ = -1`. -/
theorem exists_sign_eq_smul_of_pair_mul_eq {A C : Fin d → Matrix (Fin D) (Fin D) ℂ}
    (h : ∀ a b, C a * C b = A a * A b) {L : ℕ} (hLpos : 0 < L)
    (hA : Kraus.IsNBlkInjective A L) :
    ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧ C = σ • A := by
  classical
  have hA2 : Kraus.IsNBlkInjective A (2 * L) :=
    isNBlkInjective_of_le hLpos hA (by omega)
  -- Entrywise form: `C a i p * C b q j = A a i p * A b q j`.
  have hent : ∀ a b i p q j, C a i p * C b q j = A a i p * A b q j := by
    intro a b i p q j
    have h' := congrFun (congrFun
      (mul_mul_eq_of_pair_mul_eq h (even_two_mul L) hA2 a b (Matrix.single p q 1)) i) j
    simpa [Matrix.mul_apply, Matrix.single_apply, Finset.sum_ite_eq', Finset.sum_ite_eq,
      ite_and] using h'
  by_cases hzero : ∀ a i p, A a i p = 0
  · refine ⟨1, Or.inl rfl, ?_⟩
    funext a
    ext i p
    have hsq := hent a a i p i p
    rw [hzero a i p, zero_mul] at hsq
    simpa [hzero a i p] using mul_self_eq_zero.mp hsq
  · push Not at hzero
    obtain ⟨a₀, i₀, p₀, hα⟩ := hzero
    set α := A a₀ i₀ p₀
    set c := C a₀ i₀ p₀
    have hsq : c * c = α * α := hent a₀ a₀ i₀ p₀ i₀ p₀
    have hσ : c / α = 1 ∨ c / α = -1 := by
      have : (c / α) * (c / α) = 1 := by
        rw [div_mul_div_comm, hsq, div_self (mul_ne_zero hα hα)]
      exact mul_self_eq_one_iff.mp this
    refine ⟨c / α, hσ, ?_⟩
    funext a
    ext i p
    have hap := hent a a₀ i p i₀ p₀
    simp only [Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
    have hc : c ≠ 0 := by
      intro hc0
      rw [hc0, mul_zero] at hsq
      exact mul_ne_zero hα hα hsq.symm
    have hCa : C a i p = A a i p * α / c := (eq_div_iff hc).mpr hap
    rw [hCa, div_eq_iff hc, show c / α * A a i p * c = c * c / α * A a i p by ring, hsq]
    field_simp

end MPSTensor
