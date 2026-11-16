/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.Arbitrary.ArbitraryTensor
import TNLean.Algebra.TailPowerSumUniqueness
import QICLean.Algebra.NewtonGirard

/-!
# Eventual equality of states

For tensors `A`, `B` of any bond dimensions, if `tr A^w = tr B^w` for every word of length at
least `N₀`, then the same holds for every nonempty word: `A` and `B` have the same states at every
positive length, hence the same composition factors. No injectivity or normality is assumed; the
statement contains the finite-length
theorems ("equal from some length on").

## Main results

* `MPSTensor.sameMPV₂Pos_of_forall_le_length_trace_evalWord_eq`.

## Implementation notes

For a nonempty word `w`, the traces `tr A^{w^k} = tr (A^w)^k` are the power sums of the
eigenvalues of `A^w`. They agree with those of `B^w` for every large `k`, so the nonzero
eigenvalues of `A^w` and `B^w` agree with multiplicities (uniqueness of power sums on a tail), and
`tr A^w = tr B^w`.
-/

open scoped Matrix

namespace MPSTensor

variable {d : ℕ}

/-- Matrices with the same reverse characteristic polynomial have the same trace powers. -/
private theorem trace_pow_eq_of_charpolyRev_eq {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (h : A.charpolyRev = B.charpolyRev) (k : ℕ) :
    Matrix.trace (A ^ k) = Matrix.trace (B ^ k) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | m
    · simp
    · have hA := Matrix.newton_girard_charpolyRev_coeff A m
      have hB := Matrix.newton_girard_charpolyRev_coeff B m
      rw [Finset.sum_range_succ'] at hA hB
      have h0 : ∀ M : Matrix n n ℂ, M.charpolyRev.coeff 0 = 1 := fun M => by
        rw [Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]
      have hsum : ∑ j ∈ Finset.range m, A.charpolyRev.coeff (j + 1) *
            Matrix.trace (A ^ (m + 1 - (j + 1))) =
          ∑ j ∈ Finset.range m, B.charpolyRev.coeff (j + 1) *
            Matrix.trace (B ^ (m + 1 - (j + 1))) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [h, ih _ (by have := Finset.mem_range.mp hj; omega)]
      rw [h0, one_mul, Nat.sub_zero] at hA hB
      have hp : A.charpolyRev.coeff (m + 1) = B.charpolyRev.coeff (m + 1) := by rw [h]
      linear_combination hA - hB - hsum - ((m + 1 : ℕ) : ℂ) * hp

/-- The trace powers of a complex matrix are the power sums of the roots of its characteristic
polynomial. -/
theorem trace_pow_eq_sum_roots_charpoly {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ)
    (k : ℕ) :
    Matrix.trace (X ^ k) = (X.charpoly.roots.map (· ^ k)).sum := by
  classical
  set s := X.charpoly.roots with hs
  have hcard : Multiset.card s = n := by
    have := (Polynomial.splits_iff_card_roots).mp (IsAlgClosed.splits X.charpoly)
    rw [this, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  obtain ⟨l, hl⟩ := Quot.exists_rep s
  have hlen : l.length = n := by
    rw [← hcard, ← hl]; rfl
  let v : Fin n → ℂ := fun i => l[(i : ℕ)]'(by rw [hlen]; exact i.2)
  have hv : (Finset.univ.val.map v : Multiset ℂ) = s := by
    have : List.ofFn v = l := by
      apply List.ext_getElem (by simp [hlen])
      intro i h1 h2
      simp [v]
    rw [← hl, ← this]
    simp [Fin.univ_val_map]
  have hchar : (Matrix.diagonal v).charpoly = X.charpoly := by
    rw [Matrix.charpoly_diagonal, Finset.prod_eq_multiset_prod,
      show (fun i => Polynomial.X - Polynomial.C (v i)) =
        (fun a => Polynomial.X - Polynomial.C a) ∘ v from rfl, ← Multiset.map_map, hv, hs]
    refine Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq (Matrix.charpoly_monic X) ?_
    rw [← hs, hcard, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hrev : (Matrix.diagonal v).charpolyRev = X.charpolyRev := by
    rw [← Matrix.reverse_charpoly, ← Matrix.reverse_charpoly, hchar]
  rw [← trace_pow_eq_of_charpolyRev_eq hrev, Matrix.diagonal_pow, Matrix.trace_diagonal, ← hv,
    Multiset.map_map]
  rfl

/-- Two complex matrices whose trace powers agree from some exponent on have the same trace. -/
private theorem trace_eq_of_forall_le_trace_pow_eq {n m : ℕ} (X : Matrix (Fin n) (Fin n) ℂ)
    (Y : Matrix (Fin m) (Fin m) ℂ) (K : ℕ)
    (h : ∀ k, K ≤ k → Matrix.trace (X ^ k) = Matrix.trace (Y ^ k)) :
    Matrix.trace X = Matrix.trace Y := by
  classical
  set s := X.charpoly.roots.filter (· ≠ 0)
  set t := Y.charpoly.roots.filter (· ≠ 0)
  have hfilt : ∀ (u : Multiset ℂ) (k : ℕ), 0 < k →
      (u.map (· ^ k)).sum = ((u.filter (· ≠ 0)).map (· ^ k)).sum := by
    intro u k hk
    conv_lhs => rw [← Multiset.filter_add_not (· ≠ 0) u]
    rw [Multiset.map_add, Multiset.sum_add, add_eq_left]
    refine Multiset.sum_eq_zero fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
    have : y = 0 := by simpa using (Multiset.mem_filter.mp hy).2
    simp [this, zero_pow hk.ne']
  have hst : s = t := by
    refine Multiset.eq_of_notMem_zero_of_forall_sum_map_pow_eq (by simp [s]) (by simp [t])
      ⟨K + 1, fun L hL => ?_⟩
    rw [← hfilt _ _ (by omega), ← hfilt _ _ (by omega), ← trace_pow_eq_sum_roots_charpoly,
      ← trace_pow_eq_sum_roots_charpoly, h L (by omega)]
  have h1 := trace_pow_eq_sum_roots_charpoly X 1
  have h2 := trace_pow_eq_sum_roots_charpoly Y 1
  rw [pow_one] at h1 h2
  rw [h1, h2, hfilt X.charpoly.roots 1 one_pos, hfilt Y.charpoly.roots 1 one_pos]
  exact congrArg (fun u : Multiset ℂ => (u.map (· ^ 1)).sum) hst

/-- The word `w` repeated `k` times. -/
private theorem evalWord_flatten_replicate {D : ℕ} (A : MPSTensor d D) (w : List (Fin d))
    (k : ℕ) : Kraus.evalWord A (List.replicate k w).flatten = Kraus.evalWord A w ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons, Kraus.evalWord_append, ih, pow_succ']

/-- **Eventual equality of traces.** Equality of the traces of all words of length at least `N₀`
implies equality of the states at every positive length. -/
theorem sameMPV₂Pos_of_forall_le_length_trace_evalWord_eq {DA DB : ℕ} {A : MPSTensor d DA}
    {B : MPSTensor d DB} (N₀ : ℕ)
    (h : ∀ w : List (Fin d), N₀ ≤ w.length →
      Matrix.trace (Kraus.evalWord A w) = Matrix.trace (Kraus.evalWord B w)) :
    SameMPV₂Pos A B := by
  intro N hN σ
  simp only [mpv_eq, coeff_eq]
  refine trace_eq_of_forall_le_trace_pow_eq _ _ N₀ fun k hk => ?_
  rw [← evalWord_flatten_replicate, ← evalWord_flatten_replicate]
  refine h _ ?_
  simp only [List.length_flatten, List.map_replicate, List.sum_replicate, List.length_ofFn,
    smul_eq_mul]
  nlinarith

end MPSTensor
