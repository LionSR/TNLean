/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import TNLean.Algebra.ConstantTracePowers
import TNLean.MPS.MPDO.ActionTensor

/-!
# Rank-one actions on a normal tensor are integral

If the periodic operators of a matrix product operator tensor `T` act on the periodic vectors of
a normal tensor `A` of positive bond dimension by one length-independent scalar `c`, then `c` is
a nonnegative integer (`Notes/OpenProblemsTN/checks/asym_fibonacci_categorical_data.md`, §6.4).
This is the lattice form of the integrality of the multiplicities in the action-tensor
corollary of the multi-block asymmetric compression theorem: a block that reappears with
multiplicity `c` reappears an integral number of times.

The mechanism is the word-trace identity `tr((T · A)^w) = c · tr(A^w)` for every nonempty word
`w`, obtained from the action tensor. Normality of `A` writes a matrix unit as a combination
`∑_u x_u A^u` of words of one positive length `ℓ`, and the same combination `N = ∑_u x_u (T·A)^u`
of words of the action tensor then satisfies `tr(N^k) = c · tr((∑_u x_u A^u)^k) = c` for every
positive `k`; `Matrix.exists_nat_eq_of_forall_trace_pow_eq` concludes.

## Main results

* `MPSTensor.exists_nat_eq_of_forall_trace_evalWord_eq_mul`: the word-trace form.
* `MPOTensor.exists_nat_eq_of_mpo_mulVec_mpv_eq_smul`: the periodic-operator form.
-/

open scoped Matrix

namespace MPSTensor

variable {d DB DA : ℕ}

/-- **Rank-one word-trace relations against a normal tensor are integral.** If every nonempty
word trace of `B` is `c` times the corresponding word trace of a normal tensor `A` of positive
bond dimension, then `c` is a nonnegative integer (data file §6.4). -/
theorem exists_nat_eq_of_forall_trace_evalWord_eq_mul [NeZero DA] (B : MPSTensor d DB)
    (A : MPSTensor d DA) (hA : Kraus.IsNormal A) (c : ℂ)
    (h : ∀ w : List (Fin d), w ≠ [] →
      (Kraus.evalWord B w).trace = c * (Kraus.evalWord A w).trace) :
    ∃ m : ℕ, c = m := by
  obtain ⟨ℓ, hℓ, hspan⟩ := hA
  have hmem : Matrix.single (0 : Fin DA) 0 (1 : ℂ) ∈ Submodule.span ℂ
      (Set.range fun σ : Fin ℓ → Fin d => Kraus.evalWord A (List.ofFn σ)) :=
    hspan.span_eq_top ▸ Submodule.mem_top
  obtain ⟨x, hx⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hmem
  set N : Matrix (Fin DB) (Fin DB) ℂ := ∑ σ, x σ • Kraus.evalWord B (List.ofFn σ) with hN
  set E : Matrix (Fin DA) (Fin DA) ℂ := ∑ σ, x σ • Kraus.evalWord A (List.ofFn σ) with hE
  have hNmul : ∀ w : List (Fin d),
      N * Kraus.evalWord B w = ∑ σ, x σ • Kraus.evalWord B (List.ofFn σ ++ w) := by
    intro w
    rw [hN, Finset.sum_mul]
    simp_rw [smul_mul_assoc, Kraus.evalWord_append]
  have hEmul : ∀ w : List (Fin d),
      E * Kraus.evalWord A w = ∑ σ, x σ • Kraus.evalWord A (List.ofFn σ ++ w) := by
    intro w
    rw [hE, Finset.sum_mul]
    simp_rw [smul_mul_assoc, Kraus.evalWord_append]
  have hne : ∀ (σ : Fin ℓ → Fin d) (w : List (Fin d)), List.ofFn σ ++ w ≠ [] := by
    intro σ w hnil
    have hlen := congrArg List.length hnil
    simp only [List.length_append, List.length_ofFn, List.length_nil] at hlen
    omega
  have key : ∀ (k : ℕ) (w : List (Fin d)),
      (N ^ (k + 1) * Kraus.evalWord B w).trace =
        c * (E ^ (k + 1) * Kraus.evalWord A w).trace := by
    intro k
    induction k with
    | zero =>
      intro w
      rw [pow_one, pow_one, hNmul, hEmul, Matrix.trace_sum, Matrix.trace_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul, h _ (hne σ w)]
      ring
    | succ k ih =>
      intro w
      rw [pow_succ N (k + 1), pow_succ E (k + 1), Matrix.mul_assoc, Matrix.mul_assoc, hNmul, hEmul,
        Matrix.mul_sum,
        Matrix.mul_sum, Matrix.trace_sum, Matrix.trace_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul,
        smul_eq_mul, ih]
      ring
  have hEpow : ∀ k : ℕ, E ^ (k + 1) = Matrix.single (0 : Fin DA) 0 (1 : ℂ) := by
    intro k
    induction k with
    | zero => rw [pow_one, hx]
    | succ k ih => rw [pow_succ, ih, hx, Matrix.single_mul_single_same, mul_one]
  refine Matrix.exists_nat_eq_of_forall_trace_pow_eq N c fun k hk => ?_
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hj := key j []
  rw [Kraus.evalWord_nil, Kraus.evalWord_nil, Matrix.mul_one, Matrix.mul_one, hEpow,
    Matrix.trace_single_eq_same, mul_one] at hj
  exact hj

end MPSTensor

namespace MPOTensor

variable {d D DA : ℕ}

/-- **Rank-one actions on a normal tensor are integral** (data file §6.4). If at every positive
length the periodic operator of `T` acts on the periodic vector of a normal tensor `A` of positive
bond dimension as multiplication by one scalar `c`, then `c` is a nonnegative integer. -/
theorem exists_nat_eq_of_mpo_mulVec_mpv_eq_smul [NeZero DA] (T : MPOTensor d D)
    (A : MPSTensor d DA) (hA : Kraus.IsNormal A) (c : ℂ)
    (h : ∀ N : ℕ, 0 < N →
      mpo T N *ᵥ (fun τ : Fin N → Fin d => MPSTensor.mpv A τ) =
        c • fun σ : Fin N → Fin d => MPSTensor.mpv A σ) :
    ∃ m : ℕ, c = m := by
  refine MPSTensor.exists_nat_eq_of_forall_trace_evalWord_eq_mul (actTensor T A) A hA c
    fun w hw => ?_
  have hlen : 0 < w.length := List.length_pos_iff.mpr hw
  have hw' : w = List.ofFn w.get := (List.ofFn_get w).symm
  have hσ := congrFun ((mpo_mulVec_mpv T A w.length).symm.trans (h w.length hlen)) w.get
  simp only [Pi.smul_apply, smul_eq_mul, MPSTensor.mpv, MPSTensor.coeff] at hσ
  rw [hw']
  exact hσ

end MPOTensor
