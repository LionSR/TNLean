/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Trace
import TNLean.Algebra.FinCyclicInduction

/-!
# Path sums for ordered products of matrices

This file expands an ordered product of finitely many square matrices as a sum
over index paths: the matrix-vector product of the ordered product is the sum
over paths starting at the row index (`ofFn_prod_mulVec_apply`), and the trace
of the ordered product of a nonempty family is the sum over cyclic paths, in
which each factor connects a site to its cyclic successor
(`trace_ofFn_prod_eq_sum_cyclic`).  The cyclic form is the transfer-matrix
identity behind closed-chain contractions of matrix product operators.  For a
ring of scaled matrix units only one path survives, so the trace is the product
of the scalars when consecutive units chain cyclically and zero otherwise
(`trace_ofFn_prod_smul_single`).
-/

open scoped BigOperators

namespace Matrix

variable {ι R : Type*} [Fintype ι] [CommSemiring R]

/-- Summing over the tuples of length `L + 1` is summing over the first entry
and then over the remaining tuple. -/
lemma sum_fin_cons {L : ℕ} (F : (Fin (L + 1) → ι) → R) :
    ∑ t, F t = ∑ c, ∑ t : Fin L → ι, F (Fin.cons c t) := by
  rw [← Fintype.sum_equiv (Fin.consEquiv fun _ => ι) (fun x => F (Fin.cons x.1 x.2)) F
    (fun _ => rfl), Fintype.sum_prod_type]

-- `Matrix`'s identity, and hence `List.prod` including the empty product,
-- requires decidable equality.
variable [DecidableEq ι]

/-- **Open path expansion.**  Applying the ordered product of the matrices
`M 0, …, M (L - 1)` to a vector `v` and reading the entry at `a` sums, over all
paths `t` of length `L` starting at `a`, the product of the matrix entries along
the path times `v` at the endpoint. -/
theorem ofFn_prod_mulVec_apply :
    ∀ (L : ℕ) (M : Fin L → Matrix ι ι R) (v : ι → R) (a : ι),
      (List.ofFn M).prod.mulVec v a =
        ∑ t : Fin L → ι,
          (∏ i : Fin L, M i ((Fin.cons a t : Fin (L + 1) → ι) i.castSucc)
            ((Fin.cons a t : Fin (L + 1) → ι) i.succ)) *
            v ((Fin.cons a t : Fin (L + 1) → ι) (Fin.last L))
  | 0, M, v, a => by
      simp [List.ofFn_zero]
  | L + 1, M, v, a => by
      rw [List.ofFn_succ, List.prod_cons, ← Matrix.mulVec_mulVec]
      change (∑ c, M 0 a c * (List.ofFn fun i => M i.succ).prod.mulVec v c) = _
      rw [sum_fin_cons]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [ofFn_prod_mulVec_apply L, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Fin.prod_univ_succ, ← Fin.succ_last]
      simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, ← Fin.succ_castSucc]
      ring

/-- **Cyclic path expansion.**  The trace of the ordered product of a nonempty
family of matrices is the sum, over all assignments of an index to each site of
the cycle, of the product of the entries connecting each site to its cyclic
successor. -/
theorem trace_ofFn_prod_eq_sum_cyclic (L : ℕ) (M : Fin (L + 1) → Matrix ι ι R) :
    (List.ofFn M).prod.trace =
      ∑ t : Fin (L + 1) → ι, ∏ n, M n (t n) (t (finRotate (L + 1) n)) := by
  rw [List.ofFn_succ', List.prod_concat, Matrix.trace, sum_fin_cons]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h := ofFn_prod_mulVec_apply L (fun i => M i.castSucc) (fun c => M (Fin.last L) c a) a
  change (∑ c, _ * _) = _ at h
  rw [Matrix.diag_apply, Matrix.mul_apply, h]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.finRotate_succ_castSucc, finRotate_last, Fin.cons_zero]

/-- **Trace of a ring of scaled matrix units.**  The trace of the ordered
product of the scaled matrix units `c n • E_{l n, r n}` is the product of the
scalars when every column index `r n` equals the row index of the cyclic
successor, and zero otherwise. -/
theorem trace_ofFn_prod_smul_single (L : ℕ) (c : Fin (L + 1) → R)
    (l r : Fin (L + 1) → ι) :
    (List.ofFn fun n => c n • Matrix.single (l n) (r n) (1 : R)).prod.trace =
      if ∀ n, r n = l (finRotate (L + 1) n) then ∏ n, c n else 0 := by
  rw [trace_ofFn_prod_eq_sum_cyclic, Finset.sum_eq_single l]
  · simp only [smul_apply, single_apply, true_and, smul_eq_mul, mul_ite, mul_one, mul_zero]
    split_ifs with h
    · exact Finset.prod_congr rfl fun n _ => by simp [h n]
    · obtain ⟨n, hn⟩ := not_forall.mp h
      exact Finset.prod_eq_zero (Finset.mem_univ n) (by simp only [hn, ↓reduceIte])
  · intro t _ ht
    obtain ⟨n, hn⟩ := Function.ne_iff.mp ht
    refine Finset.prod_eq_zero (Finset.mem_univ n) ?_
    simp [Ne.symm hn]
  · simp

end Matrix
