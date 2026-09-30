/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinKronecker
import TNLean.MPS.Core.WordGrading
import TNLean.MPS.Examples.MultiBlock.ParityGraded
import TNLean.MPS.Examples.GHZ

/-!
# Occupation parity and cyclic runs of the sign-weighted pair tensor

For the tensor `ParityGraded.parA`, the number of occupied sites controls the
physical parity, while the lengths of the runs between zero letters determine
its periodic amplitudes. These are the statements `lem:asymex_parity_occupation`
and `lem:asymex_parity_runs` in the supporting blueprint appendix. The tensor is
an example constructed in this development, as documented in `ParityGraded`.

## Main results

* `ParityGraded.finKronecker_pauliZ_mulVec_mpv_parA`: physical parity fixes the vector.
* `ParityGraded.trace_evalWord_parA_eq_zero_of_odd`: odd occupation has zero amplitude.
* `ParityGraded.trace_evalWord_parA_cyclic_runs`: each cyclic run contributes its even-length
  indicator; `ParityGraded.exists_parA_cyclic_runs` covers every word containing a zero.
* `ParityGraded.trace_evalWord_parA_replicate_one`: the all-one amplitude is `1 + (-1)^N`.
-/

open scoped Matrix
open MPSTensor

namespace ParityGraded

/-- The bond grading of the pair tensor agrees with its physical occupation sign. -/
theorem pauliZ_mul_parA (i : Fin 2) :
    pauliZ * parA i = (-1 : ℂ) ^ i.val • (parA i * pauliZ) := by
  ext a b
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    norm_num [parA, parAInt, complexOfInt, complexOfRing, pauliZ,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The grading passes through a word with the sign of its occupation. -/
theorem pauliZ_mul_evalWord_parA (w : List (Fin 2)) :
    pauliZ * Kraus.evalWord parA w =
      (-1 : ℂ) ^ (w.map Fin.val).sum • (Kraus.evalWord parA w * pauliZ) := by
  have hc : (w.map fun i => (-1 : ℂ) ^ i.val).prod = (-1 : ℂ) ^ (w.map Fin.val).sum := by
    induction w with
    | nil => simp
    | cons i w ih => simp [ih, pow_add]
  simpa only [hc] using
    mul_evalWord_of_mul_eq_smul_letter parA pauliZ (fun i => (-1 : ℂ) ^ i.val)
      pauliZ_mul_parA w

/-- The periodic amplitude is unchanged by the physical occupation sign. -/
theorem occupation_sign_mul_trace_evalWord_parA (w : List (Fin 2)) :
    (-1 : ℂ) ^ (w.map Fin.val).sum * Matrix.trace (Kraus.evalWord parA w) =
      Matrix.trace (Kraus.evalWord parA w) := by
  have h := congrArg (fun M => Matrix.trace (M * pauliZ)) (pauliZ_mul_evalWord_parA w)
  rw [Matrix.trace_mul_cycle, pauliZ_sq, Matrix.one_mul, Matrix.smul_mul,
    Matrix.mul_assoc, pauliZ_sq, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul] at h
  exact h.symm

/-- Odd occupation forces the periodic amplitude to vanish. -/
theorem trace_evalWord_parA_eq_zero_of_odd (w : List (Fin 2))
    (hw : Odd (w.map Fin.val).sum) : Matrix.trace (Kraus.evalWord parA w) = 0 := by
  simpa [hw.neg_one_pow, CharZero.neg_eq_self_iff] using
    occupation_sign_mul_trace_evalWord_parA w

/-- The local conjugation identity of the occupation-parity symmetry. -/
lemma pauliZ_mul_parA_mul_pauliZ (i : Fin 2) :
    pauliZ * parA i * pauliZ = (-1 : ℂ) ^ i.val • parA i := by
  simp [pauliZ_mul_parA, Matrix.mul_assoc, pauliZ_sq]

/-- In the computational basis, physical occupation parity fixes the periodic vector. -/
theorem occupation_sign_mul_mpv_parA {N : ℕ} (σ : Fin N → Fin 2) :
    (-1 : ℂ) ^ (∑ k, (σ k).val) * mpv parA σ = mpv parA σ := by
  simpa [mpv, coeff, List.map_ofFn, List.sum_ofFn] using
    occupation_sign_mul_trace_evalWord_parA (List.ofFn σ)

private theorem parA_one_sq : parA 1 ^ 2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pow_two, parA, parAInt, complexOfInt, complexOfRing,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- A run of occupied sites has period two on the bond space. -/
theorem parA_one_pow (n : ℕ) : parA 1 ^ n = if Even n then 1 else parA 1 := by
  rw [pow_eq_pow_mod n parA_one_sq]
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [Nat.even_iff, h]

/-- Closing a run between two zero letters tests whether its length is even. -/
theorem parA_zero_mul_pow_mul_zero (n : ℕ) :
    parA 0 * parA 1 ^ n * parA 0 = (if Even n then 1 else 0 : ℂ) • parA 0 := by
  rw [parA_one_pow]
  split_ifs <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [parA, parAInt, complexOfInt, complexOfRing, Matrix.mul_apply, Fin.sum_univ_two]

/-- The trace of a zero letter followed by a run tests whether the run is even. -/
theorem trace_parA_zero_mul_pow (n : ℕ) :
    Matrix.trace (parA 0 * parA 1 ^ n) = if Even n then 1 else 0 := by
  rw [parA_one_pow]
  split_ifs <;>
    norm_num [parA, parAInt, complexOfInt, complexOfRing, Matrix.trace,
      Matrix.mul_apply, Fin.sum_univ_two]

private theorem evalWord_parA_runs_mul_zero (rs : List ℕ) :
    Kraus.evalWord parA (rs.flatMap fun r => 0 :: List.replicate r 1) * parA 0 =
      (rs.map fun r => if Even r then (1 : ℂ) else 0).prod • parA 0 := by
  induction rs with
  | nil => simp [Kraus.evalWord_nil]
  | cons r rs ih =>
      simp only [List.flatMap_cons, List.map_cons, List.prod_cons,
        Kraus.evalWord_append, Kraus.evalWord_cons, Kraus.evalWord_replicate]
      rw [Matrix.mul_assoc, ih, Matrix.mul_smul, parA_zero_mul_pow_mul_zero,
        smul_smul, mul_comm]

/-- Starting at a zero, each cyclic run contributes its even-length indicator. -/
theorem trace_evalWord_parA_runs (r : ℕ) (rs : List ℕ) :
    Matrix.trace (Kraus.evalWord parA ((r :: rs).flatMap fun n =>
      0 :: List.replicate n 1)) =
      ((r :: rs).map fun n => if Even n then (1 : ℂ) else 0).prod := by
  simp only [List.flatMap_cons, List.map_cons, List.prod_cons,
    Kraus.evalWord_append, Kraus.evalWord_cons, Kraus.evalWord_replicate]
  rw [Matrix.trace_mul_cycle, evalWord_parA_runs_mul_zero, Matrix.smul_mul,
    Matrix.trace_smul, smul_eq_mul, trace_parA_zero_mul_pow, mul_comm]

/-- The all-occupied word has amplitude two at even length and zero at odd length. -/
theorem trace_evalWord_parA_replicate_one (n : ℕ) :
    Matrix.trace (Kraus.evalWord parA (List.replicate n 1)) = 1 + (-1 : ℂ) ^ n := by
  rw [Kraus.evalWord_replicate, parA_one_pow, neg_one_pow_eq_ite]
  split_ifs <;>
    norm_num [parA, parAInt, complexOfInt, complexOfRing, Matrix.trace, Fin.sum_univ_two]

private theorem trace_evalWord_parA_rotate (w : List (Fin 2)) (n : ℕ) :
    Matrix.trace (Kraus.evalWord parA (w.rotate n)) =
      Matrix.trace (Kraus.evalWord parA w) := by
  rw [List.rotate_eq_drop_append_take_mod, Kraus.evalWord_append, Matrix.trace_mul_comm,
    ← Kraus.evalWord_append, List.take_append_drop]

/-- The run formula is independent of the site at which the cyclic word starts. -/
lemma trace_evalWord_parA_cyclic_runs {w : List (Fin 2)} (r : ℕ) (rs : List ℕ)
    (hw : w.IsRotated ((r :: rs).flatMap fun n => 0 :: List.replicate n 1)) :
    Matrix.trace (Kraus.evalWord parA w) =
      ((r :: rs).map fun n => if Even n then (1 : ℂ) else 0).prod := by
  obtain ⟨n, hn⟩ := hw
  rw [← trace_evalWord_parA_rotate w n, hn, trace_evalWord_parA_runs]

private theorem exists_runs_cons_zero (w : List (Fin 2)) :
    ∃ r rs, 0 :: w = (r :: rs).flatMap (fun n => 0 :: List.replicate n 1) := by
  induction w with
  | nil => exact ⟨0, [], rfl⟩
  | cons i w ih =>
      obtain ⟨r, rs, hw⟩ := ih
      simp only [List.flatMap_cons, List.cons_append, List.cons.injEq, true_and] at hw
      fin_cases i
      · refine ⟨0, r :: rs, ?_⟩
        simp [List.flatMap_cons, hw]
      · refine ⟨r + 1, rs, ?_⟩
        simp [List.flatMap_cons, List.replicate_succ, hw]

/-- Every word containing a zero has a nonempty cyclic list of runs of ones. -/
theorem exists_parA_cyclic_runs (w : List (Fin 2)) (hw : 0 ∈ w) :
    ∃ r rs, w.IsRotated ((r :: rs).flatMap fun n => 0 :: List.replicate n 1) := by
  obtain ⟨u, v, rfl⟩ := List.append_of_mem hw
  obtain ⟨r, rs, hr⟩ := exists_runs_cons_zero (v ++ u)
  refine ⟨r, rs, ?_⟩
  rw [← hr]
  exact List.isRotated_append

private theorem pauliZ_eq_diagonal_sign :
    pauliZ = Matrix.diagonal (fun i : Fin 2 => (-1 : ℂ) ^ i.val) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [pauliZ, Matrix.diagonal]

/-- The tensor product of physical parity operators fixes the periodic vector. -/
theorem finKronecker_pauliZ_mulVec_mpv_parA (N : ℕ) :
    (Matrix.finKronecker fun _ : Fin N => pauliZ) *ᵥ (fun σ => mpv parA σ) =
      (fun σ : Fin N → Fin 2 => mpv parA σ) := by
  rw [pauliZ_eq_diagonal_sign, Matrix.finKronecker_diagonal]
  ext σ
  simpa [Matrix.mulVec_diagonal, Finset.prod_pow_eq_pow_sum] using
    occupation_sign_mul_mpv_parA σ

end ParityGraded
