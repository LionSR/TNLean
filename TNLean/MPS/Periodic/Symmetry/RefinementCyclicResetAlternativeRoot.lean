/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.RefinementRootRankChannelSquare
import TNLean.MPS.Periodic.Symmetry.Theorem41Reverse

/-!
# A bounded alternative root of the cyclic-reset square

The cyclic-reset square has a ten-operator channel root, exceeding its own
nine-letter alphabet. Replacing the reset between the two two-dimensional
sectors by a unitary gives a seven-operator channel root of the same square.
Consequently its nine-letter tensor is two-refinable.

This resolves the alternative-root calculation in
`docs/paper-gaps/dccsp17_root_kraus_rank_thm41.tex`. It does not establish
bounded-root selection for arbitrary singular transfer maps in the converse
of arXiv:1708.00029, Theorem 4.1, lines 812--818.
-/

open scoped Matrix BigOperators

namespace MPSTensor.CyclicResetCounterexample

/-- Replace the reset from the first two-dimensional sector to the second
by the unitary carrying coordinates \(1,2\) to \(3,4\). -/
noncomputable def alternativeRoot : MPSTensor 7 7 :=
  ![Complex.invSqrtTwo • Matrix.single 1 0 1,
    Complex.invSqrtTwo • Matrix.single 2 0 1,
    Matrix.single 3 1 1 + Matrix.single 4 2 1,
    Matrix.single 5 3 1, Matrix.single 5 4 1,
    Matrix.single 6 5 1, Matrix.single 0 6 1]

private theorem alternativeRoot_map (X : Matrix (Fin 7) (Fin 7) ℂ) :
    Kraus.transferMap alternativeRoot X =
      Matrix.single 0 0 (X 6 6) +
      Matrix.single 1 1 ((2 : ℂ)⁻¹ * X 0 0) +
      Matrix.single 2 2 ((2 : ℂ)⁻¹ * X 0 0) +
      Matrix.single 3 3 (X 1 1) + Matrix.single 3 4 (X 1 2) +
      Matrix.single 4 3 (X 2 1) + Matrix.single 4 4 (X 2 2) +
      Matrix.single 5 5 (X 3 3 + X 4 4) + Matrix.single 6 6 (X 5 5) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Kraus.transferMap_apply, alternativeRoot, Fin.sum_univ_succ,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.single_apply,
      Complex.invSqrtTwo_mul_self] <;>
    ring_nf <;> simp [Complex.invSqrtTwo_sq]

/-- The seven-letter alternative root is trace preserving. -/
theorem alternativeRoot_isTP : Kraus.IsTP alternativeRoot := by
  classical
  unfold Kraus.IsTP
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [alternativeRoot, Fin.sum_univ_succ, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.single_apply, Complex.invSqrtTwo_mul_self]

/-- The alternative seven-letter tensor defines a quantum channel. -/
theorem alternativeRoot_isChannel : IsChannel (Kraus.transferMap alternativeRoot) :=
  Kraus.isChannel_mapLM alternativeRoot alternativeRoot_isTP

/-- The alternative root has exactly seven independent Kraus operators. -/
theorem choiRank_alternativeRoot : Channel.choiRank (Kraus.transferMap alternativeRoot) = 7 := by
  rw [Channel.choiRank_mapLM_eq_finrank_span]
  have hli : LinearIndependent ℂ alternativeRoot := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    let r : Fin 7 → Fin 7 := ![1, 2, 3, 5, 5, 6, 0]
    let c : Fin 7 → Fin 7 := ![0, 0, 1, 3, 4, 5, 6]
    have h := congrArg (fun M : Matrix (Fin 7) (Fin 7) ℂ => M (r i) (c i)) hg
    fin_cases i <;>
      simpa [r, c, alternativeRoot, Fin.sum_univ_succ,
        Matrix.single_apply, Complex.invSqrtTwo_ne_zero] using h
  simpa using finrank_span_eq_card hli

/-- Replacing the middle reset by a unitary leaves the square unchanged.
The preceding reset prepares the normalized identity, and the following
reset takes the trace. Source context: arXiv:1708.00029, Theorem 4.1 converse. -/
theorem transferMap_square_eq_alternativeRoot_pow :
    Kraus.transferMap square = (Kraus.transferMap alternativeRoot) ^ 2 := by
  apply LinearMap.ext
  intro X
  rw [pow_two]
  change Kraus.transferMap square X =
    Kraus.transferMap alternativeRoot (Kraus.transferMap alternativeRoot X)
  simp only [alternativeRoot_map]
  ext a b
  rw [square_map_apply]
  fin_cases a <;> fin_cases b <;>
    norm_num [sector, outputWeight, Fin.sum_univ_succ, Matrix.single_apply,
      Complex.invSqrtTwo_mul_self] <;> ring

/-- The nine-letter cyclic-reset square is two-refinable, despite having
a supplied channel root of Kraus rank ten. A different root of Kraus rank
seven fits its physical alphabet. Source context: arXiv:1708.00029,
Theorem 4.1 converse; this is a singular-target example, not the general
root-selection assertion. -/
theorem square_isPRefinable : IsPRefinable square 2 := by
  apply isPRefinable_of_channel_root_hasKrausRankLE square (by norm_num)
    (Kraus.transferMap alternativeRoot) transferMap_square_eq_alternativeRoot_pow
  exact ⟨7, by norm_num, alternativeRoot, by intro X; simp⟩

end MPSTensor.CyclicResetCounterexample
