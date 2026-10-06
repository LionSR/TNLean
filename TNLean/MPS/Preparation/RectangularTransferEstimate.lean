/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.CornerReferenceOverlap
import TNLean.MPS.Preparation.PaddedBondState
import QICLean.Algebra.RectangularChoi
import QICLean.Channel.KrausCPTP
import QICLean.Channel.SupportCompletion

/-!
# Rectangular transfer error after padding

The norm of `Matrix.linearMapMatrix E` is the Hilbert--Schmidt induced operator norm of
`E`, with the matrix-unit bases on the actual input and output spaces. A rectangular block
with both bond dimensions at most `D` has a uniformly bounded padding map in this norm.
The padded reference is the corner reset, not the full-space trace reset.

## References

* arXiv:2307.01696v2, paragraph "Inhomogeneous short-range correlated MPS", eq. (8), and
  Supplemental Material, eq. (S39).
-/

open Matrix MPSTensor
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace MPSPreparation

/-- Actual rectangular transfer error controls the transfer error of the padded tensor,
with a constant depending only on the common bond bound. The rectangular operator norm
uses matrix-unit bases, and hence the Hilbert--Schmidt norm on both matrix spaces. -/
theorem exists_norm_transferMatrix_zeroPad_sub_cornerReferenceMap_le (D : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ {d a b : ℕ} (_ha : a ≤ D) (_hb : b ≤ D)
      (A : Fin d → Matrix (Fin a) (Fin b) ℂ) (σ : Matrix (Fin a) (Fin a) ℂ),
      ‖transferMatrix (Kraus.transferMap (fun i => Matrix.zeroPad D (A i))) -
        transferMatrix (cornerReferenceMap (Matrix.zeroPad D σ) b)‖ ≤
      K * ‖Matrix.linearMapMatrix (Matrix.rectangularKrausMap A -
        Matrix.tracePrepareMap (α := Fin b) σ)‖ := by
  classical
  let R (a b : Fin (D + 1)) :
      Matrix (Fin a.val × Fin a.val) (Fin b.val × Fin b.val) ℂ →ₗ[ℂ]
        Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
    LinearMap.pi fun p => LinearMap.pi fun q =>
      if hp : p.2.val < a.val ∧ p.1.val < a.val then
        if hq : q.2.val < b.val ∧ q.1.val < b.val then
          Matrix.entryLinearMap ℂ ℂ
            ((⟨p.2.val, hp.1⟩, ⟨p.1.val, hp.2⟩) : Fin a.val × Fin a.val)
            ((⟨q.2.val, hq.1⟩, ⟨q.1.val, hq.2⟩) : Fin b.val × Fin b.val) else 0 else 0
  let Rc (a b : Fin (D + 1)) := LinearMap.toContinuousLinearMap (R a b)
  let K : ℝ := 1 + ∑ a : Fin (D + 1), ∑ b : Fin (D + 1), ‖Rc a b‖
  have hK : 0 < K := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
  refine ⟨K, hK, fun {d a b} ha hb A σ => ?_⟩
  let ai : Fin (D + 1) := ⟨a, Nat.lt_succ_of_le ha⟩
  let bi : Fin (D + 1) := ⟨b, Nat.lt_succ_of_le hb⟩
  have hRc : ‖Rc ai bi‖ ≤ K := by
    have h : (∑ j : Fin (D + 1), ‖Rc ai j‖) ≤
        ∑ i : Fin (D + 1), ∑ j : Fin (D + 1), ‖Rc i j‖ := Finset.single_le_sum
      (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg (Rc i j)) (Finset.mem_univ ai)
    have h' : ‖Rc ai bi‖ ≤ ∑ j : Fin (D + 1), ‖Rc ai j‖ :=
      Finset.single_le_sum (fun j _ => norm_nonneg (Rc ai j)) (Finset.mem_univ bi)
    dsimp [K]
    linarith
  have hentry (p : Fin a × Fin a) (q : Fin b × Fin b) :
      Matrix.linearMapMatrix (Matrix.rectangularKrausMap A -
        Matrix.tracePrepareMap (α := Fin b) σ) p q =
      (∑ i, A i p.1 q.1 * star (A i p.2 q.2)) -
        (if q.1 = q.2 then σ p.1 p.2 else 0) := by
    rcases p with ⟨p₁, p₂⟩
    rcases q with ⟨q₁, q₂⟩
    rw [Matrix.linearMapMatrix_apply, LinearMap.sub_apply, Matrix.sub_apply,
      Matrix.tracePrepareMap_apply]
    by_cases hq : q₁ = q₂
    · subst q₂
      simp [Matrix.rectangularKrausMap, Matrix.mul_apply, Matrix.single_apply,
        Matrix.conjTranspose_apply, Matrix.sum_apply, ite_and]
    · simp [Matrix.rectangularKrausMap, Matrix.mul_apply, Matrix.single_apply,
        Matrix.conjTranspose_apply, Matrix.sum_apply,
        Matrix.trace_single_eq_of_ne _ _ _ hq, hq, ite_and]
  have heq : transferMatrix (Kraus.transferMap (fun i => Matrix.zeroPad D (A i))) -
        transferMatrix (cornerReferenceMap (Matrix.zeroPad D σ) b) =
      Rc ai bi (Matrix.linearMapMatrix (Matrix.rectangularKrausMap A -
        Matrix.tracePrepareMap (α := Fin b) σ)) := by
    ext p q
    rw [Matrix.sub_apply]
    have ht := transferMatrix_mixedMapLM_apply
      (fun i => Matrix.zeroPad D (A i)) (fun i => Matrix.zeroPad D (A i)) p q
    rw [Kraus.mixedMapLM_self] at ht
    rw [ht]
    change (∑ i, Matrix.zeroPad D (A i) p.2 q.2 * star (Matrix.zeroPad D (A i) p.1 q.1)) -
      ((cornerProjection D b * Matrix.single q.2 q.1 1).trace • Matrix.zeroPad D σ) p.2 p.1 = _
    simp only [Matrix.trace_mul_single, Matrix.smul_apply, smul_eq_mul,
      cornerProjection, Matrix.diagonal_apply]
    have hR (T : Matrix (Fin a × Fin a) (Fin b × Fin b) ℂ) :
        Rc ai bi T p q = if hp : p.2.val < a ∧ p.1.val < a then
          if hq : q.2.val < b ∧ q.1.val < b then
            T (⟨p.2.val, hp.1⟩, ⟨p.1.val, hp.2⟩)
              (⟨q.2.val, hq.1⟩, ⟨q.1.val, hq.2⟩) else 0 else 0 := by
      change (if hp : p.2.val < a ∧ p.1.val < a then
        if hq : q.2.val < b ∧ q.1.val < b then
          Matrix.entryLinearMap ℂ ℂ
            ((⟨p.2.val, hp.1⟩, ⟨p.1.val, hp.2⟩) : Fin a × Fin a)
            ((⟨q.2.val, hq.1⟩, ⟨q.1.val, hq.2⟩) : Fin b × Fin b)
        else 0 else 0) T = _
      split_ifs <;> rfl
    rw [hR]
    by_cases hp : p.2.val < a ∧ p.1.val < a
    · rw [dite_eq_left hp]
      by_cases hq : q.2.val < b ∧ q.1.val < b
      · rw [dite_eq_left hq, hentry]
        simp [Matrix.zeroPad, hp.1, hp.2, hq.1, hq.2, Fin.ext_iff, eq_comm]
      · rw [dite_eq_right hq]
        rcases not_and_or.mp hq with hq | hq
        · by_cases h : q.1 = q.2
          · rw [h]
            simp [Matrix.zeroPad, hq]
          · simp [Matrix.zeroPad, hq, h]
        · by_cases h : q.1 = q.2
          · rw [← h]
            simp [Matrix.zeroPad, hq]
          · simp [Matrix.zeroPad, hq, h]
    · rw [dite_eq_right hp]
      rcases not_and_or.mp hp with hp | hp <;> simp [Matrix.zeroPad, hp]
  rw [heq]
  exact ((Rc ai bi).le_opNorm _).trans (mul_le_mul_of_nonneg_right hRc (norm_nonneg _))

end MPSPreparation
