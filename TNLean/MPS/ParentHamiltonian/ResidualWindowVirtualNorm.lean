/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.ResidualWindowCoordinates
import QICLean.Algebra.MatrixAux
/-!
# A uniform bound for the virtual prefix map

Left-canonical normalization implies that the sum of the squared Frobenius
norms of all words of a fixed length equals the bond dimension. Consequently,
the virtual map which sends a rectangular boundary to its right products
with the prefix words has norm at most the square root of that dimension.
The bound is independent of the prefix length, including length zero.

This is the elementary boundary estimate used in the residual form of
Nachtergaele's overlapping-window argument, arXiv:cond-mat/9410110,
Lemma commutation (ii), lines 2442--2531. It requires neither primitivity
nor a fixed-point hypothesis.
-/

open scoped Matrix Matrix.Norms.Frobenius InnerProductSpace BigOperators
namespace MPSTensor
variable {d D E L : ℕ}

/-- Taking the trace of left-canonical word normalization gives the total
squared Frobenius norm at every word length. This includes zero bond
dimension and zero length. -/
theorem sum_evalWord_frobenius_norm_sq_of_leftCanonical
    (B : MPSTensor d E) (hLeft : ∑ i, (B i)ᴴ * B i = 1) (K : ℕ) :
    (∑ u : Cfg d K, ‖Kraus.evalWord B (List.ofFn u)‖ ^ 2) = (E : ℝ) := by
  have h := congrArg (fun X : Matrix (Fin E) (Fin E) ℂ => (Matrix.trace X).re)
    (sum_evalWord_conjTranspose_mul_evalWord B hLeft K)
  simpa only [Matrix.trace_sum, Complex.re_sum,
    Matrix.trace_conjTranspose_mul_self_re_eq_frobenius_norm_sq,
    Matrix.trace_one, Fintype.card_fin, Complex.natCast_re] using h

/-- The right virtual prefix map has a bound independent of the prefix length.
Source: the boundary-word factorization in Nachtergaele,
arXiv:cond-mat/9410110, Lemma commutation (ii), lines 2442--2531. -/
theorem norm_residualWindowRightVirtualMapES_le_sqrt
    (B : MPSTensor (blockPhysDim d L) E) (hLeft : ∑ i, (B i)ᴴ * B i = 1) (K : ℕ) :
    ‖residualWindowRightVirtualMapES (d := d) (L := L) (D := D) B K‖ ≤ Real.sqrt E := by
  refine (residualWindowRightVirtualMapES (d := d) (L := L) (D := D) B K).opNorm_le_bound
    (Real.sqrt_nonneg _) ?_
  intro x
  obtain ⟨Y, rfl⟩ := (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E)).surjective x
  have hnorm : ‖residualWindowRightVirtualMapES (d := d) (L := L) (D := D) B K
      (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E) Y)‖ ^ 2 =
      ∑ u : Cfg (blockPhysDim d L) K, ‖Y * Kraus.evalWord B (List.ofFn u)‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    change (∑ u : Cfg (blockPhysDim d L) K, ∑ p : Fin E × Fin D,
      ‖(Y * Kraus.evalWord B (List.ofFn u)) p.2 p.1‖ ^ 2) = _
    apply Finset.sum_congr rfl
    intro u _
    rw [← (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E)).norm_map
      (Y * Kraus.evalWord B (List.ofFn u)), EuclideanSpace.norm_sq_eq]
    rfl
  have hbound : ‖residualWindowRightVirtualMapES (d := d) (L := L) (D := D) B K
      (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E) Y)‖ ^ 2 ≤ (E : ℝ) * ‖Y‖ ^ 2 := by
    rw [hnorm]
    calc
      (∑ u : Cfg (blockPhysDim d L) K, ‖Y * Kraus.evalWord B (List.ofFn u)‖ ^ 2) ≤
          ∑ u : Cfg (blockPhysDim d L) K, (‖Y‖ * ‖Kraus.evalWord B (List.ofFn u)‖) ^ 2 := by
        apply Finset.sum_le_sum
        intro u _
        exact pow_le_pow_left₀ (norm_nonneg _)
          (Matrix.frobenius_norm_mul Y (Kraus.evalWord B (List.ofFn u))) 2
      _ = ‖Y‖ ^ 2 * ∑ u : Cfg (blockPhysDim d L) K,
          ‖Kraus.evalWord B (List.ofFn u)‖ ^ 2 := by
        simp only [mul_pow, Finset.mul_sum]
      _ = (E : ℝ) * ‖Y‖ ^ 2 := by
        rw [sum_evalWord_frobenius_norm_sq_of_leftCanonical B hLeft K, mul_comm]
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg E),
    (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E)).norm_map]
  exact hbound
end MPSTensor
