/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.CommonDenominator
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalCodeHeights
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalContractionCost

/-!
# Bounds on intermediate rows in rational contraction

Sequential row propagation preserves a common denominator at each prefix.
Every partial scalar product at the next site has the denominator of the
new row. Norm bounds for these partial sums also give bounds for their
reduced rational coordinates.
-/

namespace TNLean.MPS.AreaLaw

namespace RationalRectMatrixCode

/-- Every partial scalar product has the product denominator and a norm bound
proportional to the number of terms already accumulated. -/
theorem partialDot_bounds {D N M R C : ℕ} (v w : Fin D → ℚ × ℚ)
    (s : Finset (Fin D)) (hN : 0 < N) (hM : 0 < M)
    (hv : ∀ i, HasGaussianIntegerDenominator N (decodeRationalComplex (v i)))
    (hw : ∀ i, HasGaussianIntegerDenominator M (decodeRationalComplex (w i)))
    (hvnorm : ∀ i, ‖decodeRationalComplex (v i)‖ ≤ (R : ℝ))
    (hwnorm : ∀ i, ‖decodeRationalComplex (w i)‖ ≤ (C : ℝ)) :
    HasGaussianIntegerDenominator (N * M)
      (decodeRationalComplex (∑ i ∈ s, RationalComplexCode.mul (v i) (w i))) ∧
    ‖decodeRationalComplex (∑ i ∈ s, RationalComplexCode.mul (v i) (w i))‖ ≤
      (s.card * R * C : ℕ) := by
  simp only [decodeRationalComplex_finset_sum, RationalComplexCode.decode_mul]
  refine ⟨HasGaussianIntegerDenominator.finset_sum (Nat.mul_pos hN hM)
    (fun i _hi ↦ (hv i).mul (hw i)), ?_⟩
  calc
    _ ≤ ∑ i ∈ s, ‖decodeRationalComplex (v i) * decodeRationalComplex (w i)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i ∈ s, (R : ℝ) * C := by
      apply Finset.sum_le_sum
      intro i _hi
      rw [norm_mul]
      exact mul_le_mul (hvnorm i) (hwnorm i) (norm_nonneg _) (Nat.cast_nonneg R)
    _ = (s.card * R * C : ℕ) := by simp [Nat.cast_mul, mul_assoc]

/-- One materialized row multiplication has one denominator factor for the
site and at most the row dimension times the two entry norm bounds. -/
theorem rowMul_bounds {D N M R C : ℕ} (v : Fin D → ℚ × ℚ)
    (A : RationalRectMatrixCode (Fin D) (Fin D)) (hN : 0 < N) (hM : 0 < M)
    (hv : ∀ i, HasGaussianIntegerDenominator N (decodeRationalComplex (v i)))
    (hA : ∀ i j, HasGaussianIntegerDenominator M (decodeRationalComplex (A i j)))
    (hvnorm : ∀ i, ‖decodeRationalComplex (v i)‖ ≤ (R : ℝ))
    (hAnorm : ∀ i j, ‖decodeRationalComplex (A i j)‖ ≤ (C : ℝ)) :
    ∀ j, HasGaussianIntegerDenominator (N * M) (decodeRationalComplex (rowMul v A j)) ∧
      ‖decodeRationalComplex (rowMul v A j)‖ ≤ (D * R * C : ℕ) := by
  intro j
  simpa only [rowMul, Finset.card_univ, Fintype.card_fin] using
    partialDot_bounds v (fun i ↦ A i j) Finset.univ hN hM hv
      (fun i ↦ hA i j) hvnorm (fun i ↦ hAnorm i j)

/-- Each row reached after a prefix of site matrices has one denominator
factor per site and an entry norm bound growing by at most `D C` per site. -/
theorem rowProduct_bounds {D N M R C : ℕ} (v : Fin D → ℚ × ℚ)
    (As : List (RationalRectMatrixCode (Fin D) (Fin D)))
    (hN : 0 < N) (hM : 0 < M)
    (hv : ∀ i, HasGaussianIntegerDenominator N (decodeRationalComplex (v i)))
    (hvnorm : ∀ i, ‖decodeRationalComplex (v i)‖ ≤ (R : ℝ))
    (hAs : ∀ A ∈ As, ∀ i j,
      HasGaussianIntegerDenominator M (decodeRationalComplex (A i j)))
    (hAsnorm : ∀ A ∈ As, ∀ i j, ‖decodeRationalComplex (A i j)‖ ≤ (C : ℝ)) :
    ∀ j, HasGaussianIntegerDenominator (N * M ^ As.length)
        (decodeRationalComplex (rowProduct v As j)) ∧
      ‖decodeRationalComplex (rowProduct v As j)‖ ≤ (R * (D * C) ^ As.length : ℕ) := by
  induction As generalizing N R v with
  | nil => simpa only [rowProduct_nil, List.length_nil, pow_zero, Nat.mul_one] using
      fun j ↦ And.intro (hv j) (hvnorm j)
  | cons A As ih =>
    have hnext := rowMul_bounds v A hN hM hv (hAs A (by simp)) hvnorm
      (hAsnorm A (by simp))
    have hrest := ih (rowMul v A) (Nat.mul_pos hN hM)
      (fun j ↦ (hnext j).1) (fun j ↦ (hnext j).2)
      (fun A hA ↦ hAs A (by simp [hA])) (fun A hA ↦ hAsnorm A (by simp [hA]))
    intro j
    rw [rowProduct_cons, List.length_cons]
    have hden : (N * M) * M ^ As.length = N * M ^ (As.length + 1) := by
      rw [pow_succ]
      ring
    have hnorm : (D * R * C) * (D * C) ^ As.length = R * (D * C) ^ (As.length + 1) := by
      rw [pow_succ]
      ring
    simpa only [hden, hnorm] using hrest j

/-- The preceding bounds hold simultaneously at every prefix length of the
actual sequential evaluator. -/
theorem rowProduct_take_bounds {D N M R C t : ℕ} (v : Fin D → ℚ × ℚ)
    (As : List (RationalRectMatrixCode (Fin D) (Fin D))) (ht : t ≤ As.length)
    (hN : 0 < N) (hM : 0 < M)
    (hv : ∀ i, HasGaussianIntegerDenominator N (decodeRationalComplex (v i)))
    (hvnorm : ∀ i, ‖decodeRationalComplex (v i)‖ ≤ (R : ℝ))
    (hAs : ∀ A ∈ As, ∀ i j,
      HasGaussianIntegerDenominator M (decodeRationalComplex (A i j)))
    (hAsnorm : ∀ A ∈ As, ∀ i j, ‖decodeRationalComplex (A i j)‖ ≤ (C : ℝ)) :
    ∀ j, HasGaussianIntegerDenominator (N * M ^ t)
        (decodeRationalComplex (rowProduct v (As.take t) j)) ∧
      ‖decodeRationalComplex (rowProduct v (As.take t) j)‖ ≤ (R * (D * C) ^ t : ℕ) := by
  simpa only [List.length_take, Nat.min_eq_left ht] using
    rowProduct_bounds v (As.take t) hN hM hv hvnorm
      (fun A hA ↦ hAs A (List.mem_of_mem_take hA))
      (fun A hA ↦ hAsnorm A (List.mem_of_mem_take hA))

/-- The zero-coordinate basis row used by open-chain contraction has denominator
one and unit entry bounds, so its prefixes need no initial numerical assumption. -/
theorem rowProduct_basis_take_bounds {D M C t : ℕ}
    (As : List (RationalRectMatrixCode (Fin D) (Fin D))) (ht : t ≤ As.length)
    (hM : 0 < M)
    (hAs : ∀ A ∈ As, ∀ i j,
      HasGaussianIntegerDenominator M (decodeRationalComplex (A i j)))
    (hAsnorm : ∀ A ∈ As, ∀ i j, ‖decodeRationalComplex (A i j)‖ ≤ (C : ℝ)) :
    ∀ j, HasGaussianIntegerDenominator (M ^ t)
        (decodeRationalComplex
          (rowProduct (fun a : Fin D ↦ if a.val = 0 then (1, 0) else 0) (As.take t) j)) ∧
      ‖decodeRationalComplex
          (rowProduct (fun a : Fin D ↦ if a.val = 0 then (1, 0) else 0) (As.take t) j)‖ ≤
        ((D * C) ^ t : ℕ) := by
  have hv : ∀ a : Fin D, HasGaussianIntegerDenominator 1
      (decodeRationalComplex (if a.val = 0 then (1, 0) else 0)) := by
    intro a
    split_ifs
    · exact ⟨by decide, ⟨1, by simp⟩⟩
    · exact ⟨by decide, ⟨0, by simp⟩⟩
  have hvnorm : ∀ a : Fin D,
      ‖decodeRationalComplex (if a.val = 0 then (1, 0) else 0)‖ ≤ (1 : ℝ) := by
    intro a
    split_ifs <;> simp
  simpa only [Nat.one_mul] using
    rowProduct_take_bounds (N := 1) (R := 1)
      (fun a : Fin D ↦ if a.val = 0 then (1, 0) else 0) As ht (by decide) hM hv
      (by simpa using hvnorm)
      hAs hAsnorm

/-- Both reduced rational coordinates of each intermediate row entry obey the
height bound obtained from its common denominator and norm bound. -/
theorem rowProduct_take_coordinate_heights {D N M R C t : ℕ} (v : Fin D → ℚ × ℚ)
    (As : List (RationalRectMatrixCode (Fin D) (Fin D))) (ht : t ≤ As.length)
    (hN : 0 < N) (hM : 0 < M)
    (hv : ∀ i, HasGaussianIntegerDenominator N (decodeRationalComplex (v i)))
    (hvnorm : ∀ i, ‖decodeRationalComplex (v i)‖ ≤ (R : ℝ))
    (hAs : ∀ A ∈ As, ∀ i j,
      HasGaussianIntegerDenominator M (decodeRationalComplex (A i j)))
    (hAsnorm : ∀ A ∈ As, ∀ i j, ‖decodeRationalComplex (A i j)‖ ≤ (C : ℝ)) (j : Fin D) :
    let out := rowProduct v (As.take t) j
    rationalHeight out.1 ≤ (N * M ^ t) * max 1 (R * (D * C) ^ t) ∧
      rationalHeight out.2 ≤ (N * M ^ t) * max 1 (R * (D * C) ^ t) := by
  have h := rowProduct_take_bounds v As ht hN hM hv hvnorm hAs hAsnorm j
  exact (RationalComplexCode.decode_height_iff _).mp (h.1.height_of_norm_le h.2)

end RationalRectMatrixCode

namespace RationalContractionCost

/-- Every prefix accumulator inside the counted scalar-product evaluator has
the product denominator and the corresponding partial-sum norm bound. -/
theorem dot_prefix_bounds {D a N M R C : ℕ} (ha : a ≤ D) (v w : Fin D → ℚ × ℚ)
    (hN : 0 < N) (hM : 0 < M)
    (hv : ∀ i, HasGaussianIntegerDenominator N (decodeRationalComplex (v i)))
    (hw : ∀ i, HasGaussianIntegerDenominator M (decodeRationalComplex (w i)))
    (hvnorm : ∀ i, ‖decodeRationalComplex (v i)‖ ≤ (R : ℝ))
    (hwnorm : ∀ i, ‖decodeRationalComplex (w i)‖ ≤ (C : ℝ)) :
    let out := (dot a (fun i ↦ v (Fin.castLE ha i)) (fun i ↦ w (Fin.castLE ha i))).run.1
    HasGaussianIntegerDenominator (N * M) (decodeRationalComplex out) ∧
      ‖decodeRationalComplex out‖ ≤ (a * R * C : ℕ) := by
  dsimp only
  rw [run_dot]
  simpa only [Finset.card_univ, Fintype.card_fin] using
    RationalRectMatrixCode.partialDot_bounds
      (fun i : Fin a ↦ v (Fin.castLE ha i)) (fun i : Fin a ↦ w (Fin.castLE ha i))
      Finset.univ hN hM (fun i ↦ hv _) (fun i ↦ hw _)
      (fun i ↦ hvnorm _) (fun i ↦ hwnorm _)

/-- Reduced numerator and denominator heights of both actual counted
scalar-product accumulator coordinates. -/
theorem dot_prefix_coordinate_heights {D a N M R C : ℕ} (ha : a ≤ D)
    (v w : Fin D → ℚ × ℚ) (hN : 0 < N) (hM : 0 < M)
    (hv : ∀ i, HasGaussianIntegerDenominator N (decodeRationalComplex (v i)))
    (hw : ∀ i, HasGaussianIntegerDenominator M (decodeRationalComplex (w i)))
    (hvnorm : ∀ i, ‖decodeRationalComplex (v i)‖ ≤ (R : ℝ))
    (hwnorm : ∀ i, ‖decodeRationalComplex (w i)‖ ≤ (C : ℝ)) :
    let out := (dot a (fun i ↦ v (Fin.castLE ha i)) (fun i ↦ w (Fin.castLE ha i))).run.1
    rationalHeight out.1 ≤ (N * M) * max 1 (a * R * C) ∧
      rationalHeight out.2 ≤ (N * M) * max 1 (a * R * C) := by
  have h := dot_prefix_bounds ha v w hN hM hv hw hvnorm hwnorm
  exact (RationalComplexCode.decode_height_iff _).mp (h.1.height_of_norm_le h.2)

/-- Every accumulator at the next site of sequential contraction satisfies
the prefix denominator and norm bounds. This combines the materialized row
with the actual next matrix `As[t]` and the counted scalar-product evaluator. -/
theorem rowProduct_next_dot_prefix_bounds {D a t N M R C : ℕ}
    (v : Fin D → ℚ × ℚ) (As : List (RationalRectMatrixCode (Fin D) (Fin D)))
    (ht : t < As.length) (ha : a ≤ D) (j : Fin D) (hN : 0 < N) (hM : 0 < M)
    (hv : ∀ i, HasGaussianIntegerDenominator N (decodeRationalComplex (v i)))
    (hvnorm : ∀ i, ‖decodeRationalComplex (v i)‖ ≤ (R : ℝ))
    (hAs : ∀ A ∈ As, ∀ i j,
      HasGaussianIntegerDenominator M (decodeRationalComplex (A i j)))
    (hAsnorm : ∀ A ∈ As, ∀ i j, ‖decodeRationalComplex (A i j)‖ ≤ (C : ℝ)) :
    let row := RationalRectMatrixCode.rowProduct v (As.take t)
    let out := (dot a (fun i ↦ row (Fin.castLE ha i))
      (fun i ↦ As[t] (Fin.castLE ha i) j)).run.1
    HasGaussianIntegerDenominator (N * M ^ (t + 1)) (decodeRationalComplex out) ∧
      ‖decodeRationalComplex out‖ ≤ (a * R * (D * C) ^ t * C : ℕ) := by
  intro row out
  have hrow := RationalRectMatrixCode.rowProduct_take_bounds v As ht.le hN hM
    hv hvnorm hAs hAsnorm
  have hdot := dot_prefix_bounds ha row (fun i ↦ As[t] i j)
    (Nat.mul_pos hN (pow_pos hM _)) hM (fun i ↦ (hrow i).1)
    (fun i ↦ hAs As[t] (List.getElem_mem ht) i j) (fun i ↦ (hrow i).2)
    (fun i ↦ hAsnorm As[t] (List.getElem_mem ht) i j)
  have hden : (N * M ^ t) * M = N * M ^ (t + 1) := by rw [pow_succ]; ring
  have hnorm : a * (R * (D * C) ^ t) * C = a * R * (D * C) ^ t * C := by ring
  simpa only [hden, hnorm] using hdot

end RationalContractionCost

end TNLean.MPS.AreaLaw
