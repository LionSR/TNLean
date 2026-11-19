/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalContractionTrace
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.ContractionIntermediateBounds
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.ContractionHeights
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.WeightedTransferBounds
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalArithmeticTraceCost
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalArithmeticTraceHeights

/-!
# Operation membership in rational coefficient contraction

Materializing a row concatenates the arithmetic records of its coordinates.
A scalar product at each coordinate adds one complex product to its preceding prefix.
-/

namespace TNLean.MPS.AreaLaw.RationalArithmeticTrace

/-- Each operation recorded when storing a row belongs to one coordinate evaluation. -/
theorem mem_vectorOfFnM_operations {α : Type} {D : ℕ} (f : Fin D → Arithmetic α)
    (op : Operation) (hop : op ∈ (Vector.ofFnM f).run.2) :
    ∃ i, op ∈ (f i).run.2 := by
  induction D with
  | zero =>
    rw [Vector.ofFnM_zero] at hop
    change op ∈ ([] : List Operation) at hop
    exact False.elim (List.not_mem_nil hop)
  | succ D ih =>
    rw [Vector.ofFnM_succ] at hop
    simp only [run_bind, run_pure, List.append_nil, List.mem_append] at hop
    rcases hop with h | h
    · obtain ⟨i, hi⟩ := ih (fun i ↦ f i.castSucc) h
      exact ⟨i.castSucc, hi⟩
    · exact ⟨Fin.last D, h⟩

end TNLean.MPS.AreaLaw.RationalArithmeticTrace

namespace TNLean.MPS.AreaLaw.RationalContractionTrace

open RationalArithmeticTrace

/-- Storing a matrix-product row introduces no operations outside its scalar products. -/
theorem mem_rowMul_operations {D : ℕ} (v : Fin D → ℚ × ℚ)
    (A : RationalRectMatrixCode (Fin D) (Fin D)) (op : Operation)
    (hop : op ∈ (rowMul v A).run.2) :
    ∃ j, op ∈ (dot D v (fun i ↦ A i j)).run.2 := by
  apply mem_vectorOfFnM_operations (fun j ↦ dot D v (fun i ↦ A i j)) op
  simpa only [rowMul, run_bind, run_pure, List.append_nil] using hop

/-- At a successor coordinate the record contains precisely the preceding prefix,
the new scalar multiplication, and the addition of its value to the prefix. -/
theorem mem_dot_succ_operations (D : ℕ) (v w : Fin (D + 1) → ℚ × ℚ) (op : Operation) :
    let prev := dot D (fun i ↦ v i.castSucc) (fun i ↦ w i.castSucc)
    let term := complexMul (v (Fin.last D)) (w (Fin.last D))
    op ∈ (dot (D + 1) v w).run.2 ↔ op ∈ prev.run.2 ∨ op ∈ term.run.2 ∨
      op ∈ (complexAdd prev.run.1 term.run.1).run.2 := by
  simp only [dot, run_bind, List.mem_append]

/-- A common denominator for each input vector bounds every recorded operand and
result, including the additions of actual prefix sums. -/
theorem dot_operation_height_le {D N M R C S : ℕ} (v w : Fin D → ℚ × ℚ)
    (hN : 0 < N) (hM : 0 < M)
    (hv : ∀ i, HasGaussianIntegerDenominator N (decodeRationalComplex (v i)))
    (hw : ∀ i, HasGaussianIntegerDenominator M (decodeRationalComplex (w i)))
    (hr : ∀ i, ‖decodeRationalComplex (v i)‖ ≤ (R : ℝ))
    (hc : ∀ i, ‖decodeRationalComplex (w i)‖ ≤ (C : ℝ))
    (hx : N * max 1 R ≤ S) (hy : M * max 1 C ≤ S)
    (hs : N * M * max 1 (D * R * C) ≤ S)
    (op : Operation) (hop : op ∈ (dot D v w).run.2) :
    op.height ≤ 2 * S ^ 4 := by
  induction D with
  | zero =>
    change op ∈ ([] : List Operation) at hop
    exact False.elim (List.not_mem_nil hop)
  | succ D ih =>
    have hmono (k : ℕ) (hk : k ≤ D + 1) :
        N * M * max 1 (k * R * C) ≤ S :=
      le_trans (Nat.mul_le_mul_left _ (max_le_max_left _
        (Nat.mul_le_mul_right C (Nat.mul_le_mul_right R hk)))) hs
    rcases (mem_dot_succ_operations D v w op).mp hop with hp | hm | ha
    · exact ih _ _ (fun i ↦ hv i.castSucc) (fun i ↦ hw i.castSucc)
        (fun i ↦ hr i.castSucc) (fun i ↦ hc i.castSucc) (hmono D (by omega)) hp
    · exact (Operation.height_le_iff _ _).mpr (complexMul_operation_heights _ _
        (((hv _).height_of_norm_le (hr _)).mono hx)
        (((hw _).height_of_norm_le (hc _)).mono hy) op hm)
    · have hp := RationalRectMatrixCode.partialDot_bounds
          (fun i : Fin D ↦ v i.castSucc) (fun i : Fin D ↦ w i.castSucc)
          Finset.univ hN hM (fun i ↦ hv _) (fun i ↦ hw _) (fun i ↦ hr _) (fun i ↦ hc _)
      simp only [Finset.card_univ, Fintype.card_fin] at hp
      have ht := (hv (Fin.last D)).mul (hw (Fin.last D))
      have htNorm : ‖decodeRationalComplex (v (Fin.last D)) *
          decodeRationalComplex (w (Fin.last D))‖ ≤ ((R * C : ℕ) : ℝ) := by
        rw [norm_mul, Nat.cast_mul]
        exact mul_le_mul (hr _) (hc _) (norm_nonneg _) (Nat.cast_nonneg _)
      rw [run_complexMul, (dot_value_length _ _ _).1] at ha
      have htS : N * M * max 1 (R * C) ≤ S := by simpa using hmono 1 (by omega)
      have ht' := (ht.height_of_norm_le htNorm).mono htS
      rw [← RationalComplexCode.decode_mul] at ht'
      have hh := complexAdd_operation_heights _ _
        ((hp.1.height_of_norm_le hp.2).mono (hmono D (by omega))) ht' op ha
      exact ((Operation.height_le_iff _ _).mpr hh).trans
        (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by
          have : 1 ≤ N * max 1 R := Nat.one_le_iff_ne_zero.mpr
            (Nat.mul_ne_zero (by omega) (by omega))
          omega) (by decide : 2 ≤ 4)))

/-- The scalar-product height bound holds simultaneously for every operation
used to materialize the output row. -/
theorem rowMul_operation_height_le {D N M R C S : ℕ} (v : Fin D → ℚ × ℚ)
    (A : RationalRectMatrixCode (Fin D) (Fin D)) (hN : 0 < N) (hM : 0 < M)
    (hv : ∀ i, HasGaussianIntegerDenominator N (decodeRationalComplex (v i)))
    (hw : ∀ i j, HasGaussianIntegerDenominator M (decodeRationalComplex (A i j)))
    (hr : ∀ i, ‖decodeRationalComplex (v i)‖ ≤ (R : ℝ))
    (hc : ∀ i j, ‖decodeRationalComplex (A i j)‖ ≤ (C : ℝ))
    (hx : N * max 1 R ≤ S) (hy : M * max 1 C ≤ S)
    (hs : N * M * max 1 (D * R * C) ≤ S)
    (op : Operation) (hop : op ∈ (rowMul v A).run.2) :
    op.height ≤ 2 * S ^ 4 := by
  obtain ⟨j, hj⟩ := mem_rowMul_operations v A op hop
  exact dot_operation_height_le v _ hN hM hv (fun i ↦ hw i j) hr (fun i ↦ hc i j)
    hx hy hs op hj

/-- A materialized chain with positive norm budgets incurs one common
denominator factor per site, uniformly for every operation in the record. -/
theorem rowProduct_operation_height_le {D N M R C S : ℕ} (v : Fin D → ℚ × ℚ)
    (As : List (RationalRectMatrixCode (Fin D) (Fin D))) (hD : 0 < D)
    (hN : 0 < N) (hM : 0 < M) (hR : 0 < R) (hC : 0 < C)
    (hv : ∀ i, HasGaussianIntegerDenominator N (decodeRationalComplex (v i)))
    (hr : ∀ i, ‖decodeRationalComplex (v i)‖ ≤ (R : ℝ))
    (hw : ∀ A ∈ As, ∀ i j, HasGaussianIntegerDenominator M (decodeRationalComplex (A i j)))
    (hc : ∀ A ∈ As, ∀ i j, ‖decodeRationalComplex (A i j)‖ ≤ (C : ℝ))
    (hy : M * C ≤ S) (hs : N * R * (M * D * C) ^ As.length ≤ S)
    (op : Operation) (hop : op ∈ (rowProduct v As).run.2) : op.height ≤ 2 * S ^ 4 := by
  induction As generalizing N R v with
  | nil => exact False.elim (List.not_mem_nil hop)
  | cons A As ih =>
    have hnext := RationalRectMatrixCode.rowMul_bounds v A hN hM hv
      (hw A (by simp)) hr (hc A (by simp))
    have hfactor : 1 ≤ M * D * C := Nat.mul_pos (Nat.mul_pos hM hD) hC
    have hone : N * R * (M * D * C) ≤ S :=
      (Nat.mul_le_mul_left (N * R) (by
        simpa only [pow_one] using
          Nat.pow_le_pow_right hfactor (show 1 ≤ (A :: As).length by simp))).trans hs
    simp only [rowProduct, run_bind, List.mem_append, (rowMul_value_length v A).1] at hop
    rcases hop with h | h
    · apply rowMul_operation_height_le v A hN hM hv (hw A (by simp)) hr (hc A (by simp))
        _ _ _ op h
      · rw [max_eq_right hR]
        exact (Nat.le_mul_of_pos_right _ hfactor).trans hone
      · simpa only [max_eq_right (show 1 ≤ C from hC)] using hy
      · rw [max_eq_right (show 1 ≤ D * R * C from Nat.mul_pos (Nat.mul_pos hD hR) hC)]
        convert hone using 1; ring
    · apply ih _ (Nat.mul_pos hN hM) (show 0 < D * R * C by positivity)
        (fun i ↦ (hnext i).1) (fun i ↦ (hnext i).2)
        (fun A hA ↦ hw A (List.mem_cons_of_mem _ hA))
        (fun A hA ↦ hc A (List.mem_cons_of_mem _ hA)) _ h
      simpa only [List.length_cons, pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        using hs

/-- All coefficient operations, including the final scalar cap, obey a uniform
height bound obtained from the common denominator and the entry norm budget. -/
theorem coefficient_maxHeight_le {q D n M C H : ℕ} (A : OBCChainTensor q D n)
    (cap : ℚ × ℚ) (P : OBCChainTensor.ParameterIndex A → ℚ × ℚ) (σ : Fin n → Fin q)
    (hM : 0 < M) (hC : 0 < C)
    (hcap : HasRationalComplexCoordinatesOfHeight H (decodeRationalComplex cap))
    (hp : ∀ e, HasGaussianIntegerDenominator M (decodeRationalComplex (P e)))
    (hn : ∀ e, ‖decodeRationalComplex (P e)‖ ≤ (C : ℝ)) :
    maxHeight (coefficientOfRationalParameters A cap P σ).run.2 ≤
      2 * (max H (max (M * C) ((M * D * C) ^ n))) ^ 4 := by
  let v := fun a : Fin D ↦ if a.val = 0 then ((1, 0) : ℚ × ℚ) else 0
  let As := List.ofFn fun p : Fin n ↦ OBCChainTensor.zeroPadRationalParameters A P p (σ p)
  let S := max H (max (M * C) ((M * D * C) ^ n))
  have hv (i : Fin D) : HasGaussianIntegerDenominator 1 (decodeRationalComplex (v i)) := by
    dsimp only [v]
    split
    · exact ⟨by decide, 1, by simp [decodeRationalComplex]; rfl⟩
    · exact ⟨by decide, 0, by simp [decodeRationalComplex]; rfl⟩
  have hr (i : Fin D) : ‖decodeRationalComplex (v i)‖ ≤ ((1 : ℕ) : ℝ) := by
    dsimp only [v]
    split
    · rw [show decodeRationalComplex (1, 0) = 1 by simp [decodeRationalComplex]; rfl]
      simp
    · rw [decodeRationalComplex_zero]
      simp
  have hmats (B) (hb : B ∈ As) (i j : Fin D) :
      HasGaussianIntegerDenominator M (decodeRationalComplex (B i j)) ∧
      ‖decodeRationalComplex (B i j)‖ ≤ (C : ℝ) := by
    obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hb
    exact OBCChainTensor.zeroPadRationalParameters_bounds A P hM hp hn p (σ p) i j
  have hpow : (M * D * C) ^ n ≤ S :=
    (le_max_right _ _).trans (le_max_right _ _)
  apply (maxHeight_le_iff _ _).mpr
  intro op hop
  change op ∈ (contract cap v As _).run.2 at hop
  simp only [contract, run_bind, List.mem_append, (rowProduct_value_length v As).1] at hop
  rcases hop with hop | hop
  · apply rowProduct_operation_height_le v As A.bondBound_pos (by decide : 0 < 1) hM
        (by decide : 0 < 1) hC hv hr (fun B h i j ↦ (hmats B h i j).1)
        (fun B h i j ↦ (hmats B h i j).2) _ _ op hop
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · simp [As]
  · have hrow := RationalRectMatrixCode.rowProduct_bounds v As (by decide : 0 < 1) hM
        hv hr (fun B h i j ↦ (hmats B h i j).1) (fun B h i j ↦ (hmats B h i j).2)
        (⟨0, A.bondBound_pos⟩ : Fin D)
    apply (Operation.height_le_iff _ _).mpr
    apply complexMul_operation_heights _ _ (hcap.mono (le_max_left _ _)) _ op hop
    apply (hrow.1.height_of_norm_le hrow.2).mono
    simp only [As, List.length_ofFn, Nat.one_mul,
      mul_pow, Nat.mul_assoc, max_eq_right (show 1 ≤ D ^ n * C ^ n from
        Nat.mul_pos (pow_pos A.bondBound_pos _) (pow_pos hC _))]
    exact (le_max_right _ _).trans (le_max_right _ _)

/-- Polynomial schoolbook charge for the complete coefficient record when each
input coordinate has height at most two to the given bit budget. -/
theorem coefficient_schoolbookCharge_le {q D n h : ℕ} (A : OBCChainTensor q D n)
    (cap : ℚ × ℚ) (P : OBCChainTensor.ParameterIndex A → ℚ × ℚ) (σ : Fin n → Fin q)
    (hcap : HasRationalComplexCoordinatesOfHeight (2 ^ h) (decodeRationalComplex cap))
    (hp : ∀ e, HasRationalComplexCoordinatesOfHeight (2 ^ h) (decodeRationalComplex (P e))) :
    let b := h * (2 * (n * q * D ^ 2))
    let k := (b + D + (h + 1)) * (n + 1)
    schoolbookCharge (coefficientOfRationalParameters A cap P σ).run.2 ≤
      (8 * n * D ^ 2 + 6) * 8 * (1 + k * 4 + 2) ^ 2 := by
  intro b k
  obtain ⟨M, hM, hbound, hden⟩ := exists_common_gaussianInteger_denominator hp
  have hm : M ≤ 2 ^ b := hbound.trans (by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left h
      (Nat.mul_le_mul_left 2 (OBCChainTensor.card_parameterIndex_le A))))
  let C := 2 ^ (h + 1)
  have hc : 0 < C := pow_pos (by decide) _
  have hn (e) : ‖decodeRationalComplex (P e)‖ ≤ (C : ℝ) := by
    simpa only [C, pow_succ, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_comm]
      using (hp e).norm_le_two_mul
  have ht := coefficient_maxHeight_le A cap P σ hM hc hcap hden hn
  let f := b + D + (h + 1)
  have hf : M * D * C ≤ 2 ^ f := by
    simpa only [f, C, pow_add] using Nat.mul_le_mul_right C
      (Nat.mul_le_mul hm (Nat.lt_two_pow_self.le : D ≤ 2 ^ D))
  have hfk : f ≤ k := Nat.le_mul_of_pos_right f (Nat.succ_pos _)
  have hS : max (2 ^ h) (max (M * C) ((M * D * C) ^ n)) ≤ 2 ^ k := by
    apply max_le
    · exact Nat.pow_le_pow_right (by decide) ((show h ≤ f by dsimp [f]; omega).trans hfk)
    apply max_le
    · exact (Nat.mul_le_mul_right C (Nat.le_mul_of_pos_right M A.bondBound_pos)).trans
        (hf.trans (Nat.pow_le_pow_right (by decide) hfk))
    · apply (Nat.pow_le_pow_left hf n).trans
      rw [← pow_mul]
      exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left f (Nat.le_succ n))
  have hheight := ht.trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hS 4))
  rw [← pow_mul] at hheight
  have hbinary : maxHeight (coefficientOfRationalParameters A cap P σ).run.2 ≤
      2 ^ (1 + k * 4) := by simpa only [pow_add, pow_one] using hheight
  simpa only [(coefficientOfRationalParameters_value_length A cap P σ).2] using
    schoolbookCharge_le_of_maxHeight_le_two_pow hbinary

end TNLean.MPS.AreaLaw.RationalContractionTrace
