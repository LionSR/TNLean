/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Operator.ReductionComposition
import TNLean.MPS.Operator.ActionTensorReduction

/-!
# Nilpotent remainders of composite reductions

Let `(V₁, W₁)` reduce `C` onto `B` and `(V₂, W₂)` reduce `B` onto `A`, with residual letters
`N^i = C^i - W₁ B^i V₁` and `M^i = B^i - W₂ A^i V₂` whose words vanish at lengths `N₁` and
`N₂` respectively (MGSC18, Definition 8).  The composite reduction `(V₂ V₁, W₁ W₂)`
(`MPTensor.IsReduction.trans`) has residual letters `R^i = N^i + W₁ M^i V₁`, and every word
of `R` of length `2 N₁ + N₂` vanishes.  The additive bound `N₁ + N₂` is false in general: a
chain of six basis vectors with `N₁ = 3`, `N₂ = 2` has a nonzero residual word of length five.

The proof expands residual words in three steps, all by induction on words:

* `V₁ R^w W₁ = M^w`, and `V₁ R^w N^q W₁ = 0` for nonempty `q`;
* `N^p R^w W₁ = 0` once `|p| + |w| ≥ N₁ + N₂`;
* `R^w N^q = 0` once `|w| + |q| ≥ 2 N₁ + N₂`.

The residual bound is unchanged when a reduction is tensored with an identity strand on a
stacked product of matrix product operators or on an action tensor, and when it is
transported along an invertible intertwiner of letters such as the bond associator.

These are the composite reductions of fusion trees in arXiv:2502.20257, display preceding
`eq:3-cocycle`, `main.tex` lines 1506--1535, and of arXiv:2203.12563, `sec:PBC`, lines
1026--1060, where the associator is read off on words longer than the nilpotency length of the
off-diagonal tails.

## Main results

* `MPTensor.IsReduction.mul_evalWord_reductionResidual_trans_mul`
* `MPTensor.IsReduction.isReductionResidualNilpotencyBound_trans`
* `MPSTensor.isReductionResidualNilpotencyBound_of_intertwine`
* `MPOTensor.isReductionResidualNilpotencyBound_mulTensor_kronId`,
  `MPOTensor.isReductionResidualNilpotencyBound_mulTensor_idKron`
* `MPOTensor.isReductionResidualNilpotencyBound_actTensor_kronId`,
  `MPOTensor.isReductionResidualNilpotencyBound_actTensor_idKron`
-/

open MPTensor

open scoped Matrix Kronecker

namespace MPSTensor

variable {α : Type*} {D₁ D₂ D₃ : ℕ}

/-- The residual letters of a composite reduction: `R^i = N^i + W₁ M^i V₁`, where `N` and `M`
are the residual letters of the two factors.

Source: arXiv:1706.07329v2, Proposition 21, `cornerproblem.tex` lines 3142--3144 (the residual
letters), applied to the composite of arXiv:2502.20257, `main.tex` lines 1506--1535. -/
theorem reductionResidual_trans_apply (C : MPTensor α (Fin D₃)) (B : MPTensor α (Fin D₂))
    (A : MPTensor α (Fin D₁)) (V₁ : Matrix (Fin D₂) (Fin D₃) ℂ) (W₁ : Matrix (Fin D₃) (Fin D₂) ℂ)
    (V₂ : Matrix (Fin D₁) (Fin D₂) ℂ) (W₂ : Matrix (Fin D₂) (Fin D₁) ℂ) (i : α) :
    reductionResidual C A (V₂ * V₁) (W₁ * W₂) i =
      reductionResidual C B V₁ W₁ i + W₁ * reductionResidual B A V₂ W₂ i * V₁ := by
  simp only [reductionResidual, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  abel

section IsReduction

open MPTensor.IsReduction

variable {C : MPTensor α (Fin D₃)} {B : MPTensor α (Fin D₂)} {A : MPTensor α (Fin D₁)}
  {V₁ : Matrix (Fin D₂) (Fin D₃) ℂ} {W₁ : Matrix (Fin D₃) (Fin D₂) ℂ}
  {V₂ : Matrix (Fin D₁) (Fin D₂) ℂ} {W₂ : Matrix (Fin D₂) (Fin D₁) ℂ}

private theorem _root_.MPTensor.IsReduction.evalWord_reductionResidual_trans_append_singleton
    (w : List α)
    (x : α) :
    Kraus.evalWord (reductionResidual C A (V₂ * V₁) (W₁ * W₂)) (w ++ [x]) =
      Kraus.evalWord (reductionResidual C A (V₂ * V₁) (W₁ * W₂)) w *
          reductionResidual C B V₁ W₁ x +
        Kraus.evalWord (reductionResidual C A (V₂ * V₁) (W₁ * W₂)) w * W₁ *
          reductionResidual B A V₂ W₂ x * V₁ := by
  rw [Kraus.evalWord_append, Kraus.evalWord_cons, Kraus.evalWord_nil, Matrix.mul_one,
    reductionResidual_trans_apply C B A]
  simp only [Matrix.mul_add, Matrix.mul_assoc]

/-- **Compressing a composite residual word.** For a composite reduction, the first
reduction compresses every residual word of the composite to the residual word of the second
factor, `V₁ R^w W₁ = M^w`, and annihilates it against a nonempty residual word of the first
factor, `V₁ R^w N^q W₁ = 0`.  Only the first reduction is used.

Source: arXiv:1706.07329v2, Lemma `lem:VNW=0`, `cornerproblem.tex` lines 3946--3970, applied
to the composite reductions of arXiv:2502.20257, `main.tex` lines 1506--1535. -/
theorem _root_.MPTensor.IsReduction.mul_evalWord_reductionResidual_trans_mul
    (h₁ : IsReduction C B V₁ W₁)
    (w : List α) :
    V₁ * Kraus.evalWord (reductionResidual C A (V₂ * V₁) (W₁ * W₂)) w * W₁ =
        Kraus.evalWord (reductionResidual B A V₂ W₂) w ∧
      ∀ q : List α, q ≠ [] →
        V₁ * Kraus.evalWord (reductionResidual C A (V₂ * V₁) (W₁ * W₂)) w *
          Kraus.evalWord (reductionResidual C B V₁ W₁) q * W₁ = 0 := by
  induction w using List.reverseRecOn with
  | nil =>
      refine ⟨by simp [h₁.mul_eq_one], fun q hq ↦ ?_⟩
      simpa using h₁.evalWord_reductionResidual_sandwich_eq_zero q hq
  | append_singleton w x ih =>
      obtain ⟨ih₁, ih₂⟩ := ih
      set Y := Kraus.evalWord (reductionResidual C A (V₂ * V₁) (W₁ * W₂)) w
      set N := reductionResidual C B V₁ W₁
      set M := reductionResidual B A V₂ W₂
      rw [evalWord_reductionResidual_trans_append_singleton (B := B)]
      constructor
      · have hx := ih₂ [x] (List.cons_ne_nil _ _)
        simp only [Kraus.evalWord_cons, Kraus.evalWord_nil, Matrix.mul_one] at hx
        have key : V₁ * (Y * N x + Y * W₁ * M x * V₁) * W₁ =
            V₁ * Y * N x * W₁ + (V₁ * Y * W₁) * M x * (V₁ * W₁) := by
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
        rw [key, hx, ih₁, h₁.mul_eq_one, Matrix.mul_one, zero_add, Kraus.evalWord_append,
          Kraus.evalWord_cons, Kraus.evalWord_nil, Matrix.mul_one]
      · intro q hq
        have hxq := ih₂ (x :: q) (List.cons_ne_nil _ _)
        rw [Kraus.evalWord_cons] at hxq
        have hq0 := h₁.evalWord_reductionResidual_sandwich_eq_zero q hq
        have key : V₁ * (Y * N x + Y * W₁ * M x * V₁) * Kraus.evalWord N q * W₁ =
            V₁ * Y * (N x * Kraus.evalWord N q) * W₁ +
              (V₁ * Y * W₁) * M x * (V₁ * Kraus.evalWord N q * W₁) := by
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
        rw [key, hxq, hq0, Matrix.mul_zero, add_zero]

private theorem _root_.MPTensor.IsReduction.evalWord_reductionResidual_mul_trans_mul_eq_zero
    (h₁ : IsReduction C B V₁ W₁)
    {N₁ N₂ : ℕ} (hN₁ : IsReductionResidualNilpotencyBound C B V₁ W₁ N₁)
    (hN₂ : IsReductionResidualNilpotencyBound B A V₂ W₂ N₂) (w : List α) :
    ∀ p : List α, N₁ + N₂ ≤ p.length + w.length →
      Kraus.evalWord (reductionResidual C B V₁ W₁) p *
          Kraus.evalWord (reductionResidual C A (V₂ * V₁) (W₁ * W₂)) w * W₁ = 0 := by
  induction w with
  | nil =>
      intro p hp
      rw [evalWord_reductionResidual_eq_zero_of_bound_le_length hN₁ p (by simp at hp; omega)]
      simp
  | cons x w ih =>
      intro p hp
      set N := reductionResidual C B V₁ W₁
      set M := reductionResidual B A V₂ W₂
      set R := reductionResidual C A (V₂ * V₁) (W₁ * W₂)
      have hstep := ih (p ++ [x]) (by simp at hp ⊢; omega)
      rw [Kraus.evalWord_append, Kraus.evalWord_cons, Kraus.evalWord_nil,
        Matrix.mul_one] at hstep
      have hG : V₁ * Kraus.evalWord R w * W₁ = Kraus.evalWord M w :=
        (h₁.mul_evalWord_reductionResidual_trans_mul (A := A) (V₂ := V₂) (W₂ := W₂) w).1
      have key : Kraus.evalWord N p * Kraus.evalWord R (x :: w) * W₁ =
          Kraus.evalWord N p * N x * Kraus.evalWord R w * W₁ +
            Kraus.evalWord N p * W₁ * (M x * (V₁ * Kraus.evalWord R w * W₁)) := by
        rw [Kraus.evalWord_cons, show R x = N x + W₁ * M x * V₁ from
          reductionResidual_trans_apply C B A V₁ W₁ V₂ W₂ x]
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      rw [key, hstep, hG, zero_add, ← Kraus.evalWord_cons]
      by_cases hp₁ : N₁ ≤ p.length
      · rw [evalWord_reductionResidual_eq_zero_of_bound_le_length hN₁ p hp₁]
        simp
      · rw [evalWord_reductionResidual_eq_zero_of_bound_le_length hN₂ (x :: w)
          (by simp at hp ⊢; omega)]
        simp

private theorem _root_.MPTensor.IsReduction.evalWord_reductionResidual_trans_mul_eq_zero
    (h₁ : IsReduction C B V₁ W₁)
    {N₁ N₂ : ℕ} (hN₁ : IsReductionResidualNilpotencyBound C B V₁ W₁ N₁)
    (hN₂ : IsReductionResidualNilpotencyBound B A V₂ W₂ N₂) (w : List α) :
    ∀ q : List α, 2 * N₁ + N₂ ≤ w.length + q.length →
      Kraus.evalWord (reductionResidual C A (V₂ * V₁) (W₁ * W₂)) w *
          Kraus.evalWord (reductionResidual C B V₁ W₁) q = 0 := by
  induction w using List.reverseRecOn with
  | nil =>
      intro q hq
      rw [evalWord_reductionResidual_eq_zero_of_bound_le_length hN₁ q (by simp at hq; omega)]
      simp
  | append_singleton w x ih =>
      intro q hq
      set N := reductionResidual C B V₁ W₁
      set M := reductionResidual B A V₂ W₂
      set Y := Kraus.evalWord (reductionResidual C A (V₂ * V₁) (W₁ * W₂)) w
      have hxq := ih (x :: q) (by simp at hq ⊢; omega)
      rw [Kraus.evalWord_cons] at hxq
      rw [evalWord_reductionResidual_trans_append_singleton (B := B)]
      have key : (Y * N x + Y * W₁ * M x * V₁) * Kraus.evalWord N q =
          Y * (N x * Kraus.evalWord N q) + (Y * W₁) * M x * (V₁ * Kraus.evalWord N q) := by
        simp only [Matrix.add_mul, Matrix.mul_assoc]
      rw [key, hxq, zero_add]
      by_cases hq₁ : N₁ ≤ q.length
      · rw [evalWord_reductionResidual_eq_zero_of_bound_le_length hN₁ q hq₁]
        simp
      · have hY : Y * W₁ = 0 := by
          simpa [Y] using evalWord_reductionResidual_mul_trans_mul_eq_zero h₁ hN₁ hN₂ w []
            (by simp at hq ⊢; omega)
        rw [hY]
        simp

/-- **Nilpotency of the remainder of a composite reduction.** If `(V₁, W₁)` reduces `C` onto
`B` with residual nilpotency bound `N₁` and `(V₂, W₂)` reduces `B` onto `A` with residual
nilpotency bound `N₂`, then the composite `(V₂ V₁, W₁ W₂)` has residual nilpotency bound
`2 N₁ + N₂`.  The reduction property of the second factor is not needed.

The bound cannot be lowered to `N₁ + N₂`: for a single letter acting as the shift along six
basis vectors, reduced onto the middle two and then onto a zero block, one has `N₁ = 3`,
`N₂ = 2`, and a nonzero composite residual word of length five.

Source: arXiv:1706.07329v2, Definition 8 (`cornerproblem.tex` lines 3147--3152) and Lemma
`lem:VNW=0` (lines 3946--3970); the composite reductions are those of arXiv:2502.20257,
`main.tex` lines 1506--1535, and arXiv:2203.12563, lines 1026--1060. -/
theorem _root_.MPTensor.IsReduction.isReductionResidualNilpotencyBound_trans
    (h₁ : IsReduction C B V₁ W₁)
    {N₁ N₂ : ℕ} (hN₁ : IsReductionResidualNilpotencyBound C B V₁ W₁ N₁)
    (hN₂ : IsReductionResidualNilpotencyBound B A V₂ W₂ N₂) :
    IsReductionResidualNilpotencyBound C A (V₂ * V₁) (W₁ * W₂) (2 * N₁ + N₂) := by
  intro w hw
  simpa using evalWord_reductionResidual_trans_mul_eq_zero h₁ hN₁ hN₂ w [] (by simp [hw])

end IsReduction

/-- **Transport of a residual bound along an invertible intertwiner.** If `P` is invertible
with inverse `Q` and intertwines the letters, `B' i P = P B i`, then the residual letters of
the transported reduction `(V Q, P W)` of `B'` are those of `(V, W)` conjugated by `P`, so every
residual nilpotency bound is preserved.

Source: arXiv:1706.07329v2, Definition 8, `cornerproblem.tex` lines 3147--3152; the
intertwiner is the bond associator of arXiv:1606.00608, lines 995--999. -/
theorem isReductionResidualNilpotencyBound_of_intertwine {B' : MPTensor α (Fin D₂)}
    {B : MPTensor α (Fin D₃)} {A : MPTensor α (Fin D₁)} {V : Matrix (Fin D₁) (Fin D₃) ℂ}
    {W : Matrix (Fin D₃) (Fin D₁) ℂ} {P : Matrix (Fin D₂) (Fin D₃) ℂ}
    {Q : Matrix (Fin D₃) (Fin D₂) ℂ} (hQP : Q * P = 1) (hPQ : P * Q = 1)
    (hB : ∀ i, B' i * P = P * B i) {N : ℕ}
    (hN : IsReductionResidualNilpotencyBound B A V W N) :
    IsReductionResidualNilpotencyBound B' A (V * Q) (P * W) N := by
  have hletter : ∀ i, reductionResidual B' A (V * Q) (P * W) i =
      P * reductionResidual B A V W i * Q := by
    intro i
    have hB' : B' i = P * B i * Q := by
      rw [← hB i, Matrix.mul_assoc, hPQ, Matrix.mul_one]
    simp only [reductionResidual, hB', Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  have hword : ∀ w : List α, Kraus.evalWord (reductionResidual B' A (V * Q) (P * W)) w =
      P * Kraus.evalWord (reductionResidual B A V W) w * Q := by
    intro w
    induction w with
    | nil => simp [hPQ]
    | cons i w ih =>
        rw [Kraus.evalWord_cons, Kraus.evalWord_cons, ih, hletter]
        calc
          P * reductionResidual B A V W i * Q *
              (P * Kraus.evalWord (reductionResidual B A V W) w * Q) =
              P * reductionResidual B A V W i * (Q * P) *
                Kraus.evalWord (reductionResidual B A V W) w * Q := by
            simp only [Matrix.mul_assoc]
          _ = _ := by rw [hQP, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  intro w hw
  rw [hword, hN w hw]
  simp

end MPSTensor

namespace MPOTensor

variable {d D₁ D₂ D₃ : ℕ}

private theorem sub_kronecker' {l m n p : Type*} (X Y : Matrix l m ℂ) (Z : Matrix n p ℂ) :
    (X - Y) ⊗ₖ Z = X ⊗ₖ Z - Y ⊗ₖ Z := by
  ext
  simp [sub_mul]

private theorem kronecker_sub' {l m n p : Type*} (Z : Matrix n p ℂ) (X Y : Matrix l m ℂ) :
    Z ⊗ₖ (X - Y) = Z ⊗ₖ X - Z ⊗ₖ Y := by
  ext
  simp [mul_sub]

/-- **An identity strand on the right preserves the residual bound.** If the residual words of
`(V, W)` from `X` to `A` vanish at length `N`, so do those of `(V ⊗ 1, W ⊗ 1)` from `X · P`
to `A · P`: the latter are sums of Kronecker products of the former with words of `P`.

Source: arXiv:1706.07329v2, Definition 8, `cornerproblem.tex` lines 3147--3152; the identity
strand beside a fusion tensor is that of arXiv:2502.20257, `main.tex` lines 1506--1535. -/
theorem isReductionResidualNilpotencyBound_mulTensor_kronId {X : MPOTensor d D₂}
    {A : MPOTensor d D₁} (P : MPOTensor d D₃) {V : Matrix (Fin D₁) (Fin D₂) ℂ}
    {W : Matrix (Fin D₂) (Fin D₁) ℂ} {N : ℕ}
    (hN : MPTensor.IsReductionResidualNilpotencyBound X A V W N) :
    MPTensor.IsReductionResidualNilpotencyBound (mulTensor X P) (mulTensor A P)
      (kronId V D₃) (kronId W D₃) N := by
  have hres : MPTensor.reductionResidual (mulTensor X P) (mulTensor A P)
      (kronId V D₃) (kronId W D₃) = mulTensor (MPTensor.reductionResidual X A V W) P := by
    funext ⟨i, k⟩
    simp only [MPTensor.reductionResidual, mulTensor_apply, kronId_mul_submatrix_sum,
      submatrix_sum_mul_kronId, sub_kronecker', Finset.sum_sub_distrib]
    rfl
  intro w hw
  obtain ⟨L, u, rfl⟩ := List.exists_eq_ofFn w
  rw [hres, kraus_evalWord_mulTensor_ofFn]
  have hzero : ∀ ρ : Fin L → Fin d, Kraus.evalWord (MPTensor.reductionResidual X A V W)
      (List.ofFn fun k ↦ ((u k).1, ρ k)) = 0 := fun ρ ↦ hN _ (by simpa using hw)
  simp [hzero]

/-- **An identity strand on the left preserves the residual bound.** If the residual words of
`(V, W)` from `X` to `A` vanish at length `N`, so do those of `(1 ⊗ V, 1 ⊗ W)` from `P · X`
to `P · A`.

Source: arXiv:1706.07329v2, Definition 8, `cornerproblem.tex` lines 3147--3152; the identity
strand beside a fusion tensor is that of arXiv:2502.20257, `main.tex` lines 1506--1535. -/
theorem isReductionResidualNilpotencyBound_mulTensor_idKron {X : MPOTensor d D₂}
    {A : MPOTensor d D₁} (P : MPOTensor d D₃) {V : Matrix (Fin D₁) (Fin D₂) ℂ}
    {W : Matrix (Fin D₂) (Fin D₁) ℂ} {N : ℕ}
    (hN : MPTensor.IsReductionResidualNilpotencyBound X A V W N) :
    MPTensor.IsReductionResidualNilpotencyBound (mulTensor P X) (mulTensor P A)
      (idKron D₃ V) (idKron D₃ W) N := by
  have hres : MPTensor.reductionResidual (mulTensor P X) (mulTensor P A)
      (idKron D₃ V) (idKron D₃ W) = mulTensor P (MPTensor.reductionResidual X A V W) := by
    funext ⟨i, k⟩
    simp only [MPTensor.reductionResidual, mulTensor_apply, idKron_mul_submatrix_sum,
      submatrix_sum_mul_idKron, kronecker_sub', Finset.sum_sub_distrib]
    rfl
  intro w hw
  obtain ⟨L, u, rfl⟩ := List.exists_eq_ofFn w
  rw [hres, kraus_evalWord_mulTensor_ofFn]
  have hzero : ∀ ρ : Fin L → Fin d, Kraus.evalWord (MPTensor.reductionResidual X A V W)
      (List.ofFn fun k ↦ (ρ k, (u k).2)) = 0 := fun ρ ↦ hN _ (by simpa using hw)
  simp [hzero]

/-- **Reassociation preserves the residual bound, right to left.** The residual bound of a
reduction of `M · (N · P)` carries over to the reduction of `(M · N) · P` obtained by
`MPTensor.IsReduction.mulTensor_assoc_left`.

Source: arXiv:1706.07329v2, Definition 8, `cornerproblem.tex` lines 3147--3152; the associator
is that of arXiv:1606.00608, lines 995--999. -/
theorem isReductionResidualNilpotencyBound_mulTensor_assoc_left {M : MPOTensor d D₁}
    {N : MPOTensor d D₂} {P : MPOTensor d D₃} {D : ℕ} {A : MPOTensor d D}
    {V : Matrix (Fin D) (Fin (D₁ * (D₂ * D₃))) ℂ}
    {W : Matrix (Fin (D₁ * (D₂ * D₃))) (Fin D) ℂ} {K : ℕ}
    (hK : MPTensor.IsReductionResidualNilpotencyBound
      (mulTensor M (mulTensor N P)) A V W K) :
    MPTensor.IsReductionResidualNilpotencyBound (mulTensor (mulTensor M N) P) A
      (V * mulTensorAssocInvMatrix D₁ D₂ D₃) (mulTensorAssocMatrix D₁ D₂ D₃ * W) K :=
  MPSTensor.isReductionResidualNilpotencyBound_of_intertwine
    (mulTensorAssocInvMatrix_mul_matrix D₁ D₂ D₃) (mulTensorAssocMatrix_mul_invMatrix D₁ D₂ D₃)
    (fun i ↦ mulTensor_mul_assocMatrix M N P i.1 i.2) hK

/-- **Reassociation preserves the residual bound, left to right.** The residual bound of a
reduction of `(M · N) · P` carries over to the reduction of `M · (N · P)` obtained by
`MPTensor.IsReduction.mulTensor_assoc_right`.

Source: arXiv:1706.07329v2, Definition 8, `cornerproblem.tex` lines 3147--3152; the associator
is that of arXiv:1606.00608, lines 995--999. -/
theorem isReductionResidualNilpotencyBound_mulTensor_assoc_right {M : MPOTensor d D₁}
    {N : MPOTensor d D₂} {P : MPOTensor d D₃} {D : ℕ} {A : MPOTensor d D}
    {V : Matrix (Fin D) (Fin (D₁ * D₂ * D₃)) ℂ}
    {W : Matrix (Fin (D₁ * D₂ * D₃)) (Fin D) ℂ} {K : ℕ}
    (hK : MPTensor.IsReductionResidualNilpotencyBound
      (mulTensor (mulTensor M N) P) A V W K) :
    MPTensor.IsReductionResidualNilpotencyBound (mulTensor M (mulTensor N P)) A
      (V * mulTensorAssocMatrix D₁ D₂ D₃) (mulTensorAssocInvMatrix D₁ D₂ D₃ * W) K :=
  MPSTensor.isReductionResidualNilpotencyBound_of_intertwine
    (mulTensorAssocMatrix_mul_invMatrix D₁ D₂ D₃) (mulTensorAssocInvMatrix_mul_matrix D₁ D₂ D₃)
    (fun i ↦ (assocInvMatrix_mul_mulTensor M N P i.1 i.2).symm) hK

/-- **Reducing the state inside an action tensor preserves the residual bound.** If the
residual words of `(V, W)` from `B` to `A` vanish at length `N`, so do those of
`(1 ⊗ V, 1 ⊗ W)` from `T · B` to `T · A`.

Source: arXiv:1706.07329v2, Definition 8, `cornerproblem.tex` lines 3147--3152; the action
tensors are those of arXiv:2203.12563, `sec:PBC`, lines 1062--1129. -/
theorem isReductionResidualNilpotencyBound_actTensor_idKron (T : MPOTensor d D₃)
    {B : MPSTensor d D₂} {A : MPSTensor d D₁} {V : Matrix (Fin D₁) (Fin D₂) ℂ}
    {W : Matrix (Fin D₂) (Fin D₁) ℂ} {N : ℕ}
    (hN : MPTensor.IsReductionResidualNilpotencyBound B A V W N) :
    MPTensor.IsReductionResidualNilpotencyBound (actTensor T B) (actTensor T A)
      (idKron D₃ V) (idKron D₃ W) N := by
  have hres : MPTensor.reductionResidual (actTensor T B) (actTensor T A) (idKron D₃ V)
      (idKron D₃ W) = actTensor T (MPTensor.reductionResidual B A V W) := by
    funext i
    simp only [MPTensor.reductionResidual, actTensor_apply, idKron_mul_submatrix_sum,
      submatrix_sum_mul_idKron, kronecker_sub', Finset.sum_sub_distrib]
    rfl
  intro w hw
  obtain ⟨L, σ, rfl⟩ := List.exists_eq_ofFn w
  rw [hres, evalWord_actTensor]
  have hzero : ∀ τ : Fin L → Fin d,
      Kraus.evalWord (MPTensor.reductionResidual B A V W) (List.ofFn τ) = 0 :=
    fun τ ↦ hN _ (by simpa using hw)
  simp [hzero]

/-- **Reducing the operator inside an action tensor preserves the residual bound.** If the
residual words of `(V, W)` from `X` to `Y`, on the pair alphabet, vanish at length `N`, so do
those of `(V ⊗ 1, W ⊗ 1)` from `X · B` to `Y · B`.

Source: arXiv:1706.07329v2, Definition 8, `cornerproblem.tex` lines 3147--3152; the action
tensors are those of arXiv:2203.12563, `sec:PBC`, lines 1062--1129. -/
theorem isReductionResidualNilpotencyBound_actTensor_kronId {X : MPOTensor d D₂}
    {Y : MPOTensor d D₁} (B : MPSTensor d D₃) {V : Matrix (Fin D₁) (Fin D₂) ℂ}
    {W : Matrix (Fin D₂) (Fin D₁) ℂ} {N : ℕ}
    (hN : MPTensor.IsReductionResidualNilpotencyBound X Y V W N) :
    MPTensor.IsReductionResidualNilpotencyBound (actTensor X B) (actTensor Y B)
      (kronId V D₃) (kronId W D₃) N := by
  have hres : MPTensor.reductionResidual (actTensor X B) (actTensor Y B) (kronId V D₃)
      (kronId W D₃) = actTensor (MPTensor.reductionResidual X Y V W) B := by
    funext i
    simp only [MPTensor.reductionResidual, actTensor_apply, kronId_mul_submatrix_sum,
      submatrix_sum_mul_kronId, sub_kronecker', Finset.sum_sub_distrib]
    rfl
  intro w hw
  obtain ⟨L, σ, rfl⟩ := List.exists_eq_ofFn w
  rw [hres, evalWord_actTensor]
  have hzero : ∀ τ : Fin L → Fin d,
      evalWord (MPTensor.reductionResidual X Y V W) (List.ofFn σ) (List.ofFn τ) = 0 :=
    fun τ ↦ by
      have h := hN (List.ofFn fun k ↦ (σ k, τ k)) (by simpa using hw)
      rwa [kraus_evalWord_ofFn_pair] at h
  simp [hzero]

end MPOTensor
