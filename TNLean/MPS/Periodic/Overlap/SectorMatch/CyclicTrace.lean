/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.Overlap.SectorMatch.Basic
import TNLean.Algebra.PiTensorProductPhase

/-!
# Cyclic trace separation for periodic sector matches

This module separates full-cycle corner products by matrix units and tensor
trace pairings.
-/

open scoped Matrix BigOperators ComplexOrder InnerProductSpace TensorProduct
open Filter Matrix Module

namespace MPSTensor

variable {d D : ℕ}

/-- Matrix units separate a cyclic product into its individual matrix
coefficients.

This is the coordinate form of applying the tensor of the inverses in
arXiv:1708.00029, Appendix A, lines 1048--1067. -/
private lemma cyclic_matrix_single_chain_apply
    {m : ℕ} [NeZero m] {D : ℕ}
    (M : Fin m → MatrixAlg D) (p : Fin m → Fin D × Fin D)
    (u : Fin m) (n : ℕ) (r s : Fin D) :
    ((cyclicList
        (fun k => M k * Matrix.single (p k).2 (p (k + 1)).1 (1 : ℂ))
        u (n + 1)).prod : MatrixAlg D) r s =
      if s = (p (u + (n + 1) • (1 : Fin m))).1 then
        M u r (p u).2 *
          (cyclicList (fun k => M k (p k).1 (p k).2) (u + 1) n).prod
      else 0 := by
  induction n generalizing u r with
  | zero =>
    simp only [cyclicList, List.prod_cons, List.prod_nil, mul_one]
    norm_num
    by_cases hs : s = (p (u + 1)).1
    · subst s
      simp
    · rw [if_neg hs,
        Matrix.mul_single_apply_of_ne (1 : ℂ) (p u).2 (p (u + 1)).1 r
          s hs]
  | succ n ih =>
    simp only [cyclicList, List.prod_cons]
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    rw [Finset.sum_eq_single (p u).2]
    · simp only [Matrix.single_mul_apply_same, one_mul]
      change M u r (p u).2 *
          ((cyclicList
            (fun k => M k * Matrix.single (p k).2 (p (k + 1)).1 (1 : ℂ))
            (u + 1) (n + 1)).prod : MatrixAlg D) (p (u + 1)).1 s = _
      rw [ih]
      have hindex :
          u + 1 + (n + 1) • (1 : Fin m) =
            u + (n + 1 + 1) • (1 : Fin m) := by
        have hsmul :
            (1 + (n + 1)) • (1 : Fin m) =
              1 + (n + 1) • (1 : Fin m) := by
          calc
            (1 + (n + 1)) • (1 : Fin m) =
                1 • (1 : Fin m) + (n + 1) • (1 : Fin m) :=
              add_nsmul (1 : Fin m) 1 (n + 1)
            _ = 1 + (n + 1) • (1 : Fin m) := by rw [one_nsmul]
        rw [show n + 1 + 1 = 1 + (n + 1) by omega, hsmul, add_assoc]
      rw [hindex]
      split_ifs with hs
      · rfl
      · rw [mul_zero]
    · intro a _ ha
      rw [Matrix.single_mul_apply_of_ne (1 : ℂ) (p u).2
        (p (u + 1)).1 a s ha]
      rw [mul_zero]
    · simp

/-- A projection supporting the first factor supports a nonempty cyclic
product on the left. -/
private lemma cyclic_prod_left
    {m : ℕ} [NeZero m]
    (P R : Fin m → MatrixAlg D)
    (hR_left : ∀ k, P k * R k = R k)
    (u : Fin m) (n : ℕ) :
    P u * (cyclicList R u (n + 1)).prod =
      (cyclicList R u (n + 1)).prod := by
  simp only [cyclicList, List.prod_cons, ← Matrix.mul_assoc, hR_left]

/-- Inserting the next-sector projection after every factor leaves only the
final projection at the end of a cyclic product. -/
private lemma cyclic_prod_insert_right_projection
    {m : ℕ} [NeZero m]
    (P R : Fin m → MatrixAlg D)
    (hR_left : ∀ k, P k * R k = R k)
    (u : Fin m) (n : ℕ) :
    (cyclicList (fun k => R k * P (k + 1)) u (n + 1)).prod =
      (cyclicList R u (n + 1)).prod *
        P (u + (n + 1) • (1 : Fin m)) := by
  induction n generalizing u with
  | zero => simp [cyclicList]
  | succ n ih =>
    change
      (R u * P (u + 1)) *
          (cyclicList (fun k => R k * P (k + 1)) (u + 1) (n + 1)).prod =
        R u * (cyclicList R (u + 1) (n + 1)).prod *
          P (u + (n + 1 + 1) • (1 : Fin m))
    rw [ih (u + 1)]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (P (u + 1)) (cyclicList R (u + 1) (n + 1)).prod,
      cyclic_prod_left P R hR_left (u + 1) n]
    congr 2
    have hindex :
        u + (n + 1 + 1) • (1 : Fin m) =
          u + 1 + (n + 1) • (1 : Fin m) := by
      rw [add_nsmul, one_nsmul]
      abel
    rw [hindex]

/-- Compressing every inserted matrix to the intervening corner does not
change the cyclic trace pairing.

This is the open-index interpretation of the corner inverse in
arXiv:1708.00029, Appendix A, lines 1048--1067. -/
private lemma trace_prod_corner_compression
    {m : ℕ} [NeZero m]
    (P M X : Fin m → MatrixAlg D)
    (hM_left : ∀ k, P k * M k = M k)
    (hM_right : ∀ k, M k * P (k + 1) = M k) :
    Matrix.trace
        (List.ofFn (fun k => M k * (P (k + 1) * X k * P (k + 1)))).prod =
      Matrix.trace (List.ofFn (fun k => M k * X k)).prod := by
  let R : Fin m → MatrixAlg D := fun k => M k * X k
  have hR_left : ∀ k, P k * R k = R k := by
    intro k
    simp only [R, ← Matrix.mul_assoc, hM_left]
  have hterm : ∀ k, M k * (P (k + 1) * X k * P (k + 1)) =
      R k * P (k + 1) := by
    intro k
    change M k * (P (k + 1) * X k * P (k + 1)) =
      (M k * X k) * P (k + 1)
    rw [Matrix.mul_assoc (P (k + 1))]
    rw [← Matrix.mul_assoc, hM_right]
    rw [Matrix.mul_assoc]
  have hm : m.pred + 1 = m := Nat.succ_pred_eq_of_pos (NeZero.pos m)
  have hprod :=
    cyclic_prod_insert_right_projection P R hR_left 0 m.pred
  rw [hm, nsmul_card_one_fin, zero_add] at hprod
  rw [cyclicList_zero_card_eq_ofFn, cyclicList_zero_card_eq_ofFn] at hprod
  have hcompressed :
      (List.ofFn (fun k => M k * (P (k + 1) * X k * P (k + 1)))).prod =
        (List.ofFn R).prod * P 0 := by
    calc
      (List.ofFn (fun k => M k * (P (k + 1) * X k * P (k + 1)))).prod =
          (List.ofFn (fun k => R k * P (k + 1))).prod := by
            apply congrArg List.prod
            apply List.ofFn_inj.mpr
            funext k
            exact hterm k
      _ = (List.ofFn R).prod * P 0 := hprod
  rw [hcompressed, Matrix.trace_mul_comm]
  rw [← cyclicList_zero_card_eq_ofFn]
  have hleft := cyclic_prod_left P R hR_left 0 m.pred
  rw [hm] at hleft
  simpa only [cyclicList_zero_card_eq_ofFn, R] using congrArg Matrix.trace hleft

/-- The cyclic trace against linked matrix units is the product of the selected
matrix coefficients. -/
private lemma trace_cyclic_matrix_single_chain
    {m : ℕ} [NeZero m] {D : ℕ} [NeZero D]
    (M : Fin m → MatrixAlg D) (p : Fin m → Fin D × Fin D) :
    Matrix.trace
        (List.ofFn
          (fun k => M k * Matrix.single (p k).2 (p (k + 1)).1 (1 : ℂ))).prod =
      ∏ k, M k (p k).1 (p k).2 := by
  let f : Fin m → ℂ := fun k => M k (p k).1 (p k).2
  have hm : m.pred + 1 = m := Nat.succ_pred_eq_of_pos (NeZero.pos m)
  have hdiag : ∀ r : Fin D,
      (List.ofFn
        (fun k => M k * Matrix.single (p k).2 (p (k + 1)).1 (1 : ℂ))).prod r r =
        if r = (p 0).1 then ∏ k, f k else 0 := by
    intro r
    have hchain :=
      cyclic_matrix_single_chain_apply M p 0 m.pred r r
    rw [hm, nsmul_card_one_fin, zero_add] at hchain
    rw [cyclicList_zero_card_eq_ofFn] at hchain
    by_cases hr : r = (p 0).1
    · subst r
      rw [if_pos rfl] at hchain ⊢
      rw [hchain]
      calc
        M 0 (p 0).1 (p 0).2 *
            (cyclicList f (0 + 1) m.pred).prod =
            (cyclicList f 0 m).prod := by
              have hcycle :
                  cyclicList f 0 m =
                    f 0 :: cyclicList f (0 + 1) m.pred := by
                calc
                  cyclicList f 0 m = cyclicList f 0 (m.pred + 1) :=
                    congrArg _ hm.symm
                  _ = _ := rfl
              rw [hcycle, List.prod_cons]
        _ = (List.ofFn f).prod := by rw [cyclicList_zero_card_eq_ofFn]
        _ = ∏ k, f k := List.prod_ofFn
    · rw [if_neg hr] at hchain ⊢
      exact hchain
  rw [Matrix.trace, Finset.sum_eq_single (p 0).1]
  · change
      (List.ofFn
        (fun k => M k * Matrix.single (p k).2 (p (k + 1)).1 (1 : ℂ))).prod
          (p 0).1 (p 0).1 = _
    rw [hdiag, if_pos rfl]
  · intro r _ hr
    change
      (List.ofFn
        (fun k => M k * Matrix.single (p k).2 (p (k + 1)).1 (1 : ℂ))).prod
          r r = 0
    rw [hdiag, if_neg hr]
  · simp

/-- A cyclic product identity tested on all matrices in the intervening
corners determines the corresponding product-tensor identity.

This is `eq:resultprop` in arXiv:1708.00029, Appendix A, lines 1063--1067,
with the open virtual indices read through the corner trace pairing. -/
lemma piTensorProduct_eq_smul_of_corner_cyclic_products
    {m : ℕ} [NeZero m] {D : ℕ} [NeZero D]
    (P : Fin m → MatrixAlg D)
    (A B : Fin m → MatrixAlg D) (z : ℂ)
    (hP : ∀ k, IsOrthogonalProjection (P k))
    (hA_left : ∀ k, P k * A k = A k)
    (hA_right : ∀ k, A k * P (k + 1) = A k)
    (hB_left : ∀ k, P k * B k = B k)
    (hB_right : ∀ k, B k * P (k + 1) = B k)
    (h : ∀ X : Fin m → MatrixAlg D,
      (∀ k, P (k + 1) * X k * P (k + 1) = X k) →
      (List.ofFn (fun k => A k * X k)).prod =
        z • (List.ofFn (fun k => B k * X k)).prod) :
    (⨂ₜ[ℂ] k : Fin m, A k) = z • (⨂ₜ[ℂ] k : Fin m, B k) := by
  classical
  let b : (k : Fin m) → Basis (Fin D × Fin D) ℂ (MatrixAlg D) :=
    fun _ => Matrix.stdBasis ℂ (Fin D) (Fin D)
  apply (Basis.piTensorProduct b).repr.injective
  ext p
  simp only [Basis.piTensorProduct_repr_tprod_apply, map_smul,
    Finsupp.smul_apply, smul_eq_mul]
  let X : Fin m → MatrixAlg D :=
    fun k => Matrix.single (p k).2 (p (k + 1)).1 1
  let Xc : Fin m → MatrixAlg D :=
    fun k => P (k + 1) * X k * P (k + 1)
  have hXc : ∀ k, P (k + 1) * Xc k * P (k + 1) = Xc k := by
    intro k
    simp only [Xc, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc, (hP (k + 1)).2]
  have htrace := congrArg Matrix.trace (h Xc hXc)
  have htrace' :
      Matrix.trace (List.ofFn (fun k => A k * Xc k)).prod =
        z * Matrix.trace (List.ofFn (fun k => B k * Xc k)).prod := by
    rw [Matrix.trace_smul] at htrace
    simpa only [smul_eq_mul] using htrace
  rw [trace_prod_corner_compression P A X hA_left hA_right,
    trace_prod_corner_compression P B X hB_left hB_right,
    trace_cyclic_matrix_single_chain A p,
    trace_cyclic_matrix_single_chain B p] at htrace'
  simpa [b, Matrix.stdBasis] using htrace'

/-- Arbitrary inserted matrices separate a cyclic matrix-product identity into
an identity of product tensors.

This is the algebraic passage from the inverse contraction at lines 1048--1062
to `eq:resultprop` at lines 1063--1067 of arXiv:1708.00029, Appendix A. -/
private lemma piTensorProduct_eq_smul_of_cyclic_products
    {m : ℕ} [NeZero m] {D : ℕ} [NeZero D]
    (A B : Fin m → MatrixAlg D) (z : ℂ)
    (h : ∀ X : Fin m → MatrixAlg D,
      (List.ofFn (fun k => A k * X k)).prod =
        z • (List.ofFn (fun k => B k * X k)).prod) :
    (⨂ₜ[ℂ] k : Fin m, A k) = z • (⨂ₜ[ℂ] k : Fin m, B k) := by
  classical
  let b : (k : Fin m) → Basis (Fin D × Fin D) ℂ (MatrixAlg D) :=
    fun _ => Matrix.stdBasis ℂ (Fin D) (Fin D)
  apply (Basis.piTensorProduct b).repr.injective
  ext p
  simp only [Basis.piTensorProduct_repr_tprod_apply, map_smul,
    Finsupp.smul_apply, smul_eq_mul]
  let X : Fin m → MatrixAlg D :=
    fun k => Matrix.single (p k).2 (p (k + 1)).1 1
  have hentry := congrArg (fun M : MatrixAlg D => M (p 0).1 (p 0).1) (h X)
  have hfull :
      ∀ M : Fin m → MatrixAlg D,
        (List.ofFn (fun k => M k * X k)).prod (p 0).1 (p 0).1 =
          ∏ k, M k (p k).1 (p k).2 := by
    intro M
    have hm : m.pred + 1 = m := Nat.succ_pred_eq_of_pos (NeZero.pos m)
    have hchain :=
      cyclic_matrix_single_chain_apply M p 0 m.pred (p 0).1 (p 0).1
    rw [hm, nsmul_card_one_fin, zero_add, if_pos rfl] at hchain
    calc
      (List.ofFn (fun k => M k * X k)).prod (p 0).1 (p 0).1 =
          M 0 (p 0).1 (p 0).2 *
            (cyclicList (fun k => M k (p k).1 (p k).2) (0 + 1) m.pred).prod := by
              rw [← cyclicList_zero_card_eq_ofFn]
              exact hchain
      _ = (cyclicList (fun k => M k (p k).1 (p k).2) 0 m).prod := by
        have hcycle :
            cyclicList (fun k => M k (p k).1 (p k).2) 0 m =
              M 0 (p 0).1 (p 0).2 ::
                cyclicList (fun k => M k (p k).1 (p k).2) (0 + 1) m.pred := by
          calc
            cyclicList (fun k => M k (p k).1 (p k).2) 0 m =
                cyclicList (fun k => M k (p k).1 (p k).2) 0 (m.pred + 1) :=
              congrArg _ hm.symm
            _ = _ := rfl
        rw [hcycle, List.prod_cons]
      _ = (List.ofFn (fun k => M k (p k).1 (p k).2)).prod := by
        rw [cyclicList_zero_card_eq_ofFn]
      _ = ∏ k, M k (p k).1 (p k).2 := List.prod_ofFn
  change (List.ofFn (fun k => A k * X k)).prod (p 0).1 (p 0).1 =
    z * (List.ofFn (fun k => B k * X k)).prod (p 0).1 (p 0).1 at hentry
  rw [hfull A, hfull B] at hentry
  simpa [b, Matrix.stdBasis] using hentry

end MPSTensor
