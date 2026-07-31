/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.Overlap.SectorMatch.Basic

/-!
# Cyclic corner-product transport

This module proves the concatenation, telescoping, and normalization identities
used to transport periodic corner products around a full cycle.
-/

open scoped Matrix BigOperators ComplexOrder InnerProductSpace TensorProduct
open Filter Matrix Module

namespace MPSTensor

variable {d D : ℕ}

/-- Concatenating cyclic word segments multiplies their corner products in
cyclic order.

This is the word-level concatenation in arXiv:1708.00029, Appendix A,
lines 1041--1056. -/
lemma cornerProd_cyclicList_flatten_succ
    {m : ℕ} [NeZero m]
    (P : Fin m → MatrixAlg D) (A : MPSTensor d D)
    (hP : ∀ u, IsOrthogonalProjection (P u))
    (segments : Fin m → List (Fin d))
    (hsegments : ∀ u, (segments u).length • (1 : Fin m) = 1)
    (u : Fin m) (n : ℕ) :
    cornerProd P A u (cyclicList segments u (n + 1)).flatten =
      (cyclicList (fun k => cornerProd P A k (segments k)) u (n + 1)).prod := by
  induction n generalizing u with
  | zero => simp [cyclicList]
  | succ n ih =>
      rw [show n + 1 + 1 = (n + 1) + 1 by omega, cyclicList, List.flatten_cons,
        cornerProd_append P A hP u, hsegments u, ih (u + 1), cyclicList,
        List.prod_cons]
      rw [cyclicList, cyclicList]
      simp only [List.prod_cons]

/-- Supported corner implementers telescope across a cyclic ordered product.

This is the adjacent cancellation \(U_{v+1}^\dagger U_{v+1}=Q_{v+1}\)
in arXiv:1708.00029, Appendix A, lines 1041--1056. -/
private lemma cyclic_partial_isometry_prod_succ
    {m : ℕ} [NeZero m]
    (Q : Fin m → MatrixAlg D) (q : Fin m)
    (U R : Fin m → MatrixAlg D)
    (hU_star_U : ∀ u, (U u)ᴴ * U u = Q (u + q))
    (hR_right : ∀ u, R u * Q (u + 1 + q) = R u)
    (u : Fin m) (n : ℕ) :
    (cyclicList (fun k => U k * R k * (U (k + 1))ᴴ) u (n + 1)).prod =
      U u * (cyclicList R u (n + 1)).prod *
        (U (u + (n + 1) • (1 : Fin m)))ᴴ := by
  induction n generalizing u with
  | zero => simp [cyclicList]
  | succ n ih =>
      change
        (U u * R u * (U (u + 1))ᴴ ::
          cyclicList (fun k => U k * R k * (U (k + 1))ᴴ) (u + 1) (n + 1)).prod =
        U u * (R u :: cyclicList R (u + 1) (n + 1)).prod *
          (U (u + (n + 1 + 1) • (1 : Fin m)))ᴴ
      simp only [List.prod_cons]
      rw [ih (u + 1)]
      have hindex :
          u + (n + 1 + 1) • (1 : Fin m) =
            u + 1 + (n + 1) • (1 : Fin m) := by
        rw [add_nsmul, one_nsmul]
        abel
      rw [hindex]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (U (u + 1))ᴴ (U (u + 1)),
        hU_star_U (u + 1),
        ← Matrix.mul_assoc (R u) (Q (u + 1 + q)), hR_right u]

/-- Translating the projection labels translates the starting label of a
corner product.

This is the fixed sector offset in arXiv:1708.00029, Appendix A,
equation `eq:vprop` and lines 1041--1056. -/
private lemma cornerProd_add_shift
    {m : ℕ} [NeZero m]
    (Q : Fin m → MatrixAlg D) (B : MPSTensor d D)
    (q u : Fin m) (w : List (Fin d)) :
    cornerProd (fun k => Q (k + q)) B u w =
      cornerProd Q B (u + q) w := by
  induction w generalizing u with
  | nil => rfl
  | cons i w ih =>
      simp only [cornerProd_cons, ih]
      congr 2
      abel

/-- A cyclic chain of corner products transported by adjacent partial
isometries is the transport of the concatenated corner product.

This is the cancellation of adjacent implementers in arXiv:1708.00029,
Appendix A, lines 1041--1056. -/
lemma cyclic_transport_cornerProd_segments
    {m : ℕ} [NeZero m]
    (Q : Fin m → MatrixAlg D) (B : MPSTensor d D) (q : Fin m)
    (U : Fin m → MatrixAlg D)
    (hQ : ∀ k, IsOrthogonalProjection (Q k))
    (hQ_shift : ∀ k (i : Fin d), Q k * B i = B i * Q (k + 1))
    (hU_star_U : ∀ k, (U k)ᴴ * U k = Q (k + q))
    (segments : Fin m → List (Fin d))
    (hsegments : ∀ k, (segments k).length • (1 : Fin m) = 1)
    (u : Fin m) (n : ℕ) :
    (cyclicList
        (fun k => U k * cornerProd Q B (k + q) (segments k) * (U (k + 1))ᴴ)
        u (n + 1)).prod =
      U u *
        cornerProd Q B (u + q) (cyclicList segments u (n + 1)).flatten *
          (U (u + (n + 1) • (1 : Fin m)))ᴴ := by
  let S : Fin m → MatrixAlg D := fun k => Q (k + q)
  have hS : ∀ k, IsOrthogonalProjection (S k) := fun k => hQ (k + q)
  have hS_shift : ∀ k (i : Fin d), S k * B i = B i * S (k + 1) := by
    intro k i
    change Q (k + q) * B i = B i * Q (k + 1 + q)
    rw [show k + 1 + q = k + q + 1 by abel]
    exact hQ_shift (k + q) i
  let R : Fin m → MatrixAlg D := fun k => cornerProd S B k (segments k)
  have hR_right : ∀ k, R k * S (k + 1) = R k := by
    intro k
    simpa only [R, hsegments k] using
      cornerProd_mul_finalCorner S B hS hS_shift k (segments k)
  have hconcat :=
    cornerProd_cyclicList_flatten_succ S B hS segments hsegments u n
  have hU_star_U' : ∀ k, (U k)ᴴ * U k = S (k + 0) := by
    intro k
    simpa only [S, add_zero] using hU_star_U k
  have hR_right' : ∀ k, R k * S (k + 1 + 0) = R k := by
    intro k
    simpa only [add_zero] using hR_right k
  have htransport :=
    cyclic_partial_isometry_prod_succ S (0 : Fin m) U R
      hU_star_U' hR_right' u n
  calc
    (cyclicList
        (fun k => U k * cornerProd Q B (k + q) (segments k) * (U (k + 1))ᴴ)
        u (n + 1)).prod =
        (cyclicList (fun k => U k * R k * (U (k + 1))ᴴ) u (n + 1)).prod := by
          apply congrArg List.prod
          apply congrArg (fun f => cyclicList f u (n + 1))
          funext k
          change U k * cornerProd Q B (k + q) (segments k) * (U (k + 1))ᴴ =
            U k * cornerProd S B k (segments k) * (U (k + 1))ᴴ
          rw [cornerProd_add_shift]
    _ = U u * (cyclicList R u (n + 1)).prod *
          (U (u + (n + 1) • (1 : Fin m)))ᴴ := htransport
    _ = U u * cornerProd S B u (cyclicList segments u (n + 1)).flatten *
          (U (u + (n + 1) • (1 : Fin m)))ᴴ := by rw [hconcat]
    _ = U u *
          cornerProd Q B (u + q) (cyclicList segments u (n + 1)).flatten *
            (U (u + (n + 1) • (1 : Fin m)))ᴴ := by
              rw [cornerProd_add_shift]

/-- Splitting a transported corner segment at its first letter inserts the
adjacent partial isometry and cancels it at the internal corner.

This is one local cancellation in arXiv:1708.00029, Appendix A,
lines 1041--1056. -/
lemma transported_cornerProd_cons
    {m : ℕ} [NeZero m]
    (Q : Fin m → MatrixAlg D) (B : MPSTensor d D) (q : Fin m)
    (U : Fin m → MatrixAlg D)
    (hQ : ∀ k, IsOrthogonalProjection (Q k))
    (hU_star_U : ∀ k, (U k)ᴴ * U k = Q (k + q))
    (u : Fin m) (i : Fin d) (w : List (Fin d)) :
    U u * cornerProd Q B (u + q) (i :: w) * (U (u + 1))ᴴ =
      (U u * cornerLetter Q B (u + q) i * (U (u + 1))ᴴ) *
        (U (u + 1) * cornerProd Q B (u + 1 + q) w * (U (u + 1))ᴴ) := by
  have hindex : u + q + 1 = u + 1 + q := by abel
  have hcorner :
      Q (u + 1 + q) * cornerProd Q B (u + 1 + q) w =
        cornerProd Q B (u + 1 + q) w :=
    corner_mul_cornerProd Q B (u + 1 + q) w (hQ (u + 1 + q))
  have hcorner' :
      Q (u + 1 + q) *
          (Q (u + 1 + q) *
            (cornerProd Q B (u + 1 + q) w * (U (u + 1))ᴴ)) =
        cornerProd Q B (u + 1 + q) w * (U (u + 1))ᴴ := by
    rw [← Matrix.mul_assoc, (hQ (u + 1 + q)).2]
    rw [← Matrix.mul_assoc, hcorner]
  simp only [cornerProd_cons, cornerLetter, Matrix.mul_assoc]
  rw [hindex]
  rw [← Matrix.mul_assoc (U (u + 1))ᴴ (U (u + 1))
    (cornerProd Q B (u + 1 + q) w * (U (u + 1))ᴴ)]
  rw [hU_star_U (u + 1)]
  rw [hcorner']

/-- Left-canonical normalization restricts to each one-site corner transition.

This is the norm identity used in arXiv:1708.00029, Appendix A,
lines 1082--1084. -/
lemma sum_cornerLetter_star_mul
    {m : ℕ} [NeZero m]
    (P : Fin m → MatrixAlg D) (A : MPSTensor d D)
    (hP : ∀ k, IsOrthogonalProjection (P k))
    (htransfer : ∀ k, ∑ i, (A i)ᴴ * P k * A i = P (k + 1))
    (k : Fin m) :
    ∑ i, (cornerLetter P A k i)ᴴ * cornerLetter P A k i = P (k + 1) := by
  calc
    ∑ i, (cornerLetter P A k i)ᴴ * cornerLetter P A k i =
        ∑ i, P (k + 1) * ((A i)ᴴ * P k * A i) * P (k + 1) := by
          apply Finset.sum_congr rfl
          intro i _
          simp only [cornerLetter, Matrix.conjTranspose_mul, (hP k).1.eq,
            (hP (k + 1)).1.eq, Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (P k) (P k) (A i * P (k + 1)), (hP k).2]
    _ = P (k + 1) * (∑ i, (A i)ᴴ * P k * A i) * P (k + 1) := by
      rw [Finset.mul_sum, Finset.sum_mul]
    _ = P (k + 1) := by
      rw [htransfer k, (hP (k + 1)).2]
      exact (hP (k + 1)).2

end MPSTensor
