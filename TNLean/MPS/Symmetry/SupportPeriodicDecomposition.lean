/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.IsometricBondCompression
import TNLean.MPS.Core.ProjectionTriangularTrace
import QICLean.Algebra.MatrixUnitaryBetween

/-!
# Periodic decomposition along a one-sided invariant support

An isometric support compression of a triangular tensor contributes one
summand to every positive-length periodic coefficient. The other summand
is the complementary diagonal corner. Off-diagonal letters make no trace
contribution. Neither summand is required to have the same periodic ray
as the ambient tensor.

Source context: arXiv:quant-ph/0608197, proof of the TI canonical-form theorem,
Th:TIcanonical, lines 785–815, and arXiv:1010.3732, Appendix C, lines 2653–2717.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open scoped Matrix

namespace MPSTensor

private theorem evalWord_add_of_cross_products_zero
    {d k : ℕ} (L R : MPSTensor d k)
    (hLR : ∀ i j, L i * R j = 0) (hRL : ∀ i j, R i * L j = 0)
    (w : List (Fin d)) (hw : w ≠ []) :
    Kraus.evalWord (fun i => L i + R i) w = Kraus.evalWord L w + Kraus.evalWord R w := by
  induction w with
  | nil => exact (hw rfl).elim
  | cons i w ih =>
    cases w with
    | nil => simp only [Kraus.evalWord_cons, Kraus.evalWord_nil, Matrix.mul_one]
    | cons j w =>
      rw [Kraus.evalWord_cons, ih (by simp)]
      simp only [Kraus.evalWord_cons, Matrix.add_mul, Matrix.mul_add,
        ← Matrix.mul_assoc, hLR, hRL, zero_add, add_zero]

/-- A triangular support compression splits every positive-length periodic
coefficient into the supported tensor and the complementary diagonal corner.
Source context: arXiv:quant-ph/0608197, Th:TIcanonical, lines 785–815. -/
theorem mpv_eq_compression_add_transient_of_upperZero
    {d k D N : ℕ} (B : MPSTensor d k) (C : MPSTensor d D)
    (K : Matrix (Fin k) (Fin D) ℂ) (hK : K.IsIsometry)
    (hC : ∀ i, C i = Kᴴ * B i * K)
    (hUpper : ∀ i, (K * Kᴴ) * B i * (1 - K * Kᴴ) = 0)
    (hN : 0 < N) (x : Fin N → Fin d) :
    mpv B x = mpv C x + mpv (fun i => (1 - K * Kᴴ) * B i * (1 - K * Kᴴ)) x := by
  let P := K * Kᴴ
  let Q := 1 - P
  let L : MPSTensor d k := fun i => P * B i * P
  let R : MPSTensor d k := fun i => Q * B i * Q
  have hP : IsOrthogonalProjection P := ⟨Matrix.isHermitian_mul_conjTranspose_self K, by
    simp only [P, Matrix.mul_assoc, ← Matrix.mul_assoc Kᴴ K,
      show Kᴴ * K = 1 from hK, Matrix.one_mul]⟩
  have hInt : ∀ i, L i * K = K * C i := by
    intro i
    simp only [L, P, hC, Matrix.mul_assoc, show Kᴴ * K = 1 from hK, Matrix.mul_one]
  have hRow : ∀ i, K * Kᴴ * L i = L i := by
    intro i
    change P * (P * B i * P) = P * B i * P
    calc
      P * (P * B i * P) = (P * P) * B i * P := by simp only [Matrix.mul_assoc]
      _ = P * B i * P := by rw [hP.2]
  have hCoefficientsL : mpv L x = mpv C x :=
    mpv_eq_of_supported_isometric_bond_intertwiner L C K hK hInt hRow hN x
  have hPQ : P * Q = 0 := IsIdempotentElem.mul_one_sub_self hP.2
  have hQP : Q * P = 0 := IsIdempotentElem.one_sub_mul_self hP.2
  have hLR : ∀ i j, L i * R j = 0 := by
    intro i j
    calc
      L i * R j = P * B i * (P * Q) * B j * Q := by simp only [L, R, Matrix.mul_assoc]
      _ = 0 := by rw [hPQ]; simp only [Matrix.mul_zero, Matrix.zero_mul]
  have hRL : ∀ i j, R i * L j = 0 := by
    intro i j
    calc
      R i * L j = Q * B i * (Q * P) * B j * P := by simp only [L, R, Matrix.mul_assoc]
      _ = 0 := by rw [hQP]; simp only [Matrix.mul_zero, Matrix.zero_mul]
  have hQ : IsOrthogonalProjection Q :=
    hP.isStarProjection.one_sub.isOrthogonalProjection
  have hDiag : mpv B x = mpv (fun i => R i + L i) x := by
    have h := sameMPV_diagPart_of_lowerZero B Q hQ
      (fun i => by simpa only [Q, P, sub_sub_cancel] using hUpper i) N x
    change mpv B x = mpv (fun i => Q * B i * Q + (1 - Q) * B i * (1 - Q)) x at h
    simpa only [Q, sub_sub_cancel, L, R] using h
  have hw : List.ofFn x ≠ [] := mt List.ofFn_eq_nil_iff.mp (Nat.ne_of_gt hN)
  rw [hDiag, ← hCoefficientsL]
  change (Kraus.evalWord (fun i => R i + L i) (List.ofFn x)).trace =
    (Kraus.evalWord L (List.ofFn x)).trace + (Kraus.evalWord R (List.ofFn x)).trace
  rw [evalWord_add_of_cross_products_zero R L hRL hLR _ hw, Matrix.trace_add, add_comm]

end MPSTensor
