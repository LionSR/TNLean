/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinTupleEquiv
import TNLean.MPS.RFP.KroneckerTransport

/-!
# Matrix coordinates of adjacent pair lifts

This file identifies the matrices of the two overlapping lifts of a two-site
linear map in canonical right-associated coordinates.  The first-pair lift is
the Kronecker product of the two-site matrix with the identity, and the
final-pair lift is the identity Kronecker the two-site matrix.
-/

open scoped Matrix BigOperators Kronecker

namespace MPSTensor

variable {d : ℕ}

/-! ### Matrices of adjacent pair lifts -/

@[simp] private theorem axPairCfg_vecCons (a b c : Fin d) :
    axPairCfg ![a, b, c] = ![a, b] := by
  funext k
  fin_cases k <;> rfl

@[simp] private theorem xbPairCfg_vecCons (a b c : Fin d) :
    xbPairCfg ![a, b, c] = ![b, c] := by
  funext k
  fin_cases k <;> rfl

/-- Replacing the first pair gives a prescribed triple precisely when the new
pair and untouched final coordinate agree. -/
private theorem replaceAXCfg_eq_iff (sigma tau : Cfg d 3) (alpha : Cfg d 2) :
    replaceAXCfg sigma alpha = tau ↔
      alpha = axPairCfg tau ∧ sigma 2 = tau 2 := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg axPairCfg h,
      by simpa [replaceAXCfg] using congrFun h (2 : Fin 3)⟩
  · rintro ⟨rfl, h⟩
    funext k
    fin_cases k <;> simp [replaceAXCfg, axPairCfg, h]

/-- Replacing the final pair gives a prescribed triple precisely when the new
pair and untouched initial coordinate agree. -/
private theorem replaceXBCfg_eq_iff (sigma tau : Cfg d 3) (beta : Cfg d 2) :
    replaceXBCfg sigma beta = tau ↔
      beta = xbPairCfg tau ∧ sigma 0 = tau 0 := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg xbPairCfg h,
      by simpa [replaceXBCfg] using congrFun h (0 : Fin 3)⟩
  · rintro ⟨rfl, h⟩
    funext k
    fin_cases k <;> simp [replaceXBCfg, xbPairCfg, h]

/-- Under the canonical two-site and three-site reindexings, the first-pair
action is \(Q\otimes 1\).

This is the homogeneous three-single-site coefficient-space specialization of
the \(AX\) factor action in arXiv:1606.00608, lines 2185--2186 and 2205--2218.
-/
theorem leftPairLift_toMatrix_reindex
    (Q : NSiteSpace d 2 →ₗ[ℂ] NSiteSpace d 2) :
    Matrix.reindex (finThreeArrowEquiv (Fin d))
        (finThreeArrowEquiv (Fin d))
        (LinearMap.toMatrix' (leftPairLift Q)) =
      appendixBLeftPairMatrix (Matrix.reindex (finTwoArrowEquiv (Fin d))
        (finTwoArrowEquiv (Fin d)) (LinearMap.toMatrix' Q)) := by
  classical
  ext σ τ
  by_cases h : σ.2.2 = τ.2.2
  · have hslice : (fun α ↦
        (Pi.single ((finThreeArrowEquiv (Fin d)).symm τ) (1 : ℂ) :
          NSiteSpace d 3)
          (replaceAXCfg ((finThreeArrowEquiv (Fin d)).symm σ) α)) =
        (Pi.single ((finTwoArrowEquiv (Fin d)).symm (τ.1, τ.2.1)) (1 : ℂ) :
          NSiteSpace d 2) := by
      funext α
      simp only [Pi.single_apply]
      simp only [replaceAXCfg_eq_iff]
      simp [finTwoArrowEquiv, h]
    change Q (fun α ↦
        (Pi.single ((finThreeArrowEquiv (Fin d)).symm τ) (1 : ℂ) :
          NSiteSpace d 3)
          (replaceAXCfg ((finThreeArrowEquiv (Fin d)).symm σ) α))
        (axPairCfg ((finThreeArrowEquiv (Fin d)).symm σ)) =
      Q (Pi.single ((finTwoArrowEquiv (Fin d)).symm (τ.1, τ.2.1)) (1 : ℂ))
        ((finTwoArrowEquiv (Fin d)).symm (σ.1, σ.2.1)) *
          (if σ.2.2 = τ.2.2 then 1 else 0)
    rw [hslice]
    simp [finTwoArrowEquiv, h]
  · have hslice : (fun α ↦
        (Pi.single ((finThreeArrowEquiv (Fin d)).symm τ) (1 : ℂ) :
          NSiteSpace d 3)
          (replaceAXCfg ((finThreeArrowEquiv (Fin d)).symm σ) α)) = 0 := by
      funext α
      simp only [Pi.single_apply, Pi.zero_apply]
      simp only [replaceAXCfg_eq_iff]
      simp [h]
    change Q (fun α ↦
        (Pi.single ((finThreeArrowEquiv (Fin d)).symm τ) (1 : ℂ) :
          NSiteSpace d 3)
          (replaceAXCfg ((finThreeArrowEquiv (Fin d)).symm σ) α))
        (axPairCfg ((finThreeArrowEquiv (Fin d)).symm σ)) =
      Q (Pi.single ((finTwoArrowEquiv (Fin d)).symm (τ.1, τ.2.1)) (1 : ℂ))
        ((finTwoArrowEquiv (Fin d)).symm (σ.1, σ.2.1)) *
          (if σ.2.2 = τ.2.2 then 1 else 0)
    rw [hslice]
    simp [h]

/-- Under the canonical two-site and three-site reindexings, the final-pair
action is \(1\otimes Q\).

This is the homogeneous three-single-site coefficient-space specialization of
the \(XB\) factor action in arXiv:1606.00608, lines 2185--2186 and 2205--2218.
-/
theorem rightPairLift_toMatrix_reindex
    (Q : NSiteSpace d 2 →ₗ[ℂ] NSiteSpace d 2) :
    Matrix.reindex (finThreeArrowEquiv (Fin d))
        (finThreeArrowEquiv (Fin d))
        (LinearMap.toMatrix' (rightPairLift Q)) =
      appendixBRightPairMatrix (Matrix.reindex (finTwoArrowEquiv (Fin d))
        (finTwoArrowEquiv (Fin d)) (LinearMap.toMatrix' Q)) := by
  classical
  ext σ τ
  by_cases h : σ.1 = τ.1
  · have hslice : (fun β ↦
        (Pi.single ((finThreeArrowEquiv (Fin d)).symm τ) (1 : ℂ) :
          NSiteSpace d 3)
          (replaceXBCfg ((finThreeArrowEquiv (Fin d)).symm σ) β)) =
        (Pi.single ((finTwoArrowEquiv (Fin d)).symm (τ.2.1, τ.2.2)) (1 : ℂ) :
          NSiteSpace d 2) := by
      funext β
      simp only [Pi.single_apply]
      simp only [replaceXBCfg_eq_iff]
      simp [finTwoArrowEquiv, h]
    change Q (fun β ↦
        (Pi.single ((finThreeArrowEquiv (Fin d)).symm τ) (1 : ℂ) :
          NSiteSpace d 3)
          (replaceXBCfg ((finThreeArrowEquiv (Fin d)).symm σ) β))
        (xbPairCfg ((finThreeArrowEquiv (Fin d)).symm σ)) =
      (if σ.1 = τ.1 then 1 else 0) *
        Q (Pi.single ((finTwoArrowEquiv (Fin d)).symm (τ.2.1, τ.2.2)) (1 : ℂ))
          ((finTwoArrowEquiv (Fin d)).symm (σ.2.1, σ.2.2))
    rw [hslice]
    simp [finTwoArrowEquiv, h]
  · have hslice : (fun β ↦
        (Pi.single ((finThreeArrowEquiv (Fin d)).symm τ) (1 : ℂ) :
          NSiteSpace d 3)
          (replaceXBCfg ((finThreeArrowEquiv (Fin d)).symm σ) β)) = 0 := by
      funext β
      simp only [Pi.single_apply, Pi.zero_apply]
      simp only [replaceXBCfg_eq_iff]
      simp [h]
    change Q (fun β ↦
        (Pi.single ((finThreeArrowEquiv (Fin d)).symm τ) (1 : ℂ) :
          NSiteSpace d 3)
          (replaceXBCfg ((finThreeArrowEquiv (Fin d)).symm σ) β))
        (xbPairCfg ((finThreeArrowEquiv (Fin d)).symm σ)) =
      (if σ.1 = τ.1 then 1 else 0) *
        Q (Pi.single ((finTwoArrowEquiv (Fin d)).symm (τ.2.1, τ.2.2)) (1 : ℂ))
          ((finTwoArrowEquiv (Fin d)).symm (σ.2.1, σ.2.2))
    rw [hslice]
    simp [h]

end MPSTensor
