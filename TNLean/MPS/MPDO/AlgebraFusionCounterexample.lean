/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.AlgebraStructure
import TNLean.MPS.MPDO.FusionIsometries

/-!
# Counterexample to the support-algebra converse

This file gives an explicit trace-preserving MPO tensor with a positive-definite
fixed point which satisfies `MPOTensor.IsRFP_MPDO_via_algebra` but not
`MPOTensor.IsRFP_MPDO_via_transferRetract`.

## References

* arXiv:1606.00608, Theorem 4.14(ii) and Appendix C.4, lines 2046--2085
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder

noncomputable section

namespace MPOTensor

local instance instMatrixNormedAddCommGroup :
    NormedAddCommGroup (Matrix (Fin 2) (Fin 2) ℂ) :=
  Matrix.toMatrixNormedAddCommGroup (n := Fin 2) (𝕜 := ℂ) 1
    (Matrix.PosDef.one (n := Fin 2) (R := ℂ))

local instance instMatrixInnerProductSpace :
    InnerProductSpace ℂ (Matrix (Fin 2) (Fin 2) ℂ) :=
  Matrix.toMatrixInnerProductSpace (n := Fin 2) (𝕜 := ℂ) 1
    (Matrix.PosDef.one (n := Fin 2) (R := ℂ)).posSemidef

private def phaseFlipTensor : MPSTensor 2 2 := fun i =>
  if i = 0 then (↑(3 / 5 : ℝ) : ℂ) • 1
  else (↑(4 / 5 : ℝ) : ℂ) • !![1, 0; 0, -1]

private theorem phaseFlipTensor_conjTranspose (i : Fin 2) :
    (phaseFlipTensor i)ᴴ = phaseFlipTensor i := by
  fin_cases i <;>
    ext j k <;>
    fin_cases j <;>
    fin_cases k <;>
    simp [phaseFlipTensor, Matrix.conjTranspose_apply]

private theorem phaseFlipTensor_transferMap_apply
    (X : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    MPSTensor.transferMap phaseFlipTensor X i j =
      if i = j then X i j else (-7 / 25 : ℂ) * X i j := by
  have hstarFour : (starRingEnd ℂ) (4 : ℂ) = 4 :=
    map_natCast (starRingEnd ℂ) 4
  have hstarFive : (starRingEnd ℂ) (5 : ℂ) = 5 :=
    map_natCast (starRingEnd ℂ) 5
  fin_cases i <;> fin_cases j <;>
    simp only [phaseFlipTensor, Fin.zero_eta, Fin.isValue, Fin.mk_one,
      MPSTensor.transferMap_apply, Fin.sum_univ_two, Matrix.add_apply,
      zero_ne_one, one_ne_zero, ↓reduceIte]
  all_goals simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.mul_apply,
    Matrix.conjTranspose_apply, RCLike.star_def]
  all_goals simp only [hstarFour, hstarFive]
  all_goals norm_num
  all_goals ring

private theorem phaseFlipTensor_transferMap_adjoint :
    (MPSTensor.transferMap phaseFlipTensor).adjoint =
      MPSTensor.transferMap phaseFlipTensor := by
  apply LinearMap.ext
  intro X
  rw [MPSTensor.transferMap_adjoint_apply_eq_adjointMap]
  simp [Kraus.adjointMap, MPSTensor.transferMap_apply,
    phaseFlipTensor_conjTranspose]

private theorem phaseFlipTensor_transferMap_pow_adjoint (n : ℕ) :
    ((MPSTensor.transferMap phaseFlipTensor) ^ n).adjoint =
      (MPSTensor.transferMap phaseFlipTensor) ^ n := by
  have hSymmetric : (MPSTensor.transferMap phaseFlipTensor).IsSymmetric :=
    (LinearMap.eq_adjoint_iff _ _).mp phaseFlipTensor_transferMap_adjoint.symm
  exact (hSymmetric.pow n).adjoint_eq

private theorem phaseFlipTensor_transferMap_pow_apply
    (n : ℕ) (X : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    ((MPSTensor.transferMap phaseFlipTensor) ^ n) X i j =
      if i = j then X i j else (-7 / 25 : ℂ) ^ n * X i j := by
  induction n generalizing X with
  | zero =>
      simp [Module.End.one_eq_id]
  | succ n ih =>
      rw [pow_succ, Module.End.mul_eq_comp, LinearMap.comp_apply]
      rw [ih]
      rw [phaseFlipTensor_transferMap_apply]
      by_cases hij : i = j
      · simp [hij]
      · simp only [hij, ↓reduceIte]
        rw [pow_succ]
        ring

private theorem phaseFlip_eigenvalue_pow_ne_one {n : ℕ} (hn : 0 < n) :
    (-7 / 25 : ℂ) ^ n ≠ 1 := by
  intro h
  have hnorm := congrArg norm h
  rw [norm_pow, neg_div, norm_neg, Complex.norm_div] at hnorm
  norm_num at hnorm
  have hlt : (7 / 25 : ℝ) ^ n < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) (Nat.ne_of_gt hn)
  linarith

private theorem phaseFlipTensor_transferMap_pow_fixed
    {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : MPSTensor.transferMap phaseFlipTensor X = X) (n : ℕ) :
    (MPSTensor.transferMap phaseFlipTensor ^ n) X = X := by
  rw [Module.End.pow_apply]
  exact Function.IsFixedPt.iterate hX n

private theorem phaseFlipTensor_transferMap_pow_fixed_iff
    {n : ℕ} (hn : 0 < n) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    (MPSTensor.transferMap phaseFlipTensor ^ n) X = X ↔
      MPSTensor.transferMap phaseFlipTensor X = X := by
  constructor
  · intro hX
    apply Matrix.ext
    intro i j
    rw [phaseFlipTensor_transferMap_apply]
    by_cases hij : i = j
    · simp [hij]
    · have hentry := congrArg (fun Y => Y i j) hX
      rw [phaseFlipTensor_transferMap_pow_apply] at hentry
      simp only [hij, ↓reduceIte] at hentry
      have hzero : ((-7 / 25 : ℂ) ^ n - 1) * X i j = 0 := by
        linear_combination hentry
      have hentryZero : X i j = 0 :=
        (mul_eq_zero.mp hzero).resolve_left <|
          sub_ne_zero.mpr (phaseFlip_eigenvalue_pow_ne_one hn)
      simp [hij, hentryZero]
  · intro hX
    exact phaseFlipTensor_transferMap_pow_fixed hX n

private theorem phaseFlipMPO_isTP :
    Kraus.IsTP phaseFlipTensor.toMPOTensor.toMPSTensor := by
  suffices hAdjointOne :
      Kraus.adjointMap phaseFlipTensor.toMPOTensor.toMPSTensor 1 = 1 by
    simpa [Kraus.IsTP, Kraus.adjointMap, Matrix.mul_one] using hAdjointOne
  rw [← MPSTensor.transferMap_adjoint_apply_eq_adjointMap]
  have hMap : MPSTensor.transferMap phaseFlipTensor.toMPOTensor.toMPSTensor =
      MPSTensor.transferMap phaseFlipTensor := by
    rw [← MPOTensor.transferMap_eq_toMPSTensor,
      MPSTensor.toMPOTensor_transferMap]
  rw [hMap, phaseFlipTensor_transferMap_adjoint]
  apply Matrix.ext
  intro i j
  rw [phaseFlipTensor_transferMap_apply]
  by_cases hij : i = j <;> simp [hij]

private theorem phaseFlipMPO_adjointFixedPoints_eq
    (n : ℕ) (hn : 0 < n) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    (MPOTensor.transferMap phaseFlipTensor.toMPOTensor).adjoint X = X ↔
      (blockedTransferMap phaseFlipTensor.toMPOTensor n).adjoint X = X := by
  rw [blockedTransferMap_eq_pow, MPSTensor.toMPOTensor_transferMap,
    phaseFlipTensor_transferMap_adjoint,
    phaseFlipTensor_transferMap_pow_adjoint]
  exact (phaseFlipTensor_transferMap_pow_fixed_iff hn X).symm

private theorem phaseFlipMPO_one_fixed :
    MPOTensor.transferMap phaseFlipTensor.toMPOTensor 1 = 1 := by
  rw [MPSTensor.toMPOTensor_transferMap]
  apply Matrix.ext
  intro i j
  rw [phaseFlipTensor_transferMap_apply]
  by_cases hij : i = j <;> simp [hij]

private theorem phaseFlipMPO_isRFP_MPDO_via_algebra :
    IsRFP_MPDO_via_algebra phaseFlipTensor.toMPOTensor :=
  isRFP_MPDO_via_algebra_of_adjointFixedPoints_eq_of_isTP_of_posDef_fixed
    phaseFlipMPO_isTP (Matrix.PosDef.one (n := Fin 2) (R := ℂ))
      phaseFlipMPO_one_fixed phaseFlipMPO_adjointFixedPoints_eq

private theorem phaseFlipMPO_not_isRFP_MPDO_via_transferRetract :
    ¬IsRFP_MPDO_via_transferRetract phaseFlipTensor.toMPOTensor := by
  intro hFusion
  have hRFP := isRFP_of_isRFP_MPDO_via_transferRetract hFusion
  change MPOTensor.transferMap phaseFlipTensor.toMPOTensor ∘ₗ
      MPOTensor.transferMap phaseFlipTensor.toMPOTensor =
        MPOTensor.transferMap phaseFlipTensor.toMPOTensor at hRFP
  let X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]
  have hEntry := congrArg (fun E => E X 0 1) hRFP
  simp only [LinearMap.comp_apply, MPSTensor.toMPOTensor_transferMap] at hEntry
  rw [phaseFlipTensor_transferMap_apply,
    phaseFlipTensor_transferMap_apply] at hEntry
  norm_num [X] at hEntry

/-- The support-algebra predicate does not imply the fusion predicate, even
under trace preservation and the existence of a positive-definite fixed point.

The witness is the qubit phase-flip channel with Kraus operators
\(K_0=\frac35 I\) and \(K_1=\frac45 Z\). Its off-diagonal eigenvalue is
\(-\frac7{25}\), so every positive power has the same fixed-point algebra,
while the transfer map is not idempotent.

This does not contradict arXiv:1606.00608, Theorem 4.14(ii). The converse in
Appendix C.4, lines 2046--2085, assumes the positive BNT-label coefficient
formula and the length-one idempotent trace identity, neither of which is part
of `IsRFP_MPDO_via_algebra`. -/
theorem exists_isRFP_MPDO_via_algebra_not_isRFP_MPDO_via_transferRetract :
    ∃ (M : MPOTensor 2 2) (ρ : Matrix (Fin 2) (Fin 2) ℂ),
      Kraus.IsTP M.toMPSTensor ∧ ρ.PosDef ∧ MPOTensor.transferMap M ρ = ρ ∧
        IsRFP_MPDO_via_algebra M ∧ ¬IsRFP_MPDO_via_transferRetract M :=
  ⟨phaseFlipTensor.toMPOTensor, 1, phaseFlipMPO_isTP,
    Matrix.PosDef.one (n := Fin 2) (R := ℂ), phaseFlipMPO_one_fixed,
    phaseFlipMPO_isRFP_MPDO_via_algebra, phaseFlipMPO_not_isRFP_MPDO_via_transferRetract⟩

end MPOTensor
