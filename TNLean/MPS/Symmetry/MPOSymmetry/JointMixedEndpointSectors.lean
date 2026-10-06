/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.JointMixedEndpointSupport

/-!
# Physical phase sectors of the joint mixed endpoint

The four physical summands have phase pairs \(00,01,10,11\), independently
of their block labels. Multiplication by the first virtual projection
selects the corresponding row or column phase. At parameter zero the
two-site joint support has column phase zero at its first site and row
phase zero at its second site. Its two outer phase selectors act by
multiplication of every virtual boundary, so they preserve the joint
support even when distinct blocks overlap on the shared endpoint alphabet.

Source: GLM23, arXiv:2203.12563, Section 5, lines 1695–1777.
-/

open scoped Matrix BigOperators

namespace MPSTensor.MPOSymmetry

variable {d₀ d₁ r N : ℕ} {D₀ D₁ : Fin r → ℕ}

/-- Indicator of row phase zero in the common physical alphabet.
Source: arXiv:2203.12563, Section 5, lines 1695–1704. -/
noncomputable def jointMixedRowWeight
    (p : Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁)) : ℂ :=
  match (Fintype.equivFin (JointMixedPhysical d₀ d₁ D₀ D₁)).symm p with
  | .inl _ => 1
  | .inr (.inl _) => 1
  | .inr (.inr _) => 0

/-- Indicator of column phase zero in the common physical alphabet.
Source: arXiv:2203.12563, Section 5, lines 1695–1704. -/
noncomputable def jointMixedColumnWeight
    (p : Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁)) : ℂ :=
  match (Fintype.equivFin (JointMixedPhysical d₀ d₁ D₀ D₁)).symm p with
  | .inl _ => 1
  | .inr (.inl _) => 0
  | .inr (.inr (.inl _)) => 1
  | .inr (.inr (.inr _)) => 0

/-- Both physical phase indicators take only the values zero and one.
Source: arXiv:2203.12563, Section 5, lines 1695–1704. -/
theorem jointMixedRowWeight_eq_zero_or_one
    (p : Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁)) :
    jointMixedRowWeight p = 0 ∨ jointMixedRowWeight p = 1 := by
  unfold jointMixedRowWeight
  split <;> simp

/-- Both physical phase indicators take only the values zero and one.
Source: arXiv:2203.12563, Section 5, lines 1695–1704. -/
theorem jointMixedColumnWeight_eq_zero_or_one
    (p : Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁)) :
    jointMixedColumnWeight p = 0 ∨ jointMixedColumnWeight p = 1 := by
  unfold jointMixedColumnWeight
  split <;> simp

/-- Both zero-phase conditions select exactly the single shared first
endpoint alphabet. Source: arXiv:2203.12563, Section 5, lines 1695–1704. -/
theorem jointMixedRowColumnWeight_eq_one_iff
    (p : Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁)) :
    (jointMixedRowWeight p = 1 ∧ jointMixedColumnWeight p = 1) ↔
      ∃ i, (Fintype.equivFin (JointMixedPhysical d₀ d₁ D₀ D₁)).symm p = Sum.inl i := by
  rcases hp : (Fintype.equivFin (JointMixedPhysical d₀ d₁ D₀ D₁)).symm p with
    a | a | a | a <;>
    simp [jointMixedRowWeight, jointMixedColumnWeight, hp]

/-- Left virtual projection selects the row phase of each actual joint
letter. Source: arXiv:2203.12563, Section 5, lines 1695–1704. -/
theorem bondInterpolationMatrix_zero_mul_jointMixedEndpointBase
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (x : Fin r) (p : Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁)) :
    bondInterpolationMatrix (D₀ x) (D₁ x) 0 * jointMixedEndpointBase A₀ A₁ x p =
      jointMixedRowWeight p • jointMixedEndpointBase A₀ A₁ x p := by
  classical
  ext i j
  simp only [bondInterpolationMatrix, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]
  rcases hp : (Fintype.equivFin (JointMixedPhysical d₀ d₁ D₀ D₁)).symm p with
    a | ⟨y, a, b⟩ | ⟨y, a, b⟩ | a
  · cases hi : finSumFinEquiv.symm i <;> cases hj : finSumFinEquiv.symm j <;>
      simp [jointMixedEndpointBase, jointMixedEndpointLetter, jointMixedRowWeight, hp,
        bondInterpolationWeight, hi, hj, Matrix.fromBlocks]
  · by_cases h : x = y
    · subst y
      cases hi : finSumFinEquiv.symm i <;> cases hj : finSumFinEquiv.symm j <;>
        simp [jointMixedEndpointBase, jointMixedEndpointLetter, jointMixedRowWeight, hp,
          bondInterpolationWeight, hi, hj, Matrix.single_apply]
    · simp [jointMixedEndpointBase, jointMixedEndpointLetter, hp, Pi.single_eq_of_ne h]
  · by_cases h : x = y
    · subst y
      cases hi : finSumFinEquiv.symm i <;> cases hj : finSumFinEquiv.symm j <;>
        simp [jointMixedEndpointBase, jointMixedEndpointLetter, jointMixedRowWeight, hp,
          bondInterpolationWeight, hi, hj, Matrix.single_apply]
    · simp [jointMixedEndpointBase, jointMixedEndpointLetter, hp, Pi.single_eq_of_ne h]
  · cases hi : finSumFinEquiv.symm i <;> cases hj : finSumFinEquiv.symm j <;>
      simp [jointMixedEndpointBase, jointMixedEndpointLetter, jointMixedRowWeight, hp,
        bondInterpolationWeight, hi, hj, Matrix.fromBlocks]

/-- Right virtual projection selects the column phase of each actual joint
letter. Source: arXiv:2203.12563, Section 5, lines 1695–1704. -/
theorem jointMixedEndpointBase_mul_bondInterpolationMatrix_zero
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (x : Fin r) (p : Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁)) :
    jointMixedEndpointBase A₀ A₁ x p * bondInterpolationMatrix (D₀ x) (D₁ x) 0 =
      jointMixedColumnWeight p • jointMixedEndpointBase A₀ A₁ x p := by
  classical
  ext i j
  simp only [bondInterpolationMatrix, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
  rcases hp : (Fintype.equivFin (JointMixedPhysical d₀ d₁ D₀ D₁)).symm p with
    a | ⟨y, a, b⟩ | ⟨y, a, b⟩ | a
  · cases hi : finSumFinEquiv.symm i <;> cases hj : finSumFinEquiv.symm j <;>
      simp [jointMixedEndpointBase, jointMixedEndpointLetter, jointMixedColumnWeight, hp,
        bondInterpolationWeight, hi, hj, Matrix.fromBlocks]
  · by_cases h : x = y
    · subst y
      cases hi : finSumFinEquiv.symm i <;> cases hj : finSumFinEquiv.symm j <;>
        simp [jointMixedEndpointBase, jointMixedEndpointLetter, jointMixedColumnWeight, hp,
          bondInterpolationWeight, hi, hj, Matrix.single_apply]
    · simp [jointMixedEndpointBase, jointMixedEndpointLetter, hp, Pi.single_eq_of_ne h]
  · by_cases h : x = y
    · subst y
      cases hi : finSumFinEquiv.symm i <;> cases hj : finSumFinEquiv.symm j <;>
        simp [jointMixedEndpointBase, jointMixedEndpointLetter, jointMixedColumnWeight, hp,
          bondInterpolationWeight, hi, hj, Matrix.single_apply]
    · simp [jointMixedEndpointBase, jointMixedEndpointLetter, hp, Pi.single_eq_of_ne h]
  · cases hi : finSumFinEquiv.symm i <;> cases hj : finSumFinEquiv.symm j <;>
      simp [jointMixedEndpointBase, jointMixedEndpointLetter, jointMixedColumnWeight, hp,
        bondInterpolationWeight, hi, hj, Matrix.fromBlocks]

/-- Row-phase projection at a specified site of any chain.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
noncomputable def jointMixedRowSector (d₀ d₁ : ℕ) (D₀ D₁ : Fin r → ℕ) (site : Fin N) :
    EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) N) →ₗ[ℂ]
      EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) N) :=
  Matrix.toEuclideanLin (Matrix.diagonal fun σ => jointMixedRowWeight (σ site))

/-- Column-phase projection at a specified site of any chain.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
noncomputable def jointMixedColumnSector (d₀ d₁ : ℕ) (D₀ D₁ : Fin r → ℕ) (site : Fin N) :
    EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) N) →ₗ[ℂ]
      EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) N) :=
  Matrix.toEuclideanLin (Matrix.diagonal fun σ => jointMixedColumnWeight (σ site))

@[simp]
theorem jointMixedRowSector_apply (site : Fin N)
    (v : EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) N))
    (σ : Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) N) :
    jointMixedRowSector d₀ d₁ D₀ D₁ site v σ = jointMixedRowWeight (σ site) * v σ := by
  simp [jointMixedRowSector, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    Matrix.mulVec_diagonal]

@[simp]
theorem jointMixedColumnSector_apply (site : Fin N)
    (v : EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) N))
    (σ : Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) N) :
    jointMixedColumnSector d₀ d₁ D₀ D₁ site v σ = jointMixedColumnWeight (σ site) * v σ := by
  simp [jointMixedColumnSector, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    Matrix.mulVec_diagonal]

/-- Two-site joint boundary coefficients are sums of block trace pairings.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem blockInsertedBoundaryMap_two_apply {d : ℕ} {dim : Fin r → ℕ}
    (A : (x : Fin r) → MPSTensor d (dim x))
    (W X : (x : Fin r) → Matrix (Fin (dim x)) (Fin (dim x)) ℂ) (σ : Cfg d 2) :
    blockInsertedBoundaryMap A W 2 (blockBoundaryEquiv.symm X) σ =
      ∑ x, Matrix.trace (A x (σ 0) * W x * A x (σ 1) * X x) := by
  change blockInsertedGroundSpaceMap A W 2 X σ = _
  simp [blockInsertedGroundSpaceMap_apply, insertedGroundSpaceMap_apply,
    insertedEvalWord, List.ofFn_succ, Kraus.evalWord, Matrix.mul_assoc]

/-- The outer first-row selector multiplies each boundary on the right.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedRowSector_blockInsertedBoundaryMap
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (W X : (x : Fin r) → Matrix (Fin (D₀ x + D₁ x)) (Fin (D₀ x + D₁ x)) ℂ) :
    jointMixedRowSector d₀ d₁ D₀ D₁ (0 : Fin 2)
      (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁) W 2
        (blockBoundaryEquiv.symm X)) =
      blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁) W 2
        (blockBoundaryEquiv.symm fun x => X x * bondInterpolationMatrix (D₀ x) (D₁ x) 0) := by
  ext σ
  rw [jointMixedRowSector_apply, blockInsertedBoundaryMap_two_apply,
    blockInsertedBoundaryMap_two_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  conv_rhs => rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [← Matrix.mul_assoc, bondInterpolationMatrix_zero_mul_jointMixedEndpointBase,
    Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

/-- The outer last-column selector multiplies each boundary on the left.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedColumnSector_blockInsertedBoundaryMap
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (W X : (x : Fin r) → Matrix (Fin (D₀ x + D₁ x)) (Fin (D₀ x + D₁ x)) ℂ) :
    jointMixedColumnSector d₀ d₁ D₀ D₁ (1 : Fin 2)
      (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁) W 2
        (blockBoundaryEquiv.symm X)) =
      blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁) W 2
        (blockBoundaryEquiv.symm fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0 * X x) := by
  ext σ
  rw [jointMixedColumnSector_apply, blockInsertedBoundaryMap_two_apply,
    blockInsertedBoundaryMap_two_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  conv_rhs => rw [Matrix.mul_assoc (jointMixedEndpointBase A₀ A₁ x (σ 0) * W x),
    ← Matrix.mul_assoc (jointMixedEndpointBase A₀ A₁ x (σ 1)),
    jointMixedEndpointBase_mul_bondInterpolationMatrix_zero]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
    Matrix.mul_assoc]

/-- At zero parameter the first column phase of every joint support vector
is zero. Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedColumnSector_zero_blockInsertedBoundaryMap
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (X : (x : Fin r) → Matrix (Fin (D₀ x + D₁ x)) (Fin (D₀ x + D₁ x)) ℂ) :
    jointMixedColumnSector d₀ d₁ D₀ D₁ (0 : Fin 2)
      (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
        (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2 (blockBoundaryEquiv.symm X)) =
      blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
        (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2 (blockBoundaryEquiv.symm X) := by
  ext σ
  rw [jointMixedColumnSector_apply, blockInsertedBoundaryMap_two_apply]
  rcases jointMixedColumnWeight_eq_zero_or_one (σ 0) with h | h
  · rw [h, zero_mul]
    symm
    apply Finset.sum_eq_zero
    intro x _
    rw [jointMixedEndpointBase_mul_bondInterpolationMatrix_zero, h, zero_smul,
      Matrix.zero_mul, Matrix.zero_mul, Matrix.trace_zero]
  · rw [h, one_mul]

/-- At zero parameter the second row phase of every joint support vector
is zero. Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedRowSector_one_blockInsertedBoundaryMap
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (X : (x : Fin r) → Matrix (Fin (D₀ x + D₁ x)) (Fin (D₀ x + D₁ x)) ℂ) :
    jointMixedRowSector d₀ d₁ D₀ D₁ (1 : Fin 2)
      (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
        (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2 (blockBoundaryEquiv.symm X)) =
      blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
        (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2 (blockBoundaryEquiv.symm X) := by
  ext σ
  rw [jointMixedRowSector_apply, blockInsertedBoundaryMap_two_apply]
  rcases jointMixedRowWeight_eq_zero_or_one (σ 1) with h | h
  · rw [h, zero_mul]
    symm
    apply Finset.sum_eq_zero
    intro x _
    rw [Matrix.mul_assoc (jointMixedEndpointBase A₀ A₁ x (σ 0)),
      bondInterpolationMatrix_zero_mul_jointMixedEndpointBase, h, zero_smul,
      Matrix.mul_zero, Matrix.zero_mul, Matrix.trace_zero]
  · rw [h, one_mul]

end MPSTensor.MPOSymmetry
