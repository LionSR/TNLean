/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BoundaryActionComparison
import TNLean.MPS.MPDO.BoundaryDecompositionIntertwining
import TNLean.MPS.MPDO.BoundaryZipperUniqueness

/-!
# Fixed-final multiplicity L matrices from the exact action trees

The source-oriented L matrix is extracted from sequential analysis followed
by fusion-then-action synthesis. Normality makes each fixed-final cross
product a scalar times the target identity; a simultaneous word span removes
cross terms between different final blocks.

The two finite multiplicity spaces retain the source index orders `(z,i,j)`
and `(c,k,μ)`. No entrywise nonvanishing, adjoint relation, or mixed pentagon
is assumed.

**Local fix (multiplicity indices):** the later coupled pentagon must use
the typed F factor with upper `(d,η,χ)` and lower `(f,μ,ν)`, rather than the
reversed pairs printed in GLM23. See
`docs/paper-gaps/glm23_multiplicity_l_indices.tex`. This module does not yet
assert that coherence theorem.

## References

* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, `eq:F_symbol2`,
  `1Fsymbol`, and `coupledpent`, lines 517--562.
-/

open scoped Matrix BigOperators Kronecker

namespace MPOTensor

variable {d r s : ℕ} {χ : Fin r → ℕ} {D : Fin s → ℕ}
  {N : Fin r → Fin r → Fin r → ℕ} {M : Fin r → Fin s → Fin s → ℕ}

/-- The source's fixed-final fusion-then-action index `(c,k,μ)`. -/
abbrev FusionActionMultiplicity (N : Fin r → Fin r → Fin r → ℕ)
    (M : Fin r → Fin s → Fin s → ℕ) (a b : Fin r) (x y : Fin s) :=
  (c : Fin r) × (Fin (M c x y) × Fin (N a b c))

/-- The source's fixed-final sequential-action index `(z,i,j)`. -/
abbrev SequentialActionMultiplicity (M : Fin r → Fin s → Fin s → ℕ)
    (a b : Fin r) (x y : Fin s) :=
  (z : Fin s) × (Fin (M a z y) × Fin (M b x z))

/-- Grouping the fusion-then-action paths by their final state block. -/
def fusionActionPathEquiv (a b : Fin r) (x : Fin s) :
    ((y : Fin s) × FusionActionMultiplicity N M a b x y) ≃ FusionActionPath N M a b x where
  toFun q := ⟨⟨q.2.1, q.2.2.2⟩, ⟨q.1, q.2.2.1⟩⟩
  invFun q := ⟨q.2.1, ⟨q.1.1, q.2.2, q.1.2⟩⟩
  left_inv := by rintro ⟨y, c, k, μ⟩; rfl
  right_inv := by rintro ⟨⟨c, μ⟩, y, k⟩; rfl

/-- Grouping the sequential-action paths by their final state block. -/
def sequentialActionPathEquiv (a b : Fin r) (x : Fin s) :
    ((y : Fin s) × SequentialActionMultiplicity M a b x y) ≃
      SequentialActionPath M a b x where
  toFun q := ⟨⟨q.2.1, q.2.2.2⟩, ⟨q.1, q.2.2.1⟩⟩
  invFun q := ⟨q.2.1, ⟨q.1.1, q.2.2, q.1.2⟩⟩
  left_inv := by rintro ⟨y, z, i, j⟩; rfl
  right_inv := by rintro ⟨⟨z, j⟩, y, i⟩; rfl

/-- Grouped fusion-then-action coordinates, including the final bond. -/
def fusionActionCoordinateEquiv (a b : Fin r) (x : Fin s) :
    ((y : Fin s) × (FusionActionMultiplicity N M a b x y × Fin (D y))) ≃
      FusionActionCoordinate D N M a b x where
  toFun q := ⟨fusionActionPathEquiv a b x ⟨q.1, q.2.1⟩, q.2.2⟩
  invFun q := ⟨q.1.2.1, ⟨⟨q.1.1.1, q.1.2.2, q.1.1.2⟩, q.2⟩⟩
  left_inv := by rintro ⟨y, ⟨c, k, μ⟩, z⟩; rfl
  right_inv := by rintro ⟨⟨⟨c, μ⟩, y, k⟩, z⟩; rfl

/-- Grouped sequential-action coordinates, including the final bond. -/
def sequentialActionCoordinateEquiv (a b : Fin r) (x : Fin s) :
    ((y : Fin s) × (SequentialActionMultiplicity M a b x y × Fin (D y))) ≃
      SequentialActionCoordinate D M a b x where
  toFun q := ⟨sequentialActionPathEquiv a b x ⟨q.1, q.2.1⟩, q.2.2⟩
  invFun q := ⟨q.1.2.1, ⟨⟨q.1.1.1, q.1.2.2, q.1.1.2⟩, q.2⟩⟩
  left_inv := by rintro ⟨y, ⟨z, i, j⟩, k⟩; rfl
  right_inv := by rintro ⟨⟨⟨z, j⟩, y, i⟩, k⟩; rfl

variable
  (VF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ c)) (Fin (χ a * χ b)) ℂ)
  (WF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ a * χ b)) (Fin (χ c)) ℂ)
  (VA : ∀ a x y, Fin (M a x y) → Matrix (Fin (D y)) (Fin (χ a * D x)) ℂ)
  (WA : ∀ a x y, Fin (M a x y) → Matrix (Fin (χ a * D x)) (Fin (D y)) ℂ)

/-- The actual source-oriented L entries: rows are `(z,i,j)` and columns
are `(c,k,μ)`. The normalized trace extracts the scalar final-bond factor.
Source: GLM23 `eq:F_symbol2` and `1Fsymbol`. -/
noncomputable def actionLMatrix (a b : Fin r) (x y : Fin s) :
    Matrix (SequentialActionMultiplicity M a b x y)
      (FusionActionMultiplicity N M a b x y) ℂ :=
  fun p q ↦ (D y : ℂ)⁻¹ * Matrix.trace
    (sequentialActionAnalysis VA a b x (sequentialActionPathEquiv a b x ⟨y, p⟩) *
      fusionThenActionSynthesis WF WA a b x (fusionActionPathEquiv a b x ⟨y, q⟩))

/-- The multiplicity matrix in the inverse action-tree direction. -/
noncomputable def inverseActionLMatrix (a b : Fin r) (x y : Fin s) :
    Matrix (FusionActionMultiplicity N M a b x y)
      (SequentialActionMultiplicity M a b x y) ℂ :=
  fun p q ↦ (D y : ℂ)⁻¹ * Matrix.trace
    (fusionThenActionAnalysis VF VA a b x (fusionActionPathEquiv a b x ⟨y, p⟩) *
      sequentialActionSynthesis WA a b x (sequentialActionPathEquiv a b x ⟨y, q⟩))

private theorem eq_inv_dim_trace_smul_one_of_commute
    {d D : ℕ} {A : MPSTensor d D} (hA : Kraus.IsNormal A) (hD : 0 < D)
    (S : Matrix (Fin D) (Fin D) ℂ) (hS : ∀ i, S * A i = A i * S) :
    S = ((D : ℂ)⁻¹ * Matrix.trace S) • 1 := by
  obtain ⟨z, hz⟩ := hA.eq_smul_one_of_commute hS
  rw [hz, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
    smul_eq_mul, ← mul_assoc, mul_comm _ z, mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast hD.ne'), mul_one]

variable {O : ∀ a, MPOTensor d (χ a)} {A : ∀ x, MPSTensor d (D x)}
  (hF : ∀ a b,
    MPSTensor.IsBiorthogonalDecomposition (mulTensor (O a) (O b)).toMPSTensor
      (fun q : (c : Fin r) × Fin (N a b c) ↦ (O q.1).toMPSTensor)
      (fun q ↦ VF a b q.1 q.2) (fun q ↦ WF a b q.1 q.2))
  (hA : ∀ a x,
    MPSTensor.IsBiorthogonalDecomposition (actTensor (O a) (A x))
      (fun q : (y : Fin s) × Fin (M a x y) ↦ A q.1)
      (fun q ↦ VA a x q.1 q.2) (fun q ↦ WA a x q.1 q.2))
  (hNormal : ∀ y, Kraus.IsNormal (A y)) (hD : ∀ y, 0 < D y)

include hF hA hNormal hD in
/-- Within one final block, the actual tree contraction is the L entry
times the identity. Source: GLM23 `1Fsymbol`. -/
theorem actionLMatrix_cross (a b : Fin r) (x y : Fin s)
    (p : SequentialActionMultiplicity M a b x y)
    (q : FusionActionMultiplicity N M a b x y) :
    sequentialActionAnalysis VA a b x (sequentialActionPathEquiv a b x ⟨y, p⟩) *
      fusionThenActionSynthesis WF WA a b x (fusionActionPathEquiv a b x ⟨y, q⟩) =
        actionLMatrix WF VA WA a b x y p q •
          (1 : Matrix (Fin (D y)) (Fin (D y)) ℂ) := by
  apply eq_inv_dim_trace_smul_one_of_commute (hNormal y) (hD y)
  intro i
  exact ((sequentialAction_isBiorthogonal VA WA hA a b x).cross_intertwines
    (fusionThenAction_isBiorthogonal VF WF VA WA hF hA a b x)
    (sequentialActionPathEquiv a b x ⟨y, p⟩)
    (fusionActionPathEquiv a b x ⟨y, q⟩) i).symm

include hF hA hNormal hD in
/-- The reverse tree contraction has the inverse-direction scalar factor. -/
theorem inverseActionLMatrix_cross (a b : Fin r) (x y : Fin s)
    (p : FusionActionMultiplicity N M a b x y)
    (q : SequentialActionMultiplicity M a b x y) :
    fusionThenActionAnalysis VF VA a b x (fusionActionPathEquiv a b x ⟨y, p⟩) *
      sequentialActionSynthesis WA a b x (sequentialActionPathEquiv a b x ⟨y, q⟩) =
        inverseActionLMatrix VF VA WA a b x y p q •
          (1 : Matrix (Fin (D y)) (Fin (D y)) ℂ) := by
  apply eq_inv_dim_trace_smul_one_of_commute (hNormal y) (hD y)
  intro i
  exact ((fusionThenAction_isBiorthogonal VF WF VA WA hF hA a b x).cross_intertwines
    (sequentialAction_isBiorthogonal VA WA hA a b x)
    (fusionActionPathEquiv a b x ⟨y, p⟩)
    (sequentialActionPathEquiv a b x ⟨y, q⟩) i).symm

include hF hA hNormal hD in
/-- The full source-oriented comparison is block diagonal in the final
state label, with each block equal to the actual L matrix tensored with
the final bond identity. Source: GLM23 `1Fsymbol`. -/
theorem fusionToSequentialComparison_eq_blockDiagonal (a b : Fin r) (x : Fin s)
    {L : ℕ} (hSpan : MPSTensor.WordTupleSpanTop A L) :
    (fusionToSequentialComparison WF VA WA a b x).submatrix
      (sequentialActionCoordinateEquiv (D := D) a b x)
      (fusionActionCoordinateEquiv (D := D) a b x) =
        Matrix.blockDiagonal' (fun y ↦ actionLMatrix WF VA WA a b x y ⊗ₖ
          (1 : Matrix (Fin (D y)) (Fin (D y)) ℂ)) := by
  ext ⟨y, p, u⟩ ⟨z, q, v⟩
  change (sequentialActionAnalysis VA a b x (sequentialActionPathEquiv a b x ⟨y, p⟩) *
    fusionThenActionSynthesis WF WA a b x (fusionActionPathEquiv a b x ⟨z, q⟩)) u v = _
  by_cases hyz : y = z
  · subst z
    rw [actionLMatrix_cross VF WF VA WA hF hA hNormal hD]
    exact (Matrix.blockDiagonal'_apply_eq _ y (p, u) (q, v)).symm
  · have hzero := MPSTensor.rectangularIntertwiner_eq_zero_of_wordTupleSpanTop
      hSpan y z hyz
      (sequentialActionAnalysis VA a b x (sequentialActionPathEquiv a b x ⟨y, p⟩) *
        fusionThenActionSynthesis WF WA a b x (fusionActionPathEquiv a b x ⟨z, q⟩))
      (fun i ↦ (sequentialAction_isBiorthogonal VA WA hA a b x).cross_intertwines
        (fusionThenAction_isBiorthogonal VF WF VA WA hF hA a b x)
        (sequentialActionPathEquiv a b x ⟨y, p⟩)
        (fusionActionPathEquiv a b x ⟨z, q⟩) i)
    rw [hzero, Matrix.blockDiagonal'_apply_ne _ _ _ hyz]
    rfl

include hF hA hNormal hD in
/-- The inverse full action comparison has the reverse multiplicity
matrix in each final block. -/
theorem sequentialToFusionComparison_eq_blockDiagonal (a b : Fin r) (x : Fin s)
    {L : ℕ} (hSpan : MPSTensor.WordTupleSpanTop A L) :
    (sequentialToFusionComparison VF VA WA a b x).submatrix
      (fusionActionCoordinateEquiv (D := D) a b x)
      (sequentialActionCoordinateEquiv (D := D) a b x) =
        Matrix.blockDiagonal' (fun y ↦ inverseActionLMatrix VF VA WA a b x y ⊗ₖ
          (1 : Matrix (Fin (D y)) (Fin (D y)) ℂ)) := by
  ext ⟨y, p, u⟩ ⟨z, q, v⟩
  change (fusionThenActionAnalysis VF VA a b x (fusionActionPathEquiv a b x ⟨y, p⟩) *
    sequentialActionSynthesis WA a b x (sequentialActionPathEquiv a b x ⟨z, q⟩)) u v = _
  by_cases hyz : y = z
  · subst z
    rw [inverseActionLMatrix_cross VF WF VA WA hF hA hNormal hD]
    exact (Matrix.blockDiagonal'_apply_eq _ y (p, u) (q, v)).symm
  · have hzero := MPSTensor.rectangularIntertwiner_eq_zero_of_wordTupleSpanTop
      hSpan y z hyz
      (fusionThenActionAnalysis VF VA a b x (fusionActionPathEquiv a b x ⟨y, p⟩) *
        sequentialActionSynthesis WA a b x (sequentialActionPathEquiv a b x ⟨z, q⟩))
      (fun i ↦ (fusionThenAction_isBiorthogonal VF WF VA WA hF hA a b x).cross_intertwines
        (sequentialAction_isBiorthogonal VA WA hA a b x)
        (fusionActionPathEquiv a b x ⟨y, p⟩)
        (sequentialActionPathEquiv a b x ⟨z, q⟩) i)
    rw [hzero, Matrix.blockDiagonal'_apply_ne _ _ _ hyz]
    rfl

include hF hA hNormal hD in
/-- The constructed L matrices and their reverse comparisons are inverse
on both multiplicity spaces. Zero entries and zero-dimensional multiplicity
spaces are allowed. Source: GLM23 `eq:F_symbol2` and `1Fsymbol`. -/
theorem actionLMatrix_inverse (a b : Fin r) (x y : Fin s)
    {L : ℕ} (hL : 0 < L) (hSpan : MPSTensor.WordTupleSpanTop A L) :
    actionLMatrix WF VA WA a b x y * inverseActionLMatrix VF VA WA a b x y = 1 ∧
      inverseActionLMatrix VF VA WA a b x y * actionLMatrix WF VA WA a b x y = 1 := by
  have hFull := fullActionComparison_spec VF WF VA WA hF hA a b x hL hSpan
  have hforward :
      Matrix.blockDiagonal' (fun z ↦ actionLMatrix WF VA WA a b x z ⊗ₖ
        (1 : Matrix (Fin (D z)) (Fin (D z)) ℂ)) *
      Matrix.blockDiagonal' (fun z ↦ inverseActionLMatrix VF VA WA a b x z ⊗ₖ
        (1 : Matrix (Fin (D z)) (Fin (D z)) ℂ)) = 1 := by
    rw [← fusionToSequentialComparison_eq_blockDiagonal VF WF VA WA hF hA hNormal hD
        a b x hSpan,
      ← sequentialToFusionComparison_eq_blockDiagonal VF WF VA WA hF hA hNormal hD
        a b x hSpan,
      Matrix.submatrix_mul_equiv, hFull.1, Matrix.submatrix_one_equiv]
  have hbackward :
      Matrix.blockDiagonal' (fun z ↦ inverseActionLMatrix VF VA WA a b x z ⊗ₖ
        (1 : Matrix (Fin (D z)) (Fin (D z)) ℂ)) *
      Matrix.blockDiagonal' (fun z ↦ actionLMatrix WF VA WA a b x z ⊗ₖ
        (1 : Matrix (Fin (D z)) (Fin (D z)) ℂ)) = 1 := by
    rw [← sequentialToFusionComparison_eq_blockDiagonal VF WF VA WA hF hA hNormal hD
        a b x hSpan,
      ← fusionToSequentialComparison_eq_blockDiagonal VF WF VA WA hF hA hNormal hD
        a b x hSpan,
      Matrix.submatrix_mul_equiv, hFull.2.1, Matrix.submatrix_one_equiv]
  constructor
  · apply Matrix.mul_eq_one_of_kronecker_one (hD y)
    simpa only [← Matrix.blockDiagonal'_mul, Matrix.blockDiag'_blockDiagonal',
      Matrix.blockDiag'_one, Pi.one_apply] using
      congrArg (fun Z ↦ Matrix.blockDiag' Z y) hforward
  · apply Matrix.mul_eq_one_of_kronecker_one (hD y)
    simpa only [← Matrix.blockDiagonal'_mul, Matrix.blockDiag'_blockDiagonal',
      Matrix.blockDiag'_one, Pi.one_apply] using
      congrArg (fun Z ↦ Matrix.blockDiag' Z y) hbackward

include hF hA hNormal hD in
/-- The actual L matrices carry fusion-then-action analysis to sequential
analysis, with the final bond identity explicit. This is the source
`eq:F_symbol2` in collected coordinate form. -/
theorem actionLMatrix_analysis (a b : Fin r) (x : Fin s)
    {L : ℕ} (hL : 0 < L) (hSpan : MPSTensor.WordTupleSpanTop A L) :
    Matrix.blockDiagonal' (fun y ↦ actionLMatrix WF VA WA a b x y ⊗ₖ
        (1 : Matrix (Fin (D y)) (Fin (D y)) ℂ)) *
      (MPSTensor.decompositionAnalysis (fusionThenActionAnalysis VF VA a b x)).submatrix
        (fusionActionCoordinateEquiv (D := D) a b x) id =
      (MPSTensor.decompositionAnalysis (sequentialActionAnalysis VA a b x)).submatrix
        (sequentialActionCoordinateEquiv (D := D) a b x) id := by
  rw [← fusionToSequentialComparison_eq_blockDiagonal VF WF VA WA hF hA hNormal hD
      a b x hSpan, Matrix.submatrix_mul_equiv]
  exact congrArg
    (fun Z ↦ Z.submatrix (sequentialActionCoordinateEquiv (D := D) (M := M) a b x) id)
    (fusionToSequentialComparison_mul_analysis VF WF VA WA hF hA a b x hL hSpan)

include hF hA hD in
/-- The source's individual state-block assumptions already give inverse
L matrices; the simultaneous positive word span is derived internally. -/
theorem actionLMatrix_inverse_of_isInjective
    (hInj : ∀ y, Kraus.IsInjective (A y))
    (hne : MPSTensor.BlocksNotGaugePhaseEquiv A) (a b : Fin r) (x y : Fin s) :
    actionLMatrix WF VA WA a b x y * inverseActionLMatrix VF VA WA a b x y = 1 ∧
      inverseActionLMatrix VF VA WA a b x y * actionLMatrix WF VA WA a b x y = 1 := by
  obtain ⟨L, hL, hSpan⟩ :=
    MPSTensor.exists_positive_wordTupleSpanTop_of_isInjective hInj hD hne
  exact actionLMatrix_inverse VF WF VA WA hF hA (fun y ↦ (hInj y).isNormal) hD
    a b x y hL hSpan

end MPOTensor
