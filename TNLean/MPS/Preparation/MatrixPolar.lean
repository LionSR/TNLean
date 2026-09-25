/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import QICLean.Algebra.MatrixUnitaryBetween

/-!
# Polar decomposition of a rectangular complex matrix

For a complex matrix `M : ι × κ`, viewed as a linear map from `ℂ^κ` to `ℂ^ι`, this file
constructs the polar decomposition `M = V * P` used in the log-depth preparation of matrix
product states: `P = (Mᴴ M)^{1/2}` is positive semidefinite on `ℂ^κ`, and `V` is a partial
isometry with `Vᴴ V = Π`, where `Π` is the orthogonal projector onto the range of `P`. When
`M` is injective, `Π = 1`, so `V` is an isometry and `P` is positive definite.

All three factors are built by the continuous functional calculus of the Hermitian matrix
`Mᴴ M`: `P` is its positive square root `CFC.sqrt (Mᴴ M)`, `Π` applies the indicator of the
nonzero reals, and `V = M Q` where `Q` applies the reciprocal of the square root (with
`0⁻¹ = 0`).

## Main declarations

* `Matrix.polarPos` — the positive part `(Mᴴ M)^{1/2}`.
* `Matrix.polarSupport` — the projector `Π` onto the range of the positive part.
* `Matrix.polarIso` — the partial isometry `V`.
* `Matrix.polarIso_mul_polarPos` — `V * P = M`.
* `Matrix.conjTranspose_polarIso_mul_polarIso` — `Vᴴ * V = Π`.
* `Matrix.range_polarSupport` — `Π` has the same range as `P`.
* `Matrix.isIsometry_polarIso_of_injective` — for injective `M`, `V` is an isometry
  (`Matrix.IsIsometry`, that is, `Vᴴ V = 1`).
* `Matrix.exists_polar_decomposition` — the packaged existence statement.

## References

* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), paragraph "Approximation through the
  fixed-point state" (the decomposition `B = V P` preceding eq. `eq:B_TM`), and Supplemental
  Material, "Proof of Lemma 1 and extension to non-normal tensors" (`B = V P`, `P ≥ 0`,
  `V†V = Π` the projector onto the image of `P`).
-/

open scoped Matrix MatrixOrder ComplexOrder

namespace Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

omit [Fintype κ] [DecidableEq κ] in
/-- The Gram matrix `Mᴴ M` is self-adjoint, stated with the predicate of the matrix continuous
functional calculus (for the `IsHermitian` form use `isHermitian_conjTranspose_mul_self`). -/
private lemma isSelfAdjoint_gram (M : Matrix ι κ ℂ) : IsSelfAdjoint (Mᴴ * M) :=
  isHermitian_conjTranspose_mul_self M

/-- Every real spectral value of the Gram matrix `Mᴴ M` is nonnegative. -/
private lemma gram_spectrum_nonneg (M : Matrix ι κ ℂ) :
    ∀ x ∈ spectrum ℝ (Mᴴ * M), 0 ≤ x := by
  intro x hx
  obtain ⟨i, rfl⟩ := (isHermitian_conjTranspose_mul_self M).spectrum_real_eq_range_eigenvalues ▸ hx
  exact (posSemidef_conjTranspose_mul_self M).eigenvalues_nonneg i

/-- Any real function is continuous on the (finite) real spectrum of a matrix. -/
private lemma continuousOn_spectrum (f : ℝ → ℝ) (A : Matrix κ κ ℂ) :
    ContinuousOn f (spectrum ℝ A) :=
  A.finite_real_spectrum.continuousOn f

/-- The indicator of the nonzero reals, used to build the support projector. -/
private noncomputable def nonzeroIndicator (x : ℝ) : ℝ := if x = 0 then 0 else 1

/-- The positive part `P = (Mᴴ M)^{1/2}` of the polar decomposition of `M`.

arXiv:2307.01696, paragraph "Approximation through the fixed-point state" and Supplemental
Material, "Proof of Lemma 1 and extension to non-normal tensors": `P` is the positive
semidefinite factor of `B = V P`. -/
noncomputable def polarPos (M : Matrix ι κ ℂ) : Matrix κ κ ℂ :=
  CFC.sqrt (Mᴴ * M)

/-- The positive part is the real square root applied to `Mᴴ M` by the continuous functional
calculus. -/
private lemma polarPos_eq_cfc (M : Matrix ι κ ℂ) : polarPos M = cfc Real.sqrt (Mᴴ * M) := by
  rw [polarPos, CFC.sqrt_eq_real_sqrt _ (posSemidef_conjTranspose_mul_self M).nonneg,
    cfcₙ_eq_cfc]

/-- The orthogonal projector `Π` onto the range of the positive part of `M`.

arXiv:2307.01696, Supplemental Material, "Proof of Lemma 1 and extension to non-normal
tensors": `Π` is the projector onto the image of `P`. -/
noncomputable def polarSupport (M : Matrix ι κ ℂ) : Matrix κ κ ℂ :=
  cfc nonzeroIndicator (Mᴴ * M)

/-- The pseudo-inverse of the positive part, `(Mᴴ M)^{-1/2}` on the support and zero on the
kernel. -/
private noncomputable def polarPosInv (M : Matrix ι κ ℂ) : Matrix κ κ ℂ :=
  cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (Mᴴ * M)

/-- The partial isometry `V = M (Mᴴ M)^{-1/2}` of the polar decomposition of `M`.

arXiv:2307.01696, paragraph "Approximation through the fixed-point state" and Supplemental
Material, "Proof of Lemma 1 and extension to non-normal tensors": `V` is the isometric factor
of `B = V P`. -/
noncomputable def polarIso (M : Matrix ι κ ℂ) : Matrix ι κ ℂ :=
  M * polarPosInv M

/-- The positive part of the polar decomposition is positive semidefinite.

arXiv:2307.01696, Supplemental Material, "Proof of Lemma 1 and extension to non-normal
tensors": `P` is positive semidefinite. -/
theorem posSemidef_polarPos (M : Matrix ι κ ℂ) : (polarPos M).PosSemidef :=
  nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)

/-- The positive part squares to the Gram matrix: `P * P = Mᴴ M`. -/
theorem polarPos_mul_polarPos (M : Matrix ι κ ℂ) : polarPos M * polarPos M = Mᴴ * M :=
  CFC.sqrt_mul_sqrt_self _ (posSemidef_conjTranspose_mul_self M).nonneg

/-- The support projector is Hermitian. -/
theorem isHermitian_polarSupport (M : Matrix ι κ ℂ) : (polarSupport M).IsHermitian :=
  (cfc_predicate nonzeroIndicator (Mᴴ * M) : IsSelfAdjoint _)

/-- The support projector is idempotent. -/
theorem polarSupport_mul_polarSupport (M : Matrix ι κ ℂ) :
    polarSupport M * polarSupport M = polarSupport M := by
  have hc := continuousOn_spectrum nonzeroIndicator (Mᴴ * M)
  rw [polarSupport, ← cfc_mul _ _ (Mᴴ * M) hc hc]
  refine cfc_congr fun x _ => ?_
  unfold nonzeroIndicator
  split_ifs <;> simp

/-- The support projector fixes the positive part: `Π * P = P`. -/
theorem polarSupport_mul_polarPos (M : Matrix ι κ ℂ) :
    polarSupport M * polarPos M = polarPos M := by
  rw [polarSupport, polarPos_eq_cfc, ← cfc_mul _ _ (Mᴴ * M) (continuousOn_spectrum _ _)
    (continuousOn_spectrum _ _)]
  refine cfc_congr fun x _ => ?_
  unfold nonzeroIndicator
  split_ifs with h <;> simp [h]

/-- The support projector factors through the positive part: `Π = P * Q`. -/
private lemma polarPos_mul_polarPosInv (M : Matrix ι κ ℂ) :
    polarPos M * polarPosInv M = polarSupport M := by
  rw [polarSupport, polarPos_eq_cfc, polarPosInv, ← cfc_mul _ _ (Mᴴ * M) (continuousOn_spectrum _ _)
    (continuousOn_spectrum _ _)]
  refine cfc_congr fun x hx => ?_
  have hx0 := gram_spectrum_nonneg M x hx
  unfold nonzeroIndicator
  split_ifs with h
  · simp [h]
  · exact mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne hx0 (Ne.symm h)))

/-- The same factorization with the factors in the other order: `Π = Q * P`. -/
private lemma polarPosInv_mul_polarPos (M : Matrix ι κ ℂ) :
    polarPosInv M * polarPos M = polarSupport M := by
  rw [← polarPos_mul_polarPosInv, polarPos_eq_cfc, polarPosInv, ← cfc_mul _ _ (Mᴴ * M)
    (continuousOn_spectrum _ _) (continuousOn_spectrum _ _),
    ← cfc_mul _ _ (Mᴴ * M) (continuousOn_spectrum _ _) (continuousOn_spectrum _ _)]
  exact cfc_congr fun x _ => mul_comm _ _

/-- The Gram matrix is fixed by the support projector: `Mᴴ M Π = Mᴴ M`. -/
private lemma gram_mul_polarSupport (M : Matrix ι κ ℂ) :
    Mᴴ * M * polarSupport M = Mᴴ * M := by
  conv_lhs => rw [← cfc_id' ℝ (Mᴴ * M) (isSelfAdjoint_gram M)]
  conv_rhs => rw [← cfc_id' ℝ (Mᴴ * M) (isSelfAdjoint_gram M)]
  rw [polarSupport, ← cfc_mul _ _ (Mᴴ * M) (continuousOn_spectrum _ _)
    (continuousOn_spectrum _ _)]
  refine cfc_congr fun x _ => ?_
  unfold nonzeroIndicator
  split_ifs with h <;> simp [h]

/-- The matrix is fixed by the support projector: `M Π = M`. -/
theorem mul_polarSupport (M : Matrix ι κ ℂ) : M * polarSupport M = M := by
  have h : M * (polarSupport M - 1) = 0 := (conjTranspose_mul_self_mul_eq_zero M _).mp (by
    rw [Matrix.mul_sub, gram_mul_polarSupport, Matrix.mul_one, sub_self])
  rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h
  exact h

/-- **Polar decomposition**, product form: `V * P = M`.

arXiv:2307.01696, paragraph "Approximation through the fixed-point state" (`B = V P`) and
Supplemental Material, "Proof of Lemma 1 and extension to non-normal tensors". -/
theorem polarIso_mul_polarPos (M : Matrix ι κ ℂ) : polarIso M * polarPos M = M := by
  rw [polarIso, Matrix.mul_assoc, polarPosInv_mul_polarPos, mul_polarSupport]

/-- **Polar decomposition**, partial-isometry relation: `Vᴴ * V = Π`.

arXiv:2307.01696, Supplemental Material, "Proof of Lemma 1 and extension to non-normal
tensors": `V†V = Π` for `Π` the projector onto the image of `P`. -/
theorem conjTranspose_polarIso_mul_polarIso (M : Matrix ι κ ℂ) :
    (polarIso M)ᴴ * polarIso M = polarSupport M := by
  have hQ : (polarPosInv M)ᴴ = polarPosInv M :=
    (cfc_predicate (fun x : ℝ => (Real.sqrt x)⁻¹) (Mᴴ * M) : IsSelfAdjoint _)
  rw [polarIso, conjTranspose_mul, hQ, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ]
  conv_lhs => rw [← cfc_id' ℝ (Mᴴ * M) (isSelfAdjoint_gram M)]
  rw [polarPosInv, ← cfc_mul _ _ (Mᴴ * M) (continuousOn_spectrum _ _)
    (continuousOn_spectrum _ _), ← cfc_mul _ _ (Mᴴ * M) (continuousOn_spectrum _ _)
    (continuousOn_spectrum _ _), polarSupport]
  refine cfc_congr fun x hx => ?_
  have hx0 := gram_spectrum_nonneg M x hx
  unfold nonzeroIndicator
  split_ifs with h
  · simp [h]
  · have hs : Real.sqrt x ≠ 0 := Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne hx0 (Ne.symm h))
    have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0
    field_simp
    linarith [hsq]

/-- The support projector and the positive part have the same range.

arXiv:2307.01696, Supplemental Material, "Proof of Lemma 1 and extension to non-normal
tensors": `Π` is the projector onto the image of `P`. -/
theorem range_polarSupport (M : Matrix ι κ ℂ) :
    LinearMap.range (polarSupport M).mulVecLin = LinearMap.range (polarPos M).mulVecLin := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    refine ⟨polarPosInv M *ᵥ v, ?_⟩
    simp [mulVec_mulVec, polarPos_mul_polarPosInv]
  · rintro _ ⟨v, rfl⟩
    refine ⟨polarPos M *ᵥ v, ?_⟩
    simp [mulVec_mulVec, polarSupport_mul_polarPos]

/-- For an injective matrix the support projector is the identity. -/
theorem polarSupport_eq_one_of_injective (M : Matrix ι κ ℂ) (hM : Function.Injective M.mulVec) :
    polarSupport M = 1 := by
  have hpos := PosDef.conjTranspose_mul_self M hM
  rw [polarSupport, ← cfc_one ℝ (Mᴴ * M)]
  refine cfc_congr fun x hx => ?_
  obtain ⟨i, rfl⟩ := (isHermitian_conjTranspose_mul_self M).spectrum_real_eq_range_eigenvalues ▸ hx
  simp [nonzeroIndicator, (hpos.eigenvalues_pos i).ne']

/-- **Polar decomposition of an injective matrix**: `V` is an isometry, `Vᴴ V = 1`.

arXiv:2307.01696, paragraph "Approximation through the fixed-point state": for injective `B`,
`B = V P` with `V†V = 1`. -/
theorem isIsometry_polarIso_of_injective (M : Matrix ι κ ℂ)
    (hM : Function.Injective M.mulVec) : (polarIso M).IsIsometry := by
  rw [IsIsometry, conjTranspose_polarIso_mul_polarIso, polarSupport_eq_one_of_injective M hM]

/-- **Polar decomposition of an injective matrix**: the positive part is positive definite.

arXiv:2307.01696, paragraph "Approximation through the fixed-point state": for injective `B`,
`P > 0`. -/
theorem posDef_polarPos_of_injective (M : Matrix ι κ ℂ) (hM : Function.Injective M.mulVec) :
    (polarPos M).PosDef := by
  refine ((posSemidef_polarPos M).posDef_iff_isUnit).mpr ?_
  have hunit : IsUnit (polarPos M * polarPos M) := by
    rw [polarPos_mul_polarPos]; exact (PosDef.conjTranspose_mul_self M hM).isUnit
  exact isUnit_of_mul_isUnit_left hunit

omit [DecidableEq κ] in
/-- **Polar decomposition** (existence form): every complex matrix `M` factors as `M = V P` with
`P` positive semidefinite and `Vᴴ V = Π`, where `Π` is a Hermitian idempotent whose range is
the range of `P`.

arXiv:2307.01696, Supplemental Material, "Proof of Lemma 1 and extension to non-normal
tensors". -/
theorem exists_polar_decomposition (M : Matrix ι κ ℂ) :
    ∃ (V : Matrix ι κ ℂ) (P E : Matrix κ κ ℂ), M = V * P ∧ P.PosSemidef ∧ Vᴴ * V = E ∧
      E.IsHermitian ∧ E * E = E ∧
      LinearMap.range E.mulVecLin = LinearMap.range P.mulVecLin := by
  classical
  exact ⟨polarIso M, polarPos M, polarSupport M, (polarIso_mul_polarPos M).symm,
    posSemidef_polarPos M, conjTranspose_polarIso_mul_polarIso M, isHermitian_polarSupport M,
    polarSupport_mul_polarSupport M, range_polarSupport M⟩

end Matrix
