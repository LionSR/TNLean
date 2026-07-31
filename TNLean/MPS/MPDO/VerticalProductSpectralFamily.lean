/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.VerticalProductPairBlocks

/-!
# Spectral families of retained vertical products

This file assembles the normal decompositions of all retained copy-pair
tensors, enumerates their active corners, and records their blocked-sector
comparison data.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.4, lines 2020--2029
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

noncomputable section

namespace MPOTensor

/-- The simultaneous isometry-retaining spectral decompositions of all
retained copy-pair tensors.  The local inclusions are kept explicitly because
their range projections are the projectors used in the subsequent positivity
comparison.

Source: CPSV16, Appendix C.4, lines 2020--2029. -/
structure RetainedProductSpectralFamily
    {g D : ℕ} (dim mult : Fin g → ℕ)
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (B : (α : Fin g) → MPSTensor (D * D) (dim α)) where
  /-- Number of nonzero spectral corners in a copy-pair tensor. -/
  count : VerticalCopyPair mult → ℕ
  /-- Bond dimension of a local spectral corner. -/
  localDim : (p : VerticalCopyPair mult) → Fin (count p) → ℕ
  /-- Positive spectral coefficient of a local corner. -/
  coefficient : (p : VerticalCopyPair mult) → Fin (count p) → ℂ
  /-- Normal tensor of a local corner. -/
  block : (p : VerticalCopyPair mult) → (k : Fin (count p)) →
    MPSTensor (D * D) (localDim p k)
  /-- Inclusion of a local corner into its copy-pair bond space. -/
  localInclusion : (p : VerticalCopyPair mult) → (k : Fin (count p)) →
    Matrix (Fin (dim p.1.1 * dim p.2.1)) (Fin (localDim p k)) ℂ
  /-- Every retained local corner has positive bond dimension. -/
  localDim_pos : ∀ p k, 0 < localDim p k
  /-- Every retained spectral coefficient is positive. -/
  coefficient_pos : ∀ p k, (0 : ℂ) < coefficient p k
  /-- Every retained local corner is a normal tensor. -/
  block_normal : ∀ p k, MPSTensor.IsNormalTensor (block p k)
  /-- Each local corner inclusion is an isometry. -/
  localInclusion_isometry : ∀ p k,
    (localInclusion p k)ᴴ * localInclusion p k = 1
  /-- Distinct local corners of one copy pair have orthogonal ranges. -/
  localInclusion_orthogonal : ∀ p k l, k ≠ l →
    (localInclusion p k)ᴴ * localInclusion p l = 0
  /-- Each local inclusion intertwines its weighted normal corner with the
  copy-pair tensor. -/
  local_intertwine : ∀ p k ab,
    weightedVerticalProductBlock dim mult weight B p ab * localInclusion p k =
      localInclusion p k * (coefficient p k • block p k ab)
  /-- The adjoint local inclusion satisfies the reverse intertwining
  identity. -/
  local_intertwine_adjoint : ∀ p k ab,
    (localInclusion p k)ᴴ * weightedVerticalProductBlock dim mult weight B p ab =
      (coefficient p k • block p k ab) * (localInclusion p k)ᴴ
  /-- Compression to a local corner gives its weighted normal tensor. -/
  local_compression : ∀ p k ab,
    coefficient p k • block p k ab =
      (localInclusion p k)ᴴ *
        weightedVerticalProductBlock dim mult weight B p ab *
          localInclusion p k
  /-- The local corners reconstruct every letter of their copy-pair tensor. -/
  local_reconstruction : ∀ p ab,
    weightedVerticalProductBlock dim mult weight B p ab =
      ∑ k, localInclusion p k * (coefficient p k • block p k ab) *
        (localInclusion p k)ᴴ
  /-- The local decomposition preserves every positive-length closed chain. -/
  local_sameMPV₂Pos : ∀ p, MPSTensor.SameMPV₂Pos
    (weightedVerticalProductBlock dim mult weight B p)
      (MPSTensor.toTensorFromBlocks (d := D * D)
      (μ := coefficient p) (block p))
  /-- The total local bond dimension does not exceed the copy-pair bond
  dimension. -/
  local_dimension_bound : ∀ p,
    (∑ k, localDim p k) ≤ dim p.1.1 * dim p.2.1

/-- The local spectral decompositions may be chosen simultaneously for every
retained copy pair when the blocked vertical tensor has projector closure and
no periodic vectors. Empty active families are preserved.

Source: CPSV16, Proposition 4.13, lines 1873--1893, and Appendix C.4,
lines 2020--2029. -/
theorem exists_retainedProductSpectralFamily_of_blockTwo
    {g d D : ℕ} (dim mult : Fin g → ℕ)
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (B : (α : Fin g) → MPSTensor (D * D) (dim α))
    (M : MPOTensor d D)
    (U : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ)
    (hU : U * Uᴴ = 1)
    (hReconstruct : ∀ ab, verticalTensor M ab =
      Uᴴ * verticalAssembledTensor dim mult weight B ab * U)
    (hClosure : MPSTensor.HasInvariantProjectorClosure (verticalTensor (blockTwo M)))
    (hPer : MPSTensor.HasNoPeriodicVectors (verticalTensor (blockTwo M))) :
    Nonempty (RetainedProductSpectralFamily dim mult weight B) := by
  classical
  have hExists := fun p ↦
    exists_weightedVerticalProductBlock_normalDecomposition_of_blockTwo
      dim mult weight B M U hU hReconstruct hClosure hPer p
  choose count localDim coefficient block localInclusion
    localDim_pos coefficient_pos block_normal localInclusion_isometry
    localInclusion_orthogonal local_intertwine local_intertwine_adjoint
    local_compression local_reconstruction local_sameMPV₂Pos
    local_dimension_bound using hExists
  exact ⟨{
    count := count
    localDim := localDim
    coefficient := coefficient
    block := block
    localInclusion := localInclusion
    localDim_pos := localDim_pos
    coefficient_pos := coefficient_pos
    block_normal := block_normal
    localInclusion_isometry := localInclusion_isometry
    localInclusion_orthogonal := localInclusion_orthogonal
    local_intertwine := local_intertwine
    local_intertwine_adjoint := local_intertwine_adjoint
    local_compression := local_compression
    local_reconstruction := local_reconstruction
    local_sameMPV₂Pos := local_sameMPV₂Pos
    local_dimension_bound := local_dimension_bound }⟩

/-- The local spectral decompositions may be chosen simultaneously for every
retained copy pair of a tensor in normalized BNT-refined horizontal form.
Empty active families are preserved.

**Scope restriction (BNT-refined horizontal form):** `IsHorizontalCF` is
stronger than the literal CPSV canonical form used in Appendix C.4 through
Proposition 4.13; see `docs/paper-gaps/cpgsv17_vertical_cf_grouping.tex`.

Source: CPSV16, Proposition 4.13, lines 1873--1893, and Appendix C.4,
lines 2020--2029. -/
theorem exists_retainedProductSpectralFamily
    {g d D : ℕ} (dim mult : Fin g → ℕ)
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (B : (α : Fin g) → MPSTensor (D * D) (dim α))
    (M : MPOTensor d D)
    (U : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ)
    (hU : U * Uᴴ = 1)
    (hReconstruct : ∀ ab, verticalTensor M ab =
      Uᴴ * verticalAssembledTensor dim mult weight B ab * U)
    (hHorizontal : IsHorizontalCF M) (hM : IsMPDO M) :
    Nonempty (RetainedProductSpectralFamily dim mult weight B) := by
  have hHorizontalTwo := hHorizontal.blockTwo
  have hMTwo := hM.blockTwo
  exact exists_retainedProductSpectralFamily_of_blockTwo
    dim mult weight B M U hU hReconstruct
    (hHorizontalTwo.hasInvariantProjectorClosure_verticalTensor (blockTwo M) hMTwo)
    (hasNoPeriodicVectors_verticalTensor_of_horizontalCF
      (blockTwo M) hMTwo hHorizontalTwo)

namespace RetainedProductSpectralFamily

variable {g D : ℕ} {dim mult : Fin g → ℕ}
  {weight : (α : Fin g) → Fin (mult α) → ℂ}
  {B : (α : Fin g) → MPSTensor (D * D) (dim α)}

/-- The dependent type of all active local corners over all retained copy
pairs. -/
abbrev ActiveLabel (S : RetainedProductSpectralFamily dim mult weight B) :=
  (p : VerticalCopyPair mult) × Fin (S.count p)

/-- Enumeration of all active local corners by one finite type. -/
noncomputable def activeLabelEquiv
    (S : RetainedProductSpectralFamily dim mult weight B) :
    Fin (Fintype.card S.ActiveLabel) ≃ S.ActiveLabel :=
  (Fintype.equivFin S.ActiveLabel).symm

/-- The inclusion of an active local corner into the complete retained
product bond space. -/
noncomputable def retainedInclusion
    (S : RetainedProductSpectralFamily dim mult weight B)
    (x : S.ActiveLabel) :
    Matrix
      (Fin ((∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q) *
        (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q)))
      (Fin (S.localDim x.1 x.2)) ℂ :=
  retainedProductBlockInclusion dim mult x.1 * S.localInclusion x.1 x.2

/-- The inclusion of an active local corner into the bond space of the
blocked vertical tensor. -/
noncomputable def ambientInclusion {d : ℕ}
    (S : RetainedProductSpectralFamily dim mult weight B)
    (U : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ)
    (x : S.ActiveLabel) :
    Matrix (Fin (d * d)) (Fin (S.localDim x.1 x.2)) ℂ :=
  (verticalCoisometrySquare U)ᴴ * S.retainedInclusion x

/-- Every flattened retained inclusion is an isometry. -/
theorem retainedInclusion_isometry
    (S : RetainedProductSpectralFamily dim mult weight B)
    (x : S.ActiveLabel) :
    (S.retainedInclusion x)ᴴ * S.retainedInclusion x = 1 := by
  rw [retainedInclusion, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (retainedProductBlockInclusion dim mult x.1)ᴴ,
    retainedProductBlockInclusion_isometry, Matrix.one_mul,
    S.localInclusion_isometry]

/-- Distinct active corners have orthogonal ranges in the retained product
bond space. -/
theorem retainedInclusion_orthogonal_of_ne
    (S : RetainedProductSpectralFamily dim mult weight B)
    (p q : VerticalCopyPair mult) (k : Fin (S.count p))
    (l : Fin (S.count q))
    (h : (⟨p, k⟩ : S.ActiveLabel) ≠ ⟨q, l⟩) :
    (S.retainedInclusion ⟨p, k⟩)ᴴ * S.retainedInclusion ⟨q, l⟩ = 0 := by
  by_cases hpq : p = q
  · subst q
    have hkl : k ≠ l := by
      intro hEq
      subst l
      exact h rfl
    rw [retainedInclusion, retainedInclusion, Matrix.conjTranspose_mul,
      Matrix.mul_assoc,
      ← Matrix.mul_assoc (retainedProductBlockInclusion dim mult p)ᴴ,
      retainedProductBlockInclusion_isometry, Matrix.one_mul,
      S.localInclusion_orthogonal p k l hkl]
  · rw [retainedInclusion, retainedInclusion, Matrix.conjTranspose_mul,
      Matrix.mul_assoc,
      ← Matrix.mul_assoc (retainedProductBlockInclusion dim mult p)ᴴ,
      retainedProductBlockInclusion_orthogonal_of_ne dim mult hpq,
      Matrix.zero_mul, Matrix.mul_zero]

/-- Every flattened retained inclusion intertwines its active normal corner
with the full retained product tensor. -/
theorem retained_intertwine
    (S : RetainedProductSpectralFamily dim mult weight B)
    (x : S.ActiveLabel) (ab : Fin (D * D)) :
    retainedVerticalProductTensor dim mult weight B ab * S.retainedInclusion x =
      S.retainedInclusion x * (S.coefficient x.1 x.2 • S.block x.1 x.2 ab) := by
  rw [retainedInclusion, ← Matrix.mul_assoc,
    retainedVerticalProductTensor_mul_retainedProductBlockInclusion,
    Matrix.mul_assoc, S.local_intertwine]
  exact (Matrix.mul_assoc _ _ _).symm

/-- The adjoint flattened retained inclusion satisfies the reverse
intertwining identity. -/
theorem retained_intertwine_adjoint
    (S : RetainedProductSpectralFamily dim mult weight B)
    (x : S.ActiveLabel) (ab : Fin (D * D)) :
    (S.retainedInclusion x)ᴴ * retainedVerticalProductTensor dim mult weight B ab =
      (S.coefficient x.1 x.2 • S.block x.1 x.2 ab) *
        (S.retainedInclusion x)ᴴ := by
  rw [retainedInclusion, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    retainedProductBlockInclusion_conjTranspose_mul_retainedVerticalProductTensor,
    ← Matrix.mul_assoc, S.local_intertwine_adjoint]
  exact Matrix.mul_assoc _ _ _

/-- Compressing the retained product tensor by a flattened inclusion recovers
its weighted normal corner. -/
theorem retained_compression
    (S : RetainedProductSpectralFamily dim mult weight B)
    (x : S.ActiveLabel) (ab : Fin (D * D)) :
    S.coefficient x.1 x.2 • S.block x.1 x.2 ab =
      (S.retainedInclusion x)ᴴ *
        retainedVerticalProductTensor dim mult weight B ab *
          S.retainedInclusion x := by
  rw [S.retained_intertwine_adjoint,
    Matrix.mul_assoc, S.retainedInclusion_isometry, Matrix.mul_one]

/-- Exact reconstruction of the retained product tensor by all active local
corners, before enumerating their dependent label type. -/
theorem retained_reconstruction_active
    (S : RetainedProductSpectralFamily dim mult weight B)
    (ab : Fin (D * D)) :
    retainedVerticalProductTensor dim mult weight B ab =
      ∑ x : S.ActiveLabel,
        S.retainedInclusion x *
          (S.coefficient x.1 x.2 • S.block x.1 x.2 ab) *
            (S.retainedInclusion x)ᴴ := by
  calc
    retainedVerticalProductTensor dim mult weight B ab =
        ∑ p : VerticalCopyPair mult,
          retainedProductBlockInclusion dim mult p *
            weightedVerticalProductBlock dim mult weight B p ab *
              (retainedProductBlockInclusion dim mult p)ᴴ :=
      retainedVerticalProductTensor_eq_sum_pairBlocks dim mult weight B ab
    _ = ∑ p : VerticalCopyPair mult,
        retainedProductBlockInclusion dim mult p *
          (∑ k, S.localInclusion p k *
            (S.coefficient p k • S.block p k ab) *
              (S.localInclusion p k)ᴴ) *
            (retainedProductBlockInclusion dim mult p)ᴴ := by
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      rw [← S.local_reconstruction p ab]
    _ = ∑ p : VerticalCopyPair mult, ∑ k,
        S.retainedInclusion ⟨p, k⟩ *
          (S.coefficient p k • S.block p k ab) *
            (S.retainedInclusion ⟨p, k⟩)ᴴ := by
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      rw [Matrix.mul_sum, Matrix.sum_mul]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      simp only [retainedInclusion, Matrix.conjTranspose_mul,
        Matrix.mul_assoc]
    _ = _ := by
      simpa only [ActiveLabel] using
        (Fintype.sum_sigma (fun x : S.ActiveLabel ↦
          S.retainedInclusion x *
            (S.coefficient x.1 x.2 • S.block x.1 x.2 ab) *
              (S.retainedInclusion x)ᴴ)).symm

/-- Bond dimension of an active corner after enumerating all dependent active
labels by one finite type. -/
noncomputable def flatDim
    (S : RetainedProductSpectralFamily dim mult weight B)
    (j : Fin (Fintype.card S.ActiveLabel)) : ℕ :=
  S.localDim (S.activeLabelEquiv j).1 (S.activeLabelEquiv j).2

/-- Positive coefficient of an enumerated active corner. -/
noncomputable def flatCoefficient
    (S : RetainedProductSpectralFamily dim mult weight B)
    (j : Fin (Fintype.card S.ActiveLabel)) : ℂ :=
  S.coefficient (S.activeLabelEquiv j).1 (S.activeLabelEquiv j).2

/-- Normal tensor of an enumerated active corner. -/
noncomputable def flatBlock
    (S : RetainedProductSpectralFamily dim mult weight B)
    (j : Fin (Fintype.card S.ActiveLabel)) :
    MPSTensor (D * D) (S.flatDim j) :=
  S.block (S.activeLabelEquiv j).1 (S.activeLabelEquiv j).2

/-- Retained inclusion of an enumerated active corner. -/
noncomputable def flatInclusion
    (S : RetainedProductSpectralFamily dim mult weight B)
    (j : Fin (Fintype.card S.ActiveLabel)) :
    Matrix
      (Fin ((∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q) *
        (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q)))
      (Fin (S.flatDim j)) ℂ :=
  S.retainedInclusion (S.activeLabelEquiv j)

/-- Every enumerated active corner has positive bond dimension. -/
theorem flatDim_pos
    (S : RetainedProductSpectralFamily dim mult weight B)
    (j : Fin (Fintype.card S.ActiveLabel)) : 0 < S.flatDim j :=
  S.localDim_pos (S.activeLabelEquiv j).1 (S.activeLabelEquiv j).2

/-- Every enumerated active coefficient is positive. -/
theorem flatCoefficient_pos
    (S : RetainedProductSpectralFamily dim mult weight B)
    (j : Fin (Fintype.card S.ActiveLabel)) : (0 : ℂ) < S.flatCoefficient j :=
  S.coefficient_pos (S.activeLabelEquiv j).1 (S.activeLabelEquiv j).2

/-- Every enumerated active coefficient is nonzero. -/
theorem flatCoefficient_ne
    (S : RetainedProductSpectralFamily dim mult weight B)
    (j : Fin (Fintype.card S.ActiveLabel)) : S.flatCoefficient j ≠ 0 :=
  (S.flatCoefficient_pos j).ne'

/-- Every enumerated active block is a normal tensor. -/
theorem flatBlock_normal
    (S : RetainedProductSpectralFamily dim mult weight B)
    (j : Fin (Fintype.card S.ActiveLabel)) :
    MPSTensor.IsNormalTensor (S.flatBlock j) :=
  S.block_normal (S.activeLabelEquiv j).1 (S.activeLabelEquiv j).2

/-- Enumerated active-corner inclusions are isometries. -/
theorem flatInclusion_isometry
    (S : RetainedProductSpectralFamily dim mult weight B)
    (j : Fin (Fintype.card S.ActiveLabel)) :
    (S.flatInclusion j)ᴴ * S.flatInclusion j = 1 := by
  exact S.retainedInclusion_isometry (S.activeLabelEquiv j)

/-- Distinct enumerated active-corner inclusions have orthogonal ranges. -/
theorem flatInclusion_orthogonal_of_ne
    (S : RetainedProductSpectralFamily dim mult weight B)
    (j l : Fin (Fintype.card S.ActiveLabel)) (hjl : j ≠ l) :
    (S.flatInclusion j)ᴴ * S.flatInclusion l = 0 := by
  apply S.retainedInclusion_orthogonal_of_ne
  intro hEq
  exact hjl (S.activeLabelEquiv.injective hEq)

/-- Enumerated active-corner inclusions satisfy the forward intertwining
identity. -/
theorem flat_intertwine
    (S : RetainedProductSpectralFamily dim mult weight B)
    (j : Fin (Fintype.card S.ActiveLabel)) (ab : Fin (D * D)) :
    retainedVerticalProductTensor dim mult weight B ab * S.flatInclusion j =
      S.flatInclusion j * (S.flatCoefficient j • S.flatBlock j ab) :=
  S.retained_intertwine (S.activeLabelEquiv j) ab

/-- Enumerated active-corner inclusions satisfy the adjoint intertwining
identity. -/
theorem flat_intertwine_adjoint
    (S : RetainedProductSpectralFamily dim mult weight B)
    (j : Fin (Fintype.card S.ActiveLabel)) (ab : Fin (D * D)) :
    (S.flatInclusion j)ᴴ * retainedVerticalProductTensor dim mult weight B ab =
      (S.flatCoefficient j • S.flatBlock j ab) * (S.flatInclusion j)ᴴ := by
  exact S.retained_intertwine_adjoint (S.activeLabelEquiv j) ab

/-- Compression by an enumerated inclusion gives its weighted active
corner. -/
theorem flat_compression
    (S : RetainedProductSpectralFamily dim mult weight B)
    (j : Fin (Fintype.card S.ActiveLabel)) (ab : Fin (D * D)) :
    S.flatCoefficient j • S.flatBlock j ab =
      (S.flatInclusion j)ᴴ *
        retainedVerticalProductTensor dim mult weight B ab *
          S.flatInclusion j :=
  S.retained_compression (S.activeLabelEquiv j) ab

/-- Literal reconstruction of the retained product tensor by the enumerated
active corners. -/
theorem flat_reconstruction
    (S : RetainedProductSpectralFamily dim mult weight B)
    (ab : Fin (D * D)) :
    retainedVerticalProductTensor dim mult weight B ab =
      ∑ j, S.flatInclusion j * (S.flatCoefficient j • S.flatBlock j ab) *
        (S.flatInclusion j)ᴴ := by
  rw [S.retained_reconstruction_active ab]
  exact (S.activeLabelEquiv.sum_comp (fun x : S.ActiveLabel ↦
    S.retainedInclusion x *
      (S.coefficient x.1 x.2 • S.block x.1 x.2 ab) *
        (S.retainedInclusion x)ᴴ)).symm

/-- The retained product tensor and the single finite direct sum of all its
active normal corners have the same positive-length closed chains. -/
theorem flat_sameMPV₂Pos
    (S : RetainedProductSpectralFamily dim mult weight B) :
    MPSTensor.SameMPV₂Pos (retainedVerticalProductTensor dim mult weight B)
      (MPSTensor.toTensorFromBlocks (d := D * D)
        (μ := S.flatCoefficient) S.flatBlock) :=
  MPSTensor.sameMPV₂Pos_toTensorFromBlocks_of_reconstruction
    (retainedVerticalProductTensor dim mult weight B)
    S.flatCoefficient S.flatBlock S.flatInclusion
    S.flatInclusion_isometry S.flat_intertwine_adjoint S.flat_reconstruction

/-- Every active normal corner of the retained product is gauge-phase
equivalent to some normal tensor in a BNT for the blocked vertical tensor.

This is only the coverage direction: a blocked BNT label need not occur in
the product of a prescribed pair, or even among the active product corners.
The conclusion therefore chooses a blocked label for each active corner and
makes no converse assertion.

**Scope restriction (active product BNT):** Proposition 2.7 classifies the
nonzero canonical-form coefficients.  Hence this theorem covers active
product corners only and does not assert surjectivity onto the blocked BNT.
Documented in
`docs/paper-gaps/cpsv16_bnt_uniqueness_zero_coefficient.tex`.

**Local fix (Figure-11 fixed-pair support):** A fixed product pair may have no
corner of a given blocked label; such a label has an empty multiplicity fiber.
Documented in `docs/paper-gaps/cpsv16_figure11_per_pair_support.tex`.

Source: CPSV16, Appendix C.4, lines 2025--2029, using Proposition 2.7
(`prop:char-BNT`). -/
theorem exists_blockedBNT_gaugePhase_of_flatBlock
    {d g₂ : ℕ}
    (S : RetainedProductSpectralFamily dim mult weight B)
    (M : MPOTensor d D)
    (U : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ)
    (hU : U * Uᴴ = 1)
    (hReconstruct : ∀ ab, verticalTensor M ab =
      Uᴴ * verticalAssembledTensor dim mult weight B ab * U)
    (dim₂ : Fin g₂ → ℕ)
    (A₂ : (γ : Fin g₂) → MPSTensor (D * D) (dim₂ γ))
    [∀ γ, NeZero (dim₂ γ)]
    (hBNT₂ : MPSTensor.IsCPSVBasisOfNormalTensors
      (verticalTensor (blockTwo M)) (fun γ ↦ ⟨dim₂ γ, A₂ γ⟩)) :
    ∀ j : Fin (Fintype.card S.ActiveLabel),
      ∃ γ : Fin g₂, ∃ hdim : dim₂ γ = S.flatDim j,
      ∃ X : GL (Fin (S.flatDim j)) ℂ, ∃ ζ : ℂ, ‖ζ‖ = 1 ∧
        ∀ ab, S.flatBlock j ab = ζ •
          ((X : Matrix (Fin (S.flatDim j)) (Fin (S.flatDim j)) ℂ) *
            (cast (congr_arg (MPSTensor (D * D)) hdim) (A₂ γ)) ab *
              (↑(X⁻¹) : Matrix (Fin (S.flatDim j))
                (Fin (S.flatDim j)) ℂ)) := by
  letI : ∀ j, NeZero (S.flatDim j) := fun j ↦
    ⟨(S.flatDim_pos j).ne'⟩
  have hsquare := verticalTensor_blockTwo_squared_coisometry_reconstruction
    M (verticalAssembledTensor dim mult weight B) U hU hReconstruct
  have hSame : MPSTensor.SameMPV₂Pos (verticalTensor (blockTwo M))
      (retainedVerticalProductTensor dim mult weight B) :=
    MPSTensor.sameMPV₂Pos_of_coisometry_reconstruction
      (verticalTensor (blockTwo M))
      (retainedVerticalProductTensor dim mult weight B)
      (verticalCoisometrySquare U) hsquare.1 hsquare.2
  have hBNTProduct : MPSTensor.IsCPSVBasisOfNormalTensors
      (retainedVerticalProductTensor dim mult weight B)
      (fun γ ↦ ⟨dim₂ γ, A₂ γ⟩) :=
    hBNT₂.of_sameMPV₂Pos hSame
  have hCharacterization :=
    (MPSTensor.isCPSVBasisOfNormalTensors_iff_canonicalForm_covered_and_minimal
      (retainedVerticalProductTensor dim mult weight B)
      S.flatCoefficient S.flatBlock A₂ S.flatBlock_normal
      S.flat_sameMPV₂Pos).mp hBNTProduct
  intro j
  exact hCharacterization.2.1 j (S.flatCoefficient_ne j)

/-- A simultaneous choice of the blocked BNT label, dimension equality,
gauge, and phase for every enumerated active product corner.

The map `label` need not be surjective: unused blocked BNT labels are allowed.

**Scope restriction (active product BNT):** This structure records only the
one-way coverage of active product corners.  Empty fibers record unused
blocked labels.  Documented in
`docs/paper-gaps/cpsv16_bnt_uniqueness_zero_coefficient.tex`.

**Local fix (Figure-11 fixed-pair support):** No nonempty multiplicity space is
asserted for an unused blocked label.  Documented in
`docs/paper-gaps/cpsv16_figure11_per_pair_support.tex`.

Source: CPSV16, Appendix C.4, lines 2025--2029. -/
structure FlatBlockedBNTComparison {g₂ : ℕ}
    (S : RetainedProductSpectralFamily dim mult weight B)
    (dim₂ : Fin g₂ → ℕ)
    (A₂ : (γ : Fin g₂) → MPSTensor (D * D) (dim₂ γ)) where
  /-- Blocked BNT label covering an active product corner. -/
  label : Fin (Fintype.card S.ActiveLabel) → Fin g₂
  /-- Equality of the blocked and active corner bond dimensions. -/
  dim_eq : ∀ j, dim₂ (label j) = S.flatDim j
  /-- Invertible gauge from the chosen blocked tensor to the active corner. -/
  gauge : ∀ j, GL (Fin (S.flatDim j)) ℂ
  /-- Unit-modulus proportionality phase. -/
  phase : Fin (Fintype.card S.ActiveLabel) → ℂ
  /-- Every chosen phase has modulus one. -/
  phase_norm : ∀ j, ‖phase j‖ = 1
  /-- Exact gauge-phase relation for every tensor letter. -/
  block_eq : ∀ j ab, S.flatBlock j ab = phase j •
    ((gauge j : Matrix (Fin (S.flatDim j)) (Fin (S.flatDim j)) ℂ) *
      (cast (congr_arg (MPSTensor (D * D)) (dim_eq j))
        (A₂ (label j))) ab *
      (↑((gauge j)⁻¹) : Matrix (Fin (S.flatDim j))
        (Fin (S.flatDim j)) ℂ))

/-- The active normal corners of every retained copy pair, transported back
to the original one-site BNT labels and normalized by isometries.

**Local fix (Figure-11 fixed-pair support):** A copy pair with no active
corner is represented by an empty family; no unsupported corner is inserted.
Documented in
`docs/paper-gaps/cpsv16_figure11_per_pair_support.tex`.

Source: CPSV16, Appendix C.4, lines 2020--2029. -/
structure OriginalCornerFamily
    (S : RetainedProductSpectralFamily dim mult weight B) where
  /-- Original BNT label carried by each active copy-pair corner.

  Source: CPSV16, Appendix C.4, lines 2025--2029. -/
  label : ∀ p : VerticalCopyPair mult, Fin (S.count p) → Fin g
  /-- Positive coefficient of the transported original BNT tensor.

  Source: CPSV16, Appendix C.4, lines 2025--2029. -/
  coefficient : ∀ p : VerticalCopyPair mult, Fin (S.count p) → ℂ
  /-- Every transported coefficient is positive.

  Source: CPSV16, Appendix C.4, lines 2025--2029. -/
  coefficient_pos : ∀ p k, (0 : ℂ) < coefficient p k
  /-- Isometric inclusion of an original-label corner into its raw copy-pair
  bond space.

  Source: CPSV16, Appendix C.4, lines 2025--2029. -/
  inclusion : ∀ (p : VerticalCopyPair mult) (k : Fin (S.count p)),
    Matrix (Fin (dim p.1.1 * dim p.2.1)) (Fin (dim (label p k))) ℂ
  /-- Every original-label corner inclusion is an isometry.

  Source: CPSV16, Appendix C.4, lines 2025--2029. -/
  inclusion_isometry : ∀ p k, (inclusion p k)ᴴ * inclusion p k = 1
  /-- Distinct active corners of a fixed copy pair have orthogonal ranges.

  Source: CPSV16, Appendix C.4, lines 2025--2029. -/
  inclusion_orthogonal : ∀ p k l, k ≠ l →
    (inclusion p k)ᴴ * inclusion p l = 0
  /-- Each inclusion intertwines the raw product tensor with its positive
  multiple of the original BNT tensor.

  Source: CPSV16, Appendix C.4, lines 2025--2029. -/
  intertwine : ∀ p k ab,
    (mulTensor (verticalBNTMPO (B p.1.1))
        (verticalBNTMPO (B p.2.1))).toMPSTensor ab * inclusion p k =
      inclusion p k * (coefficient p k • B (label p k) ab)
  /-- The original-label corners reconstruct every letter of the raw product
  tensor.

  Source: CPSV16, Appendix C.4, lines 2025--2029. -/
  reconstruction : ∀ p ab,
    (mulTensor (verticalBNTMPO (B p.1.1))
        (verticalBNTMPO (B p.2.1))).toMPSTensor ab =
      ∑ k, inclusion p k * (coefficient p k • B (label p k) ab) *
        (inclusion p k)ᴴ

end RetainedProductSpectralFamily

end MPOTensor
