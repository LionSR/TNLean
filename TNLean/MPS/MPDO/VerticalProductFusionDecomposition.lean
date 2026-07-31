/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.VerticalProductCornerPositivity

/-!
# Positive fusion decompositions of vertical product tensors

This file assembles positive original-label corners into the fixed-pair
fusion coisometries of CPSV16, Appendix C.4.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.4, lines 2020--2029
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

noncomputable section

namespace MPOTensor

namespace RetainedProductSpectralFamily

variable {g D : ℕ} {dim mult : Fin g → ℕ}
  {weight : (α : Fin g) → Fin (mult α) → ℂ}
  {B : (α : Fin g) → MPSTensor (D * D) (dim α)}

namespace OriginalCornerFamily

variable {S : RetainedProductSpectralFamily dim mult weight B}
variable (O : OriginalCornerFamily S)

private abbrev distinguishedPair
    (hMult : ∀ α, 0 < mult α) (α β : Fin g) : VerticalCopyPair mult :=
  (⟨α, ⟨0, hMult α⟩⟩, ⟨β, ⟨0, hMult β⟩⟩)

private noncomputable def chi
    (hMult : ∀ α, 0 < mult α) : DiagonalChiFamily (Fin g) where
  dim α β γ := Fintype.card
    {k : Fin (S.count (distinguishedPair hMult α β)) //
      O.label (distinguishedPair hMult α β) k = γ}
  entry α β γ t := O.coefficient (distinguishedPair hMult α β)
    ((Fintype.equivFin
      {k : Fin (S.count (distinguishedPair hMult α β)) //
        O.label (distinguishedPair hMult α β) k = γ}).symm t).1

private noncomputable def groupedFusionCoisometry
    (hMult : ∀ α, 0 < mult α) (α β : Fin g) :
    Matrix ((γ : Fin g) ×
        (Fin ((chi O hMult).dim α β γ) × Fin (dim γ)))
      (Fin (dim α * dim β)) ℂ :=
  let p := distinguishedPair hMult α β
  Matrix.reindex
    (Matrix.sigmaFiberBlockEquiv (O.label p) dim) (Equiv.refl _)
    (Matrix.sigmaBlockRow (O.inclusion p))

private theorem groupedFusionCoisometry_coisometry
    (hMult : ∀ α, 0 < mult α) (α β : Fin g) :
    groupedFusionCoisometry O hMult α β *
        (groupedFusionCoisometry O hMult α β)ᴴ = 1 := by
  let p := distinguishedPair hMult α β
  let W := O.inclusion p
  let rowEquiv := Matrix.sigmaFiberBlockEquiv (O.label p) dim
  change Matrix.reindex rowEquiv (Equiv.refl _) (Matrix.sigmaBlockRow W) *
      (Matrix.reindex rowEquiv (Equiv.refl _) (Matrix.sigmaBlockRow W))ᴴ = 1
  rw [Matrix.conjTranspose_reindex,
    show Matrix.reindex rowEquiv (Equiv.refl _)
        (Matrix.sigmaBlockRow W) =
      Matrix.reindexLinearEquiv ℂ ℂ rowEquiv (Equiv.refl _)
        (Matrix.sigmaBlockRow W) by rfl,
    show Matrix.reindex (Equiv.refl _) rowEquiv
        (Matrix.sigmaBlockRow W)ᴴ =
      Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) rowEquiv
        (Matrix.sigmaBlockRow W)ᴴ by rfl,
    Matrix.reindexLinearEquiv_mul ℂ ℂ rowEquiv (Equiv.refl _) rowEquiv,
    Matrix.sigmaBlockRow_isCoisometry W
      (O.inclusion_isometry p) (O.inclusion_orthogonal p),
    Matrix.reindexLinearEquiv_one]

private theorem groupedFusionCoisometry_fusion
    (hMult : ∀ α, 0 < mult α) (α β : Fin g) (ab : Fin (D * D)) :
    groupedFusionCoisometry O hMult α β *
        (mulTensor (verticalBNTMPO (B α))
          (verticalBNTMPO (B β))).toMPSTensor ab *
        (groupedFusionCoisometry O hMult α β)ᴴ =
      Matrix.blockDiagonal' fun γ =>
        (chi O hMult).matrix α β γ ⊗ₖ B γ ab := by
  let T := (mulTensor (verticalBNTMPO (B α))
    (verticalBNTMPO (B β))).toMPSTensor
  have hsigma := Matrix.sigmaBlockRow_conjugation T
    (fun k v ↦ O.coefficient (distinguishedPair hMult α β) k •
      B (O.label (distinguishedPair hMult α β) k) v)
    (O.inclusion (distinguishedPair hMult α β))
    (O.inclusion_isometry (distinguishedPair hMult α β))
    (O.inclusion_orthogonal (distinguishedPair hMult α β))
    (O.intertwine (distinguishedPair hMult α β)) ab
  have hgroup := Matrix.reindex_blockDiagonal'_sigmaFiberBlockEquiv
    (O.label (distinguishedPair hMult α β)) dim
    (O.coefficient (distinguishedPair hMult α β)) (fun γ ↦ B γ ab)
  dsimp only [groupedFusionCoisometry]
  change Matrix.reindex
        (Matrix.sigmaFiberBlockEquiv
          (O.label (distinguishedPair hMult α β)) dim)
        (Equiv.refl _)
        (Matrix.sigmaBlockRow (O.inclusion (distinguishedPair hMult α β))) *
      T ab *
      (Matrix.reindex
        (Matrix.sigmaFiberBlockEquiv
          (O.label (distinguishedPair hMult α β)) dim)
        (Equiv.refl _)
        (Matrix.sigmaBlockRow (O.inclusion (distinguishedPair hMult α β))))ᴴ = _
  rw [Matrix.conjTranspose_reindex]
  change Matrix.reindexLinearEquiv ℂ ℂ
        (Matrix.sigmaFiberBlockEquiv
          (O.label (distinguishedPair hMult α β)) dim) (Equiv.refl _)
        (Matrix.sigmaBlockRow (O.inclusion (distinguishedPair hMult α β))) *
      Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) (Equiv.refl _) (T ab) *
      Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _)
        (Matrix.sigmaFiberBlockEquiv
          (O.label (distinguishedPair hMult α β)) dim)
        (Matrix.sigmaBlockRow (O.inclusion (distinguishedPair hMult α β)))ᴴ = _
  rw [Matrix.reindexLinearEquiv_mul ℂ ℂ
      (Matrix.sigmaFiberBlockEquiv
        (O.label (distinguishedPair hMult α β)) dim)
      (Equiv.refl _) (Equiv.refl _),
    Matrix.reindexLinearEquiv_mul ℂ ℂ
      (Matrix.sigmaFiberBlockEquiv
        (O.label (distinguishedPair hMult α β)) dim)
      (Equiv.refl _)
      (Matrix.sigmaFiberBlockEquiv
        (O.label (distinguishedPair hMult α β)) dim),
    hsigma]
  change Matrix.reindex
      (Matrix.sigmaFiberBlockEquiv
        (O.label (distinguishedPair hMult α β)) dim)
      (Matrix.sigmaFiberBlockEquiv
        (O.label (distinguishedPair hMult α β)) dim)
      (Matrix.blockDiagonal' fun k =>
        O.coefficient (distinguishedPair hMult α β) k •
          B (O.label (distinguishedPair hMult α β) k) ab) = _
  dsimp only [chi, DiagonalChiFamily.matrix]
  exact hgroup

private theorem groupedFusionCoisometry_reconstruction
    (hMult : ∀ α, 0 < mult α) (α β : Fin g) (ab : Fin (D * D)) :
    (mulTensor (verticalBNTMPO (B α))
        (verticalBNTMPO (B β))).toMPSTensor ab =
      (groupedFusionCoisometry O hMult α β)ᴴ *
        (Matrix.blockDiagonal' fun γ =>
          (chi O hMult).matrix α β γ ⊗ₖ B γ ab) *
        groupedFusionCoisometry O hMult α β := by
  let T := (mulTensor (verticalBNTMPO (B α))
    (verticalBNTMPO (B β))).toMPSTensor
  have hsigma := Matrix.sigmaBlockRow_reconstruction T
    (fun k v ↦ O.coefficient (distinguishedPair hMult α β) k •
      B (O.label (distinguishedPair hMult α β) k) v)
    (O.inclusion (distinguishedPair hMult α β))
    (O.reconstruction (distinguishedPair hMult α β)) ab
  have hgroup := Matrix.reindex_blockDiagonal'_sigmaFiberBlockEquiv
    (O.label (distinguishedPair hMult α β)) dim
    (O.coefficient (distinguishedPair hMult α β)) (fun γ ↦ B γ ab)
  dsimp only [groupedFusionCoisometry]
  dsimp only [chi, DiagonalChiFamily.matrix]
  change T ab =
    (Matrix.reindex
      (Matrix.sigmaFiberBlockEquiv
        (O.label (distinguishedPair hMult α β)) dim)
      (Equiv.refl _)
      (Matrix.sigmaBlockRow (O.inclusion (distinguishedPair hMult α β))))ᴴ *
      _ *
      Matrix.reindex
        (Matrix.sigmaFiberBlockEquiv
          (O.label (distinguishedPair hMult α β)) dim)
        (Equiv.refl _)
        (Matrix.sigmaBlockRow (O.inclusion (distinguishedPair hMult α β)))
  rw [hsigma]
  rw [← hgroup]
  rw [Matrix.conjTranspose_reindex]
  change (Matrix.sigmaBlockRow
        (O.inclusion (distinguishedPair hMult α β)))ᴴ *
      Matrix.blockDiagonal' (fun k =>
        O.coefficient (distinguishedPair hMult α β) k •
          B (O.label (distinguishedPair hMult α β) k) ab) *
      Matrix.sigmaBlockRow (O.inclusion (distinguishedPair hMult α β)) =
    Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _)
          (Matrix.sigmaFiberBlockEquiv
            (O.label (distinguishedPair hMult α β)) dim)
          (Matrix.sigmaBlockRow
            (O.inclusion (distinguishedPair hMult α β)))ᴴ *
      Matrix.reindexLinearEquiv ℂ ℂ
          (Matrix.sigmaFiberBlockEquiv
            (O.label (distinguishedPair hMult α β)) dim)
          (Matrix.sigmaFiberBlockEquiv
            (O.label (distinguishedPair hMult α β)) dim)
          (Matrix.blockDiagonal' (fun k =>
            O.coefficient (distinguishedPair hMult α β) k •
              B (O.label (distinguishedPair hMult α β) k) ab)) *
      Matrix.reindexLinearEquiv ℂ ℂ
          (Matrix.sigmaFiberBlockEquiv
            (O.label (distinguishedPair hMult α β)) dim) (Equiv.refl _)
          (Matrix.sigmaBlockRow (O.inclusion (distinguishedPair hMult α β)))
  rw [Matrix.reindexLinearEquiv_mul ℂ ℂ (Equiv.refl _)
      (Matrix.sigmaFiberBlockEquiv
        (O.label (distinguishedPair hMult α β)) dim)
      (Matrix.sigmaFiberBlockEquiv
        (O.label (distinguishedPair hMult α β)) dim),
    Matrix.reindexLinearEquiv_mul ℂ ℂ (Equiv.refl _)
      (Matrix.sigmaFiberBlockEquiv
        (O.label (distinguishedPair hMult α β)) dim) (Equiv.refl _)]
  rfl

/-- The positive original-label corners determine the fusion coisometries of
the BNT family.

**Scope restriction (active product BNT):** Only active product corners are
retained.  A BNT label absent from a fixed product pair has zero fusion
multiplicity.  Documented in
`docs/paper-gaps/cpsv16_bnt_uniqueness_zero_coefficient.tex`.

**Local fix (Figure-11 fixed-pair support):** The construction uses the
distinguished retained copy of each label and permits an empty active family
for its product pair.  Documented in
`docs/paper-gaps/cpsv16_figure11_per_pair_support.tex`.

**Local fix (Figure-11 fusion coisometry):** The row map is a coisometry onto
the active direct sum; its adjoint reconstructs the raw product, including a
possible common zero corner.  Documented in
`docs/paper-gaps/cpsv16_figure11_fusion_coisometry.tex`.

Source: CPSV16, Appendix C.4, lines 2020--2029. -/
noncomputable def toBNTFusionCoisometryFamily
    (hMult : ∀ α, 0 < mult α) : BNTFusionCoisometryFamily (Fin g) D where
  bondDim := dim
  tensor := fun γ ↦ verticalBNTMPO (B γ)
  chi := chi O hMult
  posEntries := by
    intro α β γ t
    exact O.coefficient_pos _ _
  fusionCoisometry := groupedFusionCoisometry O hMult
  coisometry := groupedFusionCoisometry_coisometry O hMult
  fusion := by
    intro α β i j
    simpa only [toMPSTensor, verticalBNTMPO_apply,
      MPSTensor.finProdFinEquiv_divNat, MPSTensor.finProdFinEquiv_modNat] using
      groupedFusionCoisometry_fusion O hMult α β (finProdFinEquiv (i, j))
  reconstruction := by
    intro α β i j
    simpa only [toMPSTensor, verticalBNTMPO_apply,
      MPSTensor.finProdFinEquiv_divNat, MPSTensor.finProdFinEquiv_modNat] using
      groupedFusionCoisometry_reconstruction O hMult α β
        (finProdFinEquiv (i, j))

end OriginalCornerFamily

/-- Positive normalized product corners determine a family of fusion
coisometries for the original one-site BNT labels.

Source: CPSV16, Appendix C.4, lines 2020--2029. -/
theorem exists_bntFusionCoisometryFamily
    {g₂ : ℕ} {dim₂ : Fin g₂ → ℕ}
    {A₂ : (γ : Fin g₂) → MPSTensor (D * D) (dim₂ γ)}
    (S : RetainedProductSpectralFamily dim mult weight B)
    (C : FlatBlockedBNTComparison S dim₂ A₂)
    (hMult : ∀ α, 0 < mult α)
    (hWeight : ∀ α q, (0 : ℂ) < weight α q)
    (mult₂ : Fin g₂ → ℕ) (hMult₂ : ∀ γ, 0 < mult₂ γ)
    (weight₂ : (γ : Fin g₂) → Fin (mult₂ γ) → ℂ)
    (hWeight₂ : ∀ γ q, (0 : ℂ) < weight₂ γ q)
    (sigma : Fin g ≃ Fin g₂) (hDim : ∀ i, dim i = dim₂ (sigma i))
    (V : ∀ i, Matrix.unitaryGroup (Fin (dim₂ (sigma i))) ℂ)
    (hLetter : ∀ (i : Fin g) (ab : Fin (D * D)),
      A₂ (sigma i) ab =
        (verticalMultiplicityTrace weight i /
          verticalMultiplicityTrace weight₂ (sigma i)) •
        ((V i : Matrix (Fin (dim₂ (sigma i)))
            (Fin (dim₂ (sigma i))) ℂ) *
          Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDim i)) (B i ab) *
          (V i : Matrix (Fin (dim₂ (sigma i)))
            (Fin (dim₂ (sigma i))) ℂ)ᴴ))
    (hActivePos : ∀ j, (0 : ℂ) < S.flatCoefficient j * C.phase j)
    (omega : Fin (Fintype.card S.ActiveLabel) → ℝ)
    (homega : ∀ j, 0 < omega j)
    (hGram : ∀ j,
      (C.gauge j : Matrix (Fin (S.flatDim j)) (Fin (S.flatDim j)) ℂ)ᴴ *
        C.gauge j = (omega j : ℂ) • 1) :
    ∃ (chi : DiagonalChiFamily (Fin g))
      (U : ∀ α β : Fin g,
        Matrix
          ((γ : Fin g) × (Fin (chi.dim α β γ) × Fin (dim γ)))
          (Fin (dim α * dim β)) ℂ),
      chi.PosEntries ∧
      (∀ α β, U α β * (U α β)ᴴ = 1) ∧
      (∀ (α β : Fin g) (i j : Fin D),
        U α β *
            (mulTensor (verticalBNTMPO (B α))
              (verticalBNTMPO (B β))) i j *
            (U α β)ᴴ =
          Matrix.blockDiagonal' fun γ =>
            chi.matrix α β γ ⊗ₖ verticalBNTMPO (B γ) i j) ∧
      ∀ (α β : Fin g) (i j : Fin D),
        (mulTensor (verticalBNTMPO (B α))
          (verticalBNTMPO (B β))) i j =
          (U α β)ᴴ *
            (Matrix.blockDiagonal' fun γ =>
              chi.matrix α β γ ⊗ₖ verticalBNTMPO (B γ) i j) *
            U α β := by
  obtain ⟨O⟩ := S.exists_originalCornerFamily C hMult hWeight
    mult₂ hMult₂ weight₂ hWeight₂ sigma hDim V hLetter
    hActivePos omega homega hGram
  let Fam := O.toBNTFusionCoisometryFamily hMult
  exact ⟨Fam.chi, Fam.fusionCoisometry, Fam.posEntries,
    Fam.coisometry, Fam.fusion, Fam.reconstruction⟩

end RetainedProductSpectralFamily

/-- A fixed one-site/two-site sector transport witness determines positive
diagonal fusion data and coisometries onto the active product sectors.

This is the Figure-11 construction with the sector bijection, dimension
identifications, and unitary conjugacies supplied explicitly, so downstream
coefficient comparisons can reuse the same transport witness.

Source: CPSV16, Appendix C.4, lines 2001--2029. -/
theorem exists_positiveFusionDecomposition_of_unitaryBlockEquiv
    {g₁ g₂ d D : ℕ}
    (dim₁ mult₁ : Fin g₁ → ℕ)
    (weight₁ : (α : Fin g₁) → Fin (mult₁ α) → ℂ)
    (dim₂ mult₂ : Fin g₂ → ℕ)
    (weight₂ : (β : Fin g₂) → Fin (mult₂ β) → ℂ)
    (hMult₁ : ∀ α, 0 < mult₁ α)
    (hWeight₁ : ∀ α q, (0 : ℂ) < weight₁ α q)
    (hMult₂ : ∀ β, 0 < mult₂ β)
    (hWeight₂ : ∀ β q, (0 : ℂ) < weight₂ β q)
    (M : MPOTensor d D)
    (A₁ : (α : Fin g₁) → MPSTensor (D * D) (dim₁ α))
    (A₂ : (β : Fin g₂) → MPSTensor (D * D) (dim₂ β))
    (hBNT₂ : MPSTensor.IsCPSVBasisOfNormalTensors (verticalTensor (blockTwo M))
      (fun β ↦ ⟨dim₂ β, A₂ β⟩))
    (U₁ : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g₁, mult₁ α), verticalCopyDim dim₁ mult₁ q))
      (Fin d) ℂ)
    (U₂ : Matrix
      (Fin (∑ q : Fin (∑ β : Fin g₂, mult₂ β), verticalCopyDim dim₂ mult₂ q))
      (Fin (d * d)) ℂ)
    (hU₁ : U₁ * U₁ᴴ = 1)
    (hU₂ : U₂ * U₂ᴴ = 1)
    (hReconstruct₁ : ∀ ab, verticalTensor M ab =
      U₁ᴴ * verticalAssembledTensor dim₁ mult₁ weight₁ A₁ ab * U₁)
    (hReconstruct₂ : ∀ ab, verticalTensor (blockTwo M) ab =
      U₂ᴴ * verticalAssembledTensor dim₂ mult₂ weight₂ A₂ ab * U₂)
    (sigma : Fin g₁ ≃ Fin g₂)
    (hDim : ∀ i, dim₁ i = dim₂ (sigma i))
    (V : ∀ i, Matrix.unitaryGroup (Fin (dim₂ (sigma i))) ℂ)
    (hLetter : ∀ (i : Fin g₁) (ab : Fin (D * D)),
      A₂ (sigma i) ab =
        (verticalMultiplicityTrace weight₁ i /
          verticalMultiplicityTrace weight₂ (sigma i)) •
        ((V i : Matrix (Fin (dim₂ (sigma i))) (Fin (dim₂ (sigma i))) ℂ) *
          Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDim i)) (A₁ i ab) *
          (V i : Matrix (Fin (dim₂ (sigma i))) (Fin (dim₂ (sigma i))) ℂ)ᴴ))
    (hHorizontal : IsHorizontalCF M) (hM : IsMPDO M) :
    ∃ (chi : DiagonalChiFamily (Fin g₁))
      (U : ∀ α β : Fin g₁,
        Matrix
          ((γ : Fin g₁) × (Fin (chi.dim α β γ) × Fin (dim₁ γ)))
          (Fin (dim₁ α * dim₁ β)) ℂ),
      chi.PosEntries ∧
      (∀ α β, U α β * (U α β)ᴴ = 1) ∧
      (∀ (α β : Fin g₁) (i j : Fin D),
        U α β *
            (mulTensor (verticalBNTMPO (A₁ α))
              (verticalBNTMPO (A₁ β))) i j *
            (U α β)ᴴ =
          Matrix.blockDiagonal' fun γ =>
            chi.matrix α β γ ⊗ₖ verticalBNTMPO (A₁ γ) i j) ∧
      ∀ (α β : Fin g₁) (i j : Fin D),
        (mulTensor (verticalBNTMPO (A₁ α))
          (verticalBNTMPO (A₁ β))) i j =
          (U α β)ᴴ *
            (Matrix.blockDiagonal' fun γ =>
              chi.matrix α β γ ⊗ₖ verticalBNTMPO (A₁ γ) i j) *
            U α β := by
  classical
  obtain ⟨R⟩ := exists_retainedProductSpectralFamily
    dim₁ mult₁ weight₁ A₁ M U₁ hU₁ hReconstruct₁ hHorizontal hM
  letI : ∀ γ, NeZero (dim₂ γ) := fun γ ↦
    ⟨(hBNT₂.blocks_dim_pos γ).ne'⟩
  obtain ⟨C⟩ := R.exists_flatBlockedBNTComparison
    M U₁ hU₁ hReconstruct₁ dim₂ A₂ hBNT₂
  have hNormal₂ : ∀ γ, MPSTensor.IsNormalTensor (A₂ γ) := fun γ ↦
    hBNT₂.blocks_normal γ
  have hActivePos : ∀ j, (0 : ℂ) < R.flatCoefficient j * C.phase j := fun j ↦
    C.activeCoefficient_mul_phase_pos M hHorizontal hM
      U₁ hU₁ hReconstruct₁ mult₂ hMult₂ weight₂ hWeight₂
      U₂ hU₂ hReconstruct₂ hNormal₂ j
  choose omega homega hGram _hQ using fun j ↦
    C.exists_unitaryNormalization M hHorizontal hM
      U₁ hU₁ hReconstruct₁ mult₂ hMult₂ weight₂ hWeight₂
      U₂ hU₂ hReconstruct₂ hNormal₂ j
  exact R.exists_bntFusionCoisometryFamily C hMult₁ hWeight₁
    mult₂ hMult₂ weight₂ hWeight₂ sigma hDim V hLetter
    hActivePos omega homega hGram

/-- The one-site vertical BNT is closed under pairwise products through
positive diagonal multiplicity matrices and coisometries onto the active
product sectors.  The adjoint coisometries reconstruct every product letter,
including when a common zero corner is discarded by the forward map.

**Scope restriction (BNT-refined horizontal form):** `IsHorizontalCF` is
stronger than the literal CPSV canonical form used in Appendix C.4 through
Proposition 4.13; see `docs/paper-gaps/cpgsv17_vertical_cf_grouping.tex`.

**Scope restriction (active product BNT):** Only active product corners are
retained.  A one-site BNT label absent from a fixed product pair has zero
fusion multiplicity.  Documented in
`docs/paper-gaps/cpsv16_bnt_uniqueness_zero_coefficient.tex`.

**Local fix (Figure-11 fixed-pair support):** A fixed pair may have an empty
active family; no unsupported corner is inserted.  Documented in
`docs/paper-gaps/cpsv16_figure11_per_pair_support.tex`.

**Local fix (Figure-11 fusion coisometry):** The fusion map has retained-row
orientation and is a coisometry onto the active direct sum.  Its adjoint gives
the exact reconstruction.  Documented in
`docs/paper-gaps/cpsv16_figure11_fusion_coisometry.tex`.

Source: CPSV16, Appendix C.4, lines 2020--2029. -/
theorem transportedVerticalSector_exists_positiveFusionDecomposition
    {g₁ g₂ d D : ℕ}
    (dim₁ mult₁ : Fin g₁ → ℕ)
    (weight₁ : (α : Fin g₁) → Fin (mult₁ α) → ℂ)
    (dim₂ mult₂ : Fin g₂ → ℕ)
    (weight₂ : (β : Fin g₂) → Fin (mult₂ β) → ℂ)
    (hMult₁ : ∀ α, 0 < mult₁ α)
    (hWeight₁ : ∀ α q, (0 : ℂ) < weight₁ α q)
    (hMult₂ : ∀ β, 0 < mult₂ β)
    (hWeight₂ : ∀ β q, (0 : ℂ) < weight₂ β q)
    (M : MPOTensor d D)
    (A₁ : (α : Fin g₁) → MPSTensor (D * D) (dim₁ α))
    (A₂ : (β : Fin g₂) → MPSTensor (D * D) (dim₂ β))
    (hBNT₁ : MPSTensor.IsCPSVBasisOfNormalTensors (verticalTensor M)
      (fun α ↦ ⟨dim₁ α, A₁ α⟩))
    (hBNT₂ : MPSTensor.IsCPSVBasisOfNormalTensors (verticalTensor (blockTwo M))
      (fun β ↦ ⟨dim₂ β, A₂ β⟩))
    (U₁ : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g₁, mult₁ α), verticalCopyDim dim₁ mult₁ q))
      (Fin d) ℂ)
    (U₂ : Matrix
      (Fin (∑ q : Fin (∑ β : Fin g₂, mult₂ β), verticalCopyDim dim₂ mult₂ q))
      (Fin (d * d)) ℂ)
    (hU₁ : U₁ * U₁ᴴ = 1)
    (hU₂ : U₂ * U₂ᴴ = 1)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (Smap : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ)
    (hTCPTP : IsKrausCPTP T)
    (hSCPTP : IsKrausCPTP Smap)
    (hForward₁ : ∀ ab, U₁ * verticalTensor M ab * U₁ᴴ =
      verticalAssembledTensor dim₁ mult₁ weight₁ A₁ ab)
    (hReconstruct₁ : ∀ ab, verticalTensor M ab =
      U₁ᴴ * verticalAssembledTensor dim₁ mult₁ weight₁ A₁ ab * U₁)
    (hForward₂ : ∀ ab, U₂ * verticalTensor (blockTwo M) ab * U₂ᴴ =
      verticalAssembledTensor dim₂ mult₂ weight₂ A₂ ab)
    (hReconstruct₂ : ∀ ab, verticalTensor (blockTwo M) ab =
      U₂ᴴ * verticalAssembledTensor dim₂ mult₂ weight₂ A₂ ab * U₂)
    (hTphys : ∀ X, T (physClose1 M X) = physClose2 M X)
    (hSphys : ∀ X, Smap (physClose2 M X) = physClose1 M X)
    (hHorizontal : IsHorizontalCF M) (hM : IsMPDO M) :
    ∃ (chi : DiagonalChiFamily (Fin g₁))
      (U : ∀ α β : Fin g₁,
        Matrix
          ((γ : Fin g₁) × (Fin (chi.dim α β γ) × Fin (dim₁ γ)))
          (Fin (dim₁ α * dim₁ β)) ℂ),
      chi.PosEntries ∧
      (∀ α β, U α β * (U α β)ᴴ = 1) ∧
      (∀ (α β : Fin g₁) (i j : Fin D),
        U α β *
            (mulTensor (verticalBNTMPO (A₁ α))
              (verticalBNTMPO (A₁ β))) i j *
            (U α β)ᴴ =
          Matrix.blockDiagonal' fun γ =>
            chi.matrix α β γ ⊗ₖ verticalBNTMPO (A₁ γ) i j) ∧
      ∀ (α β : Fin g₁) (i j : Fin D),
        (mulTensor (verticalBNTMPO (A₁ α))
          (verticalBNTMPO (A₁ β))) i j =
          (U α β)ᴴ *
            (Matrix.blockDiagonal' fun γ =>
              chi.matrix α β γ ⊗ₖ verticalBNTMPO (A₁ γ) i j) *
            U α β := by
  classical
  obtain ⟨sigma, hDim, V, _hContract, hLetter⟩ :=
    transportedVerticalSector_exists_unitaryBlockEquiv_coefficient_eq
      dim₁ mult₁ weight₁ dim₂ mult₂ weight₂
      hMult₁ hWeight₁ hMult₂ hWeight₂ M A₁ A₂ hBNT₁ hBNT₂
      U₁ U₂ hU₁ hU₂ T Smap hTCPTP hSCPTP
      hForward₁ hReconstruct₁ hForward₂ hReconstruct₂ hTphys hSphys
  exact exists_positiveFusionDecomposition_of_unitaryBlockEquiv
    dim₁ mult₁ weight₁ dim₂ mult₂ weight₂
    hMult₁ hWeight₁ hMult₂ hWeight₂ M A₁ A₂ hBNT₂
    U₁ U₂ hU₁ hU₂ hReconstruct₁ hReconstruct₂
    sigma hDim V hLetter hHorizontal hM

end MPOTensor
