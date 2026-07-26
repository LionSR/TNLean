/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.VerticalProductFusionDecomposition

/-!
# Positive vertical fusion from the renormalization fixed-point condition

This file derives the positive fusion decomposition of the one-site vertical
basis of normal tensors directly from the renormalization fixed-point maps,
horizontal canonical form, and matrix-product-density-operator positivity.

## Main results

* `CPSVVerticalDecomposition`: a vertical canonical decomposition retaining
  the source basis-of-normal-tensors predicate.
* `IsHorizontalCF.exists_cpsvVerticalDecomposition`: construction of this
  decomposition from horizontal canonical form and positivity.
* `exists_positiveFusionDecomposition_of_isRFPViaTS`: the source-facing
  positive fusion theorem of CPSV16, Appendix C.4, lines 2020--2029.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Proposition 4.13 and Appendix C.4, lines 1951--2029
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

noncomputable section

namespace MPOTensor

/-- A vertical canonical decomposition which retains the CPSV16
basis-of-normal-tensors predicate.

The ordinary predicate `IsVerticalCF` records the algebraic BNT predicate used
elsewhere in the project.  The comparison of the one-site and two-site
decompositions in CPSV16, Appendix C.4, additionally uses the literal CPSV16
basis predicate.  This structure retains that assertion together with the
positive diagonal weights and both coisometric decomposition identities.

Source: arXiv:1606.00608, Proposition 4.13, lines 1863--1921. -/
structure CPSVVerticalDecomposition (M : MPOTensor d D) where
  /-- Number of vertical BNT labels. -/
  labelCount : ℕ
  /-- Bond dimension of each vertical BNT representative. -/
  bondDim : Fin labelCount → ℕ
  /-- Multiplicity of each representative. -/
  multiplicity : Fin labelCount → ℕ
  /-- Positive entries of the diagonal multiplicity matrices. -/
  weight : (α : Fin labelCount) → Fin (multiplicity α) → ℂ
  /-- The vertical BNT representatives. -/
  tensor : (α : Fin labelCount) → MPSTensor (D * D) (bondDim α)
  /-- Coisometry from the original physical space onto the retained sectors. -/
  verticalCoisometry : Matrix
    (Fin (∑ q : Fin (∑ α : Fin labelCount, multiplicity α),
      verticalCopyDim bondDim multiplicity q)) (Fin d) ℂ
  /-- Every BNT representative has at least one retained copy. -/
  multiplicity_pos : ∀ α, 0 < multiplicity α
  /-- Every retained diagonal weight is positive. -/
  weight_pos : ∀ α q, (0 : ℂ) < weight α q
  /-- The vertical representatives form a CPSV16 basis of normal tensors. -/
  isCPSVBNT : MPSTensor.IsCPSVBasisOfNormalTensors (verticalTensor M)
    (fun α ↦ ⟨bondDim α, tensor α⟩)
  /-- The vertical change of basis is a coisometry. -/
  coisometry : verticalCoisometry * verticalCoisometryᴴ = 1
  /-- Forward conjugation gives the weighted direct sum. -/
  forward : ∀ ab, verticalCoisometry * verticalTensor M ab * verticalCoisometryᴴ =
    verticalAssembledTensor bondDim multiplicity weight tensor ab
  /-- The weighted direct sum reconstructs every vertical letter. -/
  reconstruction : ∀ ab, verticalTensor M ab = verticalCoisometryᴴ *
    verticalAssembledTensor bondDim multiplicity weight tensor ab * verticalCoisometry

/-- Orthogonal grouped vertical sectors assemble into a vertical canonical
decomposition while retaining the CPSV16 basis predicate.

Source: arXiv:1606.00608, Proposition 4.13, lines 1863--1921. -/
theorem cpsvVerticalDecomposition_of_grouped_orthogonal_sectors
    (M : MPOTensor d D) {g : ℕ} (dim : Fin g → ℕ) (mult : Fin g → ℕ)
    (hMult : ∀ α, 0 < mult α)
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (hWeight : ∀ α q, (0 : ℂ) < weight α q)
    (A : (α : Fin g) → MPSTensor (D * D) (dim α))
    (hBNT : MPSTensor.IsCPSVBasisOfNormalTensors (verticalTensor M)
      (fun α ↦ ⟨dim α, A α⟩))
    (W : (p : (α : Fin g) × Fin (mult α)) →
      Matrix (Fin d) (Fin (dim p.1)) ℂ)
    (hIso : ∀ p, (W p)ᴴ * W p = 1)
    (hOrth : ∀ p q, p ≠ q → (W p)ᴴ * W q = 0)
    (hInter : ∀ p ab, verticalTensor M ab * W p =
      W p * ((weight p.1 p.2) • A p.1 ab))
    (hReconstruct : ∀ ab, verticalTensor M ab =
      ∑ q : Fin (∑ α, mult α),
        flattenGroupedSectorMap dim mult W q *
          ((verticalCopyWeights mult weight q) •
            verticalCopyBlocks dim mult A q ab) *
          (flattenGroupedSectorMap dim mult W q)ᴴ) :
    Nonempty (CPSVVerticalDecomposition M) := by
  classical
  let Wflat : (q : Fin (∑ α, mult α)) →
      Matrix (Fin d) (Fin (verticalCopyDim dim mult q)) ℂ :=
    flattenGroupedSectorMap dim mult W
  let B : (q : Fin (∑ α, mult α)) →
      MPSTensor (D * D) (verticalCopyDim dim mult q) :=
    fun q ab ↦ verticalCopyWeights mult weight q •
      verticalCopyBlocks dim mult A q ab
  let rowEquiv : ((q : Fin (∑ α, mult α)) ×
      Fin (verticalCopyDim dim mult q)) ≃
      Fin (∑ q : Fin (∑ α, mult α), verticalCopyDim dim mult q) :=
    finSigmaFinEquiv
  let U : Matrix
      (Fin (∑ q : Fin (∑ α, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ :=
    Matrix.reindex rowEquiv (Equiv.refl _) (Matrix.sigmaBlockRow Wflat)
  have hIsoFlat : ∀ q, (Wflat q)ᴴ * Wflat q = 1 := by
    intro q
    exact hIso (finSigmaFinEquiv.symm q)
  have hOrthFlat : ∀ q l, q ≠ l → (Wflat q)ᴴ * Wflat l = 0 := by
    intro q l hql
    exact hOrth (finSigmaFinEquiv.symm q) (finSigmaFinEquiv.symm l)
      (finSigmaFinEquiv.symm.injective.ne hql)
  have hInterFlat : ∀ q ab, verticalTensor M ab * Wflat q =
      Wflat q * B q ab := by
    intro q ab
    exact hInter (finSigmaFinEquiv.symm q) ab
  have hReconstructFlat : ∀ ab, verticalTensor M ab =
      ∑ q, Wflat q * B q ab * (Wflat q)ᴴ := by
    intro ab
    exact hReconstruct ab
  have hU : U * Uᴴ = 1 := by
    dsimp only [U]
    rw [Matrix.conjTranspose_reindex,
      show Matrix.reindex rowEquiv (Equiv.refl (Fin d))
          (Matrix.sigmaBlockRow Wflat) =
        Matrix.reindexLinearEquiv ℂ ℂ rowEquiv (Equiv.refl _)
          (Matrix.sigmaBlockRow Wflat) by rfl,
      show Matrix.reindex (Equiv.refl (Fin d)) rowEquiv
          (Matrix.sigmaBlockRow Wflat)ᴴ =
        Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) rowEquiv
          (Matrix.sigmaBlockRow Wflat)ᴴ by rfl,
      Matrix.reindexLinearEquiv_mul ℂ ℂ rowEquiv (Equiv.refl _) rowEquiv,
      Matrix.sigmaBlockRow_isCoisometry Wflat hIsoFlat hOrthFlat,
      Matrix.reindexLinearEquiv_one]
  have hForward : ∀ ab, U * verticalTensor M ab * Uᴴ =
      verticalAssembledTensor dim mult weight A ab := by
    intro ab
    have hSigma := Matrix.sigmaBlockRow_conjugation
      (verticalTensor M) B Wflat hIsoFlat hOrthFlat hInterFlat ab
    dsimp only [U]
    rw [Matrix.conjTranspose_reindex,
      show Matrix.reindex rowEquiv (Equiv.refl (Fin d))
          (Matrix.sigmaBlockRow Wflat) =
        Matrix.reindexLinearEquiv ℂ ℂ rowEquiv (Equiv.refl _)
          (Matrix.sigmaBlockRow Wflat) by rfl,
      show verticalTensor M ab =
        Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) (Equiv.refl _)
          (verticalTensor M ab) by rfl,
      Matrix.reindexLinearEquiv_mul ℂ ℂ rowEquiv (Equiv.refl _) (Equiv.refl _),
      show Matrix.reindex (Equiv.refl (Fin d)) rowEquiv
          (Matrix.sigmaBlockRow Wflat)ᴴ =
        Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) rowEquiv
          (Matrix.sigmaBlockRow Wflat)ᴴ by rfl,
      Matrix.reindexLinearEquiv_mul ℂ ℂ rowEquiv (Equiv.refl _) rowEquiv,
      hSigma]
    rfl
  have hReconstruction : ∀ ab, verticalTensor M ab = Uᴴ *
      verticalAssembledTensor dim mult weight A ab * U := by
    intro ab
    have hSigma := Matrix.sigmaBlockRow_reconstruction
      (verticalTensor M) B Wflat hReconstructFlat ab
    rw [hSigma]
    dsimp only [U]
    rw [Matrix.conjTranspose_reindex]
    change (Matrix.sigmaBlockRow Wflat)ᴴ *
        Matrix.blockDiagonal' (fun q ↦ B q ab) * Matrix.sigmaBlockRow Wflat =
      Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) rowEquiv
          (Matrix.sigmaBlockRow Wflat)ᴴ *
        Matrix.reindexLinearEquiv ℂ ℂ rowEquiv rowEquiv
          (Matrix.blockDiagonal' (fun q ↦ B q ab)) *
        Matrix.reindexLinearEquiv ℂ ℂ rowEquiv (Equiv.refl _)
          (Matrix.sigmaBlockRow Wflat)
    rw [Matrix.reindexLinearEquiv_mul ℂ ℂ (Equiv.refl _) rowEquiv rowEquiv,
      Matrix.reindexLinearEquiv_mul ℂ ℂ (Equiv.refl _) rowEquiv (Equiv.refl _)]
    rfl
  exact ⟨{
    labelCount := g
    bondDim := dim
    multiplicity := mult
    weight := weight
    tensor := A
    verticalCoisometry := U
    multiplicity_pos := hMult
    weight_pos := hWeight
    isCPSVBNT := hBNT
    coisometry := hU
    forward := hForward
    reconstruction := hReconstruction
  }⟩

/-- Horizontal canonical form and MPDO positivity furnish a vertical
decomposition which retains the literal CPSV16 basis predicate.

**Scope restriction (BNT-refined horizontal form):** `IsHorizontalCF` is
stronger than the literal CPSV canonical form assumed by Proposition 4.13.  The
literal implication remains open at the Lemma L separation after active-block
refinement and transport through the ambient coisometry; see
`docs/paper-gaps/cpgsv17_vertical_isometry_zero_sector.tex`.

Source: arXiv:1606.00608, Proposition 4.13, lines 1863--1921. -/
theorem IsHorizontalCF.exists_cpsvVerticalDecomposition
    (M : MPOTensor d D) (hHorizontal : IsHorizontalCF M) (hM : IsMPDO M) :
    Nonempty (CPSVVerticalDecomposition M) := by
  classical
  obtain ⟨r, dim, mu, blocks, V, hDimPos, _, hNormal, hIso, _, _, hInterStar,
    _, hReconstruct, hdim, X, zeta, _, _, hXDist, _, _, hSpectralBNT, _, _, _, _,
    hCoeffPos, hGroupedIso, hGroupedOrth, hGroupedInter, _, hGroupedCorner,
    hGroupedReconstruct⟩ :=
      hHorizontal.exists_verticalBNTGrouping_with_isometry M hM
  let C := MPSTensor.mpvPhaseClassData blocks
  have hSame : MPSTensor.SameMPV₂Pos (verticalTensor M)
      (MPSTensor.toTensorFromBlocks (d := D * D) (μ := mu) blocks) :=
    MPSTensor.sameMPV₂Pos_toTensorFromBlocks_of_reconstruction
      (verticalTensor M) mu blocks V hIso hInterStar hReconstruct
  have hBNT : MPSTensor.IsCPSVBasisOfNormalTensors (verticalTensor M)
      (fun j ↦ ⟨dim (C.repr j), blocks (C.repr j)⟩) :=
    hSpectralBNT.of_sameMPV₂Pos hSame.symm
  obtain ⟨_, W, _, hWIso, hWOrth, hWInter, hWReconstruct⟩ :=
    hM.exists_normalized_grouped_sector_maps blocks hHorizontal mu V hDimPos
      hNormal hdim X zeta hXDist hCoeffPos hGroupedIso hGroupedOrth
      hGroupedInter hGroupedCorner hGroupedReconstruct
  have hWReconstructFlat : ∀ ab, verticalTensor M ab =
      ∑ q : Fin (∑ j, C.copies j),
        flattenGroupedSectorMap (fun j ↦ dim (C.repr j)) C.copies W q *
          ((verticalCopyWeights C.copies
              (fun j q ↦ mu (C.enum j q) * zeta j q) q) •
            verticalCopyBlocks (fun j ↦ dim (C.repr j)) C.copies
              (fun j ↦ blocks (C.repr j)) q ab) *
          (flattenGroupedSectorMap
            (fun j ↦ dim (C.repr j)) C.copies W q)ᴴ := by
    intro ab
    rw [hWReconstruct ab]
    let f : ((j : Fin C.g) × Fin (C.copies j)) →
        Matrix (Fin d) (Fin d) ℂ := fun p ↦
      W p * ((mu (C.enum p.1 p.2) * zeta p.1 p.2) •
        blocks (C.repr p.1) ab) * (W p)ᴴ
    change (∑ j, ∑ q, f ⟨j, q⟩) =
      ∑ q, f (finSigmaFinEquiv.symm q)
    calc
      _ = ∑ p, f p := (Fintype.sum_sigma f).symm
      _ = _ := (Equiv.sum_comp finSigmaFinEquiv.symm f).symm
  exact cpsvVerticalDecomposition_of_grouped_orthogonal_sectors M
    (fun j ↦ dim (C.repr j)) C.copies C.copies_pos
    (fun j q ↦ mu (C.enum j q) * zeta j q) hCoeffPos
    (fun j ↦ blocks (C.repr j)) hBNT W hWIso hWOrth hWInter
    hWReconstructFlat

/-- A horizontally canonical matrix product density operator satisfying the
renormalization fixed-point condition has a positive fusion decomposition of
its vertical basis of normal tensors.

For every pair of BNT labels, the fusion map is a coisometry onto the active
direct sum.  Both forward conjugation and exact reconstruction are asserted,
so zero product tensors and proper active supports are permitted.

**Scope restriction (active product BNT):** Only active product corners are
retained.  A BNT label absent from a fixed product pair has zero fusion
multiplicity.  Documented in
`docs/paper-gaps/cpsv16_bnt_uniqueness_zero_coefficient.tex`.

**Local fix (Figure-11 fixed-pair support):** A fixed pair may have an empty
active family; no unsupported corner is inserted.  Documented in
`docs/paper-gaps/cpsv16_figure11_per_pair_support.tex`.

**Local fix (Figure-11 fusion coisometry):** The fusion map has retained-row
orientation and satisfies $UU^\dagger=1$.  Its adjoint gives the exact
reconstruction.  Documented in
`docs/paper-gaps/cpsv16_figure11_fusion_coisometry.tex`.

Source: CPSV16, Proposition 4.13, lines 1863--1921, and Appendix C.4,
lines 2020--2029. -/
theorem exists_positiveFusionDecomposition_of_isRFPViaTS
    (M : MPOTensor d D) (hHorizontal : IsHorizontalCF M) (hM : IsMPDO M)
    (hRFP : IsRFPViaTS M) :
    ∃ (g : ℕ) (dim : Fin g → ℕ)
      (A : (α : Fin g) → MPSTensor (D * D) (dim α)),
      MPSTensor.IsCPSVBasisOfNormalTensors (verticalTensor M)
          (fun α ↦ ⟨dim α, A α⟩) ∧
      ∃ (chi : DiagonalChiFamily (Fin g))
        (U : ∀ α β : Fin g,
          Matrix ((γ : Fin g) × (Fin (chi.dim α β γ) × Fin (dim γ)))
            (Fin (dim α * dim β)) ℂ),
        chi.PosEntries ∧
        (∀ α β, U α β * (U α β)ᴴ = 1) ∧
        (∀ (α β : Fin g) (i j : Fin D),
          U α β *
              (mulTensor (verticalBNTMPO (A α))
                (verticalBNTMPO (A β))) i j *
              (U α β)ᴴ =
            Matrix.blockDiagonal' fun γ ↦
              chi.matrix α β γ ⊗ₖ verticalBNTMPO (A γ) i j) ∧
        ∀ (α β : Fin g) (i j : Fin D),
          (mulTensor (verticalBNTMPO (A α))
            (verticalBNTMPO (A β))) i j =
            (U α β)ᴴ *
              (Matrix.blockDiagonal' fun γ ↦
                chi.matrix α β γ ⊗ₖ verticalBNTMPO (A γ) i j) *
              U α β := by
  classical
  obtain ⟨D₁⟩ := hHorizontal.exists_cpsvVerticalDecomposition M hM
  obtain ⟨D₂⟩ := hHorizontal.blockTwo.exists_cpsvVerticalDecomposition
    (blockTwo M) hM.blockTwo
  obtain ⟨Smap, T, hSCPTP, hTCPTP, hSphys, hTphys⟩ := hRFP
  refine ⟨D₁.labelCount, D₁.bondDim, D₁.tensor, D₁.isCPSVBNT, ?_⟩
  exact transportedVerticalSector_exists_positiveFusionDecomposition
    D₁.bondDim D₁.multiplicity D₁.weight
    D₂.bondDim D₂.multiplicity D₂.weight
    D₁.multiplicity_pos D₁.weight_pos
    D₂.multiplicity_pos D₂.weight_pos
    M D₁.tensor D₂.tensor D₁.isCPSVBNT D₂.isCPSVBNT
    D₁.verticalCoisometry D₂.verticalCoisometry
    D₁.coisometry D₂.coisometry T Smap hTCPTP hSCPTP
    D₁.forward D₁.reconstruction D₂.forward D₂.reconstruction
    hTphys hSphys hHorizontal hM

end MPOTensor
