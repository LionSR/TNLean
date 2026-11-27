/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.Vertical.GroupedSectorGram
import TNLean.MPS.MPDO.Vertical.NormalizedGroupedSectorMaps
import TNLean.MPS.MPDO.Vertical.VerticalBNT
import TNLean.MPS.MPDO.Vertical.VerticalBNTConstruction
import TNLean.MPS.MPDO.Vertical.CPSVOriginalSpaceLemmaL
import TNLean.MPS.MPDO.Vertical.CPSVPeriodicExclusion
import TNLean.MPS.MPDO.Vertical.HorizontalBlocking
import TNLean.MPS.Operator.Product.PhysicalBlocking
import TNLean.MPS.CanonicalForm.NormalBlocks.Blocking
import TNLean.MPS.CanonicalForm.PhysicalReindex
import QICLean.Algebra.Combinatorics.FinSum
import TNLean.MPS.CanonicalForm.VerticalForm.VerticalCF
import QICLean.Algebra.Unitary.IsometricFrameEmbedding

/-!
# Predicate-neutral vertical canonical form

A grouped vertical BNT decomposition and pairwise grouped-corner Gram dressing
supply all data needed for vertical canonical form. The grouped representatives
form a BNT, Gram rigidity normalizes the physical sector maps, and their block
row gives the required coisometry and exact reconstruction.

## Main results

* `MPOTensor.verticalCF_of_grouping_and_gramDressing`: grouped vertical BNT
  data and the pairwise Figure 8 hypothesis imply vertical canonical form.
* `MPOTensor.IsCPSVCanonicalForm_toMPSTensor_blockTensor`,
  `MPOTensor.IsCPSVCanonicalForm_toMPSTensor_blockTwo`: literal CPSV canonical form and MPO physical
  blocking.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Proposition 4.13, lines 1863--1921.

## Inputs of the grouped vertical decomposition

The grouped vertical construction of Proposition 4.13 consumes exactly two
properties of a matrix product density operator: the phase-class grouping of
its normal vertical sectors with their physical isometries, and the pairwise
Figure 8 comparison of two positive corners of a common representative. This
file names that pair of inputs and the additional blocked-tensor properties
needed for product decomposition. Both literal CPSV canonical form and
BNT-refined horizontal form supply them.

The two canonical-form predicates stay independent: each one proves the two
inputs from its own grouping and Figure 8 theorems, and no implication
between them is used or asserted.

### Main definitions

* `MPOTensor.HasVerticalBNTGroupingInputs`: the grouping and the
  grouped-corner Gram dressing of a matrix product density operator.
* `MPOTensor.HasVerticalBNTProductInputs`: grouping data at one and two
  sites, together with blocked projector closure, periodic exclusion, and
  sector-compression separation.

### Main results

* `MPOTensor.IsHorizontalCF.hasVerticalBNTGroupingInputs` and
  `MPTensor.IsCPSVCanonicalForm.hasVerticalBNTGroupingInputs`: each
  canonical form supplies both inputs.
* `MPOTensor.HasVerticalBNTGroupingInputs.verticalCF`: the two inputs give
  vertical canonical form.
* `MPOTensor.IsHorizontalCF.hasVerticalBNTProductInputs` and
  `MPTensor.IsCPSVCanonicalForm.hasVerticalBNTProductInputs`: each canonical
  form supplies the product inputs directly.

### References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Proposition 4.13, lines 1863--1921.

## Vertical canonical form of matrix product density operators

The grouped vertical decomposition of a matrix product density operator in
BNT-refined horizontal form supplies a basis of normal tensors and
normalized physical sector maps. The resulting positive weights and sector
maps give the coisometry and the two exact block-diagonal identities of the
vertical canonical form.

### Main result

* `MPOTensor.verticalCF_of_horizontalCF`: every matrix product density operator
  in BNT-refined horizontal form is in vertical canonical form.

### References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Proposition 4.13, lines 1863--1921.

## Vertical canonical form before and after two-site blocking

For a matrix product density operator in BNT-refined horizontal
form, the current Proposition 4.13 specialization applies both to the original
tensor and to its two-site physical blocking.
This is the first step of the two-site comparison in Appendix C.4 of
arXiv:1606.00608.

## Vertical canonical form from literal CPSV canonical form

The literal CPSV canonical-form decomposition groups the normal vertical
corners by matrix-product-vector phase class.  The grouped Figure 8 identity
normalizes their internal gauges, after which the orthogonal physical sector
maps assemble into the coisometry of the vertical canonical form.

### Main result

* `MPOTensor.verticalCF_of_cpsvCanonicalForm`: every matrix product density
  operator in literal CPSV canonical form is in vertical canonical form.

### References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Proposition 4.13, lines 1863--1921.
-/

section

/-!
## Coisometries from orthogonal vertical sectors

For a finite family of isometries with mutually orthogonal ranges, this file
forms the block-row coisometry whose rows are their adjoints.  If a tensor
intertwines each isometry with a sector tensor, conjugation by this coisometry
is the direct sum of the sector tensors.  A literal sum over the sector
corners gives the reverse reconstruction identity.

These matrix identities isolate the finite-dimensional construction needed for
the coisometry and direct-sum conclusion of arXiv:1606.00608,
Proposition 4.13, lines 1863--1870.  The reverse identity proved here is the
conditional consequence of an assumed literal sum over the sector corners.

## Main definitions

* `Matrix.sigmaBlockRow`: the block row formed from the adjoints of a family
  of rectangular matrices.
* `MPOTensor.flattenGroupedSectorMap`: the same family reindexed by its finite
  copy label.

## Main results

* `Matrix.sigmaBlockRow_isCoisometry`: orthogonal isometries give a
  coisometry.
* `Matrix.sigmaBlockRow_conjugation`: sector intertwinings give a
  block-diagonal conjugation identity.
* `Matrix.sigmaBlockRow_reconstruction`: a sum of sector corners equals the
  reverse block-diagonal compression.
* `MPOTensor.isVerticalCF_of_grouped_orthogonal_sectors`: positive grouped
  orthogonal sectors with an exact reconstruction give vertical canonical form.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Proposition 4.13, lines 1863--1870
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

/-- Reindex a family of sector maps indexed by the dependent pair
$(\alpha,q)$ by the copy index used in the vertical direct sum. -/
def flattenGroupedSectorMap {g : ℕ} (dim : Fin g → ℕ) (mult : Fin g → ℕ)
    (W : (p : (α : Fin g) × Fin (mult α)) →
      Matrix (Fin d) (Fin (dim p.1)) ℂ) :
    (q : Fin (∑ α, mult α)) →
      Matrix (Fin d) (Fin (verticalCopyDim dim mult q)) ℂ :=
  fun q ↦ W (finSigmaFinEquiv.symm q)

/-- Orthogonal grouped vertical sectors assemble to the vertical canonical form.

The sector label is the dependent pair $(\alpha,q)$, where $\alpha$ labels a
normal tensor and $q$ labels one diagonal entry of its positive multiplicity
matrix.  The two canonical finite-sum equivalences identify these labels and
their bond indices with the coordinates of the vertical direct sum.

Source: arXiv:1606.00608, Proposition 4.13, lines 1863--1870. -/
theorem isVerticalCF_of_grouped_orthogonal_sectors
    (M : MPOTensor d D) {g : ℕ} (dim : Fin g → ℕ) (mult : Fin g → ℕ)
    (hMult : ∀ α, 0 < mult α)
    (ω : (α : Fin g) → Fin (mult α) → ℂ)
    (hω : ∀ α q, (0 : ℂ) < ω α q)
    (A : (α : Fin g) → MPSTensor (D * D) (dim α))
    (hBNT : MPSTensor.IsCPSVBasisOfNormalTensors (verticalTensor M) (fun α ↦ ⟨dim α, A α⟩))
    (W : (p : (α : Fin g) × Fin (mult α)) →
      Matrix (Fin d) (Fin (dim p.1)) ℂ)
    (hiso : ∀ p, (W p)ᴴ * W p = 1)
    (horth : ∀ p q, p ≠ q → (W p)ᴴ * W q = 0)
    (hinter : ∀ p v, verticalTensor M v * W p =
      W p * ((ω p.1 p.2) • A p.1 v))
    (hreconstruct : ∀ v, verticalTensor M v =
      ∑ q : Fin (∑ α, mult α),
        flattenGroupedSectorMap dim mult W q *
          ((verticalCopyWeights mult ω q) • verticalCopyBlocks dim mult A q v) *
          (flattenGroupedSectorMap dim mult W q)ᴴ) :
    IsVerticalCF M := by
  classical
  let Wflat : (q : Fin (∑ α, mult α)) →
      Matrix (Fin d) (Fin (verticalCopyDim dim mult q)) ℂ :=
    flattenGroupedSectorMap dim mult W
  let B : (q : Fin (∑ α, mult α)) →
      MPSTensor (D * D) (verticalCopyDim dim mult q) :=
    fun q v ↦ verticalCopyWeights mult ω q • verticalCopyBlocks dim mult A q v
  let rowEquiv : ((q : Fin (∑ α, mult α)) ×
      Fin (verticalCopyDim dim mult q)) ≃
      Fin (∑ q : Fin (∑ α, mult α), verticalCopyDim dim mult q) :=
    finSigmaFinEquiv
  let U : Matrix
      (Fin (∑ q : Fin (∑ α, mult α), verticalCopyDim dim mult q)) (Fin d) ℂ :=
    Matrix.reindex rowEquiv (Equiv.refl _) (Matrix.sigmaBlockRow Wflat)
  have hisoFlat : ∀ q, (Wflat q)ᴴ * Wflat q = 1 := by
    intro q
    exact hiso (finSigmaFinEquiv.symm q)
  have horthFlat : ∀ q l, q ≠ l → (Wflat q)ᴴ * Wflat l = 0 := by
    intro q l hql
    exact horth (finSigmaFinEquiv.symm q) (finSigmaFinEquiv.symm l)
      (finSigmaFinEquiv.symm.injective.ne hql)
  have hinterFlat : ∀ q v, verticalTensor M v * Wflat q = Wflat q * B q v := by
    intro q v
    exact hinter (finSigmaFinEquiv.symm q) v
  have hreconstructFlat : ∀ v, verticalTensor M v =
      ∑ q, Wflat q * B q v * (Wflat q)ᴴ := by
    intro v
    exact hreconstruct v
  refine ⟨g, dim, mult, ω, A, U, hMult, hω, ?_, hBNT, ?_, ?_⟩
  · dsimp only [U]
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
      Matrix.sigmaBlockRow_isCoisometry Wflat hisoFlat horthFlat,
      Matrix.reindexLinearEquiv_one]
  · intro v
    have hsigma := Matrix.sigmaBlockRow_conjugation
      (verticalTensor M) B Wflat hisoFlat horthFlat hinterFlat v
    dsimp only [U]
    rw [Matrix.conjTranspose_reindex,
      show Matrix.reindex rowEquiv (Equiv.refl (Fin d))
          (Matrix.sigmaBlockRow Wflat) =
          Matrix.reindexLinearEquiv ℂ ℂ rowEquiv (Equiv.refl _)
            (Matrix.sigmaBlockRow Wflat) by rfl,
      show verticalTensor M v =
          Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) (Equiv.refl _)
            (verticalTensor M v) by rfl,
      Matrix.reindexLinearEquiv_mul ℂ ℂ rowEquiv (Equiv.refl _) (Equiv.refl _),
      show Matrix.reindex (Equiv.refl (Fin d)) rowEquiv
          (Matrix.sigmaBlockRow Wflat)ᴴ =
          Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) rowEquiv
            (Matrix.sigmaBlockRow Wflat)ᴴ by rfl,
      Matrix.reindexLinearEquiv_mul ℂ ℂ rowEquiv (Equiv.refl _) rowEquiv,
      hsigma]
    rfl
  · intro v
    have hsigma := Matrix.sigmaBlockRow_reconstruction
      (verticalTensor M) B Wflat hreconstructFlat v
    rw [hsigma]
    dsimp only [U]
    rw [Matrix.conjTranspose_reindex]
    change (Matrix.sigmaBlockRow Wflat)ᴴ * Matrix.blockDiagonal' (fun q ↦ B q v) *
        Matrix.sigmaBlockRow Wflat =
      Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) rowEquiv
          (Matrix.sigmaBlockRow Wflat)ᴴ *
        Matrix.reindexLinearEquiv ℂ ℂ rowEquiv rowEquiv
          (Matrix.blockDiagonal' (fun q ↦ B q v)) *
        Matrix.reindexLinearEquiv ℂ ℂ rowEquiv (Equiv.refl _)
          (Matrix.sigmaBlockRow Wflat)
    rw [Matrix.reindexLinearEquiv_mul ℂ ℂ (Equiv.refl _) rowEquiv rowEquiv,
      Matrix.reindexLinearEquiv_mul ℂ ℂ (Equiv.refl _) rowEquiv (Equiv.refl _)]
    rfl

end MPOTensor

end

section CPSVBlocking

/-!
## Literal CPSV canonical form and MPO physical blocking

This module specializes the MPS-level literal CPSV blocking theorem to MPO
tensors through the doubled-index MPS tensor.

### Main results

* `MPOTensor.IsCPSVCanonicalForm_toMPSTensor_blockTensor`
* `MPOTensor.IsCPSVCanonicalForm_toMPSTensor_blockTwo`

### References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608, Section 2.3 and
  Appendix C.4, lines 1951--1956.
-/

open scoped Matrix ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

/-- Literal CPSV canonical form is preserved by arbitrary positive MPO physical
blocking after passing to the doubled-index MPS tensor.

Source: arXiv:1606.00608, lines 636--659 define MPDO coarse graining by
physical blocking and its two-site tensor maps; arbitrary positive blocking is
the iterated form of the same operation. -/
theorem IsCPSVCanonicalForm_toMPSTensor_blockTensor {M : MPOTensor d D}
    (hM : MPTensor.IsCPSVCanonicalForm M.toMPSTensor) (p : ℕ) (hp : 0 < p) :
    MPTensor.IsCPSVCanonicalForm (blockTensor M p).toMPSTensor := by
  rw [toMPSTensor_blockTensor]
  exact (hM.blockTensor p hp).reindexPhysical (blockedDoubledIndexEquiv d p)

/-- Literal CPSV canonical form is preserved by concrete two-site MPO
blocking after passing to the doubled-index MPS tensor.

Source: arXiv:1606.00608, lines 636--659, especially the two-site maps
`M_2(X)` and equations `eq:Smap`--`eq:Tmap`. -/
theorem IsCPSVCanonicalForm_toMPSTensor_blockTwo {M : MPOTensor d D}
    (hM : MPTensor.IsCPSVCanonicalForm M.toMPSTensor) :
    MPTensor.IsCPSVCanonicalForm (blockTwo M).toMPSTensor := by
  rw [toMPSTensor_blockTwo]
  exact (hM.blockTensor 2 (by norm_num)).reindexPhysical (twoSiteDoubledIndexEquiv d)

end MPOTensor

end CPSVBlocking

section VerticalCanonicalForm

section

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

/-- Grouped vertical BNT data with pairwise Figure 8 comparison determine a
vertical canonical form.

The grouping contains the normal representatives, positive grouped weights,
orthogonal physical corners, and exact reconstruction. The Gram-dressing
hypothesis is the only canonical-form-specific input.

Source: arXiv:1606.00608, Proposition 4.13, lines 1863--1921. -/
theorem verticalCF_of_grouping_and_gramDressing (M : MPOTensor d D)
    (hGrouping : HasVerticalBNTGroupingWithIsometry M)
    (hDressing : HasGroupedCornerGramDressing M) :
    IsVerticalCF M := by
  classical
  obtain ⟨r, dim, mu, blocks, V, hDimPos, _, hNormal, hIso, _, _, hInterStar,
    _, hReconstruct, hdim, X, zeta, _, _, hXDist, _, _, hSpectralBNT, _, _, _, _,
    hCoeffPos, hGroupedIso, hGroupedOrth, hGroupedInter, _, hGroupedCorner,
    hGroupedReconstruct⟩ := hGrouping
  let C := MPSTensor.mpvPhaseClassData blocks
  have hBNT : MPSTensor.IsCPSVBasisOfNormalTensors (verticalTensor M)
      (fun j ↦ ⟨dim (C.repr j), blocks (C.repr j)⟩) :=
    isCPSVBasisOfNormalTensors_verticalTensor_of_grouping M mu blocks V hIso
      hInterStar hReconstruct hSpectralBNT
  have hGram : ∀ j q, ∃ omega : ℝ, 0 < omega ∧
      (X j q : Matrix (Fin (dim (C.enum j q))) (Fin (dim (C.enum j q))) ℂ)ᴴ *
          X j q = (omega : ℂ) • 1 := by
    intro j q
    apply grouped_sector_gram_eq_pos_smul_one_of_dressing blocks
      (M := M) (μ := mu) (V := V) (_hDimPos := hDimPos) (hdim := hdim)
        (X := X) (ζ := zeta) (hXDist := hXDist) (hCoeffPos := hCoeffPos)
        (hCorner := hGroupedCorner) (j := j) (q := q)
    · exact hDressing
    · intro l p
      exact ((MPSTensor.isNormalTensor_cast_iff (hdim l p)
        (blocks (C.repr l))).2 (hNormal (C.repr l))).isNormal
  obtain ⟨_, W, _, hWIso, hWOrth, hWInter, hWReconstruct⟩ :=
    exists_normalized_grouped_sector_maps_of_gram blocks mu V hdim X zeta
      hGram hGroupedIso hGroupedOrth hGroupedInter hGroupedReconstruct
  apply isVerticalCF_of_grouped_orthogonal_sectors M
    (fun j ↦ dim (C.repr j)) C.copies C.copies_pos
    (fun j q ↦ mu (C.enum j q) * zeta j q) hCoeffPos
    (fun j ↦ blocks (C.repr j)) hBNT W hWIso hWOrth hWInter
  intro v
  rw [hWReconstruct v]
  let f : ((j : Fin C.g) × Fin (C.copies j)) → Matrix (Fin d) (Fin d) ℂ :=
    fun p ↦ W p *
      ((mu (C.enum p.1 p.2) * zeta p.1 p.2) • blocks (C.repr p.1) v) *
      (W p)ᴴ
  change (∑ j, ∑ q, f ⟨j, q⟩) = ∑ q, f (finSigmaFinEquiv.symm q)
  exact (Fintype.sum_finSigmaFinEquiv f).symm

end MPOTensor

end

section

open scoped Matrix ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

/-- The two canonical-form-specific inputs of the grouped vertical
construction.

The first field groups the normal vertical sectors by matrix-product-vector
phase class while retaining their physical reducing isometries. The second
field compares the Gram dressings of any two positive vertical corners of a
common representative.

Source: arXiv:1606.00608, Proposition 4.13, lines 1863--1921. -/
structure HasVerticalBNTGroupingInputs (M : MPOTensor d D) : Prop where
  /-- The phase-class grouping with physical reducing isometries. -/
  grouping : HasVerticalBNTGroupingWithIsometry M
  /-- The pairwise Figure 8 comparison of two positive vertical corners. -/
  gramDressing : HasGroupedCornerGramDressing M

/-- Both inputs of the grouped vertical construction give vertical canonical
form.

Source: arXiv:1606.00608, Proposition 4.13, lines 1863--1921. -/
theorem HasVerticalBNTGroupingInputs.verticalCF {M : MPOTensor d D}
    (h : HasVerticalBNTGroupingInputs M) : IsVerticalCF M :=
  verticalCF_of_grouping_and_gramDressing M h.grouping h.gramDressing

/-- BNT-refined horizontal form compares the Gram dressings of two
positive vertical corners of a common representative.

Source: arXiv:1606.00608, proof of Proposition 4.13, Figures 7--8 and lines
1909--1919. -/
theorem IsHorizontalCF.hasGroupedCornerGramDressing (M : MPOTensor d D)
    (hHorizontal : IsHorizontalCF M) (hM : IsMPDO M) :
    HasGroupedCornerGramDressing M := by
  intro n A VX VY X Y cX cY hcX hcY hcornerX hcornerY
  exact hHorizontal.gramDressing_eq_of_two_grouped_corners M hM
    A VX VY X Y cX cY hcX hcY hcornerX hcornerY

/-- A matrix product density operator in BNT-refined horizontal
form supplies both inputs of the grouped vertical construction.

Source: arXiv:1606.00608, Proposition 4.13, lines 1895--1919. -/
theorem IsHorizontalCF.hasVerticalBNTGroupingInputs (M : MPOTensor d D)
    (hHorizontal : IsHorizontalCF M) (hM : IsMPDO M) :
    HasVerticalBNTGroupingInputs M :=
  ⟨hHorizontal.exists_verticalBNTGrouping_with_isometry M hM,
    hHorizontal.hasGroupedCornerGramDressing M hM⟩

end MPOTensor

namespace MPTensor.IsCPSVCanonicalForm

open MPSTensor

variable {d D : ℕ}

/-- Literal CPSV canonical form compares the Gram dressings of two positive
vertical corners of a common representative.

Source: arXiv:1606.00608, proof of Proposition 4.13, Figures 7--8 and lines
1909--1919. -/
theorem hasGroupedCornerGramDressing (M : MPOTensor d D)
    (hCanonical : IsCPSVCanonicalForm M.toMPSTensor) (hM : MPOTensor.IsMPDO M) :
    MPOTensor.HasGroupedCornerGramDressing M := by
  intro n A VX VY X Y cX cY hcX hcY hcornerX hcornerY
  exact hCanonical.gramDressing_eq_of_two_grouped_corners M hM
    A VX VY X Y cX cY hcX hcY hcornerX hcornerY

/-- A matrix product density operator in literal CPSV canonical form supplies
both inputs of the grouped vertical construction.

Source: arXiv:1606.00608, Proposition 4.13, lines 1895--1919. -/
theorem hasVerticalBNTGroupingInputs (M : MPOTensor d D)
    (hCanonical : IsCPSVCanonicalForm M.toMPSTensor) (hM : MPOTensor.IsMPDO M) :
    MPOTensor.HasVerticalBNTGroupingInputs M :=
  ⟨hCanonical.exists_verticalBNTGrouping_with_isometry M hM,
    hCanonical.hasGroupedCornerGramDressing M hM⟩

end MPTensor.IsCPSVCanonicalForm

namespace MPOTensor

variable {d D : ℕ}

/-- The grouped vertical data together with the three properties of the
two-site vertical tensor used in the product decomposition. The separate
fields keep the source hypotheses visible in each application.

Source: CPSV16, Proposition 4.13, lines 1873--1921, and Appendix C.4,
lines 2020--2029. -/
structure HasVerticalBNTProductInputs (M : MPOTensor d D) : Prop where
  /-- Grouping and comparison of positive vertical corners.
  Source: CPSV16, Proposition IV.12, equation `UMU-appendix` and the
  Gram comparison preceding equation `eq3:proof.IV.12`. -/
  groupingInputs : HasVerticalBNTGroupingInputs M
  /-- Grouping and pairwise Gram comparison for the two-site tensor, obtained
  by applying Proposition IV.12 after blocking. Source: CPSV16,
  Proposition IV.12, equation `UMU-appendix`. -/
  blockedGroupingInputs : HasVerticalBNTGroupingInputs (blockTwo M)
  /-- Orthogonal invariant projectors of the two-site vertical tensor are
  reducing projectors. Source: CPSV16, proof of Proposition IV.12,
  first paragraph after equation `UMU-appendix`. -/
  projectorClosure : MPSTensor.HasInvariantProjectorClosure (verticalTensor (blockTwo M))
  /-- The two-site vertical tensor has no nontrivial periodic vectors.
  Source: CPSV16, proof of Proposition IV.12, equation `eq2:proof.IV.12`
  and the preceding paragraph. -/
  noPeriodicVectors : MPSTensor.HasNoPeriodicVectors (verticalTensor (blockTwo M))
  /-- A nonzero two-site corner has a nonzero sector compression at some
  length. Source: CPSV16, proof of Proposition IV.12, paragraph beginning
  "Since ... CF in the horizontal direction" before equation
  `eq3:proof.IV.12`. -/
  sectorCompressionSeparation :
    ∀ P : Matrix (Fin (d * d)) (Fin (d * d)) ℂ,
      (∃ v, P * verticalTensor (blockTwo M) v * P ≠ 0) →
        ∃ N, sectorCompression (blockTwo M) P N ≠ 0

/-- BNT-refined horizontal form supplies the product inputs.

Source: CPSV16, Proposition 4.13, lines 1873--1921. -/
theorem IsHorizontalCF.hasVerticalBNTProductInputs (M : MPOTensor d D)
    (hHorizontal : IsHorizontalCF M) (hM : IsMPDO M) :
    HasVerticalBNTProductInputs M := by
  let hTwo := hHorizontal.blockTwo
  let hMTwo := hM.blockTwo
  exact ⟨hHorizontal.hasVerticalBNTGroupingInputs M hM,
    hTwo.hasVerticalBNTGroupingInputs (MPOTensor.blockTwo M) hMTwo,
    hTwo.hasInvariantProjectorClosure_verticalTensor (MPOTensor.blockTwo M) hMTwo,
    hasNoPeriodicVectors_verticalTensor_of_horizontalCF (MPOTensor.blockTwo M) hMTwo hTwo,
    fun P hP ↦ hTwo.exists_sectorCompression_ne_zero_of_corner
      (MPOTensor.blockTwo M) P hP⟩

end MPOTensor

namespace MPTensor.IsCPSVCanonicalForm

open MPSTensor

variable {d D : ℕ}

/-- Literal CPSV canonical form supplies the product inputs independently of
BNT-refined horizontal form.

Source: CPSV16, Proposition 4.13, lines 1873--1921. -/
theorem hasVerticalBNTProductInputs (M : MPOTensor d D)
    (hCanonical : IsCPSVCanonicalForm M.toMPSTensor) (hM : MPOTensor.IsMPDO M) :
    MPOTensor.HasVerticalBNTProductInputs M := by
  let hTwo := MPOTensor.IsCPSVCanonicalForm_toMPSTensor_blockTwo hCanonical
  let hMTwo := hM.blockTwo
  exact ⟨hCanonical.hasVerticalBNTGroupingInputs M hM,
    hTwo.hasVerticalBNTGroupingInputs (MPOTensor.blockTwo M) hMTwo,
    hTwo.hasInvariantProjectorClosure_verticalTensor (MPOTensor.blockTwo M) hMTwo,
    MPOTensor.hasNoPeriodicVectors_verticalTensor_of_cpsvCanonicalForm
      (MPOTensor.blockTwo M) hMTwo hTwo,
    fun P hP ↦ hTwo.exists_sectorCompression_ne_zero_of_corner
      (MPOTensor.blockTwo M) P hP⟩

end MPTensor.IsCPSVCanonicalForm

end

section

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

/-- A matrix product density operator in BNT-refined horizontal form
is also in vertical canonical form.

The same grouped vertical decomposition supplies both the algebraic basis of
normal tensors and the normalized physical sector maps.  Their positive
weights, orthogonal isometric ranges, intertwinings, and exact reconstruction
then combine to give the vertical coisometry.

Source: arXiv:1606.00608, Proposition 4.13, lines 1863--1921. -/
theorem verticalCF_of_horizontalCF (M : MPOTensor d D)
    (hHorizontal : IsHorizontalCF M) (hM : IsMPDO M) :
    IsVerticalCF M :=
  (hHorizontal.hasVerticalBNTGroupingInputs M hM).verticalCF

end MPOTensor

end

section

namespace MPOTensor

variable {d D : ℕ}

/-- A matrix product density operator in BNT-refined horizontal form
and its two-site blocking are both in vertical canonical form.

Source: arXiv:1606.00608, Appendix C.4, lines 1951--1956. -/
theorem verticalCF_and_blockTwo_of_horizontalCF (M : MPOTensor d D)
    (hHorizontal : IsHorizontalCF M) (hM : IsMPDO M) :
    IsVerticalCF M ∧ IsVerticalCF (blockTwo M) :=
  ⟨verticalCF_of_horizontalCF M hHorizontal hM,
    verticalCF_of_horizontalCF (blockTwo M) hHorizontal.blockTwo hM.blockTwo⟩

end MPOTensor

end

section

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

/-- A matrix product density operator in literal CPSV canonical form is also
in vertical canonical form.

The literal grouped decomposition supplies a basis of normal representatives
and positive grouped coefficients.  Gram normalization gives orthogonal
isometric physical sector maps.  Their block row is the required coisometry,
with orientation $U U^\dagger=I$, and the two direct-sum identities follow from
the exact letterwise reconstruction.

Source: arXiv:1606.00608, Proposition 4.13, lines 1863--1921. -/
theorem verticalCF_of_cpsvCanonicalForm (M : MPOTensor d D)
    (hCanonical : MPTensor.IsCPSVCanonicalForm M.toMPSTensor)
    (hM : IsMPDO M) :
    IsVerticalCF M :=
  (hCanonical.hasVerticalBNTGroupingInputs M hM).verticalCF

end MPOTensor

end

end VerticalCanonicalForm
