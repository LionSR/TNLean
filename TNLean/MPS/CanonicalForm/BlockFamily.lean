/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.Words.Basic
import TNLean.MPS.Transfer.Spectrum.TransferOperatorGapInjective
import TNLean.MPS.Transfer.Spectrum.TransferOperatorGapNT
import TNLean.MPS.Transfer.Spectrum.PrimitiveOverlap
import QICLean.Kraus.PrimitiveFixedPoint.Assembly
import TNLean.MPS.Tensor.DirectSum.IrreducibleDecomposition
import TNLean.MPS.Transfer.Irreducible.DiagonalFixedPoint
import QICLean.Channel.Peripheral.Spectrum.Spectrum
import Mathlib.Analysis.Complex.Basic
import TNLean.MPS.Tensor.Physical.Blocking
import TNLean.MPS.Tensor.Physical.BlockingTransfer
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Separated canonical-form hypotheses

A weighted block family may be studied through separate hypotheses: blockwise
injectivity, irreducibility, primitive transfer maps, left-canonical
normalization, non-increasing nonzero weight moduli, and self-overlap
normalization. The canonical-form conditions collect exactly these hypotheses in
the non-strict, ties-allowed order used in the reduction to canonical form.

## Main conditions

- Additive split conditions: `HasInjectiveBlocks`, `HasIrreducibleBlocks`, `HasPrimitiveBlocks`,
  `IsLeftCanonicalBlockFamily`, `HasOrderedNonzeroWeights`,
  `HasNormalizedSelfOverlap`.
- Canonical-form conditions: `IsCanonicalForm` and `IsNormalCanonicalForm`.
* `MPSTensor.exists_normalCanonicalForm_of_primitive_blockDecomp`: normal canonical form from
  primitive weighted block decompositions.
-/

open MPTensor

open scoped Matrix BigOperators

section BlockFamily

namespace MPSTensor

variable {d : ℕ}

/-! ### Normalization convention

The **left-canonical** normalization condition in this file is `∑ᵢ Aᵢ† Aᵢ = I`.
Equivalently, the associated transfer map is trace-preserving. We do **not** assume the separate
unital identity `∑ᵢ Aᵢ Aᵢ† = I`.
-/

/-! ### Additive split conditions for canonical-form hypotheses

The following conditions isolate the separate hypotheses of the canonical-form
predicates: injectivity, left-canonical normalization, non-increasing weight
ordering, and self-overlap normalization. `IsCanonicalForm` remains the compact
mathematical statement, while these records let the canonical-form reduction and
the RFP/BNT projections expose only the assumptions used at each step.
-/

/-- Each block in the family is algebraically injective. -/
structure HasInjectiveBlocks {r : ℕ} {dim : Fin r → ℕ}
    (A : (k : Fin r) → MPSTensor d (dim k)) : Prop where
  /-- Each block is algebraically injective (`span (range (A k)) = ⊤`). -/
  block_injective : ∀ k, Kraus.IsInjective (A k)

/-- Each block in the family is irreducible in the invariant-projection sense. -/
structure HasIrreducibleBlocks {r : ℕ} {dim : Fin r → ℕ}
    (A : (k : Fin r) → MPSTensor d (dim k)) : Prop where
  /-- Each block has no nontrivial invariant orthogonal projection. -/
  block_irreducible : ∀ k, Kraus.IsIrreducibleFamily (A k)

namespace HasIrreducibleBlocks

variable {r : ℕ} {dim : Fin r → ℕ}
variable {A : (k : Fin r) → MPSTensor d (dim k)}

/-- Build `HasIrreducibleBlocks` from pointwise irreducibility. -/
theorem ofForall (hA : ∀ k, Kraus.IsIrreducibleFamily (A k)) : HasIrreducibleBlocks (d := d) A where
  block_irreducible := hA

end HasIrreducibleBlocks

/-- Each block transfer map is primitive in the peripheral-spectrum sense
(`peripheralEigenvalues = {1}`).

This is intentionally stored separately from `HasIrreducibleBlocks`: under the repository's
current definition, peripheral-spectrum primitivity alone does not imply irreducibility for an
arbitrary transfer map. -/
structure HasPrimitiveBlocks {r : ℕ} {dim : Fin r → ℕ}
    (A : (k : Fin r) → MPSTensor d (dim k)) : Prop where
  /-- Each block transfer map has `1` as its unique peripheral eigenvalue. -/
  block_primitive : ∀ k,
    _root_.IsPrimitive (Kraus.transferMap (ι := Fin d) (n := Fin (dim k)) (A k))

namespace HasPrimitiveBlocks

variable {r : ℕ} {dim : Fin r → ℕ}
variable {A : (k : Fin r) → MPSTensor d (dim k)}

/-- Build `HasPrimitiveBlocks` from pointwise peripheral primitivity. -/
theorem ofForall
    (hA : ∀ k, _root_.IsPrimitive (Kraus.transferMap (ι := Fin d) (n := Fin (dim k)) (A k))) :
    HasPrimitiveBlocks (d := d) A where
  block_primitive := hA

end HasPrimitiveBlocks

/-- Left-canonical block-family normalization: each block satisfies
`∑ᵢ Aᵢ† Aᵢ = I`. -/
structure IsLeftCanonicalBlockFamily {r : ℕ} {dim : Fin r → ℕ}
    (A : (k : Fin r) → MPSTensor d (dim k)) : Prop where
  /-- Preferred field name using the project's terminology: left-canonical =
  `∑ᵢ Aᵢ† Aᵢ = I`. -/
  leftCanonical : ∀ k, ∑ i : Fin d, (A k i)ᴴ * (A k i) = 1

namespace IsLeftCanonicalBlockFamily

variable {r : ℕ} {dim : Fin r → ℕ}
variable {A : (k : Fin r) → MPSTensor d (dim k)}

/-- Build `IsLeftCanonicalBlockFamily` from pointwise left-canonical identities. -/
theorem ofForall (hA : ∀ k, ∑ i : Fin d, (A k i)ᴴ * (A k i) = 1) :
    IsLeftCanonicalBlockFamily (d := d) A where
  leftCanonical := hA

end IsLeftCanonicalBlockFamily

/-- Non-increasing weight ordering together with nonvanishing coefficients.

Source context: arXiv:1606.00608, eq. `II_CF1` and lines 237--246 introduce the
block weights in canonical form; arXiv:2011.12127, lines 1831--1836 and
1864--1884 record the same canonical-form and basis-of-normal-tensors weights.
These source statements impose no strict ordering of moduli. The `Antitone`
condition is only an indexing convention for the retained nonzero summands, and
therefore permits equal-modulus blocks. -/
structure HasOrderedNonzeroWeights {r : ℕ} (μ : Fin r → ℂ) : Prop where
  /-- Non-increasing ordering of the retained block weights by modulus. -/
  mu_antitone : Antitone (fun k : Fin r => ‖μ k‖)
  /-- No block weight vanishes. -/
  mu_ne_zero : ∀ k, μ k ≠ 0

/-- Self-overlap normalization for each block: `mpvOverlap (A k) (A k) N → 1`. -/
structure HasNormalizedSelfOverlap {r : ℕ} {dim : Fin r → ℕ}
    (A : (k : Fin r) → MPSTensor d (dim k)) : Prop where
  /-- Literature-normalized aperiodicity / overlap normalization. -/
  overlap_tendsto_one :
    ∀ k,
      Filter.Tendsto (fun N => mpvOverlap (d := d) (A k) (A k) N)
        Filter.atTop (nhds (1 : ℂ))

namespace HasNormalizedSelfOverlap

variable {r : ℕ} {dim : Fin r → ℕ}
variable {A : (k : Fin r) → MPSTensor d (dim k)}

/-- Build `HasNormalizedSelfOverlap` from pointwise self-overlap convergence. -/
theorem ofForall
    (hA : ∀ k,
      Filter.Tendsto (fun N => mpvOverlap (d := d) (A k) (A k) N)
        Filter.atTop (nhds (1 : ℂ))) :
    HasNormalizedSelfOverlap (d := d) A where
  overlap_tendsto_one := hA

end HasNormalizedSelfOverlap

/-! ### Canonical form conditions -/

/-- Canonical-form conditions combining injectivity, positive bond dimensions,
left-canonical normalization `∑ᵢ Aᵢ† Aᵢ = I`, non-increasing weights `μₖ`,
and overlap normalization.

Source context: arXiv:1606.00608, eq. `II_CF1` and lines 237--246, and
arXiv:2011.12127, lines 1831--1836. The weight ordering is `Antitone`
(non-increasing by modulus), matching the source convention that allows blocks with equal moduli.
The full CPSV predicate `IsBNTCanonicalForm` carries sector multiplicities and likewise does not
require strict ordering. -/
structure IsCanonicalForm {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k)) : Prop where
  /-- Each block is algebraically injective (`span (range (A k)) = ⊤`). -/
  block_injective : ∀ k, Kraus.IsInjective (A k)
  /-- Left-canonical normalization: `∑ᵢ Aᵢ† Aᵢ = I`. -/
  leftCanonical : ∀ k, ∑ i : Fin d, (A k i)ᴴ * (A k i) = 1
  /-- Non-increasing ordering of the block weights by modulus. -/
  mu_antitone : Antitone (fun k : Fin r => ‖μ k‖)
  /-- No block weight vanishes. -/
  mu_ne_zero : ∀ k, μ k ≠ 0
  /-- Every normal block has positive bond-space dimension.

  This positivity is implicit in the normal-block decomposition of CPSV16,
  equation `II_CF1`, lines 238--243. -/
  dim_pos : ∀ k, 0 < dim k
  /-- **Aperiodicity / overlap normalization**: the MPV self-overlap converges to `1`.

  In the normal-canonical-form formulation this conclusion is derived from irreducibility,
  left-canonical normalization, and peripheral-spectrum primitivity via
  `MPSTensor.overlap_tendsto_one_of_peripheralPrimitive_of_irreducible`. -/
  overlap_tendsto_one :
    ∀ k,
      Filter.Tendsto (fun N => mpvOverlap (d := d) (A k) (A k) N)
        Filter.atTop (nhds (1 : ℂ))

namespace IsCanonicalForm

variable {r : ℕ} {dim : Fin r → ℕ}
variable {μ : Fin r → ℂ} {A : (k : Fin r) → MPSTensor d (dim k)}

/-- **Canonical form from primitive injective blocks.**

Source context: arXiv:1606.00608, Section II.C and eq. II_CF1.
The algebraic canonical-form clauses are supplied as hypotheses. The self-overlap
clause follows from peripheral primitivity of each left-canonical injective block
via the spectral gap of the complementary transfer map. -/
theorem of_peripheral_primitive
    (hInj : ∀ k, Kraus.IsInjective (A k))
    (hLeft : ∀ k, ∑ i : Fin d, (A k i)ᴴ * (A k i) = 1)
    (hμ_antitone : Antitone (fun k : Fin r => ‖μ k‖))
    (hμ_ne_zero : ∀ k, μ k ≠ 0)
    (hDim : ∀ k, 0 < dim k)
    (hPrim : ∀ k, _root_.IsPrimitive (Kraus.transferMap (ι := Fin d) (n := Fin (dim k)) (A k))) :
    IsCanonicalForm μ A := by
  refine ⟨hInj, hLeft, hμ_antitone, hμ_ne_zero, hDim, ?_⟩
  intro k
  let : NeZero (dim k) := ⟨Nat.ne_of_gt (hDim k)⟩
  exact
    MPSTensor.overlap_tendsto_one_of_peripheralPrimitive_of_irreducible
      (A := A k) (MPSTensor.irreducibleTensor_of_injective (A k) (hInj k))
      (hLeft k) (hPrim k)

end IsCanonicalForm

/-! ### Normal canonical form conditions -/

/-- Normal-canonical-form conditions: each block is irreducible, left-canonical, and
peripheral-spectrum primitive, with non-increasing nonzero weights and positive bond dimensions.

Source context: arXiv:1606.00608, lines 233--246 and eq. `II_CF1`, and
arXiv:2011.12127, lines 1828--1836. This is the weaker “normal tensor” block notion:
each block is irreducible and its transfer map has peripheral spectrum `{1}`.
The weight ordering is `Antitone` (non-increasing by modulus), matching the paper
definitions which allow blocks with equal moduli. The BNT-level predicate
`IsNormalCanonicalFormBNT` adds only gauge-phase separation of distinct blocks;
it does not impose strict modulus ordering either.

The irreducibility field is stored separately on purpose: the repository's peripheral-spectrum
primitive condition does not by itself imply irreducibility for arbitrary transfer maps.
The self-overlap normalization is intended to be derived from primitivity rather than stored as a
field. -/
structure IsNormalCanonicalForm {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k)) : Prop where
  /-- Each block is irreducible in the invariant-projection sense. -/
  block_irreducible : ∀ k, Kraus.IsIrreducibleFamily (A k)
  /-- Left-canonical normalization: `∑ᵢ Aᵢ† Aᵢ = I`. -/
  leftCanonical : ∀ k, ∑ i : Fin d, (A k i)ᴴ * (A k i) = 1
  /-- Each block transfer map is primitive in the peripheral-spectrum sense. -/
  block_primitive : ∀ k,
    _root_.IsPrimitive (Kraus.transferMap (ι := Fin d) (n := Fin (dim k)) (A k))
  /-- Non-increasing ordering of the block weights by modulus. -/
  mu_antitone : Antitone (fun k : Fin r => ‖μ k‖)
  /-- No block weight vanishes. -/
  mu_ne_zero : ∀ k, μ k ≠ 0
  /-- All block bond dimensions are positive. -/
  dim_pos : ∀ k, 0 < dim k

namespace IsNormalCanonicalForm

variable {r : ℕ} {dim : Fin r → ℕ}
variable {μ : Fin r → ℂ} {A : (k : Fin r) → MPSTensor d (dim k)}

/-- The normal-canonical-form conditions imply blockwise irreducibility data. -/
theorem toHasIrreducibleBlocks (hNCF : IsNormalCanonicalForm μ A) :
    HasIrreducibleBlocks (d := d) A :=
  HasIrreducibleBlocks.ofForall hNCF.block_irreducible

/-- The normal-canonical-form conditions imply left-canonical block-family normalization. -/
theorem toIsLeftCanonicalBlockFamily (hNCF : IsNormalCanonicalForm μ A) :
    IsLeftCanonicalBlockFamily (d := d) A :=
  IsLeftCanonicalBlockFamily.ofForall hNCF.leftCanonical

/-- The additive split conditions imply `IsNormalCanonicalForm` with non-strict ordering. -/
theorem ofSeparatedData
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hPrim : HasPrimitiveBlocks (d := d) A)
    (hμ : HasOrderedNonzeroWeights μ)
    (hDim : ∀ k, 0 < dim k) :
    IsNormalCanonicalForm μ A where
  block_irreducible := hIrr.block_irreducible
  leftCanonical := hLeft.leftCanonical
  block_primitive := hPrim.block_primitive
  mu_antitone := hμ.mu_antitone
  mu_ne_zero := hμ.mu_ne_zero
  dim_pos := hDim

/-- In a normal canonical form, each block's self-overlap converges to `1`.

This is a direct re-use of
`MPSTensor.overlap_tendsto_one_of_peripheralPrimitive_of_irreducible`. -/
theorem overlap_tendsto_one
    (hNCF : IsNormalCanonicalForm μ A) (k : Fin r) :
    Filter.Tendsto (fun N => mpvOverlap (d := d) (A k) (A k) N)
      Filter.atTop (nhds (1 : ℂ)) := by
  let : NeZero (dim k) := ⟨Nat.ne_of_gt (hNCF.dim_pos k)⟩
  simpa using
    MPSTensor.overlap_tendsto_one_of_peripheralPrimitive_of_irreducible
      (A := A k)
      (hIrr := hNCF.block_irreducible k)
      (hNorm := hNCF.leftCanonical k)
      (hPrim := hNCF.block_primitive k)

end IsNormalCanonicalForm


end MPSTensor

end BlockFamily

section NormalCanonicalForm

/-!
## Normal canonical form from primitive weighted block decompositions

This module treats the part of the reduction that starts from a weighted family
of irreducible, left-canonical, primitive blocks with nonzero weights and
produces blocked normal canonical-form data, ordered non-increasingly by weight
modulus.

The supporting private declarations show that the present development already
has a common blocking at length `p = 1` and that the block family can be
reordered by decreasing weight norm before the final normal-form statement.
-/

open Kraus (blockPhysDim singleBlockEquiv blockTensor)

namespace MPSTensor

variable {d D : ℕ}

private theorem isIrreducibleFamily_blockTensor_one
    (A : MPSTensor d D) (hIrr : Kraus.IsIrreducibleFamily A) :
    Kraus.IsIrreducibleFamily (d := blockPhysDim d 1) (D := D)
      (blockTensor (d := d) (n := Fin D) A 1) := by
  intro hHas
  apply hIrr
  rcases hHas with ⟨P, hPproj, hP0, hP1, hLower⟩
  refine ⟨P, hPproj, hP0, hP1, ?_⟩
  intro j
  simpa using hLower ((singleBlockEquiv d).symm j)

private theorem leftCanonical_blockTensor_one
    (A : MPSTensor d D)
    (hLeft : ∑ i : Fin d, (A i)ᴴ * A i = 1) :
    ∑ i : Fin (blockPhysDim d 1),
      (blockTensor (d := d) (n := Fin D) A 1 i)ᴴ *
        blockTensor (d := d) (n := Fin D) A 1 i = 1 := by
  simpa using leftCanonical_blockTensor (d := d) (D := D) (A := A) (L := 1) hLeft

/-- A primitive weighted block family is already in common blocking length `p = 1`. -/
private theorem common_blocking_primitive
    (A : MPSTensor d D)
    {r1 : ℕ} {dim1 : Fin r1 → ℕ}
    (μ1 : Fin r1 → ℂ)
    (blocks1 : (k : Fin r1) → MPSTensor d (dim1 k))
    (hSame1 :
      SameMPV₂ A
        (toTensorFromBlocks (d := d) (μ := μ1) blocks1))
    (hIrr1 : ∀ k, Kraus.IsIrreducibleFamily (blocks1 k))
    (hLeft1 : ∀ k, ∑ i : Fin d, (blocks1 k i)ᴴ * blocks1 k i = 1)
    (hPrim1 : ∀ k,
      _root_.IsPrimitive
        (Kraus.transferMap (ι := Fin d) (n := Fin (dim1 k)) (blocks1 k)))
    (hμne1 : ∀ k, μ1 k ≠ 0)
    (hDim1 : ∀ k, 0 < dim1 k) :
    ∃ p : ℕ, 0 < p ∧
      ∃ r2 : ℕ,
      ∃ dim2 : Fin r2 → ℕ,
      ∃ μ2 : Fin r2 → ℂ,
      ∃ blocks2 : (k : Fin r2) → MPSTensor (blockPhysDim d p) (dim2 k),
        SameMPV₂
          (blockTensor (d := d) (n := Fin D) A p)
          (toTensorFromBlocks (d := blockPhysDim d p) (μ := μ2) blocks2) ∧
        (∀ k, Kraus.IsIrreducibleFamily (blocks2 k)) ∧
        (∀ k, ∑ i : Fin (blockPhysDim d p), (blocks2 k i)ᴴ * blocks2 k i = 1) ∧
        (∀ k,
          _root_.IsPrimitive
            (Kraus.transferMap (ι := Fin (blockPhysDim d p)) (n := Fin (dim2 k)) (blocks2 k))) ∧
        (∀ k, μ2 k ≠ 0) ∧
        (∀ k, 0 < dim2 k) := by
  refine ⟨1, Nat.one_pos, r1, dim1, μ1,
    (fun k => blockTensor (d := d) (n := Fin (dim1 k)) (blocks1 k) 1), ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N σ
    let σ' : Fin N → Fin d := fun n => singleBlockEquiv d (σ n)
    calc
      mpv (blockTensor (d := d) (n := Fin D) A 1) σ = mpv A σ' :=
        mpv_blockTensor_one (d := d) (D := D) (A := A) σ
      _ = mpv (toTensorFromBlocks (d := d) (μ := μ1) blocks1) σ' := hSame1 N σ'
      _ = ∑ k : Fin r1, (μ1 k) ^ N * mpv (blocks1 k) σ' := by
            simpa [smul_eq_mul] using
              (mpv_toTensorFromBlocks_eq_sum (d := d) (μ := μ1) (A := blocks1) (σ := σ'))
      _ = ∑ k : Fin r1, (μ1 k) ^ N *
            mpv (blockTensor (d := d) (n := Fin (dim1 k)) (blocks1 k) 1) σ := by
            refine Finset.sum_congr rfl ?_
            intro k _
            rw [mpv_blockTensor_one (d := d) (D := dim1 k) (A := blocks1 k) (σ := σ)]
      _ = mpv (toTensorFromBlocks
            (d := blockPhysDim d 1)
            (μ := μ1)
            (fun k => blockTensor (d := d) (n := Fin (dim1 k)) (blocks1 k) 1)) σ := by
            symm
            simpa [smul_eq_mul] using
              (mpv_toTensorFromBlocks_eq_sum
                (d := blockPhysDim d 1)
                (μ := μ1)
                (A := fun k => blockTensor (d := d) (n := Fin (dim1 k)) (blocks1 k) 1)
                (σ := σ))
  · intro k
    exact isIrreducibleFamily_blockTensor_one (d := d) (D := dim1 k) (A := blocks1 k) (hIrr1 k)
  · intro k
    exact leftCanonical_blockTensor_one (d := d) (D := dim1 k) (A := blocks1 k) (hLeft1 k)
  · intro k
    simpa [MPSTensor.transferMap_blockTensor (A := blocks1 k) (L := 1)] using hPrim1 k
  · exact hμne1
  · exact hDim1

/-- Sort a primitive weighted block family by decreasing weight norm. -/
private theorem sort_blocks_by_weight_norm
    {p Dblk : ℕ}
    (Ablk : MPSTensor (blockPhysDim d p) Dblk)
    {r2 : ℕ} {dim2 : Fin r2 → ℕ}
    (μ2 : Fin r2 → ℂ)
    (blocks2 : (k : Fin r2) → MPSTensor (blockPhysDim d p) (dim2 k))
    (hSame2 :
      SameMPV₂ Ablk
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μ2) blocks2))
    (hIrr2 : ∀ k, Kraus.IsIrreducibleFamily (blocks2 k))
    (hLeft2 : ∀ k, ∑ i : Fin (blockPhysDim d p), (blocks2 k i)ᴴ * blocks2 k i = 1)
    (hPrim2 : ∀ k,
      _root_.IsPrimitive
        (Kraus.transferMap (ι := Fin (blockPhysDim d p)) (n := Fin (dim2 k)) (blocks2 k)))
    (hμne2 : ∀ k, μ2 k ≠ 0)
    (hDim2 : ∀ k, 0 < dim2 k) :
    ∃ r : ℕ,
      ∃ dim : Fin r → ℕ,
      ∃ μ : Fin r → ℂ,
      ∃ blocks : (k : Fin r) → MPSTensor (blockPhysDim d p) (dim k),
        SameMPV₂ Ablk
          (toTensorFromBlocks (d := blockPhysDim d p) (μ := μ) blocks) ∧
        (∀ k, Kraus.IsIrreducibleFamily (blocks k)) ∧
        (∀ k, ∑ i : Fin (blockPhysDim d p), (blocks k i)ᴴ * blocks k i = 1) ∧
        (∀ k,
          _root_.IsPrimitive
            (Kraus.transferMap (ι := Fin (blockPhysDim d p)) (n := Fin (dim k)) (blocks k))) ∧
        Antitone (fun k : Fin r => ‖μ k‖) ∧
        (∀ k, μ k ≠ 0) ∧
        (∀ k, 0 < dim k) := by
  classical
  -- Reorder the blocks into non-increasing weight modulus, with ties allowed:
  -- sort ascending by `‖μ2 ·‖` and reverse.  No distinctness of the moduli is
  -- needed, so equal-modulus blocks are permitted.
  let f : Fin r2 → ℝ := fun k => ‖μ2 k‖
  let e : Fin r2 ≃ Fin r2 := Fin.revPerm.trans (Tuple.sort f)
  have he : ∀ i, e i = (Tuple.sort f) (Fin.rev i) := by
    intro i; simp [e, Equiv.trans_apply, Fin.revPerm_apply]
  let dim : Fin r2 → ℕ := fun i => dim2 (e i)
  let μ : Fin r2 → ℂ := fun i => μ2 (e i)
  let blocks : (k : Fin r2) → MPSTensor (blockPhysDim d p) (dim k) :=
    fun i => blocks2 (e i)
  refine ⟨r2, dim, μ, blocks, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N σ
    calc
      mpv Ablk σ
          = mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μ2) blocks2) σ := hSame2 N σ
      _ = ∑ k : Fin r2, (μ2 k) ^ N * mpv (blocks2 k) σ := by
            simpa [smul_eq_mul] using
              (mpv_toTensorFromBlocks_eq_sum
                (d := blockPhysDim d p) (μ := μ2) (A := blocks2) (σ := σ))
      _ = ∑ i : Fin r2, (μ2 (e i)) ^ N * mpv (blocks2 (e i)) σ := by
            symm
            simpa using (e.sum_comp (fun k : Fin r2 => (μ2 k) ^ N * mpv (blocks2 k) σ))
      _ = mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μ) blocks) σ := by
            symm
            simpa [μ, blocks, smul_eq_mul] using
              (mpv_toTensorFromBlocks_eq_sum
                (d := blockPhysDim d p) (μ := μ) (A := blocks) (σ := σ))
  · intro i
    exact hIrr2 (e i)
  · intro i
    exact hLeft2 (e i)
  · intro i
    exact hPrim2 (e i)
  · -- Non-increasing moduli: the ascending sort composed with the antitone reversal.
    have hmono : Monotone (f ∘ ⇑(Tuple.sort f)) := Tuple.monotone_sort f
    have hrev : Antitone (Fin.rev : Fin r2 → Fin r2) := Fin.rev_strictAnti.antitone
    have hanti : Antitone (fun i : Fin r2 => f (e i)) := by
      have hcomp : (fun i : Fin r2 => f (e i))
          = (f ∘ ⇑(Tuple.sort f)) ∘ (Fin.rev : Fin r2 → Fin r2) := by
        funext i; simp [he, Function.comp]
      rw [hcomp]
      exact hmono.comp_antitone hrev
    simpa [μ, f] using hanti
  · intro i
    exact hμne2 (e i)
  · intro i
    exact hDim2 (e i)

/-- Collect a primitive weighted block family into separated blocked data for
`IsNormalCanonicalForm`. -/
private theorem exists_blocked_normal_data_of_primitive_blockDecomp
    (A : MPSTensor d D)
    {r1 : ℕ} {dim1 : Fin r1 → ℕ}
    (μ1 : Fin r1 → ℂ)
    (blocks1 : (k : Fin r1) → MPSTensor d (dim1 k))
    (hSame1 :
      SameMPV₂ A
        (toTensorFromBlocks (d := d) (μ := μ1) blocks1))
    (hIrr1 : ∀ k, Kraus.IsIrreducibleFamily (blocks1 k))
    (hLeft1 : ∀ k, ∑ i : Fin d, (blocks1 k i)ᴴ * blocks1 k i = 1)
    (hPrim1 : ∀ k,
      _root_.IsPrimitive
        (Kraus.transferMap (ι := Fin d) (n := Fin (dim1 k)) (blocks1 k)))
    (hμne1 : ∀ k, μ1 k ≠ 0)
    (hDim1 : ∀ k, 0 < dim1 k) :
    ∃ p : ℕ, 0 < p ∧
      ∃ r : ℕ,
      ∃ dim : Fin r → ℕ,
      ∃ μ : Fin r → ℂ,
      ∃ blocks : (k : Fin r) → MPSTensor (blockPhysDim d p) (dim k),
        SameMPV₂
          (blockTensor (d := d) (n := Fin D) A p)
          (toTensorFromBlocks (d := blockPhysDim d p) (μ := μ) blocks) ∧
        (∀ k, Kraus.IsIrreducibleFamily (blocks k)) ∧
        (∀ k, ∑ i : Fin (blockPhysDim d p), (blocks k i)ᴴ * blocks k i = 1) ∧
        (∀ k,
          _root_.IsPrimitive
            (Kraus.transferMap (ι := Fin (blockPhysDim d p)) (n := Fin (dim k)) (blocks k))) ∧
        Antitone (fun k : Fin r => ‖μ k‖) ∧
        (∀ k, μ k ≠ 0) ∧
        (∀ k, 0 < dim k) := by
  obtain ⟨p, hp, r2, dim2, μ2, blocks2, hSame2, hIrr2, hLeft2, hPrim2, hμne2,
      hDim2⟩ :=
    common_blocking_primitive
      (A := A) (r1 := r1) (dim1 := dim1) (μ1 := μ1) blocks1
      hSame1 hIrr1 hLeft1 hPrim1 hμne1 hDim1
  obtain ⟨r, dim, μ, blocks, hSame, hIrr, hLeft, hPrim, hμanti, hμne, hDim⟩ :=
    sort_blocks_by_weight_norm
      (d := d)
      (p := p)
      (Ablk := blockTensor (d := d) (n := Fin D) A p)
      (r2 := r2) (dim2 := dim2) (μ2 := μ2) blocks2
      hSame2 hIrr2 hLeft2 hPrim2 hμne2 hDim2
  exact ⟨p, hp, r, dim, μ, blocks, hSame, hIrr, hLeft, hPrim, hμanti, hμne, hDim⟩

/-- A primitive weighted block decomposition admits a blocked normal canonical form.

Hypotheses:

* `A` is `SameMPV₂`-equivalent to the weighted block tensor `toTensorFromBlocks μ1 blocks1`;
* each block `blocks1 k` is irreducible;
* each block is left-canonical: `∑ i, (blocks1 k i)ᴴ * blocks1 k i = 1`;
* each block transfer map is primitive;
* each weight `μ1 k` is nonzero;
* each bond dimension `dim1 k` is positive.

Conclusion: after a common blocking (currently `p = 1`) and reordering by
non-increasing weight modulus (ties allowed),
`blockTensor A p` is `SameMPV₂`-equivalent to a weighted block family in
`IsNormalCanonicalForm`.

Source context: Perez-Garcia--Verstraete--Wolf--Cirac 2007,
Theorem Th:TIcanonical, lines 742--763, starts from an arbitrary
translation-invariant MPS representation. Its proof first performs the
fixed-point gauge and invariant-support splitting of lines 765--826, then
the dual fixed-point diagonalization of lines 827--832.

**Scope restriction (prepared primitive block decomposition):** This theorem
assumes an existing weighted block decomposition, irreducibility,
trace-preserving normalization, primitivity, nonzero weights, and positive bond
dimensions. The cited source theorem starts from an arbitrary
translation-invariant MPS representation and derives these structures; see
`docs/paper-gaps/pgvwc07_ti_canonical_form_scope.tex`. -/
theorem exists_normalCanonicalForm_of_primitive_blockDecomp
    (A : MPSTensor d D)
    {r1 : ℕ} {dim1 : Fin r1 → ℕ}
    (μ1 : Fin r1 → ℂ)
    (blocks1 : (k : Fin r1) → MPSTensor d (dim1 k))
    (hSame1 :
      SameMPV₂ A
        (toTensorFromBlocks (d := d) (μ := μ1) blocks1))
    (hIrr1 : ∀ k, Kraus.IsIrreducibleFamily (blocks1 k))
    (hLeft1 : ∀ k, ∑ i : Fin d, (blocks1 k i)ᴴ * blocks1 k i = 1)
    (hPrim1 : ∀ k,
      _root_.IsPrimitive
        (Kraus.transferMap (ι := Fin d) (n := Fin (dim1 k)) (blocks1 k)))
    (hμne1 : ∀ k, μ1 k ≠ 0)
    (hDim1 : ∀ k, 0 < dim1 k) :
    ∃ p : ℕ, 0 < p ∧
      ∃ r : ℕ,
      ∃ dim : Fin r → ℕ,
      ∃ μ : Fin r → ℂ,
      ∃ blocks : (k : Fin r) → MPSTensor (blockPhysDim d p) (dim k),
        SameMPV₂
          (blockTensor (d := d) (n := Fin D) A p)
          (toTensorFromBlocks (d := blockPhysDim d p) (μ := μ) blocks) ∧
        IsNormalCanonicalForm (d := blockPhysDim d p) μ blocks := by
  obtain ⟨p, hp, r, dim, μ, blocks, hSame, hIrr, hLeft, hPrim, hμanti, hμne, hDim⟩ :=
    exists_blocked_normal_data_of_primitive_blockDecomp
      (A := A) (r1 := r1) (dim1 := dim1) (μ1 := μ1) blocks1
      hSame1 hIrr1 hLeft1 hPrim1 hμne1 hDim1
  refine ⟨p, hp, r, dim, μ, blocks, hSame, ?_⟩
  let hμ : HasOrderedNonzeroWeights μ := {
    mu_antitone := hμanti
    mu_ne_zero := hμne
  }
  exact
    IsNormalCanonicalForm.ofSeparatedData
      (d := blockPhysDim d p)
      (A := blocks)
      (μ := μ)
      (HasIrreducibleBlocks.ofForall hIrr)
      (IsLeftCanonicalBlockFamily.ofForall hLeft)
      (HasPrimitiveBlocks.ofForall hPrim)
      hμ
      hDim


end MPSTensor

end NormalCanonicalForm
