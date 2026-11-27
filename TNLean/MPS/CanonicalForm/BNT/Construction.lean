/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Transfer.Spectrum.TransferOperatorGapInjective
import TNLean.MPS.Transfer.Spectrum.TransferOperatorGapNT
import TNLean.MPS.Transfer.Spectrum.GaugePhase
import TNLean.MPS.CanonicalForm.BNT.Separation
import TNLean.MPS.CanonicalForm.BNT.Basic
import TNLean.MPS.Tensor.Words.Basic
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
normalization. Statements take exactly these hypotheses, with weights in the
non-strict, ties-allowed order used in the reduction to canonical form.

## Main conditions

- Weight condition: `HasOrderedNonzeroWeights`. The blockwise conditions (injectivity,
  irreducibility, primitivity, left-canonical normalization, self-overlap normalization) are
  stated directly as `∀ k, P (A k)`.
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

/-! ### Separated canonical-form hypotheses

The blockwise hypotheses of the canonical-form predicates (injectivity, irreducibility,
peripheral primitivity, left-canonical normalization, and self-overlap normalization) are
written directly as `∀ k, P (A k)`; only the weight condition, which couples the ordering and
the nonvanishing of the weights, is recorded as a structure. The separated hypotheses let the
canonical-form reduction and the RFP/BNT projections expose only the assumptions used at each
step.
-/

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
    Kraus.IsIrreducibleFamily (ι := Fin (blockPhysDim d 1)) (n := Fin D)
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
  exact Kraus.IsTP.blockTensor (A := A) hLeft 1

/-- A primitive weighted block family is already in common blocking length `p = 1`. -/
private theorem common_blocking_primitive
    (A : MPSTensor d D)
    {r1 : ℕ} {dim1 : Fin r1 → ℕ}
    (μ1 : Fin r1 → ℂ)
    (blocks1 : (k : Fin r1) → MPSTensor d (dim1 k))
    (hSame1 :
      SameMPV₂ A
        (toTensorFromBlocks (α := Fin d) (μ := μ1) blocks1))
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
          (toTensorFromBlocks (α := Fin (blockPhysDim d p)) (μ := μ2) blocks2) ∧
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
      _ = mpv (toTensorFromBlocks (α := Fin d) (μ := μ1) blocks1) σ' := hSame1 N σ'
      _ = ∑ k : Fin r1, (μ1 k) ^ N * mpv (blocks1 k) σ' := by
            simpa [smul_eq_mul] using
              (mpv_toTensorFromBlocks_eq_sum (α := Fin d) (μ := μ1) (A := blocks1) (σ := σ'))
      _ = ∑ k : Fin r1, (μ1 k) ^ N *
            mpv (blockTensor (d := d) (n := Fin (dim1 k)) (blocks1 k) 1) σ := by
            refine Finset.sum_congr rfl ?_
            intro k _
            rw [mpv_blockTensor_one (d := d) (D := dim1 k) (A := blocks1 k) (σ := σ)]
      _ = mpv (toTensorFromBlocks
            (α := Fin (blockPhysDim d 1))
            (μ := μ1)
            (fun k => blockTensor (d := d) (n := Fin (dim1 k)) (blocks1 k) 1)) σ := by
            symm
            simpa [smul_eq_mul] using
              (mpv_toTensorFromBlocks_eq_sum
                (α := Fin (blockPhysDim d 1))
                (μ := μ1)
                (A := fun k => blockTensor (d := d) (n := Fin (dim1 k)) (blocks1 k) 1)
                (σ := σ))
  · intro k
    exact isIrreducibleFamily_blockTensor_one (d := d) (D := dim1 k) (A := blocks1 k) (hIrr1 k)
  · intro k
    exact leftCanonical_blockTensor_one (d := d) (D := dim1 k) (A := blocks1 k) (hLeft1 k)
  · intro k
    simpa [Kraus.transferMap_blockTensor (A := blocks1 k) (L := 1)] using hPrim1 k
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
        (toTensorFromBlocks (α := Fin (blockPhysDim d p)) (μ := μ2) blocks2))
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
          (toTensorFromBlocks (α := Fin (blockPhysDim d p)) (μ := μ) blocks) ∧
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
          = mpv (toTensorFromBlocks (α := Fin (blockPhysDim d p)) (μ := μ2) blocks2) σ := hSame2 N σ
      _ = ∑ k : Fin r2, (μ2 k) ^ N * mpv (blocks2 k) σ := by
            simpa [smul_eq_mul] using
              (mpv_toTensorFromBlocks_eq_sum
                (α := Fin (blockPhysDim d p)) (μ := μ2) (A := blocks2) (σ := σ))
      _ = ∑ i : Fin r2, (μ2 (e i)) ^ N * mpv (blocks2 (e i)) σ := by
            symm
            simpa using (e.sum_comp (fun k : Fin r2 => (μ2 k) ^ N * mpv (blocks2 k) σ))
      _ = mpv (toTensorFromBlocks (α := Fin (blockPhysDim d p)) (μ := μ) blocks) σ := by
            symm
            simpa [μ, blocks, smul_eq_mul] using
              (mpv_toTensorFromBlocks_eq_sum
                (α := Fin (blockPhysDim d p)) (μ := μ) (A := blocks) (σ := σ))
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

/-- Collect a primitive weighted block family into separated blocked normal data. -/
private theorem exists_blocked_normal_data_of_primitive_blockDecomp
    (A : MPSTensor d D)
    {r1 : ℕ} {dim1 : Fin r1 → ℕ}
    (μ1 : Fin r1 → ℂ)
    (blocks1 : (k : Fin r1) → MPSTensor d (dim1 k))
    (hSame1 :
      SameMPV₂ A
        (toTensorFromBlocks (α := Fin d) (μ := μ1) blocks1))
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
          (toTensorFromBlocks (α := Fin (blockPhysDim d p)) (μ := μ) blocks) ∧
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
`blockTensor A p` is `SameMPV₂`-equivalent to a weighted block family whose blocks
are irreducible, left-canonical and primitive (hence normal tensors), with nonzero
weights ordered by non-increasing modulus and positive bond dimensions.

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
        (toTensorFromBlocks (α := Fin d) (μ := μ1) blocks1))
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
          (toTensorFromBlocks (α := Fin (blockPhysDim d p)) (μ := μ) blocks) ∧
        (∀ k, Kraus.IsIrreducibleFamily (blocks k)) ∧
        (∀ k, ∑ i : Fin (blockPhysDim d p), (blocks k i)ᴴ * blocks k i = 1) ∧
        (∀ k,
          _root_.IsPrimitive
            (Kraus.transferMap (ι := Fin (blockPhysDim d p)) (n := Fin (dim k)) (blocks k))) ∧
        HasOrderedNonzeroWeights μ ∧
        (∀ k, 0 < dim k) := by
  obtain ⟨p, hp, r, dim, μ, blocks, hSame, hIrr, hLeft, hPrim, hμanti, hμne, hDim⟩ :=
    exists_blocked_normal_data_of_primitive_blockDecomp
      (A := A) (r1 := r1) (dim1 := dim1) (μ1 := μ1) blocks1
      hSame1 hIrr1 hLeft1 hPrim1 hμne1 hDim1
  exact ⟨p, hp, r, dim, μ, blocks, hSame, hIrr, hLeft, hPrim, ⟨hμanti, hμne⟩, hDim⟩


end MPSTensor

end NormalCanonicalForm

/-!
# Basis of normal tensors from separated block hypotheses

Separated blockwise hypotheses pass from canonical-form and
normal-canonical-form hypotheses to the basis-of-normal-tensors formulation.
The source BNT expansion in arXiv:1606.00608, Section II keeps repeated copies
inside a sector with coefficients `μ_{j,q}` and multiplicities `M_j`; that
paper-faithful sector structure is represented by `IsLeftCanonicalBNTPresentation` in the
fundamental-theorem files. The results here are auxiliary tools for already
separated finite block families.

## Main results

1. **`BlocksNotGaugePhaseEquiv`**: the separation condition asserting that distinct
   equal-dimension blocks are not gauge-phase equivalent.

2. **`cross_overlap_tendsto_zero_of_separated_bnt_data`**: separated injective
   left-canonical blocks have decaying cross-overlaps. The proof combines:
   - Dimension-mismatch case: `mpvOverlap_tendsto_zero_of_dim_ne`
   - Same-dimension case: `mpvOverlap_tendsto_zero` (using `blocks_not_equiv` to supply
     `¬GaugePhaseEquiv`)

3. **`exists_eventually_linearIndependent_of_overlap_tendsto_orthonormal`**: asymptotically
   orthonormal overlaps give eventual linear independence of the matrix product vectors.

4. **`cross_overlap_tendsto_zero_of_separated_normal_bnt_data`**: the same decay for
   separated irreducible left-canonical blocks. That normal tensors form a basis of normal
   tensors of their weighted direct sum exactly when they are gauge-phase separated is
   `isCPSVBasisOfNormalTensors_toTensorFromBlocks_iff` in
   `TNLean.MPS.CanonicalForm.NormalBlocks.NormalTensorGauge`.

## Design note on coefficients

In the full paper (arXiv:1606.00608, eq. decBSV), the decomposition into a basis of normal
tensors uses summed coefficients `c_j(N) = Σ_{q in group j} μ_{j,q}^N`.
The results below concern already separated one-representative block families
and do not perform the raw coefficient comparison for the two-layer BNT
decomposition. That comparison is carried out for sector decompositions, where
the sums `Σ_q μ_{j,q}^N` and their multiplicities remain visible.
-/

open MPTensor

open scoped Matrix BigOperators
open Filter

namespace MPSTensor

variable {d : ℕ}

/-- Distinct same-dimension blocks in a separated irreducible trace-preserving
family are not proportional at arbitrarily large chain lengths. -/
theorem exists_ge_not_forall_mpv_eq_mul_of_blocksNotGaugePhaseEquiv_of_irreducible_TP
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hIrr : ∀ k, Kraus.IsIrreducibleFamily (A k))
    (hLeft : ∀ k, ∑ i : Fin d, (A k i)ᴴ * (A k i) = 1)
    (hOverlap : ∀ k, Filter.Tendsto (fun N => mpvOverlap (α := Fin d) (A k) (A k) N)
      Filter.atTop (nhds (1 : ℂ)))
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    {j k : Fin r} (hjk : j ≠ k) (hdim : dim j = dim k) (Nmin : ℕ) :
    ∃ N : ℕ, Nmin ≤ N ∧
      ¬ ∃ c : ℂ, ∀ σ : Fin N → Fin d,
        mpv (cast (congr_arg (MPSTensor d) hdim) (A j)) σ = c * mpv (A k) σ := by
  have hA_self_cast :
      Tendsto
        (fun N =>
          mpvOverlap (α := Fin d) (cast (congr_arg (MPSTensor d) hdim) (A j))
            (cast (congr_arg (MPSTensor d) hdim) (A j)) N)
        atTop (nhds (1 : ℂ)) := by
    refine (hOverlap j).congr ?_
    intro N
    unfold mpvOverlap
    apply Finset.sum_congr rfl
    intro σ _
    rw [mpv_cast_dim hdim (A j) N σ]
  exact exists_ge_not_forall_mpv_eq_mul_of_not_gaugePhaseEquiv_of_irreducible_TP
    (cast (congr_arg (MPSTensor d) hdim) (A j)) (A k)
    ((isIrreducibleFamily_cast_dim hdim (A j)).mpr (hIrr j))
    (hIrr k)
    ((leftCanonical_cast_dim hdim (A j)).mpr (hLeft j))
    (hLeft k)
    hA_self_cast (hOverlap k)
    (hBlocks j k hjk hdim) Nmin

/-- **Existential BNT linear independence from asymptotic orthonormal overlaps.**

If the self-overlaps of a finite block family tend to `1` and the cross-overlaps
of distinct blocks tend to `0`, then the MPV states are linearly independent for
every sufficiently large system size.  This is the threshold form of
`eventually_linearIndependent_of_finite_overlap_tendsto_orthonormal`. -/
lemma exists_eventually_linearIndependent_of_overlap_tendsto_orthonormal
    {r : ℕ} {dim : Fin r → ℕ}
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hSelf : ∀ j,
      Tendsto (fun N => mpvOverlap (α := Fin d) (A j) (A j) N) atTop (nhds (1 : ℂ)))
    (hOff : ∀ i j, i ≠ j →
      Tendsto (fun N => mpvOverlap (α := Fin d) (A i) (A j) N) atTop (nhds (0 : ℂ))) :
    ∃ N0 : ℕ, ∀ N > N0,
      LinearIndependent ℂ (fun j : Fin r => mpvState (d := d) (A j) N) := by
  have hOrtho := eventually_linearIndependent_of_finite_overlap_tendsto_orthonormal A hSelf hOff
  rw [Filter.Eventually] at hOrtho
  obtain ⟨N0, hN0⟩ := Filter.mem_atTop_sets.mp hOrtho
  exact ⟨N0, fun N hN => hN0 N (le_of_lt hN)⟩

/-! ### Cross-overlap decay from separated BNT hypotheses -/

section SeparatedBNT

variable {r : ℕ} {dim : Fin r → ℕ}
variable {μ : Fin r → ℂ} {A : (k : Fin r) → MPSTensor d (dim k)}

/-- Separated-hypotheses version of BNT cross-overlap decay.

Only injectivity, left-canonical normalization, and the BNT non-equivalence assumption are used. -/
theorem cross_overlap_tendsto_zero_of_separated_bnt_data
    [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hInj : ∀ k, Kraus.IsInjective (A k))
    (hLeft : ∀ k, ∑ i : Fin d, (A k i)ᴴ * (A k i) = 1)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (j k : Fin r) (hjk : j ≠ k) :
    Tendsto (fun N => mpvOverlap (α := Fin d) (A j) (A k) N) atTop (nhds 0) := by
  by_cases hdim : dim j = dim k
  · exact mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left_of_irreducible_TP
      (hdim := hdim) (A := A j) (B := A k)
      (hA_irr := irreducibleTensor_of_injective (A j) (hInj j))
      (hB_irr := irreducibleTensor_of_injective (A k) (hInj k))
      (hA_norm := hLeft j)
      (hB_norm := hLeft k)
      (hNot := hBlocks j k hjk hdim)
  · exact mpvOverlap_tendsto_zero_of_dim_ne (A j) (A k)
      (hInj j)
      (hInj k)
      (hLeft j)
      (hLeft k)
      hdim

end SeparatedBNT

/-! ### Cross-overlap decay from separated normal BNT hypotheses -/

section SeparatedNormalBNT

variable {r : ℕ} {dim : Fin r → ℕ}
variable {A : (k : Fin r) → MPSTensor d (dim k)}

/-- Separated-hypotheses version of normal BNT cross-overlap decay.

Only irreducibility, left-canonical normalization, and the BNT non-equivalence
assumption are used. -/
theorem cross_overlap_tendsto_zero_of_separated_normal_bnt_data
    [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hIrr : ∀ k, Kraus.IsIrreducibleFamily (A k))
    (hLeft : ∀ k, ∑ i : Fin d, (A k i)ᴴ * (A k i) = 1)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (j k : Fin r) (hjk : j ≠ k) :
    Tendsto (fun N => mpvOverlap (α := Fin d) (A j) (A k) N) atTop (nhds 0) := by
  by_cases hdim : dim j = dim k
  · exact mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left_of_irreducible_TP
      (hdim := hdim) (A := A j) (B := A k)
      (hA_irr := hIrr j)
      (hB_irr := hIrr k)
      (hA_norm := hLeft j)
      (hB_norm := hLeft k)
      (hNot := hBlocks j k hjk hdim)
  · exact mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP (A j) (A k)
      (hIrr j)
      (hIrr k)
      (hLeft j)
      (hLeft k)
      hdim

end SeparatedNormalBNT

end MPSTensor
