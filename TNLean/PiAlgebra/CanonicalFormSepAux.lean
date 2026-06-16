/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Core.RepeatedWord
import TNLean.PiAlgebra.FundamentalTheoremComplete
import TNLean.Algebra.MatrixAux
import TNLean.Spectral.TransferOperatorGap
import TNLean.Spectral.TransferOperatorGapNT
import TNLean.Spectral.MPVOverlapDecay
import TNLean.Spectral.PrimitiveOverlap
import TNLean.QPF.Assembly
import TNLean.MPS.CanonicalForm.Reduction
import TNLean.MPS.FundamentalTheorem.Proportional
import TNLean.MPS.Irreducible.FormII
import TNLean.MPS.Overlap.PeripheralToTransferMapGap
import TNLean.Channel.Peripheral.Spectrum
import Mathlib.Analysis.Complex.Basic

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
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open scoped Matrix BigOperators

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
  block_injective : ∀ k, IsInjective (A k)

namespace HasInjectiveBlocks

variable {r : ℕ} {dim : Fin r → ℕ}
variable {A : (k : Fin r) → MPSTensor d (dim k)}

/-- Build `HasInjectiveBlocks` from pointwise injectivity. -/
def ofForall (hA : ∀ k, IsInjective (A k)) : HasInjectiveBlocks (d := d) A where
  block_injective := hA

end HasInjectiveBlocks

/-- Each block in the family is irreducible in the invariant-projection sense. -/
structure HasIrreducibleBlocks {r : ℕ} {dim : Fin r → ℕ}
    (A : (k : Fin r) → MPSTensor d (dim k)) : Prop where
  /-- Each block has no nontrivial invariant orthogonal projection. -/
  block_irreducible : ∀ k, IsIrreducibleTensor (A k)

namespace HasIrreducibleBlocks

variable {r : ℕ} {dim : Fin r → ℕ}
variable {A : (k : Fin r) → MPSTensor d (dim k)}

/-- Build `HasIrreducibleBlocks` from pointwise irreducibility. -/
def ofForall (hA : ∀ k, IsIrreducibleTensor (A k)) : HasIrreducibleBlocks (d := d) A where
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
    _root_.IsPrimitive (transferMap (d := d) (D := dim k) (A k))

namespace HasPrimitiveBlocks

variable {r : ℕ} {dim : Fin r → ℕ}
variable {A : (k : Fin r) → MPSTensor d (dim k)}

/-- Build `HasPrimitiveBlocks` from pointwise peripheral primitivity. -/
def ofForall (hA : ∀ k, _root_.IsPrimitive (transferMap (d := d) (D := dim k) (A k))) :
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
def ofForall (hA : ∀ k, ∑ i : Fin d, (A k i)ᴴ * (A k i) = 1) :
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
def ofForall
    (hA : ∀ k,
      Filter.Tendsto (fun N => mpvOverlap (d := d) (A k) (A k) N)
        Filter.atTop (nhds (1 : ℂ))) :
    HasNormalizedSelfOverlap (d := d) A where
  overlap_tendsto_one := hA

end HasNormalizedSelfOverlap

/-! ### Canonical form conditions -/

/-- Canonical-form conditions combining injectivity, left-canonical normalization
`∑ᵢ Aᵢ† Aᵢ = I`, non-increasing weight data, and overlap normalization.

Source context: arXiv:1606.00608, eq. `II_CF1` and lines 237--246, and
arXiv:2011.12127, lines 1831--1836. The weight ordering is `Antitone`
(non-increasing by modulus), matching the source convention that allows blocks with equal moduli.
The full CPSV predicate `IsBNTCanonicalForm` carries sector multiplicities and likewise does not
require strict ordering. -/
structure IsCanonicalForm {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k)) : Prop where
  /-- Each block is algebraically injective (`span (range (A k)) = ⊤`). -/
  block_injective : ∀ k, IsInjective (A k)
  /-- Left-canonical normalization: `∑ᵢ Aᵢ† Aᵢ = I`. -/
  leftCanonical : ∀ k, ∑ i : Fin d, (A k i)ᴴ * (A k i) = 1
  /-- Non-increasing ordering of the block weights by modulus. -/
  mu_antitone : Antitone (fun k : Fin r => ‖μ k‖)
  /-- No block weight vanishes. -/
  mu_ne_zero : ∀ k, μ k ≠ 0
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
The first four canonical-form clauses are supplied as hypotheses. The
self-overlap clause follows from peripheral primitivity of each left-canonical
injective block via the spectral gap of the complementary transfer map. -/
theorem of_peripheral_primitive
    (hInj : ∀ k, IsInjective (A k))
    (hLeft : ∀ k, ∑ i : Fin d, (A k i)ᴴ * (A k i) = 1)
    (hμ_antitone : Antitone (fun k : Fin r => ‖μ k‖))
    (hμ_ne_zero : ∀ k, μ k ≠ 0)
    (hDim : ∀ k, 0 < dim k)
    (hPrim : ∀ k, _root_.IsPrimitive (transferMap (d := d) (D := dim k) (A k))) :
    IsCanonicalForm μ A := by
  refine ⟨hInj, hLeft, hμ_antitone, hμ_ne_zero, ?_⟩
  intro k
  letI : NeZero (dim k) := ⟨Nat.ne_of_gt (hDim k)⟩
  exact
    MPSTensor.overlap_tendsto_one_of_peripheralPrimitive
      (A := A k) (hInj k) (hLeft k) (hPrim k)

/-- The canonical-form conditions imply blockwise injectivity data. -/
def toHasInjectiveBlocks (hCF : IsCanonicalForm μ A) : HasInjectiveBlocks (d := d) A :=
  HasInjectiveBlocks.ofForall hCF.block_injective

/-- The canonical-form conditions imply left-canonical block-family normalization. -/
def toIsLeftCanonicalBlockFamily (hCF : IsCanonicalForm μ A) :
    IsLeftCanonicalBlockFamily (d := d) A :=
  IsLeftCanonicalBlockFamily.ofForall hCF.leftCanonical

/-- The canonical-form conditions imply self-overlap normalization data. -/
def toHasNormalizedSelfOverlap (hCF : IsCanonicalForm μ A) :
    HasNormalizedSelfOverlap (d := d) A :=
  HasNormalizedSelfOverlap.ofForall hCF.overlap_tendsto_one

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
  block_irreducible : ∀ k, IsIrreducibleTensor (A k)
  /-- Left-canonical normalization: `∑ᵢ Aᵢ† Aᵢ = I`. -/
  leftCanonical : ∀ k, ∑ i : Fin d, (A k i)ᴴ * (A k i) = 1
  /-- Each block transfer map is primitive in the peripheral-spectrum sense. -/
  block_primitive : ∀ k,
    _root_.IsPrimitive (transferMap (d := d) (D := dim k) (A k))
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
def toHasIrreducibleBlocks (hNCF : IsNormalCanonicalForm μ A) :
    HasIrreducibleBlocks (d := d) A :=
  HasIrreducibleBlocks.ofForall hNCF.block_irreducible

/-- The normal-canonical-form conditions imply left-canonical block-family normalization. -/
def toIsLeftCanonicalBlockFamily (hNCF : IsNormalCanonicalForm μ A) :
    IsLeftCanonicalBlockFamily (d := d) A :=
  IsLeftCanonicalBlockFamily.ofForall hNCF.leftCanonical

/-- The normal-canonical-form conditions imply blockwise peripheral primitivity data. -/
def toHasPrimitiveBlocks (hNCF : IsNormalCanonicalForm μ A) :
    HasPrimitiveBlocks (d := d) A :=
  HasPrimitiveBlocks.ofForall hNCF.block_primitive

/-- The additive split conditions imply `IsNormalCanonicalForm` with non-strict ordering. -/
def ofSeparatedData
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
  letI : NeZero (dim k) := ⟨Nat.ne_of_gt (hNCF.dim_pos k)⟩
  simpa using
    MPSTensor.overlap_tendsto_one_of_peripheralPrimitive_of_irreducible
      (A := A k)
      (hIrr := hNCF.block_irreducible k)
      (hNorm := hNCF.leftCanonical k)
      (hPrim := hNCF.block_primitive k)

/-- Project normal-canonical-form data to the overlap-normalization interface used by the
existing separated FT statements. -/
def toHasNormalizedSelfOverlap
    (hNCF : IsNormalCanonicalForm μ A) :
    HasNormalizedSelfOverlap (d := d) A :=
  HasNormalizedSelfOverlap.ofForall hNCF.overlap_tendsto_one

end IsNormalCanonicalForm


end MPSTensor
