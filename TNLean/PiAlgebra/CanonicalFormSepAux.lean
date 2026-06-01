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
# Separated canonical-form hypotheses — auxiliary definitions and lemmas

This file defines the additive split hypotheses for a weighted block family
(blockwise injectivity, irreducibility, primitive transfer maps, left-canonical
normalization, non-increasing nonzero weight moduli, and self-overlap
normalization) together with the canonical-form predicates they characterize,
used in the canonical-form reduction.

## Contents

- Additive split conditions: `HasInjectiveBlocks`, `HasIrreducibleBlocks`, `HasPrimitiveBlocks`,
  `IsLeftCanonicalBlockFamily`, `HasOrderedNonzeroWeights`,
  `HasNormalizedSelfOverlap`.
- Bundled conditions: `IsCanonicalForm`, `IsNormalCanonicalForm` with projections and
  the `ofSeparatedData` constructor.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.style.show false

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

/-! ### Normalization convention

The **left-canonical** normalization condition in this file is `∑ᵢ Aᵢ† Aᵢ = I`.
Equivalently, the associated transfer map is trace-preserving. We do **not** assume the separate
unital identity `∑ᵢ Aᵢ Aᵢ† = I`.
-/

/-! ### Additive split conditions for canonical-form hypotheses

The structures below isolate the separate hypotheses used in the block-separation
argument: injectivity, left-canonical normalization, weight ordering, and
self-overlap normalization. The bundled `IsCanonicalForm` predicate remains the
compact mathematical statement, while these records make the proofs expose only
the assumptions used at each step.
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

This is the weight-ordering condition matching the paper definitions
(PGVWC07, Cirac--Perez-Garcia--Schuch--Verstraete 2021): block weights are
non-increasing by modulus, but ties are permitted, so equal-modulus blocks are
allowed. -/
structure HasOrderedNonzeroWeights {r : ℕ} (μ : Fin r → ℂ) : Prop where
  /-- Non-increasing ordering of the block weights by modulus. -/
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

/-- Bundled canonical-form conditions combining injectivity, left-canonical normalization
`∑ᵢ Aᵢ† Aᵢ = I`, non-increasing weight data, and overlap normalization in a single proposition.

The weight ordering is `Antitone` (non-increasing by modulus), matching the paper definitions
(PGVWC07, Cirac--Perez-Garcia--Schuch--Verstraete 2021) which allow blocks with equal moduli.
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

/-- Project the bundled conditions to blockwise injectivity data. -/
def toHasInjectiveBlocks (hCF : IsCanonicalForm μ A) : HasInjectiveBlocks (d := d) A :=
  HasInjectiveBlocks.ofForall hCF.block_injective

/-- Project the bundled conditions to left-canonical block-family normalization. -/
def toIsLeftCanonicalBlockFamily (hCF : IsCanonicalForm μ A) :
    IsLeftCanonicalBlockFamily (d := d) A :=
  IsLeftCanonicalBlockFamily.ofForall hCF.leftCanonical

/-- Project the bundled conditions to self-overlap normalization data. -/
def toHasNormalizedSelfOverlap (hCF : IsCanonicalForm μ A) :
    HasNormalizedSelfOverlap (d := d) A :=
  HasNormalizedSelfOverlap.ofForall hCF.overlap_tendsto_one

end IsCanonicalForm

/-! ### Normal canonical form conditions -/

/-- Bundled normal-canonical-form conditions: each block is irreducible,
left-canonical, and peripheral-spectrum primitive, with non-increasing
nonzero weights and positive bond dimensions.

This is the weaker “normal tensor” block notion from arXiv:1606.00608:
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

/-- Project the bundled conditions to blockwise irreducibility data. -/
def toHasIrreducibleBlocks (hNCF : IsNormalCanonicalForm μ A) :
    HasIrreducibleBlocks (d := d) A :=
  HasIrreducibleBlocks.ofForall hNCF.block_irreducible

/-- Project the bundled conditions to left-canonical block-family normalization. -/
def toIsLeftCanonicalBlockFamily (hNCF : IsNormalCanonicalForm μ A) :
    IsLeftCanonicalBlockFamily (d := d) A :=
  IsLeftCanonicalBlockFamily.ofForall hNCF.leftCanonical

/-- Project the bundled conditions to blockwise peripheral primitivity data. -/
def toHasPrimitiveBlocks (hNCF : IsNormalCanonicalForm μ A) :
    HasPrimitiveBlocks (d := d) A :=
  HasPrimitiveBlocks.ofForall hNCF.block_primitive

/-- Assemble `IsNormalCanonicalForm` from the additive split conditions (relaxed ordering). -/
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
