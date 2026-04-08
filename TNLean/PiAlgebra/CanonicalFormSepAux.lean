/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.PiAlgebra.BlockSeparation
import TNLean.PiAlgebra.FundamentalTheoremComplete
import TNLean.Algebra.MatrixAux
import TNLean.Spectral.SpectralGap
import TNLean.Spectral.SpectralGapNT
import TNLean.Spectral.MPVOverlapDecay
import TNLean.Spectral.PrimitiveOverlap
import TNLean.QPF.Assembly
import TNLean.MPS.CanonicalForm.Reduction
import TNLean.MPS.FundamentalTheorem.Proportional
import TNLean.MPS.Irreducible.FormII
import TNLean.MPS.Overlap.PeripheralToSpectralGap
import TNLean.Channel.Peripheral.Spectrum
import Mathlib.Analysis.Complex.Basic

/-!
# Separated canonical-form hypotheses — Auxiliary definitions and helpers

This file contains the structure definitions, algebraic lemmas, overlap bounds, peeling lemma,
and block-separation core helper lemmas that underpin the main block-separation results in
`CanonicalFormSep.lean`.

## Contents

- Additive split API: `HasInjectiveBlocks`, `HasIrreducibleBlocks`, `HasPrimitiveBlocks`,
  `IsLeftCanonicalBlockFamily`, `HasStrictOrderedNonzeroWeights`, `HasNormalizedSelfOverlap`.
- Bundled predicates: `IsCanonicalForm`, `IsNormalCanonicalForm` with projections and
  round-trip constructors.
- Section `AlgebraicLemmas`: characteristic polynomial utilities.
- Section `OverlapBounds`: MPV overlap bounds from left-canonical normalization.
- Left-canonical trace bounds: `leftCanonical_evalWord_trace_bound`.
- Section `PeelingLemma`: `peeling_exponential_bound` for the block-separation induction.
- Section `BlockSeparationCoreHelpers`: local helper lemmas used by the induction in
  `CanonicalFormSep.lean`.
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

/-! ### Additive split API for canonical-form hypotheses

The existing `IsCanonicalForm` bundle is kept unchanged for backwards compatibility.  The
structures below expose weaker pieces of data so theorem signatures can migrate gradually without
forcing an immediate project-wide refactor.
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

/-- Alias emphasizing that left-canonical blocks are trace-preserving. -/
theorem tp_gauge (hA : IsLeftCanonicalBlockFamily (d := d) A) :
    ∀ k, ∑ i : Fin d, (A k i)ᴴ * (A k i) = 1 :=
  hA.leftCanonical

end IsLeftCanonicalBlockFamily

/-- Strict weight ordering together with nonvanishing coefficients. -/
structure HasStrictOrderedNonzeroWeights {r : ℕ} (μ : Fin r → ℂ) : Prop where
  /-- Strict ordering of the block weights by modulus. -/
  mu_strict_anti : StrictAnti (fun k : Fin r => ‖μ k‖)
  /-- No block weight vanishes. -/
  mu_ne_zero : ∀ k, μ k ≠ 0

namespace HasStrictOrderedNonzeroWeights

variable {r : ℕ}
variable {μ : Fin r → ℂ}

/-- Strictly modulus-ordered nonzero block weights are injective. -/
theorem mu_injective (hμ : HasStrictOrderedNonzeroWeights μ) : Function.Injective μ := by
  intro j k hjk
  have h : ‖μ j‖ = ‖μ k‖ := by rw [hjk]
  exact hμ.mu_strict_anti.injective h

/-- The modulus profile of strict nonzero weights is injective. -/
theorem mu_norm_injective (hμ : HasStrictOrderedNonzeroWeights μ) :
    Function.Injective (fun k : Fin r => ‖μ k‖) :=
  hμ.mu_strict_anti.injective

end HasStrictOrderedNonzeroWeights

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

/-! ### Canonical form predicate -/

/-- Bundled canonical-form conditions combining injectivity, left-canonical normalization
`∑ᵢ Aᵢ† Aᵢ = I`, strict weight data, and overlap normalization in a single proposition. -/
structure IsCanonicalForm {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k)) : Prop where
  /-- Each block is algebraically injective (`span (range (A k)) = ⊤`). -/
  block_injective : ∀ k, IsInjective (A k)
  /-- Left-canonical normalization: `∑ᵢ Aᵢ† Aᵢ = I`. -/
  leftCanonical : ∀ k, ∑ i : Fin d, (A k i)ᴴ * (A k i) = 1
  /-- Strict ordering of the block weights by modulus. -/
  mu_strict_anti : StrictAnti (fun k : Fin r => ‖μ k‖)
  /-- No block weight vanishes. -/
  mu_ne_zero : ∀ k, μ k ≠ 0
  /-- **Aperiodicity / overlap normalization**: the MPV self-overlap converges to `1`.

  This field is kept for backward compatibility with the original separated FT interface. In the
  normal-canonical-form API the same conclusion is derived from irreducibility, left-canonical
  normalization, and peripheral-spectrum primitivity via
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

/-- Project the bundled conditions to the separated weight data. -/
def toHasStrictOrderedNonzeroWeights (hCF : IsCanonicalForm μ A) :
    HasStrictOrderedNonzeroWeights μ where
  mu_strict_anti := hCF.mu_strict_anti
  mu_ne_zero := hCF.mu_ne_zero

/-- Project the bundled conditions to self-overlap normalization data. -/
def toHasNormalizedSelfOverlap (hCF : IsCanonicalForm μ A) :
    HasNormalizedSelfOverlap (d := d) A :=
  HasNormalizedSelfOverlap.ofForall hCF.overlap_tendsto_one

/-- Rebuild the `IsCanonicalForm` bundle from the additive split API. -/
def ofSeparatedData
    (hInj : HasInjectiveBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hμ : HasStrictOrderedNonzeroWeights μ)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A) :
    IsCanonicalForm μ A where
  block_injective := hInj.block_injective
  leftCanonical := hLeft.leftCanonical
  mu_strict_anti := hμ.mu_strict_anti
  mu_ne_zero := hμ.mu_ne_zero
  overlap_tendsto_one := hOverlap.overlap_tendsto_one

theorem mu_injective (hCF : IsCanonicalForm μ A) : Function.Injective μ :=
  hCF.toHasStrictOrderedNonzeroWeights.mu_injective

theorem mu_norm_injective (hCF : IsCanonicalForm μ A) :
    Function.Injective (fun k : Fin r => ‖μ k‖) :=
  hCF.toHasStrictOrderedNonzeroWeights.mu_norm_injective

end IsCanonicalForm

/-! ### Normal canonical form predicate -/

/-- Bundled normal-canonical-form conditions: each block is irreducible,
left-canonical, and peripheral-spectrum primitive, with strictly ordered
nonzero weights and positive bond dimensions.

This is the weaker “normal tensor” block notion from arXiv:1606.00608:
each block is irreducible and its transfer map has peripheral spectrum `{1}`.
The irreducibility field is stored separately on purpose: the repository's peripheral-spectrum
primitive predicate does not by itself imply irreducibility for arbitrary transfer maps.
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
  /-- Strict ordering of the block weights by modulus. -/
  mu_strict_anti : StrictAnti (fun k : Fin r => ‖μ k‖)
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

/-- Project the bundled conditions to the separated weight data. -/
def toHasStrictOrderedNonzeroWeights (hNCF : IsNormalCanonicalForm μ A) :
    HasStrictOrderedNonzeroWeights μ where
  mu_strict_anti := hNCF.mu_strict_anti
  mu_ne_zero := hNCF.mu_ne_zero

/-- Rebuild the `IsNormalCanonicalForm` bundle from the additive split API. -/
def ofSeparatedData
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hPrim : HasPrimitiveBlocks (d := d) A)
    (hμ : HasStrictOrderedNonzeroWeights μ)
    (hDim : ∀ k, 0 < dim k) :
    IsNormalCanonicalForm μ A where
  block_irreducible := hIrr.block_irreducible
  leftCanonical := hLeft.leftCanonical
  block_primitive := hPrim.block_primitive
  mu_strict_anti := hμ.mu_strict_anti
  mu_ne_zero := hμ.mu_ne_zero
  dim_pos := hDim

theorem mu_injective (hNCF : IsNormalCanonicalForm μ A) : Function.Injective μ :=
  hNCF.toHasStrictOrderedNonzeroWeights.mu_injective

theorem mu_norm_injective (hNCF : IsNormalCanonicalForm μ A) :
    Function.Injective (fun k : Fin r => ‖μ k‖) :=
  hNCF.toHasStrictOrderedNonzeroWeights.mu_norm_injective

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

namespace IsCanonicalForm

/-- Upgrade an `IsCanonicalForm` witness to the weaker normal-canonical-form interface,
provided irreducibility, peripheral primitivity, and positive bond dimensions are supplied
separately. -/
theorem toIsNormalCanonicalForm
    {r : ℕ} {dim : Fin r → ℕ}
    {μ : Fin r → ℂ} {A : (k : Fin r) → MPSTensor d (dim k)}
    (hCF : IsCanonicalForm μ A)
    (hIrr : ∀ k, IsIrreducibleTensor (A k))
    (hPrim : ∀ k, _root_.IsPrimitive (transferMap (d := d) (D := dim k) (A k)))
    (hDim : ∀ k, 0 < dim k) :
    IsNormalCanonicalForm μ A where
  block_irreducible := hIrr
  leftCanonical := hCF.leftCanonical
  block_primitive := hPrim
  mu_strict_anti := hCF.mu_strict_anti
  mu_ne_zero := hCF.mu_ne_zero
  dim_pos := hDim

end IsCanonicalForm

/-! ### MPV overlap bounds from left-canonical normalization

For the peeling argument in `block_separation_core` we need uniform (in the chain length) bounds on
MPV overlaps. The key input is the left-canonical normalization
`∑ᵢ Aᵢ† Aᵢ = I`, together with the iterated TP identity
`word_conjTranspose_mul_sum` and the elementary trace inequality
$|\mathrm{tr}(M)|^2 \le D\,\mathrm{tr}(M^\dagger M)$.
-/

open scoped InnerProductSpace

section OverlapBounds

variable {d : ℕ}

-- `norm_sq_sum_mul_le` is now provided by `TNLean.Spectral.FrobeniusNorm`.

/-- Trace inequality: $|\mathrm{tr}(M)|^2 \le D\,\mathrm{tr}(M^\dagger M)$. -/
private lemma norm_trace_sq_le_dim_mul_trace_conjTranspose_mul
    {D : ℕ} [NeZero D] (M : Matrix (Fin D) (Fin D) ℂ) :
    ‖Matrix.trace M‖ ^ 2 ≤ (D : ℝ) * (Matrix.trace (Mᴴ * M)).re := by
  classical
  -- Cauchy–Schwarz on the diagonal sum.
  have hCS :
      ‖(∑ i : Fin D, M i i)‖ ^ 2 ≤ (D : ℝ) * (∑ i : Fin D, ‖M i i‖ ^ 2) := by
    have h := norm_sq_sum_mul_le (a := fun _ : Fin D => (1 : ℂ)) (b := fun i => M i i)
    -- simplify the constant factor `∑ ‖1‖^2 = D`.
    simpa [Matrix.trace, norm_mul, one_mul, pow_two, Finset.sum_const, Finset.card_fin] using h
  -- Bound the diagonal square sum by the full Frobenius square sum.
  have hdiag :
      (∑ i : Fin D, ‖M i i‖ ^ 2) ≤ ∑ i : Fin D, ∑ j : Fin D, ‖M i j‖ ^ 2 := by
    have hper : ∀ i : Fin D, ‖M i i‖ ^ 2 ≤ ∑ j : Fin D, ‖M i j‖ ^ 2 := by
      intro i
      have hnonneg : ∀ j : Fin D, 0 ≤ ‖M i j‖ ^ 2 := fun _ => by positivity
      -- `‖M i i‖^2` is one term of the `j`-sum.
      -- Use the fact that a single term is bounded by the whole sum.
      have hsingle : ‖M i i‖ ^ 2 ≤ ∑ j : Fin D, ‖M i j‖ ^ 2 := by
        -- We specify `f` explicitly so Lean does not guess the wrong function.
        simpa using
          (Finset.single_le_sum (s := (Finset.univ : Finset (Fin D)))
            (f := fun j : Fin D => ‖M i j‖ ^ 2)
            (fun j _ => hnonneg j) (Finset.mem_univ i))
      exact hsingle
    exact Finset.sum_le_sum (fun i _ => hper i)
  -- Rewrite the Frobenius square sum as `trace(M†M).re`.
  have hfrob : (Matrix.trace (Mᴴ * M)).re = ∑ i : Fin D, ∑ j : Fin D, ‖M i j‖ ^ 2 :=
    (MPSTensor.frobSq_trace M).symm
  -- Assemble.
  calc
    ‖Matrix.trace M‖ ^ 2
        = ‖(∑ i : Fin D, M i i)‖ ^ 2 := by simp [Matrix.trace]
    _ ≤ (D : ℝ) * (∑ i : Fin D, ‖M i i‖ ^ 2) := hCS
    _ ≤ (D : ℝ) * (∑ i : Fin D, ∑ j : Fin D, ‖M i j‖ ^ 2) := by
          gcongr
    _ = (D : ℝ) * (Matrix.trace (Mᴴ * M)).re := by simp [hfrob]

/-- Under the left-canonical normalization `∑ᵢ Aᵢ† Aᵢ = I`,
the MPV self-overlap is uniformly bounded: `‖mpvOverlap A A N‖ ≤ D^2`. -/
lemma leftCanonical_mpvOverlap_self_bound
    {D : ℕ} [NeZero D]
    (A : MPSTensor d D)
    (hA_lc : ∑ i : Fin d, (A i)ᴴ * (A i) = 1)
    (N : ℕ) :
    ‖mpvOverlap (d := d) A A N‖ ≤ (D : ℝ) ^ 2 := by
  classical
  -- Let `Mσ` be the word-evaluation matrices.
  let M : (Fin N → Fin d) → Matrix (Fin D) (Fin D) ℂ :=
    fun σ => evalWord A (List.ofFn σ)
  -- Start from the overlap and bound it by the sum of squared traces.
  have h1 :
      ‖mpvOverlap (d := d) A A N‖ ≤ ∑ σ : Fin N → Fin d, ‖Matrix.trace (M σ)‖ ^ 2 := by
    simp only [mpvOverlap, MPSTensor.mpv, MPSTensor.coeff, M]
    -- Use the triangle inequality for the finite sum.
    simpa using
      (calc
        ‖∑ σ : Fin N → Fin d,
            Matrix.trace (evalWord A (List.ofFn σ)) *
              star (Matrix.trace (evalWord A (List.ofFn σ)))‖
            ≤ ∑ σ : Fin N → Fin d,
                ‖Matrix.trace (evalWord A (List.ofFn σ)) *
                  star (Matrix.trace (evalWord A (List.ofFn σ)))‖ :=
          norm_sum_le (s := (Finset.univ : Finset (Fin N → Fin d))) _
        _ = ∑ σ : Fin N → Fin d, ‖Matrix.trace (evalWord A (List.ofFn σ))‖ ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro σ _
          simp [norm_mul, norm_star, pow_two])
  -- Use the iterated TP condition.
  have hword :
      ∑ σ : Fin N → Fin d, (M σ)ᴴ * M σ = (1 : Matrix (Fin D) (Fin D) ℂ) := by
    simpa [M] using (word_conjTranspose_mul_sum (K := A) hA_lc N)
  -- Bound the RHS by `D^2`.
  have h2 : (∑ σ : Fin N → Fin d, ‖Matrix.trace (M σ)‖ ^ 2) ≤ (D : ℝ) ^ 2 := by
    -- Apply the trace inequality termwise, then use `hword`.
    have hterm :
        ∀ σ : Fin N → Fin d, ‖Matrix.trace (M σ)‖ ^ 2 ≤
          (D : ℝ) * (Matrix.trace ((M σ)ᴴ * M σ)).re := fun σ =>
        norm_trace_sq_le_dim_mul_trace_conjTranspose_mul (D := D) (M σ)
    have hsum :
        (∑ σ : Fin N → Fin d, ‖Matrix.trace (M σ)‖ ^ 2) ≤
          ∑ σ : Fin N → Fin d, (D : ℝ) * (Matrix.trace ((M σ)ᴴ * M σ)).re :=
      Finset.sum_le_sum (fun σ _ => hterm σ)
    -- Reassociate and compute the trace sum using `hword`.
    calc
      (∑ σ : Fin N → Fin d, ‖Matrix.trace (M σ)‖ ^ 2)
          ≤ ∑ σ : Fin N → Fin d, (D : ℝ) * (Matrix.trace ((M σ)ᴴ * M σ)).re := hsum
      _ = (D : ℝ) * ∑ σ : Fin N → Fin d, (Matrix.trace ((M σ)ᴴ * M σ)).re := by
            simp [Finset.mul_sum]
      _ = (D : ℝ) * (Matrix.trace (∑ σ : Fin N → Fin d, (M σ)ᴴ * M σ)).re := by
            -- Move `re` and `trace` outside the finite sum (as in `SpectralGap.sum_frobSq_words`).
            congr 1
            rw [← Complex.re_sum, ← Matrix.trace_sum]
      _ = (D : ℝ) * (Matrix.trace (1 : Matrix (Fin D) (Fin D) ℂ)).re := by
            simp [hword]
      _ = (D : ℝ) * (D : ℝ) := by
            simp [Matrix.trace_one, Fintype.card_fin]
      _ = (D : ℝ) ^ 2 := by ring
  exact h1.trans h2

/-- Under the left-canonical normalization `∑ᵢ Aᵢ† Aᵢ = I`,
the MPV state has uniformly bounded norm: `‖mpvState A N‖ ≤ D`. -/
lemma leftCanonical_mpvState_norm_bound
    {D : ℕ} [NeZero D]
    (A : MPSTensor d D)
    (hA_lc : ∑ i : Fin d, (A i)ᴴ * (A i) = 1)
    (N : ℕ) :
    ‖mpvState (d := d) A N‖ ≤ (D : ℝ) := by
  classical
  have hself : ‖mpvOverlap (d := d) A A N‖ ≤ (D : ℝ) ^ 2 :=
    leftCanonical_mpvOverlap_self_bound (d := d) (A := A) hA_lc N
  have hEq : ‖mpvOverlap (d := d) A A N‖ = ‖mpvState (d := d) A N‖ ^ 2 := by
    -- `mpvOverlap = star (mpvInner)` and `⟪x,x⟫ = ‖x‖²`.
    -- The RHS is a nonnegative real number, so its complex norm is just an absolute value.
    simp [mpvOverlap_eq_star_mpvInner, mpvInner, inner_self_eq_norm_sq_to_K,
      RCLike.norm_ofReal, abs_of_nonneg (sq_nonneg (‖mpvState (d := d) A N‖))]
  have hsq : ‖mpvState (d := d) A N‖ ^ 2 ≤ (D : ℝ) ^ 2 := by
    simpa [hEq] using hself
  have hsqrt :
      Real.sqrt (‖mpvState (d := d) A N‖ ^ 2) ≤ Real.sqrt ((D : ℝ) ^ 2) :=
    Real.sqrt_le_sqrt hsq
  -- Simplify `√(x^2) = x` for nonnegative `x`.
  simpa [Real.sqrt_sq (norm_nonneg (mpvState (d := d) A N)),
    Real.sqrt_sq (Nat.cast_nonneg D)] using hsqrt

/-- Under the left-canonical normalization `∑ᵢ Aᵢ† Aᵢ = I`,
MPV overlaps are uniformly bounded: `‖mpvOverlap A B N‖ ≤ D₁ · D₂`. -/
lemma leftCanonical_mpvOverlap_bound
    {D₁ D₂ : ℕ} [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hA_lc : ∑ i : Fin d, (A i)ᴴ * (A i) = 1)
    (hB_lc : ∑ i : Fin d, (B i)ᴴ * (B i) = 1)
    (N : ℕ) :
    ‖mpvOverlap (d := d) A B N‖ ≤ (D₁ : ℝ) * (D₂ : ℝ) := by
  classical
  -- Convert to Lean's inner product, then apply Cauchy–Schwarz.
  have hCS : ‖mpvInner (d := d) A B N‖ ≤
      ‖mpvState (d := d) A N‖ * ‖mpvState (d := d) B N‖ :=
    norm_inner_le_norm (mpvState (d := d) A N) (mpvState (d := d) B N)
  -- `mpvOverlap = star (mpvInner)`.
  have hOverlap : ‖mpvOverlap (d := d) A B N‖ = ‖mpvInner (d := d) A B N‖ := by
    simp [mpvOverlap_eq_star_mpvInner]
  -- Apply the one-sided normalization bounds on each factor.
  have hA : ‖mpvState (d := d) A N‖ ≤ (D₁ : ℝ) :=
    leftCanonical_mpvState_norm_bound (d := d) A hA_lc N
  have hB : ‖mpvState (d := d) B N‖ ≤ (D₂ : ℝ) :=
    leftCanonical_mpvState_norm_bound (d := d) B hB_lc N
  calc
    ‖mpvOverlap (d := d) A B N‖ = ‖mpvInner (d := d) A B N‖ := hOverlap
    _ ≤ ‖mpvState (d := d) A N‖ * ‖mpvState (d := d) B N‖ := hCS
    _ ≤ (D₁ : ℝ) * (D₂ : ℝ) := by gcongr

end OverlapBounds


/-! ### Left-canonical normalization implies trace bound

**Mathematical content**: Under the left-canonical normalization
`∑_i A_i† A_i = I`, the iterated TP condition
`word_conjTranspose_mul_sum` gives
`∑_σ (evalWord A (ofFn σ))† (evalWord A (ofFn σ)) = I`
for words of any length. Each term is PSD, so for any specific word `w`,
`(evalWord A w)† (evalWord A w) ≤ I`
(in the Loewner order). This means each diagonal entry satisfies ‖M_ii‖ ≤ 1,
giving |tr(M)| ≤ ∑ ‖M_ii‖ ≤ D. For `M = (evalWord A w)^L`, we use the
identity `(evalWord A w)^L = evalWord A (w ++ w ++ ... ++ w)`. -/

open scoped ComplexOrder

private lemma star_mul_self_re_eq' (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by
  have : star z = starRingEnd ℂ z := rfl; rw [this, Complex.conj_mul']; norm_cast

private lemma star_mul_self_re_nonneg' (z : ℂ) : 0 ≤ (star z * z).re := by
  rw [star_mul_self_re_eq']; exact sq_nonneg _

/-- If ∑_σ (f σ)† (f σ) = I, then each diagonal entry of each f σ₀ has norm ≤ 1.
This follows from the PSD ordering: each (f σ₀)† (f σ₀) ≤ I. -/
private lemma norm_diag_le_one_from_sum_eq_one
    {D' : ℕ} {ι : Type*} [Fintype ι]
    (f : ι → Matrix (Fin D') (Fin D') ℂ)
    (hf : ∑ σ, (f σ)ᴴ * f σ = 1)
    (σ₀ : ι) (i : Fin D') :
    ‖f σ₀ i i‖ ≤ 1 := by
  classical
  -- 1 - M†M is PSD (sum of remaining PSD terms)
  have h_psd : (1 - (f σ₀)ᴴ * f σ₀).PosSemidef := by
    have hsub : 1 - (f σ₀)ᴴ * f σ₀ = ∑ σ ∈ Finset.univ.erase σ₀, (f σ)ᴴ * f σ := by
      rw [← hf, ← Finset.add_sum_erase _ _ (Finset.mem_univ σ₀), add_sub_cancel_left]
    rw [hsub]
    exact Matrix.posSemidef_sum _ (fun σ _ => Matrix.posSemidef_conjTranspose_mul_self (f σ))
  -- (M†M)_ii ≤ 1 via ComplexOrder
  have h_diag_nn : 0 ≤ (1 - (f σ₀)ᴴ * f σ₀) i i := h_psd.diag_nonneg
  rw [Matrix.sub_apply, Matrix.one_apply_eq] at h_diag_nn
  have h_le : ((f σ₀)ᴴ * f σ₀) i i ≤ 1 := sub_nonneg.mp h_diag_nn
  -- Extract real-part bound
  have h_re : (((f σ₀)ᴴ * f σ₀) i i).re ≤ 1 := by
    have := (Complex.le_def.mp h_le).1; simpa using this
  -- (M†M)_ii = ∑_j star(M_ji) * M_ji
  have h_expand : ((f σ₀)ᴴ * f σ₀) i i = ∑ j, star ((f σ₀) j i) * (f σ₀) j i := by
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  -- ‖M_ii‖² ≤ re(∑_j star(M_ji) * M_ji) = re((M†M)_ii) ≤ 1
  have h_sq : ‖f σ₀ i i‖ ^ 2 ≤ 1 := by
    have h1 : (star (f σ₀ i i) * f σ₀ i i).re ≤
        (∑ j : Fin D', star (f σ₀ j i) * f σ₀ j i).re := by
      simp only [Complex.re_sum]
      have : ∀ j : Fin D', j ∈ Finset.univ →
          0 ≤ (fun k => (star (f σ₀ k i) * f σ₀ k i).re) j :=
        fun j _ => star_mul_self_re_nonneg' (f σ₀ j i)
      exact Finset.single_le_sum this (Finset.mem_univ i)
    calc ‖f σ₀ i i‖ ^ 2
        = (star (f σ₀ i i) * f σ₀ i i).re := (star_mul_self_re_eq' _).symm
      _ ≤ (∑ j : Fin D', star (f σ₀ j i) * f σ₀ j i).re := h1
      _ = (((f σ₀)ᴴ * f σ₀) i i).re := by rw [h_expand]
      _ ≤ 1 := h_re
  rwa [← abs_of_nonneg (norm_nonneg _), ← sq_le_one_iff_abs_le_one]

/-- Under the left-canonical normalization `∑ᵢ Aᵢ† Aᵢ = I`,
the trace of any power of any word evaluation is bounded by `D`.
Uses the iterated TP condition and PSD diagonal bounds. -/
lemma leftCanonical_evalWord_trace_bound
    {D : ℕ} [NeZero D]
    (A : MPSTensor d D)
    (hA_lc : ∑ i : Fin d, (A i)ᴴ * (A i) = 1)
    (w : List (Fin d)) (L : ℕ) :
    ‖Matrix.trace ((evalWord A w) ^ L)‖ ≤ (D : ℝ) := by
  -- (evalWord A w)^L = evalWord A ((replicate L w).flatten)
  set n := w.length * L
  rw [← evalWord_flatten_replicate A w L]
  set w' := (List.replicate L w).flatten
  have hlen : w'.length = n := by
    simp [w', n, List.length_flatten, List.map_replicate,
      List.sum_replicate, smul_eq_mul, mul_comm]
  -- Express w' as List.ofFn σ₀ for a specific σ₀
  set σ₀ : Fin n → Fin d := fun i => w'.get (Fin.cast hlen.symm i)
  have hofFn : List.ofFn σ₀ = w' := by
    simpa [σ₀, hlen] using (List.ofFn_getElem (xs := w'))
  rw [← hofFn]
  -- word_conjTranspose_mul_sum: ∑_σ (evalWord A (ofFn σ))† (evalWord A (ofFn σ)) = I
  have h_sum := word_conjTranspose_mul_sum (fun i => A i) hA_lc n
  -- Each diagonal entry of evalWord A (ofFn σ₀) has norm ≤ 1
  have h_diag : ∀ i : Fin D, ‖evalWord A (List.ofFn σ₀) i i‖ ≤ 1 :=
    norm_diag_le_one_from_sum_eq_one
      (fun σ => evalWord A (List.ofFn σ)) h_sum σ₀
  -- ‖tr(M)‖ ≤ ∑_i ‖M_ii‖ ≤ ∑_i 1 = D
  calc ‖Matrix.trace (evalWord A (List.ofFn σ₀))‖
      ≤ ∑ i : Fin D, ‖evalWord A (List.ofFn σ₀) i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin D, (1 : ℝ) := Finset.sum_le_sum (fun i _ => h_diag i)
    _ = (D : ℝ) := by simp [Finset.sum_const, Finset.card_fin]

/-! ### Peeling lemma -/

section PeelingLemma

/-- **Peeling lemma**: Given a weighted sum ∑_k α_k^L · δ_k(L) = 0 where
the leading coefficient |α₀| strictly dominates the others (|α_k| ≤ |α₀|·ρ
for k ≠ 0 with ρ < 1), and all δ_k are uniformly bounded, then δ₀(L)
decays exponentially: |δ₀(L)| ≤ C · ρ^L.

This is the key technical tool for extracting per-block information from
the global identity. In the canonical-form application, the geometric decay
comes from strict weight ordering after dividing by the leading weight
(`|μ_k / μ₀| ≤ ρ < 1` for `k ≠ 0`), while the overlap estimates are used
only to provide the uniform bounds on the coefficients `δ_k(L)`. -/
theorem peeling_exponential_bound
    {r : ℕ} (hr : 0 < r)
    (α : Fin r → ℂ) (hα₀ : α ⟨0, hr⟩ ≠ 0)
    (δ : Fin r → ℕ → ℂ)
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hδ_bound : ∀ k L, ‖δ k L‖ ≤ B)
    (h_sum : ∀ L : ℕ, ∑ k : Fin r, (α k) ^ L * δ k L = 0)
    (ρ : ℝ) (hρ_pos : 0 < ρ) (hρ_lt : ρ < 1)
    (hρ_bound : ∀ k : Fin r, k ≠ ⟨0, hr⟩ → ‖α k‖ ≤ ‖α ⟨0, hr⟩‖ * ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℕ,
      ‖δ ⟨0, hr⟩ L‖ ≤ C * ρ ^ L := by
  set idx₀ : Fin r := ⟨0, hr⟩
  refine ⟨↑(r - 1) * B, mul_nonneg (Nat.cast_nonneg' _) hB_nn, ?_⟩
  intro L
  have h_eq := h_sum L
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ idx₀)] at h_eq
  have h_neg : (α idx₀) ^ L * δ idx₀ L =
      -(∑ k ∈ Finset.univ.erase idx₀, (α k) ^ L * δ k L) :=
    eq_neg_of_add_eq_zero_left h_eq
  have h_norm_eq : ‖(α idx₀) ^ L‖ * ‖δ idx₀ L‖ =
      ‖∑ k ∈ Finset.univ.erase idx₀, (α k) ^ L * δ k L‖ := by
    rw [← norm_mul, h_neg, norm_neg]
  have h_term_le : ∀ k ∈ Finset.univ.erase idx₀,
      ‖(α k) ^ L * δ k L‖ ≤ (‖α idx₀‖ * ρ) ^ L * B := by
    intro k hk
    rw [Finset.mem_erase] at hk
    rw [norm_mul, norm_pow]
    apply mul_le_mul
    · exact pow_le_pow_left₀ (norm_nonneg _) (hρ_bound k hk.1) L
    · exact hδ_bound k L
    · exact norm_nonneg _
    · exact pow_nonneg (mul_nonneg (norm_nonneg _) hρ_pos.le) L
  have h_erase_card : (Finset.univ.erase idx₀).card = r - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_fin]
  have h_sum_le : ‖∑ k ∈ Finset.univ.erase idx₀, (α k) ^ L * δ k L‖ ≤
      ↑(r - 1) * ((‖α idx₀‖ * ρ) ^ L * B) := by
    calc ‖∑ k ∈ Finset.univ.erase idx₀, (α k) ^ L * δ k L‖
        ≤ ∑ k ∈ Finset.univ.erase idx₀, ‖(α k) ^ L * δ k L‖ :=
          norm_sum_le (Finset.univ.erase idx₀) _
      _ ≤ ∑ _k ∈ Finset.univ.erase idx₀, ((‖α idx₀‖ * ρ) ^ L * B) :=
          Finset.sum_le_sum h_term_le
      _ = ↑(Finset.univ.erase idx₀).card * ((‖α idx₀‖ * ρ) ^ L * B) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ↑(r - 1) * ((‖α idx₀‖ * ρ) ^ L * B) := by rw [h_erase_card]
  have hα₀_pow_pos : (0 : ℝ) < ‖α idx₀‖ ^ L :=
    pow_pos (norm_pos_iff.mpr hα₀) L
  have h_chain : ‖α idx₀‖ ^ L * ‖δ idx₀ L‖ ≤
      ↑(r - 1) * ((‖α idx₀‖ * ρ) ^ L * B) := by
    calc ‖α idx₀‖ ^ L * ‖δ idx₀ L‖
        = ‖(α idx₀) ^ L‖ * ‖δ idx₀ L‖ := by rw [norm_pow]
      _ = ‖∑ k ∈ Finset.univ.erase idx₀, (α k) ^ L * δ k L‖ := h_norm_eq
      _ ≤ ↑(r - 1) * ((‖α idx₀‖ * ρ) ^ L * B) := h_sum_le
  rw [mul_pow] at h_chain
  have : ↑(r - 1) * (‖α idx₀‖ ^ L * ρ ^ L * B) =
      ‖α idx₀‖ ^ L * (↑(r - 1) * B * ρ ^ L) := by ring
  rw [this] at h_chain
  exact le_of_mul_le_mul_left h_chain hα₀_pow_pos

end PeelingLemma

section BlockSeparationCoreHelpers

private lemma eq_one_of_tendsto_pow_atTop_nhds_one (z : ℂ)
    (hz : Filter.Tendsto (fun N : ℕ => z ^ N) Filter.atTop (nhds (1 : ℂ))) :
    z = 1 := by
  have hz_shift :
      Filter.Tendsto (fun N : ℕ => z ^ (N + 1)) Filter.atTop (nhds (1 : ℂ)) :=
    (Filter.tendsto_add_atTop_iff_nat 1).2 hz
  have hz_mul : Filter.Tendsto (fun N : ℕ => z ^ (N + 1)) Filter.atTop (nhds z) := by
    have h := (Filter.Tendsto.mul_const (b := z) hz)
    simpa [pow_succ, mul_assoc] using h
  have huniq := tendsto_nhds_unique hz_shift hz_mul
  simpa [eq_comm] using huniq

/-- For injective left-canonical tensors of the same bond dimension, a mixed overlap
converging to `1` forces gauge-phase equivalence.

In the block-separation proof, the equal-dimension hypothesis is encoded by the
shared type parameter `D`; any bond-dimension mismatch is excluded one step earlier
by the rectangular overlap-decay lemma. -/
lemma gaugePhaseEquiv_of_mpvOverlap_tendsto_one
    {D : ℕ} [NeZero D] (A B : MPSTensor d D)
    (hA_inj : IsInjective A) (hB_inj : IsInjective B)
    (hA_lc : ∑ i : Fin d, (A i)ᴴ * (A i) = 1)
    (hB_lc : ∑ i : Fin d, (B i)ᴴ * (B i) = 1)
    (h : Filter.Tendsto (fun N => mpvOverlap (d := d) A B N) Filter.atTop (nhds (1 : ℂ))) :
    GaugePhaseEquiv A B := by
  by_contra hnot
  have hto0 :=
    mpvOverlap_tendsto_zero (A := A) (B := B) hA_inj hB_inj hA_lc hB_lc hnot
  exact (h.ne_nhds one_ne_zero) hto0

/-- Irreducible TP analogue of `gaugePhaseEquiv_of_mpvOverlap_tendsto_one`.

Again the two tensors already share the bond dimension `D`; in the block-separation
proof the dimension-mismatch case is ruled out separately by
`mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP`, and the nondecaying
equal-dimension overlap is then identified via the modulus-one-eigenvalue
rigidity theorem for irreducible tensors. -/
lemma gaugePhaseEquiv_of_mpvOverlap_tendsto_one_of_irreducible_TP
    {D : ℕ} [NeZero D] (A B : MPSTensor d D)
    (hA_irr : IsIrreducibleTensor A) (hB_irr : IsIrreducibleTensor B)
    (hA_lc : ∑ i : Fin d, (A i)ᴴ * (A i) = 1)
    (hB_lc : ∑ i : Fin d, (B i)ᴴ * (B i) = 1)
    (h : Filter.Tendsto (fun N => mpvOverlap (d := d) A B N) Filter.atTop (nhds (1 : ℂ))) :
    GaugePhaseEquiv A B := by
  by_contra hnot
  have hto0 :=
    mpvOverlap_tendsto_zero_of_irreducible_TP
      (A := A) (B := B) hA_irr hB_irr hA_lc hB_lc hnot
  exact (h.ne_nhds one_ne_zero) hto0

private lemma mpvOverlap_eq_pow_mul_self_of_mpv_eq_pow_mul
    {D : ℕ} (A B : MPSTensor d D) (ζ : ℂ)
    (hmpv : ∀ (N : ℕ) (σ : Fin N → Fin d), mpv B σ = ζ ^ N * mpv A σ) :
    ∀ N : ℕ,
      mpvOverlap (d := d) A B N = (star ζ) ^ N * mpvOverlap (d := d) A A N := by
  intro N
  classical
  calc
    mpvOverlap (d := d) A B N = ∑ σ : Fin N → Fin d, mpv A σ * star (mpv B σ) := by
      simp [mpvOverlap]
    _ = ∑ σ : Fin N → Fin d, mpv A σ * star (ζ ^ N * mpv A σ) := by
      refine Finset.sum_congr rfl ?_
      intro σ _
      rw [hmpv N σ]
    _ = ∑ σ : Fin N → Fin d, mpv A σ * (star (mpv A σ) * (star ζ) ^ N) := by
      refine Finset.sum_congr rfl ?_
      intro σ _
      simp [star_mul, star_pow, mul_assoc, mul_left_comm, mul_comm]
    _ = (star ζ) ^ N * ∑ σ : Fin N → Fin d, mpv A σ * star (mpv A σ) := by
      -- factor out the constant `(star ζ) ^ N`
      simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    _ = (star ζ) ^ N * mpvOverlap (d := d) A A N := by
      simp [mpvOverlap]

lemma sameMPV_of_gaugePhaseEquiv_of_mpvOverlap_tendsto_one
    {D : ℕ} (A B : MPSTensor d D)
    (hSelf : Filter.Tendsto (fun N => mpvOverlap (d := d) A A N) Filter.atTop (nhds (1 : ℂ)))
    (hCross : Filter.Tendsto (fun N => mpvOverlap (d := d) A B N) Filter.atTop (nhds (1 : ℂ)))
    (hGaugePhase : GaugePhaseEquiv A B) :
    SameMPV A B := by
  classical
  rcases hGaugePhase with ⟨X, ζ, hζ, hX⟩
  have hmpv : ∀ (N : ℕ) (σ : Fin N → Fin d), mpv B σ = ζ ^ N * mpv A σ :=
    mpv_eq_pow_mul_of_gaugePhase (A := A) (B := B) X ζ hX
  have hoverlap :
      ∀ N : ℕ,
        mpvOverlap (d := d) A B N = (star ζ) ^ N * mpvOverlap (d := d) A A N :=
    mpvOverlap_eq_pow_mul_self_of_mpv_eq_pow_mul (A := A) (B := B) (ζ := ζ) hmpv
  have hSelf_ne :
      (∀ᶠ N in Filter.atTop, mpvOverlap (d := d) A A N ≠ 0) :=
    hSelf.eventually_ne (by simp)
  have hratio_tendsto :
      Filter.Tendsto
        (fun N => mpvOverlap (d := d) A B N / mpvOverlap (d := d) A A N)
        Filter.atTop (nhds (1 : ℂ)) := by
    simpa using (Filter.Tendsto.div hCross hSelf (by simp))
  have hratio_eq :
      ∀ᶠ N in Filter.atTop,
        mpvOverlap (d := d) A B N / mpvOverlap (d := d) A A N = (star ζ) ^ N := by
    filter_upwards [hSelf_ne] with N hN
    have hEq := hoverlap N
    calc
      mpvOverlap (d := d) A B N / mpvOverlap (d := d) A A N
          = ((star ζ) ^ N * mpvOverlap (d := d) A A N) / mpvOverlap (d := d) A A N := by
              simp [hEq]
      _ = (star ζ) ^ N := by
            simpa using (mul_div_cancel_right₀ ((star ζ) ^ N) hN)
  have hpow_tendsto :
      Filter.Tendsto (fun N : ℕ => (star ζ) ^ N) Filter.atTop (nhds (1 : ℂ)) :=
    Filter.Tendsto.congr' hratio_eq hratio_tendsto
  have hstarζ : star ζ = (1 : ℂ) :=
    eq_one_of_tendsto_pow_atTop_nhds_one (z := star ζ) hpow_tendsto
  have hζ : ζ = 1 := by
    have := congrArg star hstarζ
    simpa using this
  have hGauge : GaugeEquiv A B := by
    refine ⟨X, ?_⟩
    intro i
    simp [hζ, hX i]
  exact GaugeEquiv.sameMPV hGauge

end BlockSeparationCoreHelpers

end MPSTensor
