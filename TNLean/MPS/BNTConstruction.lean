import TNLean.PiAlgebra.CanonicalFormSep
import TNLean.Spectral.SpectralGapRect
import TNLean.Spectral.SpectralGapNT
import TNLean.MPS.BNT
import TNLean.MPS.BNTPermutationThm44
import TNLean.MPS.CastLemmas

/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# BNT construction from canonical form

This module introduces `IsCanonicalFormBNT`, which extends `IsCanonicalForm` with the
requirement that distinct blocks are not gauge-phase equivalent (i.e., equivalent blocks
have already been merged). This captures the "BNT" property of Def. 4.2 / Prop. char-BNT
in arXiv:2011.12127 and arXiv:1606.00608, lines 1145–1148.

## Main results

1. **`IsCanonicalFormBNT`**: A strengthened canonical form where no two distinct blocks are
   gauge-phase equivalent (the BNT grouping step has been performed).

2. **`cross_overlap_tendsto_zero_of_separated_CFBNT_data`** and the legacy wrapper
   **`IsCanonicalFormBNT.cross_overlap_tendsto_zero`**: distinct CF-BNT blocks have decaying
   cross-overlaps. The proof combines:
   - Dimension-mismatch case: `mpvOverlap_tendsto_zero_of_dim_ne`
   - Same-dimension case: `mpvOverlap_tendsto_zero` (using `blocks_not_equiv` to supply
     `¬GaugePhaseEquiv`)

3. **`isBNT_of_separated_CFBNT_data`** and the legacy wrapper **`IsCanonicalFormBNT.isBNT`**:
   a canonical-form BNT decomposition yields a valid `IsBNT` structure, assembling all overlap
   and independence properties.

4. **`fundamentalTheorem_of_separated_CFBNT_data`** and the legacy wrapper
   **`fundamentalTheorem_of_IsCanonicalFormBNT`**: if two CF-BNT decompositions generate
   proportional MPVs with convergent nonzero coefficients, then the blocks match up to
   permutation, dimension equality, and gauge-phase equivalence. This is a bridge from
   canonical/BNT split data to the hypotheses of `BNTPermutationThm44`.

## Design note on coefficients

In the full paper (arXiv:1606.00608, eq. decBSV), the BNT decomposition uses summed
coefficients `c_j(N) = Σ_{q in group j} μ_{j,q}^N`.
These coefficients do **not** converge in general after normalization: unit-modulus terms can
still oscillate. The present `IsCanonicalFormBNT` predicate sidesteps that issue by requiring
that the grouping has already been done (each BNT block corresponds to a single CF block), and
the proportional-case theorem below takes whatever convergent coefficient data it needs as
explicit hypotheses.
-/

open scoped Matrix BigOperators
open Filter

namespace MPSTensor

variable {d : ℕ}

/-- Distinct equal-dimension blocks in a family are not gauge-phase equivalent. -/
abbrev BlocksNotGaugePhaseEquiv {r : ℕ} {dim : Fin r → ℕ}
    (A : (k : Fin r) → MPSTensor d (dim k)) : Prop :=
  ∀ j k : Fin r, j ≠ k →
    ∀ h : dim j = dim k,
      ¬ GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (A j)) (A k)

/-! ### `IsCanonicalFormBNT` predicate -/

/-- **Canonical form with BNT separation**: extends `IsCanonicalForm` with the requirement
that distinct blocks are not gauge-phase equivalent. This means that the "BNT grouping"
step (merging gauge-phase-equivalent CF blocks) has already been performed.

In the language of arXiv:2011.12127 Def. 4.2, this corresponds to a canonical form where
each BNT block is represented by a single CF block. -/
structure IsCanonicalFormBNT {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k)) : Prop extends
    IsCanonicalForm μ A where
  /-- Distinct blocks are not gauge-phase equivalent (BNT separation). -/
  blocks_not_equiv : ∀ j k : Fin r, j ≠ k →
    ∀ (h : dim j = dim k),
      ¬ GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (A j)) (A k)

namespace IsCanonicalFormBNT

variable {r : ℕ} {dim : Fin r → ℕ}
variable {μ : Fin r → ℂ} {A : (k : Fin r) → MPSTensor d (dim k)}

/-- Project CF-BNT data to blockwise injectivity. -/
def toHasInjectiveBlocks (hCF : IsCanonicalFormBNT μ A) : HasInjectiveBlocks (d := d) A :=
  hCF.toIsCanonicalForm.toHasInjectiveBlocks

/-- Project CF-BNT data to left-canonical block-family normalization. -/
def toIsLeftCanonicalBlockFamily (hCF : IsCanonicalFormBNT μ A) :
    IsLeftCanonicalBlockFamily (d := d) A :=
  hCF.toIsCanonicalForm.toIsLeftCanonicalBlockFamily

/-- Project CF-BNT data to separated weight data. -/
def toHasStrictOrderedNonzeroWeights (hCF : IsCanonicalFormBNT μ A) :
    HasStrictOrderedNonzeroWeights μ :=
  hCF.toIsCanonicalForm.toHasStrictOrderedNonzeroWeights

/-- Project CF-BNT data to self-overlap normalization. -/
def toHasNormalizedSelfOverlap (hCF : IsCanonicalFormBNT μ A) :
    HasNormalizedSelfOverlap (d := d) A :=
  hCF.toIsCanonicalForm.toHasNormalizedSelfOverlap

/-- Rebuild `IsCanonicalFormBNT` from the additive split API plus the BNT separation axiom. -/
def ofSeparatedData
    (hInj : HasInjectiveBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hμ : HasStrictOrderedNonzeroWeights μ)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A) :
    IsCanonicalFormBNT μ A where
  toIsCanonicalForm := IsCanonicalForm.ofSeparatedData hInj hLeft hμ hOverlap
  blocks_not_equiv := hBlocks

end IsCanonicalFormBNT

/-- An `IsCanonicalForm` family with pairwise distinct block dimensions automatically satisfies
`IsCanonicalFormBNT`, since the separation axiom is vacuous. -/
theorem IsCanonicalForm.toIsCanonicalFormBNT_of_distinct_dims
    {r : ℕ} {dim : Fin r → ℕ}
    {μ : Fin r → ℂ} {A : (k : Fin r) → MPSTensor d (dim k)}
    (hCF : IsCanonicalForm μ A)
    (hDistinct : Function.Injective dim) :
    IsCanonicalFormBNT μ A :=
  IsCanonicalFormBNT.ofSeparatedData
    hCF.toHasInjectiveBlocks
    hCF.toIsLeftCanonicalBlockFamily
    hCF.toHasStrictOrderedNonzeroWeights
    hCF.toHasNormalizedSelfOverlap
    (fun _ _ hjk h => absurd (hDistinct h) hjk)

/-! ### `IsNormalCanonicalFormBNT` predicate -/

/-- Normal canonical form with BNT separation: extends `IsNormalCanonicalForm` with the
requirement that distinct blocks are not gauge-phase equivalent. -/
structure IsNormalCanonicalFormBNT {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k)) : Prop extends
    IsNormalCanonicalForm μ A where
  /-- Distinct blocks are not gauge-phase equivalent (BNT separation). -/
  blocks_not_equiv : ∀ j k : Fin r, j ≠ k →
    ∀ (h : dim j = dim k),
      ¬ GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (A j)) (A k)

namespace IsNormalCanonicalFormBNT

variable {r : ℕ} {dim : Fin r → ℕ}
variable {μ : Fin r → ℂ} {A : (k : Fin r) → MPSTensor d (dim k)}

/-- Project normal-CF-BNT data to blockwise irreducibility. -/
def toHasIrreducibleBlocks (hNCF : IsNormalCanonicalFormBNT μ A) :
    HasIrreducibleBlocks (d := d) A :=
  hNCF.toIsNormalCanonicalForm.toHasIrreducibleBlocks

/-- Project normal-CF-BNT data to left-canonical block-family normalization. -/
def toIsLeftCanonicalBlockFamily (hNCF : IsNormalCanonicalFormBNT μ A) :
    IsLeftCanonicalBlockFamily (d := d) A :=
  hNCF.toIsNormalCanonicalForm.toIsLeftCanonicalBlockFamily

/-- Project normal-CF-BNT data to blockwise primitive transfer maps. -/
def toHasPrimitiveBlocks (hNCF : IsNormalCanonicalFormBNT μ A) :
    HasPrimitiveBlocks (d := d) A :=
  hNCF.toIsNormalCanonicalForm.toHasPrimitiveBlocks

/-- Project normal-CF-BNT data to separated weight data. -/
def toHasStrictOrderedNonzeroWeights (hNCF : IsNormalCanonicalFormBNT μ A) :
    HasStrictOrderedNonzeroWeights μ :=
  hNCF.toIsNormalCanonicalForm.toHasStrictOrderedNonzeroWeights

/-- Project normal-CF-BNT data to self-overlap normalization. -/
def toHasNormalizedSelfOverlap [∀ k, NeZero (dim k)]
    (hNCF : IsNormalCanonicalFormBNT μ A) :
    HasNormalizedSelfOverlap (d := d) A :=
  hNCF.toIsNormalCanonicalForm.toHasNormalizedSelfOverlap

/-- Rebuild `IsNormalCanonicalFormBNT` from the additive split API plus the BNT separation
axiom. -/
def ofSeparatedData
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hPrim : HasPrimitiveBlocks (d := d) A)
    (hμ : HasStrictOrderedNonzeroWeights μ)
    (hDim : ∀ k, 0 < dim k)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A) :
    IsNormalCanonicalFormBNT μ A where
  toIsNormalCanonicalForm := IsNormalCanonicalForm.ofSeparatedData hIrr hLeft hPrim hμ hDim
  blocks_not_equiv := hBlocks

end IsNormalCanonicalFormBNT

/-- The block-diagonal tensor `toTensorFromBlocks μ A` carries the obvious coefficient
expansion over its blocks. -/
private theorem spans_mpv_toTensorFromBlocks
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k)) :
    ∀ N : ℕ, ∃ c : Fin r → ℂ, ∀ σ : Fin N → Fin d,
      mpv (toTensorFromBlocks μ A) σ = ∑ k : Fin r, c k * mpv (A k) σ := by
  intro N
  refine ⟨fun k => μ k ^ N, ?_⟩
  intro σ
  simpa [smul_eq_mul] using mpv_toTensorFromBlocks_eq_sum μ A σ

/-- Overlaps converging to the Kronecker delta give eventual linear independence of block MPVs. -/
private theorem eventually_li_of_overlap_limits
    {r : ℕ} {dim : Fin r → ℕ}
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hSelf : ∀ j,
      Tendsto (fun N => mpvOverlap (d := d) (A j) (A j) N) atTop (nhds (1 : ℂ)))
    (hOff : ∀ i j, i ≠ j →
      Tendsto (fun N => mpvOverlap (d := d) (A i) (A j) N) atTop (nhds (0 : ℂ))) :
    ∃ N0 : ℕ, ∀ N > N0,
      LinearIndependent ℂ (fun j : Fin r => mpvState (d := d) (A j) N) := by
  have hOrtho := bntFamilies_eventually_linearIndependent A hSelf hOff
  rw [Filter.Eventually] at hOrtho
  obtain ⟨N0, hN0⟩ := Filter.mem_atTop_sets.mp hOrtho
  exact ⟨N0, fun N hN => hN0 N (le_of_lt hN)⟩

/-! ### Cross-overlap decay from separated CF-BNT data -/

section SeparatedCFBNT

variable {r : ℕ} {dim : Fin r → ℕ}
variable {μ : Fin r → ℂ} {A : (k : Fin r) → MPSTensor d (dim k)}

/-- Split-data version of CF-BNT cross-overlap decay.

Only injectivity, left-canonical normalization, and the BNT non-equivalence axiom are used. -/
theorem cross_overlap_tendsto_zero_of_separated_CFBNT_data
    [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hInj : HasInjectiveBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (j k : Fin r) (hjk : j ≠ k) :
    Tendsto (fun N => mpvOverlap (d := d) (A j) (A k) N) atTop (nhds 0) := by
  by_cases hdim : dim j = dim k
  · have hNotEquiv : ¬ GaugePhaseEquiv (cast (congr_arg (MPSTensor d) hdim) (A j)) (A k) :=
      hBlocks j k hjk hdim
    have hAj_inj : IsInjective (cast (congr_arg (MPSTensor d) hdim) (A j)) :=
      (isInjective_cast_dim hdim (A j)).mpr (hInj.block_injective j)
    have hAj_norm : ∑ i : Fin d,
        (cast (congr_arg (MPSTensor d) hdim) (A j) i)ᴴ *
        (cast (congr_arg (MPSTensor d) hdim) (A j) i) = 1 :=
      (leftCanonical_cast_dim hdim (A j)).mpr (hLeft.leftCanonical j)
    have hto0 := mpvOverlap_tendsto_zero
      (cast (congr_arg (MPSTensor d) hdim) (A j)) (A k)
      hAj_inj (hInj.block_injective k)
      hAj_norm (hLeft.leftCanonical k)
      hNotEquiv
    exact hto0.congr fun N => mpvOverlap_cast_dim_left hdim (A j) (A k) N
  · exact mpvOverlap_tendsto_zero_of_dim_ne (A j) (A k)
      (hInj.block_injective j)
      (hInj.block_injective k)
      (hLeft.leftCanonical j)
      (hLeft.leftCanonical k)
      hdim

/-- Split-data version of `IsCanonicalFormBNT.isBNT`.

The only role of `μ` is to specify the block-diagonal tensor `toTensorFromBlocks μ A` and its
obvious coefficient decomposition.  Strict weight ordering is not used here. -/
theorem isBNT_of_separated_CFBNT_data [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ)
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hInj : HasInjectiveBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A) :
    IsBNT (toTensorFromBlocks μ A) r dim A where
  normal := fun j => by
    refine ⟨1, ?_⟩
    have hAj_inj := hInj.block_injective j
    have hkey : ∀ σ : Fin 1 → Fin d, evalWord (A j) (List.ofFn σ) = A j (σ 0) := by
      intro σ
      simp [List.ofFn_succ, List.ofFn_zero, evalWord]
    suffices h : Set.range (fun σ : Fin 1 → Fin d => evalWord (A j) (List.ofFn σ)) =
        Set.range (A j) by
      rw [IsNBlkInjective, h]
      exact hAj_inj
    ext M
    simp only [Set.mem_range, hkey]
    exact ⟨fun ⟨σ, hσ⟩ => ⟨σ 0, hσ⟩, fun ⟨i, hi⟩ => ⟨fun _ => i, hi⟩⟩
  spans_mpv := spans_mpv_toTensorFromBlocks μ A
  eventually_li :=
    eventually_li_of_overlap_limits A
      hOverlap.overlap_tendsto_one
      (fun i j hij =>
        cross_overlap_tendsto_zero_of_separated_CFBNT_data A hInj hLeft hBlocks i j hij)

end SeparatedCFBNT

namespace IsCanonicalFormBNT

variable {r : ℕ} {dim : Fin r → ℕ}
variable {μ : Fin r → ℂ} {A : (k : Fin r) → MPSTensor d (dim k)}

/-! ### Cross-overlap decay -/

/-- **Cross-overlap decay for CF-BNT blocks**: distinct blocks have
`mpvOverlap (A j) (A k) N → 0` as `N → ∞`.

This legacy theorem now delegates to `cross_overlap_tendsto_zero_of_separated_CFBNT_data`. -/
theorem cross_overlap_tendsto_zero
    [∀ k, NeZero (dim k)]
    (hCF : IsCanonicalFormBNT μ A) (j k : Fin r) (hjk : j ≠ k) :
    Tendsto (fun N => mpvOverlap (d := d) (A j) (A k) N) atTop (nhds 0) :=
  cross_overlap_tendsto_zero_of_separated_CFBNT_data A
    hCF.toHasInjectiveBlocks
    hCF.toIsLeftCanonicalBlockFamily
    hCF.blocks_not_equiv
    j k hjk

/-! ### BNT structure from CF-BNT -/

/-- A canonical-form BNT decomposition yields a valid `IsBNT` structure.

This legacy theorem now delegates to `isBNT_of_separated_CFBNT_data`. -/
theorem isBNT [∀ k, NeZero (dim k)]
    (hCF : IsCanonicalFormBNT μ A) :
    IsBNT (toTensorFromBlocks μ A) r dim A :=
  isBNT_of_separated_CFBNT_data μ A
    hCF.toHasInjectiveBlocks
    hCF.toIsLeftCanonicalBlockFamily
    hCF.toHasNormalizedSelfOverlap
    hCF.blocks_not_equiv

end IsCanonicalFormBNT

/-! ### Cross-overlap decay from separated normal-CF-BNT data -/

section SeparatedNormalCFBNT

variable {r : ℕ} {dim : Fin r → ℕ}
variable {μ : Fin r → ℂ} {A : (k : Fin r) → MPSTensor d (dim k)}

/-- Split-data version of normal-CF-BNT cross-overlap decay.

Only irreducibility, left-canonical normalization, and the BNT non-equivalence axiom are used. -/
theorem cross_overlap_tendsto_zero_of_separated_normalCFBNT_data
    [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (j k : Fin r) (hjk : j ≠ k) :
    Tendsto (fun N => mpvOverlap (d := d) (A j) (A k) N) atTop (nhds 0) := by
  by_cases hdim : dim j = dim k
  · have hNotEquiv : ¬ GaugePhaseEquiv (cast (congr_arg (MPSTensor d) hdim) (A j)) (A k) :=
      hBlocks j k hjk hdim
    have hAj_irr : IsIrreducibleTensor (cast (congr_arg (MPSTensor d) hdim) (A j)) :=
      (isIrreducibleTensor_cast_dim hdim (A j)).mpr (hIrr.block_irreducible j)
    have hAj_norm : ∑ i : Fin d,
        (cast (congr_arg (MPSTensor d) hdim) (A j) i)ᴴ *
        (cast (congr_arg (MPSTensor d) hdim) (A j) i) = 1 :=
      (leftCanonical_cast_dim hdim (A j)).mpr (hLeft.leftCanonical j)
    have hto0 := mpvOverlap_tendsto_zero_of_irreducible_TP
      (cast (congr_arg (MPSTensor d) hdim) (A j)) (A k)
      hAj_irr (hIrr.block_irreducible k)
      hAj_norm (hLeft.leftCanonical k)
      hNotEquiv
    exact hto0.congr fun N => mpvOverlap_cast_dim_left hdim (A j) (A k) N
  · exact mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP (A j) (A k)
      (hIrr.block_irreducible j)
      (hIrr.block_irreducible k)
      (hLeft.leftCanonical j)
      (hLeft.leftCanonical k)
      hdim

/-- The NT hypotheses already supply the `spans_mpv` and `eventually_li` data used by the
proportional-FT / permutation arguments. The only missing ingredient for a full `IsBNT`
package is blockwise `IsNormal`. -/
theorem spans_mpv_and_eventually_li_of_separated_normalCFBNT_data [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ)
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hNCF : IsNormalCanonicalForm μ A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A) :
    (∀ N : ℕ, ∃ c : Fin r → ℂ, ∀ σ : Fin N → Fin d,
      mpv (toTensorFromBlocks μ A) σ = ∑ j : Fin r, c j * mpv (A j) σ) ∧
    (∃ N0 : ℕ, ∀ N > N0,
      LinearIndependent ℂ (fun j : Fin r => mpvState (d := d) (A j) N)) := by
  constructor
  · exact spans_mpv_toTensorFromBlocks μ A
  · exact
      eventually_li_of_overlap_limits A
        (fun j => hNCF.overlap_tendsto_one j)
        (fun i j hij =>
          cross_overlap_tendsto_zero_of_separated_normalCFBNT_data A
            hNCF.toHasIrreducibleBlocks
            hNCF.toIsLeftCanonicalBlockFamily
            hBlocks i j hij)

/-- Split-data version of `IsNormalCanonicalFormBNT.isBNT`, assuming blockwise `IsNormal`
has already been supplied by an external primitive-to-normal bridge. -/
theorem isBNT_of_separated_normalCFBNT_data [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ)
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hNCF : IsNormalCanonicalForm μ A)
    (hNormal : ∀ j, IsNormal (A j))
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A) :
    IsBNT (toTensorFromBlocks μ A) r dim A := by
  obtain ⟨hSpans, hLI⟩ :=
    spans_mpv_and_eventually_li_of_separated_normalCFBNT_data μ A hNCF hBlocks
  exact ⟨hNormal, hSpans, hLI⟩

end SeparatedNormalCFBNT

namespace IsNormalCanonicalFormBNT

variable {r : ℕ} {dim : Fin r → ℕ}
variable {μ : Fin r → ℂ} {A : (k : Fin r) → MPSTensor d (dim k)}

/-- Cross-overlap decay for normal-CF-BNT blocks. -/
theorem cross_overlap_tendsto_zero
    [∀ k, NeZero (dim k)]
    (hNCF : IsNormalCanonicalFormBNT μ A) (j k : Fin r) (hjk : j ≠ k) :
    Tendsto (fun N => mpvOverlap (d := d) (A j) (A k) N) atTop (nhds 0) :=
  cross_overlap_tendsto_zero_of_separated_normalCFBNT_data A
    hNCF.toHasIrreducibleBlocks
    hNCF.toIsLeftCanonicalBlockFamily
    hNCF.blocks_not_equiv
    j k hjk

/-- A normal-canonical-form BNT decomposition yields a valid `IsBNT` structure once
blockwise `IsNormal` is supplied separately. -/
theorem isBNT [∀ k, NeZero (dim k)]
    (hNCF : IsNormalCanonicalFormBNT μ A)
    (hNormal : ∀ j, IsNormal (A j)) :
    IsBNT (toTensorFromBlocks μ A) r dim A :=
  isBNT_of_separated_normalCFBNT_data μ A
    hNCF.toIsNormalCanonicalForm
    hNormal
    hNCF.blocks_not_equiv

end IsNormalCanonicalFormBNT

/-! ### Bridge to BNTPermutationThm44 -/

/-- Split-data bridge theorem for CF-BNT-style decompositions (Thm 4.4).

The theorem only needs the separated pieces of data used by the proportional-MPV argument:
blockwise injectivity, left-canonical normalization, self-overlap normalization, and the BNT
non-equivalence condition that forces cross-overlap decay. -/
theorem fundamentalTheorem_of_separated_CFBNT_data
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {DtotA DtotB : ℕ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hA_inj : HasInjectiveBlocks (d := d) A)
    (hA_left : IsLeftCanonicalBlockFamily (d := d) A)
    (hA_overlap : HasNormalizedSelfOverlap (d := d) A)
    (hA_blocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (hB_inj : HasInjectiveBlocks (d := d) B)
    (hB_left : IsLeftCanonicalBlockFamily (d := d) B)
    (hB_overlap : HasNormalizedSelfOverlap (d := d) B)
    (hB_blocks : BlocksNotGaugePhaseEquiv (d := d) B)
    (A_total : MPSTensor d DtotA)
    (B_total : MPSTensor d DtotB)
    (aCoeff : ℕ → Fin rA → ℂ) (bCoeff : ℕ → Fin rB → ℂ)
    (aLim : Fin rA → ℂ) (bLim : Fin rB → ℂ)
    (c : ℕ → ℂ) (cLim : ℂ)
    (hA_decomp : ∀ N (σ : Fin N → Fin d),
      mpv A_total σ = ∑ j : Fin rA, (aCoeff N j) * mpv (A j) σ)
    (hB_decomp : ∀ N (σ : Fin N → Fin d),
      mpv B_total σ = ∑ k : Fin rB, (bCoeff N k) * mpv (B k) σ)
    (haCoeff : ∀ j, Tendsto (fun N => aCoeff N j) atTop (nhds (aLim j)))
    (hbCoeff : ∀ k, Tendsto (fun N => bCoeff N k) atTop (nhds (bLim k)))
    (haLim_ne : ∀ j, aLim j ≠ 0)
    (hbLim_ne : ∀ k, bLim k ≠ 0)
    (hProp : ∀ N (σ : Fin N → Fin d), mpv A_total σ = c N * mpv B_total σ)
    (hc : Tendsto c atTop (nhds cLim))
    (hcLim_ne : cLim ≠ 0) :
    ∃ _h : rA = rB,
      ∃ perm : Fin rA ≃ Fin rB,
        ∀ j : Fin rA,
          ∃ hdim : dimA j = dimB (perm j),
            GaugePhaseEquiv (d := d)
              (cast (congr_arg (MPSTensor d) hdim) (A j))
              (B (perm j)) :=
  exists_eq_numBlocks_and_equiv_gaugePhase_of_proportional_decomp
    (A := A) (B := B)
    (hA_inj := hA_inj.block_injective)
    (hB_inj := hB_inj.block_injective)
    (hA_norm := hA_left.leftCanonical)
    (hB_norm := hB_left.leftCanonical)
    (hA_self := hA_overlap.overlap_tendsto_one)
    (hA_off := fun i j hij =>
      cross_overlap_tendsto_zero_of_separated_CFBNT_data A hA_inj hA_left hA_blocks i j hij)
    (hB_self := hB_overlap.overlap_tendsto_one)
    (hB_off := fun i j hij =>
      cross_overlap_tendsto_zero_of_separated_CFBNT_data B hB_inj hB_left hB_blocks i j hij)
    (A_total := A_total) (B_total := B_total)
    (aCoeff := aCoeff) (bCoeff := bCoeff)
    (aLim := aLim) (bLim := bLim)
    (c := c) (cLim := cLim)
    (hA_decomp := hA_decomp) (hB_decomp := hB_decomp)
    (haCoeff := haCoeff) (hbCoeff := hbCoeff)
    (_haLim_ne := haLim_ne) (_hbLim_ne := hbLim_ne)
    (hProp := hProp) (hc := hc) (_hcLim_ne := hcLim_ne)

/-- **Fundamental theorem bridge for CF-BNT decompositions (Thm 4.4).**

If two families of tensors in canonical-form BNT give rise to proportional MPVs
(with convergent nonzero coefficients), then the families have the same number
of blocks, and blocks match up to permutation, dimension equality, and gauge-phase
equivalence.

This legacy theorem now delegates to `fundamentalTheorem_of_separated_CFBNT_data`. -/
theorem fundamentalTheorem_of_IsCanonicalFormBNT
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {DtotA DtotB : ℕ}
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hA : IsCanonicalFormBNT μA A)
    (hB : IsCanonicalFormBNT μB B)
    (A_total : MPSTensor d DtotA)
    (B_total : MPSTensor d DtotB)
    (aCoeff : ℕ → Fin rA → ℂ) (bCoeff : ℕ → Fin rB → ℂ)
    (aLim : Fin rA → ℂ) (bLim : Fin rB → ℂ)
    (c : ℕ → ℂ) (cLim : ℂ)
    (hA_decomp : ∀ N (σ : Fin N → Fin d),
      mpv A_total σ = ∑ j : Fin rA, (aCoeff N j) * mpv (A j) σ)
    (hB_decomp : ∀ N (σ : Fin N → Fin d),
      mpv B_total σ = ∑ k : Fin rB, (bCoeff N k) * mpv (B k) σ)
    (haCoeff : ∀ j, Tendsto (fun N => aCoeff N j) atTop (nhds (aLim j)))
    (hbCoeff : ∀ k, Tendsto (fun N => bCoeff N k) atTop (nhds (bLim k)))
    (haLim_ne : ∀ j, aLim j ≠ 0)
    (hbLim_ne : ∀ k, bLim k ≠ 0)
    (hProp : ∀ N (σ : Fin N → Fin d), mpv A_total σ = c N * mpv B_total σ)
    (hc : Tendsto c atTop (nhds cLim))
    (hcLim_ne : cLim ≠ 0) :
    ∃ _h : rA = rB,
      ∃ perm : Fin rA ≃ Fin rB,
        ∀ j : Fin rA,
          ∃ hdim : dimA j = dimB (perm j),
            GaugePhaseEquiv (d := d)
              (cast (congr_arg (MPSTensor d) hdim) (A j))
              (B (perm j)) :=
  fundamentalTheorem_of_separated_CFBNT_data A B
    hA.toHasInjectiveBlocks
    hA.toIsLeftCanonicalBlockFamily
    hA.toHasNormalizedSelfOverlap
    hA.blocks_not_equiv
    hB.toHasInjectiveBlocks
    hB.toIsLeftCanonicalBlockFamily
    hB.toHasNormalizedSelfOverlap
    hB.blocks_not_equiv
    A_total B_total aCoeff bCoeff aLim bLim c cLim
    hA_decomp hB_decomp haCoeff hbCoeff haLim_ne hbLim_ne hProp hc hcLim_ne

/-- Split-data bridge theorem for normal-CF-BNT-style decompositions (NT Thm 4.4). -/
theorem fundamentalTheorem_of_separated_normalCFBNT_data
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {DtotA DtotB : ℕ}
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hA_ncf : IsNormalCanonicalForm μA A)
    (hA_blocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (hB_ncf : IsNormalCanonicalForm μB B)
    (hB_blocks : BlocksNotGaugePhaseEquiv (d := d) B)
    (A_total : MPSTensor d DtotA)
    (B_total : MPSTensor d DtotB)
    (aCoeff : ℕ → Fin rA → ℂ) (bCoeff : ℕ → Fin rB → ℂ)
    (aLim : Fin rA → ℂ) (bLim : Fin rB → ℂ)
    (c : ℕ → ℂ) (cLim : ℂ)
    (hA_decomp : ∀ N (σ : Fin N → Fin d),
      mpv A_total σ = ∑ j : Fin rA, (aCoeff N j) * mpv (A j) σ)
    (hB_decomp : ∀ N (σ : Fin N → Fin d),
      mpv B_total σ = ∑ k : Fin rB, (bCoeff N k) * mpv (B k) σ)
    (haCoeff : ∀ j, Tendsto (fun N => aCoeff N j) atTop (nhds (aLim j)))
    (hbCoeff : ∀ k, Tendsto (fun N => bCoeff N k) atTop (nhds (bLim k)))
    (haLim_ne : ∀ j, aLim j ≠ 0)
    (hbLim_ne : ∀ k, bLim k ≠ 0)
    (hProp : ∀ N (σ : Fin N → Fin d), mpv A_total σ = c N * mpv B_total σ)
    (hc : Tendsto c atTop (nhds cLim))
    (hcLim_ne : cLim ≠ 0) :
    ∃ _h : rA = rB,
      ∃ perm : Fin rA ≃ Fin rB,
        ∀ j : Fin rA,
          ∃ hdim : dimA j = dimB (perm j),
            GaugePhaseEquiv (d := d)
              (cast (congr_arg (MPSTensor d) hdim) (A j))
              (B (perm j)) :=
  exists_eq_numBlocks_and_equiv_gaugePhase_of_proportional_decomp_of_irreducible_TP
    (A := A) (B := B)
    (hA_irr := hA_ncf.block_irreducible)
    (hB_irr := hB_ncf.block_irreducible)
    (hA_norm := hA_ncf.leftCanonical)
    (hB_norm := hB_ncf.leftCanonical)
    (hA_self := fun j => hA_ncf.overlap_tendsto_one j)
    (hA_off := fun i j hij =>
      cross_overlap_tendsto_zero_of_separated_normalCFBNT_data A
        hA_ncf.toHasIrreducibleBlocks
        hA_ncf.toIsLeftCanonicalBlockFamily
        hA_blocks i j hij)
    (hB_self := fun j => hB_ncf.overlap_tendsto_one j)
    (hB_off := fun i j hij =>
      cross_overlap_tendsto_zero_of_separated_normalCFBNT_data B
        hB_ncf.toHasIrreducibleBlocks
        hB_ncf.toIsLeftCanonicalBlockFamily
        hB_blocks i j hij)
    (A_total := A_total) (B_total := B_total)
    (aCoeff := aCoeff) (bCoeff := bCoeff)
    (aLim := aLim) (bLim := bLim)
    (c := c) (cLim := cLim)
    (hA_decomp := hA_decomp) (hB_decomp := hB_decomp)
    (haCoeff := haCoeff) (hbCoeff := hbCoeff)
    (_haLim_ne := haLim_ne) (_hbLim_ne := hbLim_ne)
    (hProp := hProp) (hc := hc) (_hcLim_ne := hcLim_ne)

/-- Fundamental theorem bridge for normal-CF-BNT decompositions (NT Thm 4.4). -/
theorem fundamentalTheorem_of_IsNormalCanonicalFormBNT
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {DtotA DtotB : ℕ}
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hA : IsNormalCanonicalFormBNT μA A)
    (hB : IsNormalCanonicalFormBNT μB B)
    (A_total : MPSTensor d DtotA)
    (B_total : MPSTensor d DtotB)
    (aCoeff : ℕ → Fin rA → ℂ) (bCoeff : ℕ → Fin rB → ℂ)
    (aLim : Fin rA → ℂ) (bLim : Fin rB → ℂ)
    (c : ℕ → ℂ) (cLim : ℂ)
    (hA_decomp : ∀ N (σ : Fin N → Fin d),
      mpv A_total σ = ∑ j : Fin rA, (aCoeff N j) * mpv (A j) σ)
    (hB_decomp : ∀ N (σ : Fin N → Fin d),
      mpv B_total σ = ∑ k : Fin rB, (bCoeff N k) * mpv (B k) σ)
    (haCoeff : ∀ j, Tendsto (fun N => aCoeff N j) atTop (nhds (aLim j)))
    (hbCoeff : ∀ k, Tendsto (fun N => bCoeff N k) atTop (nhds (bLim k)))
    (haLim_ne : ∀ j, aLim j ≠ 0)
    (hbLim_ne : ∀ k, bLim k ≠ 0)
    (hProp : ∀ N (σ : Fin N → Fin d), mpv A_total σ = c N * mpv B_total σ)
    (hc : Tendsto c atTop (nhds cLim))
    (hcLim_ne : cLim ≠ 0) :
    ∃ _h : rA = rB,
      ∃ perm : Fin rA ≃ Fin rB,
        ∀ j : Fin rA,
          ∃ hdim : dimA j = dimB (perm j),
            GaugePhaseEquiv (d := d)
              (cast (congr_arg (MPSTensor d) hdim) (A j))
              (B (perm j)) :=
  fundamentalTheorem_of_separated_normalCFBNT_data A B
    hA.toIsNormalCanonicalForm hA.blocks_not_equiv
    hB.toIsNormalCanonicalForm hB.blocks_not_equiv
    A_total B_total aCoeff bCoeff aLim bLim c cLim
    hA_decomp hB_decomp haCoeff hbCoeff haLim_ne hbLim_ne hProp hc hcLim_ne

end MPSTensor
