import TNLean.PiAlgebra.CanonicalFormSep
import TNLean.Spectral.SpectralGapRect
import TNLean.MPS.BNT
import TNLean.MPS.BNTPermutationThm44
import TNLean.MPS.CastLemmas

/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.style.show false

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
    (hBlocks : ∀ j k : Fin r, j ≠ k →
      ∀ (h : dim j = dim k),
        ¬ GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (A j)) (A k)) :
    IsCanonicalFormBNT μ A where
  toIsCanonicalForm := IsCanonicalForm.ofSeparatedData hInj hLeft hμ hOverlap
  blocks_not_equiv := hBlocks

end IsCanonicalFormBNT

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
    (hBlocks : ∀ j k : Fin r, j ≠ k →
      ∀ (h : dim j = dim k),
        ¬ GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (A j)) (A k))
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
    (hBlocks : ∀ j k : Fin r, j ≠ k →
      ∀ (h : dim j = dim k),
        ¬ GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (A j)) (A k)) :
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
  spans_mpv := fun N =>
    ⟨fun k => μ k ^ N, fun σ => by
      simpa [smul_eq_mul] using mpv_toTensorFromBlocks_eq_sum μ A σ⟩
  eventually_li := by
    have hOrtho := eventually_linearIndependent_of_overlap_tendsto_orthonormal A
      hOverlap.overlap_tendsto_one
      (fun i j hij =>
        cross_overlap_tendsto_zero_of_separated_CFBNT_data A hInj hLeft hBlocks i j hij)
    rw [Filter.Eventually] at hOrtho
    obtain ⟨N0, hN0⟩ := Filter.mem_atTop_sets.mp hOrtho
    exact ⟨N0, fun N hN => hN0 N (le_of_lt hN)⟩

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
    (hA_blocks : ∀ j k : Fin rA, j ≠ k →
      ∀ (h : dimA j = dimA k),
        ¬ GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (A j)) (A k))
    (hB_inj : HasInjectiveBlocks (d := d) B)
    (hB_left : IsLeftCanonicalBlockFamily (d := d) B)
    (hB_overlap : HasNormalizedSelfOverlap (d := d) B)
    (hB_blocks : ∀ j k : Fin rB, j ≠ k →
      ∀ (h : dimB j = dimB k),
        ¬ GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (B j)) (B k))
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

end MPSTensor
