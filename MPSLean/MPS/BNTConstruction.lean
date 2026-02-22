/-
Copyright (c) 2025 MPSLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MPSLean.PiAlgebra.CanonicalFormSep
import MPSLean.Spectral.SpectralGapRect
import MPSLean.MPS.BNTPermutationThm44
import MPSLean.MPS.FundamentalTheoremThm44
import MPSLean.MPS.CastLemmas

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

2. **`IsCanonicalFormBNT.cross_overlap_tendsto_zero`**: Distinct CF-BNT blocks have
   decaying cross-overlaps. The proof combines:
   - Dimension-mismatch case: `mpvOverlap_tendsto_zero_of_dim_ne`
   - Same-dimension case: `mpvOverlap_tendsto_zero` (using `blocks_not_equiv` to supply
     `¬GaugePhaseEquiv`)

3. **`IsCanonicalFormBNT.isBNT`**: A canonical-form BNT decomposition yields a valid `IsBNT`
   structure, assembling all overlap and independence properties.

4. **`fundamentalTheorem_of_IsCanonicalFormBNT`**: If two CF-BNT decompositions generate
   proportional MPVs with convergent nonzero coefficients, then the blocks match up to
   permutation, dimension equality, and gauge-phase equivalence. This is a bridge from
   `IsCanonicalFormBNT` to the hypotheses of `BNTPermutationThm44`.

## Design note on coefficients

In the full paper (arXiv:1606.00608, eq. decBSV), the BNT decomposition uses summed
coefficients `c_j(N) = Σ_{q in group j} μ_{j,q}^N`, which converge after normalization.
The `IsCanonicalFormBNT` predicate sidesteps this by requiring that the grouping has already
been done (each BNT block corresponds to a single CF block). The coefficient convergence
question is deferred to a future assembly module.
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

/-! ### Cross-overlap decay -/

/-- **Cross-overlap decay for CF-BNT blocks**: distinct blocks have
`mpvOverlap (A j) (A k) N → 0` as `N → ∞`.

The proof splits into two cases:
- **Dimension mismatch** (`dim j ≠ dim k`): apply `mpvOverlap_tendsto_zero_of_dim_ne`.
- **Same dimension** (`dim j = dim k`): cast `A j` to the same type as `A k`, invoke
  `blocks_not_equiv` for `¬GaugePhaseEquiv`, then apply `mpvOverlap_tendsto_zero`. -/
theorem cross_overlap_tendsto_zero
    [∀ k, NeZero (dim k)]
    (hCF : IsCanonicalFormBNT μ A) (j k : Fin r) (hjk : j ≠ k) :
    Tendsto (fun N => mpvOverlap (d := d) (A j) (A k) N) atTop (nhds 0) := by
  by_cases hdim : dim j = dim k
  · -- Same bond dimension: cast `A j` to match `A k`'s type
    have hNotEquiv : ¬ GaugePhaseEquiv (cast (congr_arg (MPSTensor d) hdim) (A j)) (A k) :=
      hCF.blocks_not_equiv j k hjk hdim
    have hAj_inj : IsInjective (cast (congr_arg (MPSTensor d) hdim) (A j)) :=
      (isInjective_cast_dim hdim (A j)).mpr (hCF.toIsCanonicalForm.block_injective j)
    have hAj_norm : ∑ i : Fin d,
        (cast (congr_arg (MPSTensor d) hdim) (A j) i)ᴴ *
        (cast (congr_arg (MPSTensor d) hdim) (A j) i) = 1 :=
      (dsGauge_cast_dim hdim (A j)).mpr (hCF.toIsCanonicalForm.ds_gauge j)
    have hto0 := mpvOverlap_tendsto_zero
      (cast (congr_arg (MPSTensor d) hdim) (A j)) (A k)
      hAj_inj (hCF.toIsCanonicalForm.block_injective k)
      hAj_norm (hCF.toIsCanonicalForm.ds_gauge k)
      hNotEquiv
    exact hto0.congr fun N => mpvOverlap_cast_dim_left hdim (A j) (A k) N
  · -- Different bond dimensions: use the rectangular spectral gap
    exact mpvOverlap_tendsto_zero_of_dim_ne (A j) (A k)
      (hCF.toIsCanonicalForm.block_injective j)
      (hCF.toIsCanonicalForm.block_injective k)
      (hCF.toIsCanonicalForm.ds_gauge j)
      (hCF.toIsCanonicalForm.ds_gauge k)
      hdim

/-! ### BNT structure from CF-BNT -/

/-- A canonical-form BNT decomposition yields a valid `IsBNT` structure.

The BNT blocks are the CF blocks `A k`, the total tensor is
`toTensorFromBlocks μ A`, and the decomposition coefficients are `μ k ^ N`.

The three `IsBNT` requirements are verified as:
1. **Normal**: each `A k` is injective (hence normal).
2. **Spans MPV**: `mpv_toTensorFromBlocks_eq_sum` provides the linear combination.
3. **Eventually LI**: follows from asymptotic orthonormality (self-overlap → 1,
   cross-overlap → 0) via `eventually_linearIndependent_of_overlap_tendsto_orthonormal`. -/
theorem isBNT [∀ k, NeZero (dim k)]
    (hCF : IsCanonicalFormBNT μ A) :
    IsBNT (toTensorFromBlocks μ A) r dim A where
  normal := fun j => by
    -- Injective implies normal (with N = 1): `IsInjective = IsNBlkInjective 1`.
    refine ⟨1, ?_⟩
    have hInj := hCF.toIsCanonicalForm.block_injective j
    -- Show the two ranges coincide.
    -- `IsNBlkInjective A 1` ↔ `IsInjective A` because `evalWord A [i] = A i`.
    have hkey : ∀ σ : Fin 1 → Fin d, evalWord (A j) (List.ofFn σ) = A j (σ 0) := by
      intro σ; simp [List.ofFn_succ, List.ofFn_zero, evalWord]
    suffices h : Set.range (fun σ : Fin 1 → Fin d => evalWord (A j) (List.ofFn σ)) =
        Set.range (A j) by
      rw [IsNBlkInjective, h]; exact hInj
    ext M; simp only [Set.mem_range, hkey]
    exact ⟨fun ⟨σ, h⟩ => ⟨σ 0, h⟩, fun ⟨i, h⟩ => ⟨fun _ => i, h⟩⟩
  spans_mpv := fun N => by
    -- The decomposition identity `mpv_toTensorFromBlocks_eq_sum` provides this
    exact ⟨fun k => μ k ^ N, fun σ => by
      have := mpv_toTensorFromBlocks_eq_sum μ A σ
      simp only [smul_eq_mul] at this
      exact this⟩
  eventually_li := by
    -- Asymptotic orthonormality gives eventual linear independence
    have hOrtho := eventually_linearIndependent_of_overlap_tendsto_orthonormal A
      hCF.toIsCanonicalForm.overlap_tendsto_one
      (fun i j hij => hCF.cross_overlap_tendsto_zero i j hij)
    -- Extract an N0 from the `∀ᶠ` filter
    rw [Filter.Eventually] at hOrtho
    obtain ⟨N0, hN0⟩ := (Filter.mem_atTop_sets.mp hOrtho)
    exact ⟨N0, fun N hN => hN0 N (le_of_lt hN)⟩

end IsCanonicalFormBNT

/-! ### Bridge to BNTPermutationThm44 -/

/-- **Fundamental theorem bridge for CF-BNT decompositions (Thm 4.4).**

If two families of tensors in canonical-form BNT give rise to proportional MPVs
(with convergent nonzero coefficients), then the families have the same number
of blocks, and blocks match up to permutation, dimension equality, and gauge-phase
equivalence.

This combines `IsCanonicalFormBNT` overlap properties with
`exists_eq_numBlocks_and_equiv_gaugePhase_of_proportional_decomp` from
`BNTPermutationThm44.lean`. -/
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
  exists_eq_numBlocks_and_equiv_gaugePhase_of_proportional_decomp
    (A := A) (B := B)
    (hA_inj := hA.toIsCanonicalForm.block_injective)
    (hB_inj := hB.toIsCanonicalForm.block_injective)
    (hA_norm := hA.toIsCanonicalForm.ds_gauge)
    (hB_norm := hB.toIsCanonicalForm.ds_gauge)
    (hA_self := hA.toIsCanonicalForm.overlap_tendsto_one)
    (hA_off := fun i j hij => hA.cross_overlap_tendsto_zero i j hij)
    (hB_self := hB.toIsCanonicalForm.overlap_tendsto_one)
    (hB_off := fun k₁ k₂ hk => hB.cross_overlap_tendsto_zero k₁ k₂ hk)
    (A_total := A_total) (B_total := B_total)
    (aCoeff := aCoeff) (bCoeff := bCoeff)
    (aLim := aLim) (bLim := bLim)
    (c := c) (cLim := cLim)
    (hA_decomp := hA_decomp) (hB_decomp := hB_decomp)
    (haCoeff := haCoeff) (hbCoeff := hbCoeff)
    (_haLim_ne := haLim_ne) (_hbLim_ne := hbLim_ne)
    (hProp := hProp) (hc := hc) (_hcLim_ne := hcLim_ne)

end MPSTensor
