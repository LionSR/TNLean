/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.Full.NondecayingPartnerUnique
import TNLean.MPS.FundamentalTheorem.Full.ProportionalDominant

/-!
# Fixed-block decay contradictions for proportional BNT families

The two fixed-block decay contradictions used in the proof of Theorem
`thm1` in arXiv:1606.00608 (CPSV16):

* the right form, fixing a `B`-block `B_{k₀}` and ruling out the assumption
  that all overlaps `⟪V^{(N)}(A_j), V^{(N)}(B_{k₀})⟫ → 0`;
* the left form, fixing an `A`-block `A_{j₀}` and ruling out the assumption
  that all overlaps `⟪V^{(N)}(A_{j₀}), V^{(N)}(B_k)⟫ → 0`.

The general (arbitrary fixed block) form is currently an open obligation on
the `IsCanonicalFormBNT` surface — see the structural analysis in
`audits/2026-05-13_cpsv16_ft_bridge_gap.md`.  The **dominant**-block
specialisations (`k₀ = ⟨0, _⟩` for the right form, `j₀ = ⟨0, _⟩` for the left
form) are unconditionally proved below using the dominant-weight
adjusted scalar limit (`ProportionalDominant.lean`) and the self-overlap
normalisation supplied by `IsCanonicalForm`.

## Main statements

* `fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT`
  (open, general fixed block);
* `fixed_left_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT`
  (open, general fixed block);
* `fixed_right_dominant_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT`
  (closed, dominant `B` block);
* `fixed_left_dominant_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT`
  (closed, dominant `A` block).

## References

* Cirac, Pérez-García, Schuch, Verstraete, *Matrix Product Density Operators:
  Renormalization Fixed Points and Boundary Theories*, arXiv:1606.00608 (2017).

## Tags

matrix product states, fundamental theorem, BNT, overlap, decay contradiction
-/

open scoped BigOperators
open Filter

namespace MPSTensor

section HeteroEqualCase

/-- **Fixed-right all-overlaps-decay contradiction for proportional BNT families.**

Source: arXiv:1606.00608, Theorem `thm1`, line 1182. In the proof, after
fixing a block `B_k`, the authors say that it is impossible for all overlaps
with the `A_j` blocks to tend to zero, because otherwise the total MPV families
could not be proportional by Lemma `Lem1`.

This statement names the cancellation step implicit in that sentence. The
local Lemma `Lem1` input is
`eventually_linearIndependent_all_left_single_right_of_all_overlaps_decay_CFBNT`.
The remaining formal proof obligation is documented in
`docs/paper-gaps/cpsv16_fixed_block_cancellation.tex` and tracked in issue
#1607.

**Scope restriction (one-copy-per-sector):** The local hypotheses
`IsCanonicalFormBNT` are the already-grouped one-copy-per-sector canonical
forms. CPSV16 allows BNT multiplicities inside a sector. This restriction is
documented in `docs/paper-gaps/ft_one_copy_scope_restriction.tex`.

**Open obligation (non-dominant `k₀`).** The general statement for arbitrary
fixed block `k₀ : Fin rB` is currently open on the `IsCanonicalFormBNT`
surface.  The dominant block (`k₀ = ⟨0, _⟩`) is handled separately by
`fixed_right_dominant_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT`
below.  For non-dominant `k₀`, under `mu_strict_anti` the canonical-form
unit-modulus hypothesis required by the paper-faithful per-block projection
lemma fails (every weight after the first has modulus strictly less than the
dominant weight), so the correspondence with
`TNLean.MPS.FundamentalTheorem.SectorDecomposition.PerBlockProjection`
established for the `SectorDecomposition` surface does not transfer
directly.  Resolution requires the structural reorganization of
`IsCanonicalFormBNT` described in
`audits/2026-05-13_cpsv16_ft_bridge_gap.md` §Resolution, separating the
spectral level (`λ_j` with `|λ_0| > |λ_1| > …`) from the within-sector
unit-modulus weights (`μ_{j,q}` with `‖μ_{j,q}‖ = 1`).  Tracked in
issue #1641 (Plan C). -/
lemma fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hA : IsCanonicalFormBNT μA A)
    (hB : IsCanonicalFormBNT μB B)
    (hrA : rA ≠ 0) (hrB : rB ≠ 0)
    (hProp : EventuallyNonzeroProportionalMPV₂
      (toTensorFromBlocks μA A) (toTensorFromBlocks μB B))
    (k₀ : Fin rB)
    (hAllDecay : ∀ j : Fin rA,
      Tendsto (fun N => mpvOverlap (d := d) (A j) (B k₀) N) atTop (nhds 0)) :
    False := by
  sorry

/-- **Fixed-left all-overlaps-decay contradiction for proportional BNT families.**

Source: arXiv:1606.00608, Theorem `thm1`, lines 1182--1185. The proof repeats
the fixed-block argument with the two tensor families interchanged to obtain
the opposite block-count inequality. Thus, for a fixed block `A_j`, it is
impossible for all overlaps with the `B_k` blocks to tend to zero under
eventual nonzero proportionality of the total MPV families.

This statement names the symmetric cancellation step implicit in the source.
The local Lemma `Lem1` input is
`eventually_linearIndependent_all_right_single_left_of_all_overlaps_decay_CFBNT`.
The remaining formal proof obligation is documented in
`docs/paper-gaps/cpsv16_fixed_block_cancellation.tex` and tracked in issue
#1607.

**Scope restriction (one-copy-per-sector):** The local hypotheses
`IsCanonicalFormBNT` are the already-grouped one-copy-per-sector canonical
forms. CPSV16 allows BNT multiplicities inside a sector. This restriction is
documented in `docs/paper-gaps/ft_one_copy_scope_restriction.tex`.

**Open obligation (non-dominant `j₀`).** The general statement for arbitrary
fixed block `j₀ : Fin rA` is currently open.  The dominant block
(`j₀ = ⟨0, _⟩`) is handled by
`fixed_left_dominant_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT`
below.  See the right-block sibling
`fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT`
for the structural notes shared with this lemma. -/
lemma fixed_left_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hA : IsCanonicalFormBNT μA A)
    (hB : IsCanonicalFormBNT μB B)
    (hrA : rA ≠ 0) (hrB : rB ≠ 0)
    (hProp : EventuallyNonzeroProportionalMPV₂
      (toTensorFromBlocks μA A) (toTensorFromBlocks μB B))
    (j₀ : Fin rA)
    (hAllDecay : ∀ k : Fin rB,
      Tendsto (fun N => mpvOverlap (d := d) (A j₀) (B k) N) atTop (nhds 0)) :
    False := by
  sorry

/-! ### Dominant-block specialisations -/

/-- **Dominant-block fixed-right all-overlaps-decay contradiction.**

The specialisation of
`fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT`
to the dominant `B`-block `k₀ = ⟨0, _⟩`.  In this case the analytic
non-cancellation step that obstructs the non-dominant statement is supplied
unconditionally by combining

* the dominant-weight-adjusted scalar limit
  `‖c N · (μB 0 / μA 0)^N‖ → 1`
  (`exists_dominant_adjusted_scalar_tendsto_norm_one_of_eventuallyNonzeroProportionalMPV₂_CFBNT`),
* the normalised self-overlap limit
  `(μB 0)^(-N) · ⟨V^{(N)}(B), V^{(N)}(B_0)⟩ → 1`
  (from `hB.toHasNormalizedSelfOverlap.overlap_tendsto_one` together with
  the decay of cross-overlaps `mpvOverlap (B k) (B 0) → 0` for `k ≠ 0`
  obtained from `hB.cross_overlap_tendsto_zero` plus `bounded_mul_tendsto_zero`).

The product of these two limits has modulus tending to `1`, but the same
quantity also tends to `0` by the LHS expansion (Steps 1--6 of the original
argument).  Contradiction.

**Scope restriction (one-copy-per-sector):** inherited from `IsCanonicalFormBNT`.
See `docs/paper-gaps/ft_one_copy_scope_restriction.tex`. -/
lemma fixed_right_dominant_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hA : IsCanonicalFormBNT μA A)
    (hB : IsCanonicalFormBNT μB B)
    (hrA : rA ≠ 0) (hrB : rB ≠ 0)
    (hProp : EventuallyNonzeroProportionalMPV₂
      (toTensorFromBlocks μA A) (toTensorFromBlocks μB B))
    (hAllDecay : ∀ j : Fin rA,
      Tendsto (fun N => mpvOverlap (d := d) (A j)
        (B ⟨0, Nat.pos_of_ne_zero hrB⟩) N) atTop (nhds 0)) :
    False := by
  classical
  set a0 : Fin rA := ⟨0, Nat.pos_of_ne_zero hrA⟩
  set b0 : Fin rB := ⟨0, Nat.pos_of_ne_zero hrB⟩
  have hμA_ne : μA a0 ≠ 0 := hA.toHasStrictOrderedNonzeroWeights.mu_ne_zero a0
  have hμB_ne : μB b0 ≠ 0 := hB.toHasStrictOrderedNonzeroWeights.mu_ne_zero b0
  -- Step 0: dominant-adjusted scalar.  Modulus of `c N · (μB 0 / μA 0)^N` → 1.
  obtain ⟨c, _hcNe, hState, hcAdj⟩ :=
    exists_dominant_adjusted_scalar_tendsto_norm_one_of_eventuallyNonzeroProportionalMPV₂_CFBNT
      A B hA hB hrA hrB hProp
  -- Step 1: convert weighted-mpvState equality `hState` to σ-level mpv proportionality.
  have hc_eq : ∀ᶠ N in atTop, ∀ σ : Fin N → Fin d,
      mpv (toTensorFromBlocks μA A) σ =
        c N * mpv (toTensorFromBlocks μB B) σ := by
    refine hState.mono ?_
    intro N hN σ
    have hAstate :
        mpvState (d := d) (toTensorFromBlocks μA A) N =
          ∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N := by
      refine mpvState_eq_sum_of_decomp (d := d) (toTensorFromBlocks μA A) A
        (N := N) (fun j : Fin rA => (μA j) ^ N) ?_
      intro σ'
      simpa [smul_eq_mul] using
        mpv_toTensorFromBlocks_eq_sum (d := d) (μ := μA) (A := A) σ'
    have hBstate :
        mpvState (d := d) (toTensorFromBlocks μB B) N =
          ∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N := by
      refine mpvState_eq_sum_of_decomp (d := d) (toTensorFromBlocks μB B) B
        (N := N) (fun k : Fin rB => (μB k) ^ N) ?_
      intro σ'
      simpa [smul_eq_mul] using
        mpv_toTensorFromBlocks_eq_sum (d := d) (μ := μB) (A := B) σ'
    have hTotal :
        mpvState (d := d) (toTensorFromBlocks μA A) N =
          c N • mpvState (d := d) (toTensorFromBlocks μB B) N := by
      rw [hAstate, hN, hBstate]
    have hσ := congr_arg (fun v => v σ) hTotal
    simpa [mpvState_apply, mpv, smul_eq_mul] using hσ
  -- Step 2: project σ-level proportionality onto `B b0`.
  have hOverlap : ∀ᶠ N in atTop,
      mpvOverlap (d := d) (toTensorFromBlocks μA A) (B b0) N
        = c N * mpvOverlap (d := d) (toTensorFromBlocks μB B) (B b0) N := by
    refine hc_eq.mono ?_
    intro N hN
    exact mpvOverlap_eq_mul_of_mpv_eq_mul (d := d)
      (toTensorFromBlocks μA A) (toTensorFromBlocks μB B) (c N) hN (B b0)
  -- Step 3: expand the LHS overlap as a block sum on `A`-side.
  have hLHS_decomp : ∀ N : ℕ,
      mpvOverlap (d := d) (toTensorFromBlocks μA A) (B b0) N
        = ∑ j : Fin rA, (μA j) ^ N * mpvOverlap (d := d) (A j) (B b0) N := by
    intro N
    refine mpvOverlap_eq_sum_of_decomp_left
      (d := d) (g := rA) (dim := dimA)
      (toTensorFromBlocks μA A) A (N := N)
      (fun j => (μA j) ^ N) ?_ (B b0)
    intro σ
    have hexp := mpv_toTensorFromBlocks_eq_sum μA A σ (N := N)
    simpa [smul_eq_mul] using hexp
  -- Step 4: each normalised `(μA a0)^(-N) · (μA j)^N · overlap → 0`.
  have hSummandA : ∀ j : Fin rA,
      Tendsto
        (fun N =>
          (μA a0 ^ N)⁻¹ * ((μA j) ^ N * mpvOverlap (d := d) (A j) (B b0) N))
        atTop (nhds 0) := by
    intro j
    by_cases hj : j = a0
    · subst hj
      have hcong : ∀ N : ℕ,
          (μA a0 ^ N)⁻¹ * ((μA a0) ^ N * mpvOverlap (d := d) (A a0) (B b0) N)
            = mpvOverlap (d := d) (A a0) (B b0) N := by
        intro N
        rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero N hμA_ne), one_mul]
      refine Tendsto.congr ?_ (hAllDecay a0)
      intro N; exact (hcong N).symm
    · have hratio_lt : ‖μA j / μA a0‖ < 1 := by
        rw [norm_div]
        exact (div_lt_one (norm_pos_iff.mpr hμA_ne)).mpr
          (hA.mu_strict_anti (by
            simp only [a0, Fin.lt_def]
            exact Nat.pos_of_ne_zero (fun h => hj (Fin.ext h))))
      have hgeom :
          Tendsto
            (fun N => (μA j / μA a0) ^ N * mpvOverlap (d := d) (A j) (B b0) N)
            atTop (nhds 0) :=
        bounded_mul_tendsto_zero (μA j / μA a0) _
          (le_of_lt hratio_lt) (hAllDecay j)
      have hpow_eq : ∀ N : ℕ,
          (μA a0 ^ N)⁻¹ * ((μA j) ^ N * mpvOverlap (d := d) (A j) (B b0) N)
            = (μA j / μA a0) ^ N * mpvOverlap (d := d) (A j) (B b0) N := by
        intro N
        rw [div_pow]
        field_simp [pow_ne_zero N hμA_ne]
      refine Tendsto.congr ?_ hgeom
      intro N; exact (hpow_eq N).symm
  -- Step 5: normalised LHS overlap tends to zero.
  have hSumZero : Tendsto
      (fun N => (μA a0 ^ N)⁻¹ *
        mpvOverlap (d := d) (toTensorFromBlocks μA A) (B b0) N)
      atTop (nhds 0) := by
    have hSum :
        Tendsto
          (fun N =>
            ∑ j : Fin rA, (μA a0 ^ N)⁻¹ *
              ((μA j) ^ N * mpvOverlap (d := d) (A j) (B b0) N))
          atTop (nhds (∑ _j : Fin rA, (0 : ℂ))) :=
      tendsto_finset_sum Finset.univ (fun j _ => hSummandA j)
    have hSumZero' : Tendsto
        (fun N =>
          ∑ j : Fin rA, (μA a0 ^ N)⁻¹ *
            ((μA j) ^ N * mpvOverlap (d := d) (A j) (B b0) N))
        atTop (nhds 0) := by simpa using hSum
    refine hSumZero'.congr ?_
    intro N
    rw [hLHS_decomp N, Finset.mul_sum]
  -- Step 6: combine with proportionality to land the LHS-of-contradiction expression.
  have hContra : Tendsto
      (fun N => (μA a0 ^ N)⁻¹ * c N *
        mpvOverlap (d := d) (toTensorFromBlocks μB B) (B b0) N)
      atTop (nhds 0) := by
    refine hSumZero.congr' ?_
    filter_upwards [hOverlap] with N hN
    show (μA a0 ^ N)⁻¹ * mpvOverlap (d := d) (toTensorFromBlocks μA A) (B b0) N
      = (μA a0 ^ N)⁻¹ * c N
        * mpvOverlap (d := d) (toTensorFromBlocks μB B) (B b0) N
    rw [hN]; ring
  -- Step 7: dominant self-overlap normalisation on the `B` side.
  have hRHS_decomp : ∀ N : ℕ,
      mpvOverlap (d := d) (toTensorFromBlocks μB B) (B b0) N
        = ∑ k : Fin rB, (μB k) ^ N * mpvOverlap (d := d) (B k) (B b0) N := by
    intro N
    refine mpvOverlap_eq_sum_of_decomp_left
      (d := d) (g := rB) (dim := dimB)
      (toTensorFromBlocks μB B) B (N := N)
      (fun k => (μB k) ^ N) ?_ (B b0)
    intro σ
    have hexp := mpv_toTensorFromBlocks_eq_sum μB B σ (N := N)
    simpa [smul_eq_mul] using hexp
  have hSelfTendOne :
      Tendsto (fun N => mpvOverlap (d := d) (B b0) (B b0) N) atTop (nhds 1) :=
    hB.toHasNormalizedSelfOverlap.overlap_tendsto_one b0
  have hCrossTendZero : ∀ k : Fin rB, k ≠ b0 →
      Tendsto (fun N => mpvOverlap (d := d) (B k) (B b0) N) atTop (nhds 0) :=
    fun k hk => hB.cross_overlap_tendsto_zero k b0 hk
  have hSummandB : ∀ k : Fin rB,
      Tendsto
        (fun N =>
          (μB b0 ^ N)⁻¹ * ((μB k) ^ N * mpvOverlap (d := d) (B k) (B b0) N))
        atTop (nhds (if k = b0 then (1 : ℂ) else 0)) := by
    intro k
    by_cases hk : k = b0
    · subst hk
      simp only [↓reduceIte]
      have hcong : ∀ N : ℕ,
          (μB b0 ^ N)⁻¹ * ((μB b0) ^ N * mpvOverlap (d := d) (B b0) (B b0) N)
            = mpvOverlap (d := d) (B b0) (B b0) N := by
        intro N
        rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero N hμB_ne), one_mul]
      refine Tendsto.congr ?_ hSelfTendOne
      intro N; exact (hcong N).symm
    · simp only [if_neg hk]
      have hratio_lt : ‖μB k / μB b0‖ < 1 := by
        rw [norm_div]
        exact (div_lt_one (norm_pos_iff.mpr hμB_ne)).mpr
          (hB.mu_strict_anti (by
            simp only [b0, Fin.lt_def]
            exact Nat.pos_of_ne_zero (fun h => hk (Fin.ext h))))
      have hgeom :
          Tendsto
            (fun N => (μB k / μB b0) ^ N * mpvOverlap (d := d) (B k) (B b0) N)
            atTop (nhds 0) :=
        bounded_mul_tendsto_zero (μB k / μB b0) _
          (le_of_lt hratio_lt) (hCrossTendZero k hk)
      have hpow_eq : ∀ N : ℕ,
          (μB b0 ^ N)⁻¹ * ((μB k) ^ N * mpvOverlap (d := d) (B k) (B b0) N)
            = (μB k / μB b0) ^ N * mpvOverlap (d := d) (B k) (B b0) N := by
        intro N
        rw [div_pow]
        field_simp [pow_ne_zero N hμB_ne]
      refine Tendsto.congr ?_ hgeom
      intro N; exact (hpow_eq N).symm
  have hSumOne : Tendsto
      (fun N => (μB b0 ^ N)⁻¹ *
        mpvOverlap (d := d) (toTensorFromBlocks μB B) (B b0) N)
      atTop (nhds (1 : ℂ)) := by
    have hSum :
        Tendsto
          (fun N =>
            ∑ k : Fin rB, (μB b0 ^ N)⁻¹ *
              ((μB k) ^ N * mpvOverlap (d := d) (B k) (B b0) N))
          atTop (nhds (∑ k : Fin rB, if k = b0 then (1 : ℂ) else 0)) :=
      tendsto_finset_sum Finset.univ (fun k _ => hSummandB k)
    have hSumIf : (∑ k : Fin rB, if k = b0 then (1 : ℂ) else 0) = 1 := by
      rw [Finset.sum_ite_eq']
      simp [Finset.mem_univ]
    have hSumOne' : Tendsto
        (fun N =>
          ∑ k : Fin rB, (μB b0 ^ N)⁻¹ *
            ((μB k) ^ N * mpvOverlap (d := d) (B k) (B b0) N))
        atTop (nhds (1 : ℂ)) := by
      rw [← hSumIf]; exact hSum
    refine hSumOne'.congr ?_
    intro N
    rw [hRHS_decomp N, Finset.mul_sum]
  -- Step 8: factor the LHS-of-contradiction expression and derive modulus → 1.
  have hFactored : ∀ N : ℕ,
      (μA a0 ^ N)⁻¹ * c N *
        mpvOverlap (d := d) (toTensorFromBlocks μB B) (B b0) N
      = c N * (μB b0 / μA a0) ^ N *
        ((μB b0 ^ N)⁻¹ * mpvOverlap (d := d) (toTensorFromBlocks μB B) (B b0) N) := by
    intro N
    rw [div_pow]
    field_simp [pow_ne_zero N hμA_ne, pow_ne_zero N hμB_ne]
  have hSumOneNorm :
      Tendsto
        (fun N => ‖(μB b0 ^ N)⁻¹ * mpvOverlap (d := d) (toTensorFromBlocks μB B) (B b0) N‖)
        atTop (nhds (1 : ℝ)) := by
    have h := hSumOne.norm
    simpa using h
  have hNormProd : Tendsto
      (fun N => ‖(μA a0 ^ N)⁻¹ * c N *
        mpvOverlap (d := d) (toTensorFromBlocks μB B) (B b0) N‖)
      atTop (nhds (1 : ℝ)) := by
    have hMul :
        Tendsto
          (fun N => ‖c N * (μB b0 / μA a0) ^ N‖ *
            ‖(μB b0 ^ N)⁻¹ * mpvOverlap (d := d) (toTensorFromBlocks μB B) (B b0) N‖)
          atTop (nhds ((1 : ℝ) * 1)) :=
      hcAdj.mul hSumOneNorm
    have hMul' :
        Tendsto
          (fun N => ‖c N * (μB b0 / μA a0) ^ N‖ *
            ‖(μB b0 ^ N)⁻¹ * mpvOverlap (d := d) (toTensorFromBlocks μB B) (B b0) N‖)
          atTop (nhds (1 : ℝ)) := by
      simpa using hMul
    refine Tendsto.congr ?_ hMul'
    intro N
    have heq :
        ‖(μA a0 ^ N)⁻¹ * c N *
            mpvOverlap (d := d) (toTensorFromBlocks μB B) (B b0) N‖
        = ‖c N * (μB b0 / μA a0) ^ N‖ *
            ‖(μB b0 ^ N)⁻¹ * mpvOverlap (d := d) (toTensorFromBlocks μB B) (B b0) N‖ := by
      rw [hFactored N, norm_mul]
    exact heq.symm
  -- Step 9: combine `hContra` (norm → 0) and `hNormProd` (norm → 1).
  have hContraNorm :
      Tendsto
        (fun N => ‖(μA a0 ^ N)⁻¹ * c N *
          mpvOverlap (d := d) (toTensorFromBlocks μB B) (B b0) N‖)
        atTop (nhds 0) := by
    have := hContra.norm
    simpa using this
  have h01 : (0 : ℝ) = 1 := tendsto_nhds_unique hContraNorm hNormProd
  exact absurd h01 (by norm_num)

/-- **Dominant-block fixed-left all-overlaps-decay contradiction.**

Symmetric specialisation of
`fixed_left_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT`
to the dominant `A`-block `j₀ = ⟨0, _⟩`.  The proof reduces to
`fixed_right_dominant_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT`
after swapping the two families via `EventuallyNonzeroProportionalMPV₂.symm`
and `tendsto_mpvOverlap_zero_swap`.

**Scope restriction (one-copy-per-sector):** inherited from `IsCanonicalFormBNT`.
See `docs/paper-gaps/ft_one_copy_scope_restriction.tex`. -/
lemma fixed_left_dominant_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hA : IsCanonicalFormBNT μA A)
    (hB : IsCanonicalFormBNT μB B)
    (hrA : rA ≠ 0) (hrB : rB ≠ 0)
    (hProp : EventuallyNonzeroProportionalMPV₂
      (toTensorFromBlocks μA A) (toTensorFromBlocks μB B))
    (hAllDecay : ∀ k : Fin rB,
      Tendsto (fun N => mpvOverlap (d := d)
        (A ⟨0, Nat.pos_of_ne_zero hrA⟩) (B k) N) atTop (nhds 0)) :
    False := by
  have hPropSwap : EventuallyNonzeroProportionalMPV₂
      (toTensorFromBlocks μB B) (toTensorFromBlocks μA A) :=
    hProp.symm
  have hAllDecaySwap : ∀ k : Fin rB,
      Tendsto (fun N => mpvOverlap (d := d) (B k)
        (A ⟨0, Nat.pos_of_ne_zero hrA⟩) N) atTop (nhds 0) := by
    intro k
    exact tendsto_mpvOverlap_zero_swap (d := d)
      (A ⟨0, Nat.pos_of_ne_zero hrA⟩) (B k) (hAllDecay k)
  exact fixed_right_dominant_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT
    B A hB hA hrB hrA hPropSwap hAllDecaySwap

end HeteroEqualCase

end MPSTensor
