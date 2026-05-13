/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.SectorDecomposition
import TNLean.MPS.FundamentalTheorem.SectorDecomposition.IsBNTCanonicalFormSD

/-!
# Paper Step 1 on the `SectorDecomposition` surface

This module re-states and proves Step 1 of arXiv:1606.00608, Theorem `thm1`
(the per-block-projection cancellation argument) on the paper-faithful
`SectorDecomposition` surface introduced by issue #1641 / Plan C.

## Main statements

* `fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_sectorDecomp`:
  fix a `Q`-block `k₀` and assume all overlaps from `P.basis j` to `Q.basis k₀`
  decay; the projected proportionality identity is then asymptotically
  contradictory.
* `fixed_left_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_sectorDecomp`:
  the symmetric statement obtained by swapping the two families.
* `EventuallyNonzeroProportionalMPV₂.symm` (in `TNLean.MPS.Defs`):
  `EventuallyNonzeroProportionalMPV₂` is symmetric in its two arguments;
  used (via dot notation `hProp.symm`) to reduce the left case to the right case.
* `SectorDecomposition.norm_coeff_le_spectral_pow_mul_copies` and
  `SectorDecomposition.norm_coeff_le_copies_of_IsBNTCanonicalFormSD`:
  two-layer counterparts of `norm_coeff_le_copies`, giving a geometric
  bound `‖coeff N j‖ ≤ ‖λ_j‖^N · copies j` and (under dominant
  normalization) the uniform bound `‖coeff N j‖ ≤ copies j`.
* The two-layer counterparts
  `fixed_{right,left}_all_overlaps_decay_false_of`
  `_eventuallyNonzeroProportionalMPV₂_sectorDecomp_twoLayer`: they consume
  `IsBNTCanonicalFormSD P` (resp. `IsBNTCanonicalFormSD Q`) in place of
  the unit-modulus hypothesis on the per-sector weights.  The abstract
  `hNoCancel` hypothesis is unchanged in shape; analytic discharge in
  the two-layer setting is deferred to a downstream module.

## Scope and load-bearing hypothesis

The argument is decoupled from `IsCanonicalFormBNT`.  The hypotheses are the
paper's: every per-sector weight has unit modulus, so the BNT coefficient
`coeff N j = ∑_q (weight j q)^N` is bounded in modulus by the multiplicity
`copies j`.  The load-bearing non-cancellation hypothesis `hNoCancel` is
factored out: it asserts that the projected proportionality right-hand side
`c_N · ⟪V(Q.toTensor), V(Q.basis k₀)⟫_N` does not tend to zero for the scalar
witnesses `c` produced by `hProp`.  In the paper this non-cancellation
follows from almost-periodicity of finite `N`-th power sums of unit-modulus
complex numbers combined with the dominant-weight-adjusted scalar limit;
both ingredients live outside this module.

## References

* Cirac, Pérez-García, Schuch, Verstraete, *Matrix Product Density Operators:
  Renormalization Fixed Points and Boundary Theories*, arXiv:1606.00608 (2017),
  Theorem `thm1`, lines 1170--1192.
* `audits/2026-05-13_cpsv16_ft_definition_audit.md` §10 (the per-block
  projection algebra).
-/

open scoped Matrix BigOperators
open Filter

namespace MPSTensor

variable {d : ℕ}

section PerBlockProjection

/-- **Bounded BNT coefficient from unit-modulus sector weights.**

If every sector weight has unit modulus, then the coefficient
`coeff N j = ∑_q (μ_{j,q})^N` is bounded in modulus by the multiplicity
`copies j` uniformly in `N`.  This is the boundedness ingredient required for
the per-block projection argument. -/
lemma SectorDecomposition.norm_coeff_le_copies
    (P : SectorDecomposition d)
    (hP_unit : ∀ j q, ‖P.sectors.weight j q‖ = 1)
    (N : ℕ) (j : Fin P.basisCount) :
    ‖P.coeff N j‖ ≤ (P.copies j : ℝ) := by
  classical
  unfold SectorDecomposition.coeff SectorWeightData.coeff
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ q : Fin (P.copies j), ‖(P.weight j q) ^ N‖ = 1 := by
    intro q
    rw [norm_pow, hP_unit j q, one_pow]
  have hsum :
      (∑ q : Fin (P.copies j), ‖(P.weight j q) ^ N‖) = (P.copies j : ℝ) := by
    calc
      (∑ q : Fin (P.copies j), ‖(P.weight j q) ^ N‖)
          = ∑ q : Fin (P.copies j), (1 : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro q _
            exact hterm q
      _ = (P.copies j : ℝ) := by
            simp
  exact hsum.le

/-- **Geometric BNT coefficient bound on the two-layer surface.**

For a two-layer BNT canonical form (`IsBNTCanonicalFormSD`), the spectral
level `λ_j` extracted by `hP.spectralLevel` and the unit-modulus quotient
`weight j q / λ_j` jointly give the geometric bound
`‖coeff N j‖ ≤ ‖λ_j‖^N · copies j`.  This is the natural two-layer
counterpart of `norm_coeff_le_copies`: each summand
`(weight j q)^N` has norm `‖λ_j‖^N` (since `‖weight j q‖ = ‖λ_j‖` by
the unit-modulus quotient), so the triangle inequality on the inner
sum of `copies j` terms yields the stated bound.

Combined with `IsBNTCanonicalFormSD.spectralLevel_norm_le_one` (dominant
normalization + strict-anti gives `‖λ_j‖ ≤ 1`), this specialises to the
uniform bound `‖coeff N j‖ ≤ copies j` in
`norm_coeff_le_copies_of_IsBNTCanonicalFormSD`. -/
lemma SectorDecomposition.norm_coeff_le_spectral_pow_mul_copies
    (P : SectorDecomposition d) (hP : IsBNTCanonicalFormSD P)
    (N : ℕ) (j : Fin P.basisCount) :
    ‖P.coeff N j‖ ≤ ‖hP.spectralLevel j‖ ^ N * (P.copies j : ℝ) := by
  classical
  unfold SectorDecomposition.coeff SectorWeightData.coeff
  refine (norm_sum_le _ _).trans ?_
  -- `‖weight j q‖ = ‖λ j‖` from the unit-modulus quotient.
  have hlam_ne : hP.spectralLevel j ≠ 0 := hP.spectralLevel_ne_zero j
  have hlam_norm_ne : ‖hP.spectralLevel j‖ ≠ 0 := norm_ne_zero_iff.mpr hlam_ne
  have hwnorm : ∀ q : Fin (P.copies j), ‖P.weight j q‖ = ‖hP.spectralLevel j‖ := by
    intro q
    have hquot : ‖P.sectors.weight j q / hP.spectralLevel j‖ = 1 :=
      hP.weight_factor j q
    rw [norm_div] at hquot
    -- `‖weight‖ / ‖lam‖ = 1`, with `‖lam‖ ≠ 0` ⇒ `‖weight‖ = ‖lam‖`.
    have := (div_eq_one_iff_eq hlam_norm_ne).mp hquot
    -- `P.weight` is an `abbrev` for `P.sectors.weight`, so they are defeq.
    change ‖P.sectors.weight j q‖ = ‖hP.spectralLevel j‖
    exact this
  have hterm : ∀ q : Fin (P.copies j),
      ‖(P.weight j q) ^ N‖ = ‖hP.spectralLevel j‖ ^ N := by
    intro q
    rw [norm_pow, hwnorm q]
  have hsum_eq : (∑ q : Fin (P.copies j), ‖(P.weight j q) ^ N‖)
      = ‖hP.spectralLevel j‖ ^ N * (P.copies j : ℝ) := by
    calc
      (∑ q : Fin (P.copies j), ‖(P.weight j q) ^ N‖)
          = ∑ _q : Fin (P.copies j), ‖hP.spectralLevel j‖ ^ N := by
            refine Finset.sum_congr rfl ?_
            intro q _
            exact hterm q
      _ = (P.copies j : ℝ) * ‖hP.spectralLevel j‖ ^ N := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                nsmul_eq_mul]
      _ = ‖hP.spectralLevel j‖ ^ N * (P.copies j : ℝ) := by ring
  exact hsum_eq.le

/-- **Uniform BNT coefficient bound on the two-layer surface
(dominant-normalized).**

Specialization of `norm_coeff_le_spectral_pow_mul_copies` using the
dominant normalization `‖λ_0‖ = 1` together with strict-anti
(`IsBNTCanonicalFormSD.spectralLevel_norm_le_one`): every spectral
level satisfies `‖λ_j‖ ≤ 1`, hence `‖λ_j‖^N ≤ 1`, and the geometric
bound collapses to the uniform bound `‖coeff N j‖ ≤ copies j`.

This matches the one-layer `norm_coeff_le_copies` conclusion and is
exactly what the per-block projection argument consumes, allowing the
two-layer `_sectorDecomp_twoLayer` lemmas to reuse the one-layer
algebraic skeleton without change. -/
lemma SectorDecomposition.norm_coeff_le_copies_of_IsBNTCanonicalFormSD
    (P : SectorDecomposition d) (hP : IsBNTCanonicalFormSD P)
    (N : ℕ) (j : Fin P.basisCount) :
    ‖P.coeff N j‖ ≤ (P.copies j : ℝ) := by
  refine (P.norm_coeff_le_spectral_pow_mul_copies hP N j).trans ?_
  have hlam_le : ‖hP.spectralLevel j‖ ≤ 1 := hP.spectralLevel_norm_le_one j
  have hlam_nn : 0 ≤ ‖hP.spectralLevel j‖ := norm_nonneg _
  have hpow : ‖hP.spectralLevel j‖ ^ N ≤ 1 := pow_le_one₀ hlam_nn hlam_le
  have hcopies_nn : 0 ≤ (P.copies j : ℝ) := Nat.cast_nonneg _
  calc
    ‖hP.spectralLevel j‖ ^ N * (P.copies j : ℝ)
        ≤ 1 * (P.copies j : ℝ) :=
          mul_le_mul_of_nonneg_right hpow hcopies_nn
    _ = (P.copies j : ℝ) := one_mul _


/-- **Per-block projection contradiction (fixed right block).**

Source: arXiv:1606.00608, Theorem `thm1`, lines 1170--1192.

Given two paper-faithful sector decompositions `P, Q` with unit-modulus
sector weights on `P`, eventual nonzero proportionality of the assembled
tensors, and a fixed `Q`-block index `k₀` such that all cross-overlaps from
`P.basis j` to `Q.basis k₀` decay to zero, the projected proportionality
forces the scalar-weighted projected sum to tend to zero.  Combined with the
non-cancellation hypothesis `hNoCancel`, this is contradictory.

This is Plan C on the `SectorDecomposition` surface (paper Step 1) for an
arbitrary fixed block, without any combined-family linear-independence input.

**Load-bearing hypothesis:** `hNoCancel` asserts that for every scalar
sequence `c` witnessing the eventual proportionality, the product
`c N · ⟪V(Q.toTensor), V(Q.basis k₀)⟫_N` does not tend to zero.  In the paper
this follows from (i) almost-periodicity giving `lim sup |coeff_Q N k₀| > 0`,
(ii) decay of off-diagonal `Q` cross-overlaps and bounded `|coeff_Q|` from
unit-modulus weights, and (iii) `|c_N|` bounded below via the dominant-weight
scaling lemma.  Folding (i)--(iii) into a single hypothesis decouples the
algebraic skeleton (here) from the analytic non-cancellation step. -/
lemma fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_sectorDecomp
    (P Q : SectorDecomposition d)
    (hP_unit : ∀ j q, ‖P.sectors.weight j q‖ = 1)
    (hProp : EventuallyNonzeroProportionalMPV₂ P.toTensor Q.toTensor)
    (k₀ : Fin Q.basisCount)
    (hAllDecay : ∀ j : Fin P.basisCount,
      Tendsto (fun N => mpvOverlap (d := d) (P.basis j) (Q.basis k₀) N)
        atTop (nhds 0))
    (hNoCancel : ∀ c : ℕ → ℂ,
      (∀ᶠ N in atTop, ∀ σ : Fin N → Fin d,
        mpv P.toTensor σ = c N * mpv Q.toTensor σ) →
      ¬ Tendsto
        (fun N => c N * mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N)
        atTop (nhds 0)) :
    False := by
  classical
  -- Step 1: extract a scalar sequence `c` witnessing the eventual
  -- proportionality, in the same style as
  -- `exists_eventually_weighted_mpvState_eq_smul_sequence_of_eventuallyNonzeroProportionalMPV₂`.
  set Pprop : ℕ → Prop := fun N =>
    ∃ c : ℂ, c ≠ 0 ∧ ∀ σ : Fin N → Fin d,
      mpv P.toTensor σ = c * mpv Q.toTensor σ
  have hEvent : ∀ᶠ N in atTop, Pprop N := hProp
  let c : ℕ → ℂ := fun N => if hN : Pprop N then Classical.choose hN else 1
  have hc_eq : ∀ᶠ N in atTop, ∀ σ : Fin N → Fin d,
      mpv P.toTensor σ = c N * mpv Q.toTensor σ := by
    refine hEvent.mono ?_
    intro N hN
    simp only [c]
    rw [dif_pos hN]
    exact (Classical.choose_spec hN).2
  -- Step 2: the projected proportionality identity holds eventually in `N`.
  --   `mpvOverlap P.toTensor (Q.basis k₀) N = c N * mpvOverlap Q.toTensor (Q.basis k₀) N`
  have hProj : ∀ᶠ N in atTop,
      mpvOverlap (d := d) P.toTensor (Q.basis k₀) N
        = c N * mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N := by
    refine hc_eq.mono ?_
    intro N hN
    exact
      mpvOverlap_eq_mul_of_mpv_eq_mul (d := d) P.toTensor Q.toTensor
        (c N) hN (Q.basis k₀)
  -- Step 3: the LHS expands by the BNT decomposition for `P.toTensor`.
  have hLHS_decomp : ∀ N : ℕ,
      mpvOverlap (d := d) P.toTensor (Q.basis k₀) N
        = ∑ j : Fin P.basisCount,
            P.coeff N j * mpvOverlap (d := d) (P.basis j) (Q.basis k₀) N := by
    intro N
    refine mpvOverlap_eq_sum_of_decomp_left
      (d := d) (g := P.basisCount) (dim := P.basisDim)
      P.toTensor P.basis (N := N)
      (fun j => P.coeff N j) ?_ (Q.basis k₀)
    intro σ
    exact P.mpv_toTensor_eq_sum_coeff (N := N) σ
  -- Step 4: each summand on the LHS tends to zero.
  -- Bounded coefficient × decaying overlap = decaying product.
  have hSummand : ∀ j : Fin P.basisCount,
      Tendsto
        (fun N => P.coeff N j * mpvOverlap (d := d) (P.basis j) (Q.basis k₀) N)
        atTop (nhds 0) := by
    intro j
    -- `|coeff N j * overlap N| ≤ copies j * |overlap N|`.
    refine squeeze_zero_norm
      (f := fun N => P.coeff N j * mpvOverlap (d := d) (P.basis j) (Q.basis k₀) N)
      (a := fun N => (P.copies j : ℝ)
                      * ‖mpvOverlap (d := d) (P.basis j) (Q.basis k₀) N‖)
      ?_ ?_
    · intro N
      simp only [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (P.norm_coeff_le_copies hP_unit N j) (norm_nonneg _)
    · -- multiply the decay limit by the constant `(copies j : ℝ)`.
      have h0 : Tendsto
          (fun N => ‖mpvOverlap (d := d) (P.basis j) (Q.basis k₀) N‖)
          atTop (nhds 0) :=
        (tendsto_zero_iff_norm_tendsto_zero.mp (hAllDecay j))
      have := h0.const_mul (P.copies j : ℝ)
      simpa using this
  -- Step 5: the LHS therefore tends to zero.
  have hLHS_tendsto : Tendsto
      (fun N => mpvOverlap (d := d) P.toTensor (Q.basis k₀) N)
      atTop (nhds 0) := by
    have hSum : Tendsto
        (fun N => ∑ j : Fin P.basisCount,
            P.coeff N j * mpvOverlap (d := d) (P.basis j) (Q.basis k₀) N)
        atTop (nhds 0) := by
      have hTo : Tendsto
          (fun N => ∑ j : Fin P.basisCount,
              P.coeff N j * mpvOverlap (d := d) (P.basis j) (Q.basis k₀) N)
          atTop (nhds (∑ _j : Fin P.basisCount, (0 : ℂ))) :=
        tendsto_finset_sum (Finset.univ : Finset (Fin P.basisCount))
          (fun j _ => hSummand j)
      simpa using hTo
    refine hSum.congr' ?_
    refine Filter.Eventually.of_forall ?_
    intro N
    exact (hLHS_decomp N).symm
  -- Step 6: combine with the projected proportionality identity to obtain the
  -- scalar limit `c N * mpvOverlap Q.toTensor (Q.basis k₀) N → 0`.
  have hRHS_tendsto : Tendsto
      (fun N => c N * mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N)
      atTop (nhds 0) := by
    refine hLHS_tendsto.congr' ?_
    exact hProj
  -- Step 7: contradiction with `hNoCancel`.
  exact hNoCancel c hc_eq hRHS_tendsto

/-- **Per-block projection contradiction (fixed left block).**

Source: arXiv:1606.00608, Theorem `thm1`, lines 1182--1185.

Symmetric counterpart of
`fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_sectorDecomp`.
Fixing a `P`-block `j₀` instead of a `Q`-block, the projected proportionality
identity is contradictory with the per-block decay of all cross-overlaps to
`P.basis j₀`.

The proof reduces to the right-block version after swapping `P` and `Q`:
the swapped proportionality witness `c⁻¹` plays the role of `c`, and the
hypothesis `hAllDecay` is rephrased via `tendsto_mpvOverlap_zero_swap`. -/
lemma fixed_left_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_sectorDecomp
    (P Q : SectorDecomposition d)
    (hQ_unit : ∀ k q, ‖Q.sectors.weight k q‖ = 1)
    (hProp : EventuallyNonzeroProportionalMPV₂ P.toTensor Q.toTensor)
    (j₀ : Fin P.basisCount)
    (hAllDecay : ∀ k : Fin Q.basisCount,
      Tendsto (fun N => mpvOverlap (d := d) (P.basis j₀) (Q.basis k) N)
        atTop (nhds 0))
    (hNoCancel : ∀ c : ℕ → ℂ,
      (∀ᶠ N in atTop, ∀ σ : Fin N → Fin d,
        mpv Q.toTensor σ = c N * mpv P.toTensor σ) →
      ¬ Tendsto
        (fun N => c N * mpvOverlap (d := d) P.toTensor (P.basis j₀) N)
        atTop (nhds 0)) :
    False := by
  -- Swap P and Q and apply the right-block version.
  refine
    fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_sectorDecomp
      Q P hQ_unit hProp.symm j₀ ?_ hNoCancel
  intro k
  exact tendsto_mpvOverlap_zero_swap (d := d) (P.basis j₀) (Q.basis k)
    (hAllDecay k)

set_option linter.style.longLine false in
/-- **Two-layer per-block projection contradiction (fixed right block).**

Two-layer counterpart of
`fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_sectorDecomp`
consuming `IsBNTCanonicalFormSD P` in place of the unit-modulus
hypothesis on the per-sector weights of `P`.  The two-layer surface
gives the uniform coefficient bound `‖P.coeff N j‖ ≤ copies j` via
`norm_coeff_le_copies_of_IsBNTCanonicalFormSD` (combining the unit-modulus
quotient `‖weight j q / λ_j‖ = 1` with the dominant-normalised
`‖λ_j‖ ≤ 1`), so the algebraic skeleton of the one-layer argument lifts
without change.

The abstract `hNoCancel` hypothesis retains the same shape as in the
one-layer statement.  The two-layer analytic discharge of `hNoCancel`
on the `SectorDecomposition` surface is not provided here; it is the
subject of a separate downstream module on the
`IsBNTCanonicalFormSD` surface. -/
lemma fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_sectorDecomp_twoLayer
    (P Q : SectorDecomposition d)
    (hP : IsBNTCanonicalFormSD P)
    (hProp : EventuallyNonzeroProportionalMPV₂ P.toTensor Q.toTensor)
    (k₀ : Fin Q.basisCount)
    (hAllDecay : ∀ j : Fin P.basisCount,
      Tendsto (fun N => mpvOverlap (d := d) (P.basis j) (Q.basis k₀) N)
        atTop (nhds 0))
    (hNoCancel : ∀ c : ℕ → ℂ,
      (∀ᶠ N in atTop, ∀ σ : Fin N → Fin d,
        mpv P.toTensor σ = c N * mpv Q.toTensor σ) →
      ¬ Tendsto
        (fun N => c N * mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N)
        atTop (nhds 0)) :
    False := by
  classical
  -- Extract a scalar sequence `c` witnessing the eventual proportionality.
  set Pprop : ℕ → Prop := fun N =>
    ∃ c : ℂ, c ≠ 0 ∧ ∀ σ : Fin N → Fin d,
      mpv P.toTensor σ = c * mpv Q.toTensor σ
  have hEvent : ∀ᶠ N in atTop, Pprop N := hProp
  let c : ℕ → ℂ := fun N => if hN : Pprop N then Classical.choose hN else 1
  have hc_eq : ∀ᶠ N in atTop, ∀ σ : Fin N → Fin d,
      mpv P.toTensor σ = c N * mpv Q.toTensor σ := by
    refine hEvent.mono ?_
    intro N hN
    simp only [c]
    rw [dif_pos hN]
    exact (Classical.choose_spec hN).2
  -- Projected proportionality identity holds eventually.
  have hProj : ∀ᶠ N in atTop,
      mpvOverlap (d := d) P.toTensor (Q.basis k₀) N
        = c N * mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N := by
    refine hc_eq.mono ?_
    intro N hN
    exact
      mpvOverlap_eq_mul_of_mpv_eq_mul (d := d) P.toTensor Q.toTensor
        (c N) hN (Q.basis k₀)
  -- LHS expansion by BNT decomposition for `P.toTensor`.
  have hLHS_decomp : ∀ N : ℕ,
      mpvOverlap (d := d) P.toTensor (Q.basis k₀) N
        = ∑ j : Fin P.basisCount,
            P.coeff N j * mpvOverlap (d := d) (P.basis j) (Q.basis k₀) N := by
    intro N
    refine mpvOverlap_eq_sum_of_decomp_left
      (d := d) (g := P.basisCount) (dim := P.basisDim)
      P.toTensor P.basis (N := N)
      (fun j => P.coeff N j) ?_ (Q.basis k₀)
    intro σ
    exact P.mpv_toTensor_eq_sum_coeff (N := N) σ
  -- Each summand tends to zero (uniform `copies j` bound on `‖coeff‖`).
  have hSummand : ∀ j : Fin P.basisCount,
      Tendsto
        (fun N => P.coeff N j * mpvOverlap (d := d) (P.basis j) (Q.basis k₀) N)
        atTop (nhds 0) := by
    intro j
    refine squeeze_zero_norm
      (f := fun N => P.coeff N j * mpvOverlap (d := d) (P.basis j) (Q.basis k₀) N)
      (a := fun N => (P.copies j : ℝ)
                      * ‖mpvOverlap (d := d) (P.basis j) (Q.basis k₀) N‖)
      ?_ ?_
    · intro N
      simp only [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (P.norm_coeff_le_copies_of_IsBNTCanonicalFormSD hP N j) (norm_nonneg _)
    · have h0 : Tendsto
          (fun N => ‖mpvOverlap (d := d) (P.basis j) (Q.basis k₀) N‖)
          atTop (nhds 0) :=
        (tendsto_zero_iff_norm_tendsto_zero.mp (hAllDecay j))
      have := h0.const_mul (P.copies j : ℝ)
      simpa using this
  -- LHS tends to zero.
  have hLHS_tendsto : Tendsto
      (fun N => mpvOverlap (d := d) P.toTensor (Q.basis k₀) N)
      atTop (nhds 0) := by
    have hSum : Tendsto
        (fun N => ∑ j : Fin P.basisCount,
            P.coeff N j * mpvOverlap (d := d) (P.basis j) (Q.basis k₀) N)
        atTop (nhds 0) := by
      have hTo : Tendsto
          (fun N => ∑ j : Fin P.basisCount,
              P.coeff N j * mpvOverlap (d := d) (P.basis j) (Q.basis k₀) N)
          atTop (nhds (∑ _j : Fin P.basisCount, (0 : ℂ))) :=
        tendsto_finset_sum (Finset.univ : Finset (Fin P.basisCount))
          (fun j _ => hSummand j)
      simpa using hTo
    refine hSum.congr' ?_
    refine Filter.Eventually.of_forall ?_
    intro N
    exact (hLHS_decomp N).symm
  -- Combine with projected proportionality to get the scalar limit.
  have hRHS_tendsto : Tendsto
      (fun N => c N * mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N)
      atTop (nhds 0) := by
    refine hLHS_tendsto.congr' ?_
    exact hProj
  -- Contradiction with `hNoCancel`.
  exact hNoCancel c hc_eq hRHS_tendsto

set_option linter.style.longLine false in
/-- **Two-layer per-block projection contradiction (fixed left block).**

Symmetric counterpart of
`fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_sectorDecomp_twoLayer`
fixing a `P`-block `j₀` instead of a `Q`-block.  Reduces to the
right-block two-layer version after swapping `P` and `Q`. -/
lemma fixed_left_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_sectorDecomp_twoLayer
    (P Q : SectorDecomposition d)
    (hQ : IsBNTCanonicalFormSD Q)
    (hProp : EventuallyNonzeroProportionalMPV₂ P.toTensor Q.toTensor)
    (j₀ : Fin P.basisCount)
    (hAllDecay : ∀ k : Fin Q.basisCount,
      Tendsto (fun N => mpvOverlap (d := d) (P.basis j₀) (Q.basis k) N)
        atTop (nhds 0))
    (hNoCancel : ∀ c : ℕ → ℂ,
      (∀ᶠ N in atTop, ∀ σ : Fin N → Fin d,
        mpv Q.toTensor σ = c N * mpv P.toTensor σ) →
      ¬ Tendsto
        (fun N => c N * mpvOverlap (d := d) P.toTensor (P.basis j₀) N)
        atTop (nhds 0)) :
    False := by
  refine
    fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_sectorDecomp_twoLayer
      Q P hQ hProp.symm j₀ ?_ hNoCancel
  intro k
  exact tendsto_mpvOverlap_zero_swap (d := d) (P.basis j₀) (Q.basis k)
    (hAllDecay k)

end PerBlockProjection

end MPSTensor
