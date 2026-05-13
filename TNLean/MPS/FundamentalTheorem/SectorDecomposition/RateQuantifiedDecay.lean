/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.SectorDecomposition
import TNLean.MPS.FundamentalTheorem.SectorDecomposition.IsBNTCanonicalFormSD

/-!
# Rate-quantified BNT cross-overlap decay on `SectorDecomposition`

**Status note (issue #1678).** This module is part of the rate-quantified
non-dominant per-block discharge stack.  Per issue #1678, the discharge
route this stack was built to support is **no longer active**: the
proportional-MPV non-decaying-overlap dispatcher
`exists_nondecaying_overlap_of_nonzeroProportionalMPV₂_CFBNT` now exposes
only the weak combined-family existential and is closed directly via
`TNLean.MPS.FundamentalTheorem.Full.NondecayingOverlap.CombinedLI`.  This
module is retained as a parametric conditional-discharge framework for
potential future incarnations of the proof.

This module introduces the `Prop`-level predicate
`HasRateQuantifiedCrossOverlapDecay` over a `SectorDecomposition P` and a
spectral level `lam : Fin P.basisCount → ℂ`.  The predicate strengthens the
qualitative cross-overlap decay carried by `IsBNTCanonicalFormSD` (and by
`mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left_of_irreducible_TP`
in `TNLean/MPS/Overlap/CastDecay.lean`) with a **quantitative geometric
rate** that beats the spectral weight ratio.

## Why a separate predicate

The two-layer per-block-projection lemmas

* `fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_sectorDecomp_twoLayer`
  in
  `TNLean/MPS/FundamentalTheorem/SectorDecomposition/PerBlockProjection.lean`
  (line 363), and
* `fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_paperFaithful_twoLayer`
  in
  `TNLean/MPS/FundamentalTheorem/SectorDecomposition/HNoCancelDischarge.lean`
  (line 446),

carry an abstract hypothesis `hNoCancel` that rules out cancellation of
the assembled overlap against the chosen projection block.  The analysis
recorded in `audits/2026-05-13_cpsv16_ft_path_beta_pr2_5_design.md` shows
that for a non-dominant projection index `k₀`, none of the three natural
discharge strategies on the present `IsBNTCanonicalFormSD` surface
succeeds.  In particular, factoring out the dominant weight
`μ_B^{(k₀)}` and renormalising the assembled overlap leaves a sum whose
`k < k₀` terms blow up like `(μ_B^{(k)} / μ_B^{(k₀)})^N`; the only way to
suppress them is for the cross-overlap
`⟨V^{(N)}(P.basis j), V^{(N)}(P.basis k)⟩` between distinct basis blocks
to decay **faster** than this weight ratio.

The qualitative limit
`mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left_of_irreducible_TP`
guarantees decay with an implicit rate `< 1` controlled by the transfer
matrix spectral gap, but the comparison

```
η_{j,k} · ‖λ_j / λ_k‖ < 1
```

is independent of the BNT structure and may fail generically.  We
therefore make the rate an **explicit hypothesis** at the structural
level and defer the analytic source (a derivation from the transfer
matrix spectral gap) to a downstream module.

## Why `lam` is an explicit parameter

`IsBNTCanonicalFormSD` packages the spectral level inside an
existential and exposes it through `Classical.choose`-based accessors
(`IsBNTCanonicalFormSD.spectralLevel` and friends).  The
rate-quantified predicate must compare `η_{j,k}` against the ratio
`‖λ_j / λ_k‖`, so it needs *a specific* `lam` rather than the abstract
existential.  Taking `lam` as an explicit parameter keeps the predicate
free of any commitment to `Classical.choose`: a caller building on top
of `IsBNTCanonicalFormSD P` instantiates `lam := h.spectralLevel`,
while a caller working with a concrete sector decomposition (e.g. via
`IsCanonicalFormBNT.toIsBNTCanonicalFormSD`) instantiates `lam` with
its rescaled weights directly.

## References

* CPSV16: Cirac--Pérez-García--Schuch--Verstraete, *Matrix Product
  Density Operators: Renormalization Fixed Points and Boundary
  Theories*, Ann. Phys. **378**, 100 (2017); arXiv:1606.00608.
  - §II Step~1, lines 1170–1192: the BNT cross-overlap argument
    implicitly assumes a rate fast enough to dominate any
    weight-ratio blow-up; the assumption is not stated explicitly.
* CPSV21: Cirac--Pérez-García--Schuch--Verstraete, *Matrix product
  states and projected entangled pair states: Concepts, symmetries,
  theorems*, Rev. Mod. Phys. **93**, 045003 (2021); arXiv:2011.12127.
  - Definition 4.3 (`def:4:BNT`, lines 1846–1850): packages eventual
    linear independence of the BNT vectors without quantifying the
    decay rate.
* `audits/2026-05-13_cpsv16_ft_path_beta_pr2_5_design.md` for the
  obstruction analysis.
* `docs/paper-gaps/cpsv16_bnt_rate_quantification.tex` for the
  paper-gap note recording this structural hypothesis.
* `TNLean/MPS/Overlap/CastDecay.lean` —
  `mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left_of_irreducible_TP`
  is the qualitative source from which a rate is in principle
  recoverable via the transfer matrix spectral gap.
-/

namespace MPSTensor

variable {d : ℕ}

/-- **Rate-quantified BNT cross-overlap decay** for a sector
decomposition.

Given a `SectorDecomposition P` and a spectral level
`lam : Fin P.basisCount → ℂ`, the predicate
`HasRateQuantifiedCrossOverlapDecay P lam` asserts the existence of
nonnegative constants `C j k` and rates `η j k ∈ [0, 1)` for every
ordered pair `j ≠ k`, such that

* `η j k · ‖lam j / lam k‖ < 1` — the rate is strict enough to beat the
  spectral weight ratio along the direction `j ⟶ k`; and
* `‖mpvOverlap (P.basis j) (P.basis k) N‖ ≤ C j k · (η j k)^N` for every
  `N`.

The hypothesis is the missing analytic input identified by the path β
PR 2.5 design memo
(`audits/2026-05-13_cpsv16_ft_path_beta_pr2_5_design.md`): it is what
lets the abstract `hNoCancel` field of the two-layer per-block-projection
lemmas

* `fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_sectorDecomp_twoLayer`
  (`PerBlockProjection.lean:363`), and
* `fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_paperFaithful_twoLayer`
  (`HNoCancelDischarge.lean:446`)

be discharged for non-dominant projection indices `k₀`.

The spectral level `lam` is an **explicit parameter** rather than an
existentially packaged field: the predicate is meant to be bundled with
whatever `lam` a caller is working with.  A caller building on top of
`IsBNTCanonicalFormSD P` instantiates `lam := h.spectralLevel`; a caller
working with a concrete weight family instantiates `lam` directly.
This decoupling avoids any commitment to `Classical.choose` at the
structural level.

Conceptually the rate
`η_{j,k}` is controlled by the transfer matrix spectral gap of the
mixed transfer operator
`mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left_of_irreducible_TP`
in `TNLean/MPS/Overlap/CastDecay.lean`, but the comparison with
`‖lam j / lam k‖` is independent of the BNT structure and may fail
generically.  The downstream analytic derivation is the subject of
"Option~2" of the design memo and is not addressed here.

## References

* CPSV16 §II Step~1, lines 1170–1192 (arXiv:1606.00608).
* CPSV21 Definition~4.3, lines 1846–1850 (arXiv:2011.12127). -/
structure HasRateQuantifiedCrossOverlapDecay (P : SectorDecomposition d)
    (lam : Fin P.basisCount → ℂ) : Prop where
  /-- There exist a constant family `C` and a rate family `η`, indexed by
  ordered pairs of basis blocks, satisfying the four-fold conjunction of
  nonnegativity, sub-unitality, weight-ratio compatibility, and a
  geometric cross-overlap bound. -/
  exists_rate :
    ∃ (C η : Fin P.basisCount → Fin P.basisCount → ℝ),
      (∀ j k, j ≠ k →
        0 ≤ C j k ∧ 0 ≤ η j k ∧ η j k < 1 ∧
        η j k * ‖lam j / lam k‖ < 1) ∧
      (∀ j k, j ≠ k → ∀ N,
        ‖mpvOverlap (d := d) (P.basis j) (P.basis k) N‖
          ≤ C j k * (η j k) ^ N)

namespace HasRateQuantifiedCrossOverlapDecay

variable {P : SectorDecomposition d} {lam : Fin P.basisCount → ℂ}

/-- **Rate constant** `C j k` for the cross-overlap bound between basis
blocks `j` and `k`.  Only the off-diagonal values (`j ≠ k`) carry
meaningful nonnegativity and bound assertions; see `rate_nonneg` and
`overlap_bound`. -/
noncomputable def rateC (h : HasRateQuantifiedCrossOverlapDecay P lam) :
    Fin P.basisCount → Fin P.basisCount → ℝ :=
  h.exists_rate.choose

/-- **Geometric decay rate** `η j k ∈ [0, 1)` for the cross-overlap
between basis blocks `j` and `k`.  Combined with `rate_compatible` this
rate strictly beats the spectral weight ratio `‖lam j / lam k‖`. -/
noncomputable def rateEta (h : HasRateQuantifiedCrossOverlapDecay P lam) :
    Fin P.basisCount → Fin P.basisCount → ℝ :=
  h.exists_rate.choose_spec.choose

/-- Both the rate constant and the rate itself are nonnegative for every
off-diagonal pair `j ≠ k`. -/
theorem rate_nonneg (h : HasRateQuantifiedCrossOverlapDecay P lam)
    {j k : Fin P.basisCount} (hjk : j ≠ k) :
    0 ≤ h.rateC j k ∧ 0 ≤ h.rateEta j k :=
  ⟨(h.exists_rate.choose_spec.choose_spec.1 j k hjk).1,
   (h.exists_rate.choose_spec.choose_spec.1 j k hjk).2.1⟩

/-- The rate is strictly less than `1` for every off-diagonal pair. -/
theorem rate_lt_one (h : HasRateQuantifiedCrossOverlapDecay P lam)
    {j k : Fin P.basisCount} (hjk : j ≠ k) :
    h.rateEta j k < 1 :=
  (h.exists_rate.choose_spec.choose_spec.1 j k hjk).2.2.1

/-- **Weight-ratio compatibility.**  The rate is strict enough to beat
the spectral weight ratio along the direction `j ⟶ k`:
`η j k · ‖lam j / lam k‖ < 1`.  This is the critical inequality that
the abstract `hNoCancel` hypothesis demands in the non-dominant
projection branch of the two-layer per-block-projection lemmas. -/
theorem rate_compatible (h : HasRateQuantifiedCrossOverlapDecay P lam)
    {j k : Fin P.basisCount} (hjk : j ≠ k) :
    h.rateEta j k * ‖lam j / lam k‖ < 1 :=
  (h.exists_rate.choose_spec.choose_spec.1 j k hjk).2.2.2

/-- **Geometric overlap bound.**  The cross-overlap between distinct
basis blocks decays at least as fast as `C j k · (η j k)^N`. -/
theorem overlap_bound (h : HasRateQuantifiedCrossOverlapDecay P lam)
    {j k : Fin P.basisCount} (hjk : j ≠ k) (N : ℕ) :
    ‖mpvOverlap (d := d) (P.basis j) (P.basis k) N‖
      ≤ h.rateC j k * (h.rateEta j k) ^ N :=
  h.exists_rate.choose_spec.choose_spec.2 j k hjk N

end HasRateQuantifiedCrossOverlapDecay

end MPSTensor
