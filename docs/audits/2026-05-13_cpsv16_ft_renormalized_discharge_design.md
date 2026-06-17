# Renormalised discharge of the non-dominant per-block projection on the
# two-layer `IsBNTCanonicalFormSD` surface

**Date:** 2026-05-13
**Branch:** `feat/mps-ft-path-beta-renorm-discharge-scout`
**Status:** Scout + first implementation increment.  Confirms the abstract
`hNoCancel` of the two-layer skeleton is unusable for non-dominant `k₀`
and supplies the analytic centerpiece of a renormalised replacement.
**Context:** Continuation of `audits/2026-05-13_cpsv16_ft_path_beta_pr2_5_design.md`,
issue #1641 (Plan~C), PR #1669 (structural `HasRateQuantifiedCrossOverlapDecay`).

## Executive summary

The audit memo `audits/2026-05-13_cpsv16_ft_path_beta_pr2_5_design.md`
identified rate-quantified Q-internal cross-overlap decay as the
missing analytic input for the non-dominant per-block projection.
Re-examining the discharge:

1. The abstract `hNoCancel` hypothesis carried by
   `fixed_*_sectorDecomp_twoLayer` (`PerBlockProjection.lean:363`) and
   `fixed_*_paperFaithful_twoLayer` (`HNoCancelDischarge.lean:446`) is
   **unsatisfiable** for non-dominant `k₀` on the two-layer surface:
   both `c N` and `mpvOverlap Q.toTensor (Q.basis k₀) N` decay
   individually, so the product `c N · mpvOverlap Q.toTensor (Q.basis k₀) N`
   tends to zero unconditionally.  Any attempt to "discharge" `hNoCancel`
   would have to prove the impossible.

2. The route forward is a **renormalised** discharge:
   project the proportionality identity, then multiply both sides by
   `(λ_{k₀})^{-N}`.  The renormalised Q-side
   `T N := (λ_{k₀})^N⁻¹ * mpvOverlap Q.toTensor (Q.basis k₀) N`
   is the analytic centerpiece — it does **not** tend to zero, and
   discharging this fact replaces the load-bearing role formerly played
   by `hNoCancel`.

3. Two rate hypotheses are required: Q-internal (already merged as
   `HasRateQuantifiedCrossOverlapDecay`, PR #1669) **and** a new
   cross-family rate predicate comparing `‖λ_{P,j} / λ_{Q,k₀}‖` against
   the decay rate of `mpvOverlap (P.basis j) (Q.basis k₀)`.

## Validation of the obstruction

### Question 1 — Is `hNoCancel` vacuously false for non-dominant `k₀`?

**Verdict: yes.**  We trace through each factor.

**Subquestion 1a (`c N` bounded above):**
On the two-layer `IsBNTCanonicalFormSD` surface produced via the Choice~B
adapter (`IsCanonicalFormBNT.toIsBNTCanonicalFormSD`), the dominant
spectral levels satisfy `‖λ_{P,0}‖ = ‖λ_{Q,0}‖ = 1`
(`spectralLevel_dom_norm_one`).  The dominant-adjusted scalar
`c N · (μ_{B,0} / μ_{A,0})^N` has modulus tending to `1`
(`exists_dominant_adjusted_scalar_tendsto_norm_one_of_eventuallyNonzeroProportionalMPV₂_CFBNT`);
under Choice~B rescaling this reads `‖c N‖ → 1`, so `c N` is in
particular bounded above.

**Subquestion 1b (`mpvOverlap Q.toTensor (Q.basis k₀) N → 0`):**
Expanding via `mpv_toTensor_eq_sum_coeff` and the linearity of
`mpvOverlap`,

```
mpvOverlap Q.toTensor (Q.basis k₀) N
  = ∑ k, Q.coeff N k · mpvOverlap (Q.basis k) (Q.basis k₀) N.
```

By `norm_coeff_le_spectral_pow_mul_copies`,
`‖Q.coeff N k‖ ≤ ‖λ_{Q,k}‖^N · copies k`.  Three subcases:

* **`k = k₀` (non-dominant by hypothesis):** `‖λ_{Q,k₀}‖ < 1` (strict-anti
  + `‖λ_{Q,0}‖ = 1`), so `‖λ_{Q,k₀}‖^N → 0`; the self-overlap is bounded,
  so the diagonal term tends to zero.
* **`k > k₀`:** `‖λ_{Q,k}‖ < ‖λ_{Q,k₀}‖ < 1`, hence `‖λ_{Q,k}‖^N → 0`; the
  qualitative cross-overlap decay from
  `mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left_of_irreducible_TP`
  (or, in the structured setting, from `bnt_data`) is at least bounded.
* **`k < k₀`:** `‖λ_{Q,k}‖ ≤ 1` (dominant normalization), so
  `‖λ_{Q,k}‖^N ≤ 1` is bounded; cross-overlap decays to zero by the
  qualitative hypothesis.  Bounded times decay yields decay.

All three subcases tend to zero, hence the sum tends to zero.

**Subquestion 1c (the product `c N · overlap → 0`):**
Bounded × decay → 0.  The abstract `hNoCancel` claims this **does not**
tend to zero, which is in contradiction with the conclusion just
established.  Hence the hypothesis cannot be discharged on the two-layer
surface for non-dominant `k₀`; it is provably false.

**Subquestion 1d (impact on the skeleton):**
The skeleton `fixed_*_sectorDecomp_twoLayer` exposes `hNoCancel` as a
side condition and combines it with an LHS-decay argument to derive
`False`.  If `hNoCancel` is vacuously false, the skeleton cannot be
instantiated.  Equivalently: a downstream caller that wants to feed a
genuine analytic argument into the skeleton must provide a witness of
`hNoCancel`, but no such witness exists.  The skeleton must be
re-derived with a different load-bearing fact.

### Question 2 — Is the renormalised skeleton correct?

**Verdict: yes, under the rate hypothesis.**

Define
```
T N := (h.spectralLevel k₀ ^ N)⁻¹ * mpvOverlap Q.toTensor (Q.basis k₀) N.
```

Using the factorisation `Q.weight k q = h.spectralLevel k · ν_{k,q}` with
`‖ν_{k,q}‖ = 1` (from `weight_factor`), the coefficient factors as
`Q.coeff N k = (h.spectralLevel k)^N · ∑_q ν_{k,q}^N`.

After renormalisation,
```
T N = ∑ k, (h.spectralLevel k / h.spectralLevel k₀)^N ·
              (∑ q, ν_{k,q}^N) · mpvOverlap (Q.basis k) (Q.basis k₀) N.
```

**Diagonal `k = k₀`:** the geometric factor is `1`, so the term equals
`(∑ q, ν_{k₀,q}^N) · mpvOverlap (Q.basis k₀) (Q.basis k₀) N`.
By `unitModulus_power_sum_not_tendsto_zero` (`Algebra/UnitModulusPowerSum.lean`),
the unit-modulus power sum `∑ q, ν_{k₀,q}^N` does **not** tend to zero.
The self-overlap is assumed to tend to a nonzero limit `ℓ ≠ 0`.  Hence
the diagonal does not tend to zero either.

**Off-diagonal `k ≠ k₀`:** the norm of the summand is bounded by
```
copies k · ‖(λ_{Q,k} / λ_{Q,k₀})^N · mpvOverlap (Q.basis k) (Q.basis k₀) N‖
  ≤ copies k · ‖λ_{Q,k} / λ_{Q,k₀}‖^N
                · h.rateC k k₀ · h.rateEta k k₀ ^ N
  = copies k · h.rateC k k₀
                · (‖λ_{Q,k} / λ_{Q,k₀}‖ · h.rateEta k k₀)^N.
```
The base `‖λ_{Q,k} / λ_{Q,k₀}‖ · h.rateEta k k₀ < 1` by `rate_compatible`,
so the off-diagonal summand tends to zero geometrically.  Summing over
the finite index set, the off-diagonal contribution tends to zero.

**Conclusion:**  If `T N → 0`, then off-diagonal contribution → 0
forces the diagonal `(∑ q, ν_{k₀,q}^N) · mpvOverlap (Q.basis k₀) (Q.basis k₀) N`
to tend to zero, which divided by the eventually-nonzero self-overlap
forces `∑ q, ν_{k₀,q}^N → 0`, contradicting
`unitModulus_power_sum_not_tendsto_zero`.

### Question 3 — Is the renormalised LHS handleable?

**Verdict: yes, provided a cross-family rate hypothesis is added.**

The renormalised LHS reads
```
U N := (h.spectralLevel k₀ ^ N)⁻¹ * mpvOverlap P.toTensor (Q.basis k₀) N
     = ∑ j, (λ_{P,j} / λ_{Q,k₀})^N
              · (∑ q, ν_{P,j,q}^N) · mpvOverlap (P.basis j) (Q.basis k₀) N.
```

The `(∑ q, ν_{P,j,q}^N)` factor is bounded by `copies_P j`, and the
qualitative `mpvOverlap (P.basis j) (Q.basis k₀) N → 0` is available
from the wider `hAllDecay` assumption.  But the geometric factor
`(λ_{P,j} / λ_{Q,k₀})^N` may grow when `‖λ_{P,j}‖ > ‖λ_{Q,k₀}‖`.  A
**cross-family rate predicate** is required:

```
∀ j, ∃ C ≥ 0, η ∈ [0, 1),
   η · ‖λ_{P,j} / λ_{Q,k₀}‖ < 1 ∧
   ∀ N, ‖mpvOverlap (P.basis j) (Q.basis k₀) N‖ ≤ C · η^N.
```

This is the cross-family analogue of `HasRateQuantifiedCrossOverlapDecay`
applied to a single `Q`-target.  Under this hypothesis,
`U N → 0` follows by the same geometric × bounded × decay argument as
for the Q-side off-diagonal.

### Question 4 — Statement of the cross-family rate predicate

Two natural shapes:

**Shape A (pointwise per (P, Q) pair):**
```
structure HasCrossFamilyRateDecay
    (P Q : SectorDecomposition d)
    (lamP : Fin P.basisCount → ℂ) (lamQ : Fin Q.basisCount → ℂ) : Prop where
  exists_rate :
    ∃ (C η : Fin P.basisCount → Fin Q.basisCount → ℝ),
      (∀ j k, 0 ≤ C j k ∧ 0 ≤ η j k ∧ η j k < 1 ∧
              η j k * ‖lamP j / lamQ k‖ < 1) ∧
      (∀ j k N,
        ‖mpvOverlap (d := d) (P.basis j) (Q.basis k) N‖
          ≤ C j k * (η j k) ^ N)
```

**Shape B (per-target, fixing `k₀ : Fin Q.basisCount`):**  Wraps Shape~A
to a fixed `Q`-index.  Mirrors the way the per-block-projection skeleton
is structured around a fixed `k₀`.

**Recommendation:** Shape A — uniform over all `(j, k)` pairs, mirroring
`HasRateQuantifiedCrossOverlapDecay`'s structure.  The pointwise
per-target view is recoverable by specialising `k`.  Deferred to a
subsequent increment.

### Question 5 — Statement of the discharge theorem

```
theorem fixed_right_all_overlaps_decay_false_..._twoLayer_rateQuantified
    (P Q : SectorDecomposition d)
    (hP : IsBNTCanonicalFormSD P)
    (hQ : IsBNTCanonicalFormSD Q)
    (hPRate : HasRateQuantifiedCrossOverlapDecay P hP.spectralLevel)
    (hQRate : HasRateQuantifiedCrossOverlapDecay Q hQ.spectralLevel)
    (hCross : HasCrossFamilyRateDecay P Q hP.spectralLevel hQ.spectralLevel)
    (hProp : EventuallyNonzeroProportionalMPV₂ P.toTensor Q.toTensor)
    (k₀ : Fin Q.basisCount)
    (hAllDecay : ∀ j : Fin P.basisCount,
        Tendsto (fun N => mpvOverlap (d := d) (P.basis j) (Q.basis k₀) N)
          atTop (nhds 0))
    {ℓ : ℂ} (hℓ_ne : ℓ ≠ 0)
    (hQ_self_limit :
        Tendsto (fun N => mpvOverlap (d := d) (Q.basis k₀) (Q.basis k₀) N)
          atTop (nhds ℓ))
    (hc_lower : ∀ c : ℕ → ℂ,
        (∀ᶠ N in atTop, ∀ σ : Fin N → Fin d,
          mpv P.toTensor σ = c N * mpv Q.toTensor σ) →
        ∃ δ > 0, ∀ᶠ N in atTop, δ ≤ ‖c N‖) :
    False
```

The proof composes the cross-family bound on the LHS expansion (→ 0)
with the renormalised Q-side non-decay (≠ 0 in the limit) using the
`c`-lower-bound; cancellation is impossible.

## Status of Phase 2 implementation

**Option A** has been implemented:
`mpvOverlap_toTensor_basis_renorm_not_tendsto_zero` — the renormalised
Q-side analytic centerpiece.  Lives in
`TNLean/MPS/FundamentalTheorem/SectorDecomposition/RenormalizedNonCancellation.lean`.
Closed without `sorry`/`axiom`.  Builds.

Deferred to subsequent increments (each with explicit factored
sub-lemma names):

* `HasCrossFamilyRateDecay` predicate (Shape~A above) — to be added in
  the next increment as a sibling of `HasRateQuantifiedCrossOverlapDecay`.
* `mpvOverlap_toTensor_basis_renorm_LHS_tendsto_zero` — the LHS
  expansion bound consuming `HasCrossFamilyRateDecay`.
* `hNoCancel_renorm_single_seq` — the single-sequence non-cancellation
  consumer of `mpvOverlap_toTensor_basis_renorm_not_tendsto_zero`,
  analogous to `hNoCancel_single_seq` in `HNoCancelDischarge.lean`.
* `fixed_right_all_overlaps_decay_false_..._twoLayer_rateQuantified` —
  the full discharge theorem above.

## Open caveats

* The `c`-lower-bound hypothesis on the rescaled SD surface flows from
  `exists_dominant_adjusted_scalar_tendsto_norm_one_of_eventuallyNonzeroProportionalMPV₂_CFBNT`
  combined with the Choice~B rescaling; the path β scout PR~1.5
  records that this geometric problem dissolves under dominant
  normalization `‖λ_0‖ = 1`.  Independent of the rate-quantification
  issue addressed here.

* The renormalised self-overlap limit `mpvOverlap (Q.basis k₀) (Q.basis k₀) N → ℓ ≠ 0`
  is treated as an input.  Its source is the
  `HasNormalizedSelfOverlap` field of the canonical form, applied to
  the basis-block tensor `Q.basis k₀`.

## References

* CPSV16 (arXiv:1606.00608), Theorem~1, lines 1170--1192.
* CPSV21 (arXiv:2011.12127), Definition~4.3 (BNT eventual LI).
* `audits/2026-05-13_cpsv16_ft_path_beta_pr2_5_design.md` — original
  obstruction analysis, before the renormalisation re-examination.
* `audits/2026-05-13_cpsv16_ft_path_beta_scout.md` — path β architecture.
* `docs/paper-gaps/cpsv16_bnt_rate_quantification.tex` — paper-gap note
  recording the rate-quantification structural hypothesis.
* `TNLean/MPS/FundamentalTheorem/SectorDecomposition/RateQuantifiedDecay.lean` —
  Q-internal rate predicate (PR #1669).
* `TNLean/MPS/FundamentalTheorem/SectorDecomposition/HNoCancelDischarge.lean` —
  one-layer paper-faithful discharge (unchanged by this increment).
* `TNLean/MPS/FundamentalTheorem/SectorDecomposition/PerBlockProjection.lean` —
  two-layer skeleton (`hNoCancel` flagged vacuous for non-dominant `k₀`).
* `TNLean/Algebra/UnitModulusPowerSum.lean` —
  `unitModulus_power_sum_not_tendsto_zero`, the non-decay source.
* `TNLean/MPS/FundamentalTheorem/Full/NondecayingOverlap/FixedBlockDecay.lean:107, 152` —
  the two open sorries this work targets.

## Issue tracking

* #1641 (Plan~C tracker) — to be updated with these findings.
* #1607 (original CFBNT sorry tracker) — remains open until the full
  discharge lands.

## Forbidden directions (carry forward)

* NO combined-family LI / RSE / Option-LI hypotheses (vacuous in FT
  regime per execution `e0a5ec0f6a31`).
* NO induction-via-exact-coefficient (path α infeasible per
  `cpsv16_ft_exact_leading_coeff.md`).
* NO peel-arbitrary-`k₀` induction architecture.
* NO new `sorry` / `axiom` / `unsafe` without explicit factored
  documented sub-lemma name (see Phase~2 deferred list).
