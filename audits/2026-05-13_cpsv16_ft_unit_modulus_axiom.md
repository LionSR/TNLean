# CPSV16 FT — unit-modulus power-sum non-decay (Objective A, Plan C)

**Date:** 2026-05-13
**Scope:** Plan C, Objective A (per issue #1641) — discharge of the load-
bearing `hNoCancel` hypothesis in the paper-faithful per-block projection
on `SectorDecomposition`.
**Status:** Closed.  Both the analytic ingredient and the MPS-side
discharge are formalized; no new `sorry`, `axiom`, or `unsafe` is
introduced.

## Context

Plan C (issue #1641) re-states arXiv:1606.00608 Theorem `thm1` Step 1 on
the paper-faithful `SectorDecomposition` surface in
`TNLean/MPS/FundamentalTheorem/SectorDecomposition/PerBlockProjection.lean`.
The two main theorems

  `fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_sectorDecomp`
  `fixed_left_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_sectorDecomp`

both carry a load-bearing analytic hypothesis `hNoCancel`, factored out
on purpose to keep the per-block-projection algebraic skeleton clean and
independent of the analytic content.  Objective A asks to **discharge**
`hNoCancel` from paper-faithful inputs.

## Resolution

A single new analytic theorem is proved and lives in
`TNLean/Algebra/UnitModulusPowerSum.lean`:

```lean
theorem unitModulus_power_sum_not_tendsto_zero
    {r : ℕ} (hr : 0 < r) (μ : Fin r → ℂ) (hμ : ∀ q, ‖μ q‖ = 1) :
    ¬ Tendsto (fun N : ℕ => ∑ q : Fin r, (μ q) ^ N) atTop (nhds 0)
```

The proof is the standard Cesaro / Wiener argument:

1. If the power sum tended to zero, so would its squared norm `‖S N‖²`.
2. Expand `‖S N‖² = ∑_{q, q'} (μ q · star (μ q'))^N` as a finite double
   sum over `Fin r × Fin r`.
3. Cesaro-average term-by-term: each pair `(q, q')` contributes either
   `1` (when the unit-modulus ratio `μ q · star (μ q')` equals `1`, in
   particular for diagonal `q = q'`) or `0` (when the ratio differs from
   `1`, the geometric partial sums are bounded uniformly in `T`).
4. The Cesaro limit is therefore the cardinality of the resonant set
   `{(q, q') : μ q · star (μ q') = 1}`, which contains the diagonal and
   is `≥ r > 0`.  Combined with the Cesaro mean of a vanishing sequence
   being `0`, this is a contradiction.

The proof is entirely self-contained: it depends only on
`Filter.Tendsto.cesaro_smul`, `geom_sum_eq`, `Complex.mul_conj`,
`Complex.normSq_eq_norm_sq`, and standard finite-sum manipulations.  No
external axiom is introduced.

## MPS-side use

The discharge of the full `hNoCancel` is in
`TNLean/MPS/FundamentalTheorem/SectorDecomposition/HNoCancelDischarge.lean`.
The intermediate lemma

```lean
lemma mpvOverlap_toTensor_basis_not_tendsto_zero
    (Q : SectorDecomposition d)
    (hQ_unit : ∀ k q, ‖Q.sectors.weight k q‖ = 1)
    (k₀ : Fin Q.basisCount)
    (hQ_decay_offdiag : ∀ k, k ≠ k₀ →
        Tendsto (mpvOverlap (Q.basis k) (Q.basis k₀)) atTop (nhds 0))
    {ℓ : ℂ} (hℓ_ne : ℓ ≠ 0)
    (hQ_self_limit :
        Tendsto (mpvOverlap (Q.basis k₀) (Q.basis k₀)) atTop (nhds ℓ)) :
    ¬ Tendsto (mpvOverlap Q.toTensor (Q.basis k₀)) atTop (nhds 0)
```

is the bridge from the analytic ingredient to the projected
proportionality identity.  Combined with a lower bound `‖c N‖ ≥ δ > 0`
on the proportionality scalar, this gives the single-sequence
`hNoCancel_single_seq` and the universally-quantified
`hNoCancel_of_unitModulus_decay_c_norm_lower`.

End-to-end corollaries with discharged `hNoCancel`:

```lean
theorem fixed_right_all_overlaps_decay_false_paperFaithful : False
theorem fixed_left_all_overlaps_decay_false_paperFaithful : False
```

The `hc_lower` ingredient (positive lower bound on the proportionality
scalar) is taken as a hypothesis.  Deriving `hc_lower` from
`IsCanonicalFormBNT` is Objective B (the strict-anti structural refactor
of `IsCanonicalFormBNT`, out of scope for this workstream — see
`audits/2026-05-13_cpsv16_ft_bridge_gap.md`).

## Why this is *not* a factored axiom

The original Objective A plan permitted leaving the unit-modulus
power-sum non-decay statement as a factored axiom if a Lean proof proved
too analytically expensive (Bohr / Weyl equidistribution).  In the
event, the Wiener-style Cesaro argument is elementary enough to
formalize directly, and we did so.  No new `axiom` is introduced.

## References

* arXiv:1606.00608 Theorem `thm1`, lines 1170--1192 (per-block projection
  step; the unit-modulus power-sum non-decay is the non-cancellation
  ingredient there).
* `audits/2026-05-13_cpsv16_ft_definition_audit.md` §10 (Plan C YES
  verdict).
* `audits/2026-05-13_cpsv16_ft_bridge_gap.md` (Objective B / bridge gap
  to `IsCanonicalFormBNT`; out of scope for Objective A).
* `audits/2026-05-13_cpsv16_ft_discharge_attempt.md` (Plan A blocker;
  context only).
* Issue #1641 (Plan C workplan).
