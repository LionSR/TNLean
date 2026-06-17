# CPSV16 Proportional FT: Discharge Attempt Report

**Date:** 2026-05-13
**Branch:** `feat/mps-ft-discharge-fixed-block-sorries`
**Predecessor:** PR #1639 (`feat/mps-ft-delete-wrong-direction-scaffolding`)
**Task:** Discharge the two remaining `sorry`s in
`TNLean/MPS/FundamentalTheorem/Full/NondecayingOverlap.lean`:
- `fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT`
- `fixed_left_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT`

## Outcome

**Sorries NOT discharged.** Two concrete pieces of progress, plus a precise
diagnosis of the obstruction.

### What was attempted, what landed, what blocked

| Step | Status | Notes |
|------|--------|-------|
| 0. Verify obstacle | ✅ Confirmed | Direct projection for `k₀ ≠ b₀` produces both LHS → 0 and RHS → 0; no contradiction. See "Why direct projection fails" below. |
| 1. Per-block projection with cleverer normalization | ✅ Tried, failed | All three normalizations (by `μA(0)^N`, by `μB(0)^N`, by `μA(0)^N · μB(k₀)^N / μB(0)^N`) collapse to the same vanishing/vanishing structure. |
| 2a. Dominant partner decay (A_0 ↔ B for k>0) | ⚠️ Partial | Proved via `unique_right_nondecaying_overlap_partner_CFBNT` *assuming* A_0's partner is B_0. We do not yet have an analogue of `match_B0_is_A0` (equal-MPV `NondecayingOverlap.lean:288`) for the proportional case — see "Plan A blockers" below. |
| 2b. Exact coefficient identity `μA(a0)^N = c_N · (μB b0 · ζ)^N` | ❌ Blocked | The strongest asymptotic statement is `c_N · ((μB b0 · ζ) / μA a0)^N → 1` (Tendsto in ℂ). Upgrading to exact eventual equality is the key open math problem. |
| 2c. Tail proportionality via subtraction | ⚪ Not started | Mechanical once 2b is in hand (see `ProportionalExpansion.lean:434` `_tail_succ_of_total_and_selected`). |
| 2d. Recursion on `rA + rB` | ⚪ Not started | Direct clone of equal-MPV induction (see `NondecayingOverlap.lean:82–623`). |

### Concrete commit content

1. **Restored** the previously deleted lemma
   `exists_dominant_phase_adjusted_scalar_tendsto_one_of_eventuallyNonzeroProportionalMPV₂_CFBNT`
   in `TNLean/MPS/FundamentalTheorem/Full/ProportionalDominant.lean`. The
   discharge plan §7.2 Phase 1 explicitly identifies this as the building
   block for the missing exact eventual coefficient identity; it should
   not have been deleted as "orphan" in the deletion PR.
   - Input: phase relation `V(B b0) = ζ^N • V(A a0)` and `EventuallyNonzeroProportionalMPV₂`.
   - Output: `c_N · ((μB b0 · ζ) / μA a0)^N → 1` (Tendsto, **complex value**, not just norm).
   - This is the analog of "ratio^N → 1" in the equal-MPV case (where then
     `eq_one_of_pow_tendsto_nhds_one` immediately upgrades to `ratio = 1`).

2. **This audit report**, explicitly capturing the obstruction.

The two `sorry`s remain in place.

## Why direct projection fails for `k₀ ≠ b₀` (Step 0 confirmation)

Project the proportionality identity
`Σ_j (μA j)^N • V(A_j) = c_N · Σ_k (μB k)^N • V(B_k)`
onto `V(B_{k₀})`, normalize by `μA(a0)^N`:

- LHS / μA(a0)^N = Σ_j (μA j / μA a0)^N · ⟨B_{k₀}, A_j⟩_N.
  - All ratios `|μA j / μA a0| ≤ 1` (by `mu_antitone`).
  - All inners → 0 (from `hAllDecay`).
  - ⇒ LHS / μA(a0)^N → 0.
- RHS / μA(a0)^N = c_N · Σ_k (μB k / μA a0)^N · ⟨B_{k₀}, B_k⟩_N.
  - Diagonal k = k₀: `‖c_N · (μB k₀ / μA a0)^N‖`
    = `‖c_N · (μB b0 / μA a0)^N‖ · ‖(μB k₀ / μB b0)^N‖`
    → 1 · 0 = 0 (because `‖μB k₀ / μB b0‖ < 1` by `mu_strict_anti` for k₀ > 0).
  - Off-diagonal: bounded × → 0 = → 0.
  - ⇒ RHS / μA(a0)^N → 0.

Both sides tend to 0. **No contradiction.**

The leading-block case `k₀ = b₀` works because `‖μB b0 / μB b0‖ = 1`, making
the diagonal RHS term tend to a nonzero limit (1), giving the
0 ≠ 1 contradiction.

This confirms that in the one-copy-per-sector restricted surface, the
paper's per-block argument **inherently** depends on `k₀ = b₀`. The
restriction kills non-leading blocks geometrically; the paper's proof
relies on each sector carrying multiplicity contributing a sum of
unit-modulus numbers that does not vanish.

## Plan A blockers in detail

The discharge plan §7.2 prescribes a strong-induction architecture:
1. Match the leading pair (A_a0, B_b0).
2. Subtract the matched pair from the proportionality identity exactly,
   obtaining `EventuallyNonzeroProportionalMPV₂` on the (rA−1)×(rB−1) tails.
3. Recurse.

### Blocker 1: Identification of the leading partner

The equal-MPV proof's `match_B0_is_A0` (NondecayingOverlap.lean:288–339)
argues that the non-decaying partner of B_b0 must be A_a0. The argument
uses:
- `‖μA(a0)‖ = ‖μB(b0)‖` (from `dominant_weight_norm_eq_of_sameMPV₂_CFBNT`).
- `mu_strict_anti`: `‖μA(j₁)/μB(b0)‖ < 1` for j₁ ≠ a0.
- Normalized identity projection: LHS → 0 (geometric decay) ≠ RHS → 1 (diagonal).

In the proportional case, **we lack `‖μA(a0)‖ = ‖μB(b0)‖`.**
`exists_dominant_adjusted_scalar_tendsto_norm_one_*` gives only
`‖c_N · (μB b0 / μA a0)^N‖ → 1`. The proportionality scalar `c_N`
absorbs the leading-norm mismatch; the two leading norms need not be
equal.

**Consequence:** the leading-partner uniqueness argument does not
transcribe directly. A weaker statement still holds:

> If `(A_a0, B_{k_*})` is non-decaying for some `k_*`, then `k_* = b0`.

But proving this requires a non-trivial detour through the
proportionality scalar's behavior, which is itself the underlying
issue.

Sub-route: use `unique_right_nondecaying_overlap_partner_CFBNT` plus
the dominant-projection conjunct `((∀ k, A_a0 ↔ B_k decay) → False)`
to derive existence of *some* partner k_*. Then prove k_* = b0
separately. The cleanest attack is to project the proportionality
onto V(A_a0) and *normalize by `(μB b0)^N · ζ_{k_*}^N`* (where
ζ_{k_*} comes from the partner phase relation), but this analysis
inverts the role of which block is "dominant" and re-encounters the
same issue.

### Blocker 2: Exact eventual coefficient identity

Even granting that A_a0 ↔ B_b0 is the leading match with phase ζ,
the central blocker is upgrading

  `c_N · ((μB b0 · ζ) / μA a0)^N → 1`  (Tendsto in ℂ)

to

  `c_N · (μB b0 · ζ)^N = μA(a0)^N` for all sufficiently large N.

In the equal-MPV case `c_N = 1` identically, reducing this to
`ratio^N → 1 ⇒ ratio = 1` via `eq_one_of_pow_tendsto_nhds_one`. In
the proportional case `c_N` is free, so the "discretization" trick
does not apply.

Attempted attacks that **do not work**:

- **BNT-A linear independence to extract the V(A_a0) coefficient.**
  Substituting `V(B b0) = ζ^N · V(A a0)` into hState and isolating V(A_a0):
  ```
  δ_N · V(A_a0) + Σ_{j≠a0} (μA j)^N · V(A_j) = c_N · Σ_{k≠b0} (μB k)^N · V(B_k)
  ```
  where `δ_N := (μA a0)^N - c_N · (μB b0 · ζ)^N`. The right side contains
  `V(B_k)` for k > 0, which are **not** in the A-LI family. We can project
  onto V(A_a0) but the RHS projection `c_N · Σ_{k≠b0} (μB k)^N · ⟨A_a0, B_k⟩_N`
  tends to 0 (giving δ_N → 0, which we already had asymptotically) — without
  giving δ_N exactly 0.

- **Combined-family LI (CFLI / RSE / Option-LI).** Vacuous in the FT regime
  (the conclusion forces the combined family to be linearly dependent).
  Explicitly forbidden by the task and the cleanup PR #1639.

- **Phase-`c_N` extraction.** No, `c_N` does not have a known recursive or
  multiplicative structure across N values; the proportionality is given
  pointwise.

What *might* work (untried, conjectural):

- **Rate-of-convergence boosting.** If we can show
  `c_N · ((μB b0 · ζ) / μA a0)^N - 1` decays *faster than any geometric
  sequence*, combined with the fact that c_N · (μB b0 · ζ)^N lies in a
  countable set parametrized by C[x]-style polynomial relations
  (it doesn't — c_N is free!), we'd discretize. This is the discharge
  plan's "(a) discreteness + algebraic constraints" candidate (§4.3).
  Looks hard.

- **Renormalize to equal-MPV.** Define `μ̃_A := μA / μA(a0)`, run the
  equal-MPV argument on rescaled families. The proportionality scalar
  becomes a new c̃_N that asymptotically tends to a complex unit. Then
  exact-equality follows from `eq_one_of_pow_tendsto_nhds_one`-style
  arguments on the rescaled scalar's *limit form*. This is the discharge
  plan's "(c) normalize to equal-MPV case" — estimated ~150–200 lines,
  essentially a full re-proof.

## Assessment & recommendation

**The remaining sorries cannot be discharged within this PR's scope
without resolving the exact coefficient identity, which is itself a
non-trivial sub-problem.**

Two recommended next steps (in priority order):

1. **Open a focused issue:** "Prove the exact eventual coefficient
   identity `c_N · (μB b0 · ζ)^N = μA(a0)^N` for the proportional FT."
   This is the gateway to closing both sorries via Plan A. Estimated
   effort: 50–200 lines, depending on which of the discharge plan's
   candidate routes (a/b/c) succeeds. The restored lemma
   `exists_dominant_phase_adjusted_scalar_tendsto_one_*` is the
   starting point.

2. **Provisional sorry consolidation:** Replace the two existing sorries
   with a single named hypothesis (currently sketched as
   `exact_leading_coefficient_eventually_eq_*`) so that the rest of
   Plan A (peel + induction) can be implemented and the math gap is
   exposed in a single location. This was *not* done in this PR
   because the peel + induction is itself ~200 lines and would not
   meaningfully reduce the sorry count.

## References

- Discharge plan (Plan A vs Plan B): `audits/2026-05-13_cpsv16_ft_sorry_discharge_plan.md`
- Structural map (where each step lives): `audits/2026-05-13_cpsv16_ft_paper_vs_code_structural_map.md`
- Deletion archaeology: `audits/2026-05-13_cpsv16_ft_deletion_candidates_and_archaeology.md`
- Source-paper analysis: `blueprint/comments202605/cpsv16_fundamental_theorem_analysis.md`
- Scope restriction: `docs/paper-gaps/ft_one_copy_scope_restriction.tex`
- Equal-MPV induction (the architecture we are mirroring): `NondecayingOverlap.lean:82–623`
- Leading-block contradiction (Plan A's base case): `ProportionalDominant.lean:850` (`dominant_projection_contradictions_*`)
- Restored phase-adjusted helper (this PR): `ProportionalDominant.lean:368–509`
