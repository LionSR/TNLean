# CPSV16 FT — probe of the "exact leading coefficient" sub-lemma

**Date:** 2026-05-13
**Scope:** Path α (induction-based proportional FT) gate decision,
relative to the workplan in `audits/2026-05-13_cpsv16_ft_sorry_discharge_plan.md` §4.3.
**Status:** **Fundamental obstruction.** The exact identity is *false*
in general at finite chain length; the asymptotic input cannot upgrade
to eventual equality from `IsCanonicalFormBNT` hypotheses alone.
**Recommendation:** Path β (two-layer canonical form via
`IsBNTCanonicalFormSD` on the `SectorDecomposition` surface).

---

## 1. The target lemma

Path α (the equal-MPV induction analog for the proportional case)
requires the following gateway:

```lean
lemma exact_leading_coefficient_eventually_eq_of_eventuallyNonzeroProportionalMPV₂_CFBNT
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hA : IsCanonicalFormBNT μA A) (hB : IsCanonicalFormBNT μB B)
    (hrA : rA ≠ 0) (hrB : rB ≠ 0)
    (hProp : EventuallyNonzeroProportionalMPV₂
              (toTensorFromBlocks μA A) (toTensorFromBlocks μB B))
    {ζ : ℂ} (hζ_unit : ‖ζ‖ = 1)
    (hPhase : ∀ N : ℕ,
      mpvState (d := d) (B ⟨0, Nat.pos_of_ne_zero hrB⟩) N =
        ζ ^ N • mpvState (d := d) (A ⟨0, Nat.pos_of_ne_zero hrA⟩) N) :
    ∃ c : ℕ → ℂ,
      (∀ᶠ N in atTop, c N ≠ 0) ∧
      (∀ᶠ N in atTop,
        (∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N) =
          c N • (∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N)) ∧
      (∀ᶠ N in atTop,
        (μA ⟨0, Nat.pos_of_ne_zero hrA⟩) ^ N =
          c N * (μB ⟨0, Nat.pos_of_ne_zero hrB⟩ * ζ) ^ N)
```

The `c_N` is the proportionality scalar extracted via
`exists_eventually_weighted_mpvState_eq_smul_sequence_of_eventuallyNonzeroProportionalMPV₂`
(`ProportionalExpansion.lean:142`); it is uniquely determined by the
proportionality identity at each length `N` where the right-hand sum is
nonzero.

The asymptotic counterpart
`c N · ((μB 0 · ζ) / μA 0) ^ N → 1`
is already available as
`exists_dominant_phase_adjusted_scalar_tendsto_one_of_eventuallyNonzeroProportionalMPV₂_CFBNT`
(`ProportionalDominant.lean:388`).

The probe question: can the asymptotic limit be upgraded to an exact
eventual equality `(μA 0)^N = c_N · (μB 0 · ζ)^N` (i.e.,
`δ_N := (μA 0)^N - c_N (μB 0 ζ)^N = 0` eventually)?

---

## 2. Algebraic identity of the residue

Notation: `a0 := ⟨0, _⟩ : Fin rA`, `b0 := ⟨0, _⟩ : Fin rB`,
`V(X) := mpvState X` viewed as a vector in `ℂ^{d^N}`. All overlaps below
are with respect to the standard Hermitian inner product
`mpvInner X Y N`.

The exact proportionality identity is, *eventually*,

  `Σ_j (μA j)^N V(A_j) = c_N · Σ_k (μB k)^N V(B_k)`.        (★)

Use the single-family BNT linear independence of `{V(A_j) : j ∈ Fin rA}`
(eventually LI; `IsCanonicalFormBNT.isBNT`). Let
`P_A : H → span{V(A_j)}` be the orthogonal projection onto the A-span.
Apply `P_A` to both sides of (★). The LHS lives in the A-span, so
`P_A`-projection is the identity on it; the RHS becomes
`c_N · Σ_k (μB k)^N P_A V(B_k)`. Hence

  `Σ_j (μA j)^N V(A_j) = c_N · Σ_k (μB k)^N · P_A V(B_k)`.

Expand `P_A V(B_k) = Σ_j [V(B_k)]_{A_j} V(A_j)` (well-defined since
the A-family is LI eventually). Reordering and using A-LI
(`coefficient_eventually_eq_of_eventually_linearIndependent`, `Basic.lean:172`)
gives, for every `j`,

  `(μA j)^N = c_N · Σ_k (μB k)^N · [V(B_k)]_{A_j}`.           (†)

For `j = 0`, split `k = 0` and `k ≠ 0`. The phase relation
`hPhase` gives `V(B_0) = ζ^N · V(A_0)`, so
`P_A V(B_0) = ζ^N · V(A_0)`, i.e., `[V(B_0)]_{A_0} = ζ^N` and
`[V(B_0)]_{A_j} = 0` for `j ≠ 0`. Substituting into (†) at `j = 0`:

  `(μA 0)^N = c_N · (μB 0)^N · ζ^N
             + c_N · Σ_{k ≠ 0} (μB k)^N · [V(B_k)]_{A_0}`.

Equivalently,

  **`δ_N = c_N · Σ_{k ≠ 0} (μB k)^N · [V(B_k)]_{A_0}`**.       (‡)

This is the *exact* algebraic expression for the residue under
`IsCanonicalFormBNT` + phase hypothesis.

---

## 3. Why (‡) is generically nonzero at finite `N`

Each scalar `[V(B_k)]_{A_0}` is the `V(A_0)`-coordinate of
`P_A V(B_k)` in the A-basis. Equivalently it is the unique scalar
satisfying
  `<V(B_k), V(A_0)> = [V(B_k)]_{A_0} · <V(A_0), V(A_0)> + Σ_{j≠0} [V(B_k)]_{A_j} · <V(A_j), V(A_0)>`.

Under `IsCanonicalFormBNT`:

* `<V(A_0), V(A_0)> = mpvOverlap (A 0) (A 0) N → 1` (self-overlap
  normalized, `HasNormalizedSelfOverlap`).
* `<V(A_0), V(A_j)> = mpvOverlap (A 0) (A j) N → 0` for `j ≠ 0`
  (within-A cross-overlap decay, `IsCanonicalFormBNT.cross_overlap_tendsto_zero`).
* `<V(A_0), V(B_k)> → 0` for `k ≠ 0` *eventually-asymptotically* — this
  follows from uniqueness of the non-decaying right partner of `A 0`
  (which is `B 0` by `hPhase`), via
  `unique_right_nondecaying_overlap_partner_CFBNT`.

These three statements *together* imply
`[V(B_k)]_{A_0} → 0` as `N → ∞`. **They do not imply
`[V(B_k)]_{A_0} = 0` at any finite `N`.**

The matched FT regime (where `V(B_k) = ξ_k^N V(A_{σ(k)})` for some
permutation `σ` of `Fin r` with `σ 0 = 0` and unit `ξ_k`) is precisely
the case where `[V(B_k)]_{A_0} = 0` exactly for `k ≠ 0`. But this
exact matching is **what the FT concludes**, not a hypothesis at the
peeling step. At the start of the induction step we have only
`IsCanonicalFormBNT` separation, the phase relation for the leading
pair `(A_0, B_0)`, and asymptotic decay for `(A_0, B_k)`, `k ≠ 0`.

Concrete witness that (‡) is generically nonzero at finite `N`:

> Take `rA = rB = 2`, `μA 0 = μB 0 = 1`, `μA 1 = μB 1 = 1/2`,
> `V(A_0) = e_1`, `V(A_1) = e_2`, `ζ = 1` so `V(B_0) = e_1`.
> Let `V(B_1) = α V(A_0) + β V(A_1)` with `α, β` complex.
> Proportionality at length `N` forces
> `c_N = (1 - c_N · α · (1/2)^N)` and `(1/2)^N = c_N · β · (1/2)^N`,
> i.e., `c_N = 1/β` and `α = (β - 1) · 2^N`. For the asymptotic regime
> `β_N → 1` (gauge-phase compatible) and `α_N → 0`, but the *finite-N*
> values of `(α_N, β_N)` are not forced to be `(0, ζ_1^N)` exactly.
> Then `δ_N = c_N · α_N · (1/2)^N = (α_N / β_N) · (1/2)^N`, which is
> generically nonzero (and indeed → 0).

So `δ_N` is a *bona fide* sequence that converges to `0` but does not
vanish identically. **The exact identity `δ_N = 0 eventually` is FALSE
in general under the stated hypotheses.**

---

## 4. Strategies attempted and their obstructions

### 4.1 Strategy 1 — Combined-family LI (`Lem1` route)

The target identity (★) rearranges (after substituting `V(B_0)` via
`hPhase`) to

  `δ_N · V(A_0) + Σ_{j ≠ 0} (μA j)^N V(A_j)
      = c_N · Σ_{k ≠ 0} (μB k)^N V(B_k)`.

If the combined family
`{V(A_0)} ∪ {V(A_j) : j ≠ 0} ∪ {V(B_k) : k ≠ 0}` were eventually
linearly independent, then matching coefficients via
`coefficient_eventually_eq_of_eventually_linearIndependent` would force
`δ_N = 0` *and* `(μA j)^N = 0` for `j ≠ 0` *and* `c_N · (μB k)^N = 0`
for `k ≠ 0`. The last two are impossible (nonzero weights, nonzero
`c_N`), so this LI hypothesis is itself inconsistent with (★) for
`rA ≥ 2` or `rB ≥ 2`.

What we *do* have eventually-LI under uniqueness of partners:
`{V(A_0)} ∪ {V(B_k) : k ≠ 0}` (singleton-A + tail-B), via
`eventually_linearIndependent_of_two_family_overlap_tendsto_orthonormal`
in `BNT/Basic.lean:195`, since
  – `(A_0, A_0)` self-overlap → 1,
  – `(B_k, B_k)` self-overlap → 1 for `k ≠ 0`,
  – `(B_k, B_l)` → 0 for `k ≠ l`, both nonzero,
  – `(A_0, B_k)` → 0 for `k ≠ 0` (uniqueness of right partner from `hPhase`).

But the equation (★) involves `V(A_j)` for `j ≠ 0`, which are **not**
in this LI family. Re-expressing each `V(A_j)` (j ≠ 0) in
`{V(A_0)} ∪ {V(B_k) : k ≠ 0}` requires the very matching
`σ : Fin (rA - 1) ↪ Fin (rB - 1)` we are trying to construct
inductively. Direct LI-coefficient extraction in any LI sub-family that
actually contains all members of (★) is therefore unavailable.

**Verdict:** Strategy 1 cannot close the gap with the hypotheses given.

### 4.2 Strategy 2 — Algebraic identity (‡) combined with rate bounds

Identity (‡) tells us *exactly* what `δ_N` is:
`δ_N = c_N · Σ_{k≠0} (μB k)^N · [V(B_k)]_{A_0}`.

For `δ_N = 0` eventually, we need
`c_N · Σ_{k ≠ 0} (μB k)^N · [V(B_k)]_{A_0} = 0` for `N ≥ N_0`. Since
`c_N ≠ 0` eventually, this reduces to
  `Σ_{k ≠ 0} (μB k)^N · [V(B_k)]_{A_0} = 0`.

This is a relation in `ℂ` that must hold for *every* `N ≥ N_0`. As the
`(μB k)^N` are distinct geometric sequences (`‖μB k‖` strictly
decreasing for `k ∈ Fin rB`), uniqueness of representation of `0` as a
linear combination of distinct exponentials would force each
`[V(B_k)]_{A_0} = 0` for `k ≠ 0`.

But `[V(B_k)]_{A_0}` is itself *N-dependent* — it is the inner-product
projection of `V(B_k) = mpvState (B k) N` (an `N`-dependent vector)
onto `V(A_0)` (also `N`-dependent). So the algebraic uniqueness of
exponential representations does not apply: the coefficients of the
"exponential decomposition" themselves vary with `N`.

**Verdict:** Strategy 2 reduces to the algebraic obstruction `(‡)
generically nonzero at finite N` of §3.

### 4.3 Strategy 3 — Factor out `(μA 0)^N` and use convergence rate

Divide both sides of (★) by `(μA 0)^N` and project onto `V(A_0)`:

  `<V(A_0), V(A_0)> + Σ_{j ≠ 0} (μA j / μA 0)^N <V(A_0), V(A_j)>
      = c_N · (μB 0 ζ / μA 0)^N · <V(A_0), V(A_0)>
      + c_N · Σ_{k ≠ 0} (μB k / μA 0)^N · <V(A_0), V(B_k)>`.

The LHS → 1, the RHS → 1. Subtracting, dividing by `<V(A_0), V(A_0)>`
(eventually nonzero), one obtains

  `1 - c_N · (μB 0 ζ / μA 0)^N
      = (small terms tending to 0)`.

Multiply by `(μA 0)^N`:

  `δ_N · <V(A_0), V(A_0)> = (μA 0)^N · (RHS_small_terms - LHS_small_terms)`.

This *says* `δ_N = o(1) · (μA 0)^N` in the appropriate sense, but does
not establish `δ_N = 0`. The right-hand side of (‡) is *exactly* this
"small" combination, and §3 shows it is generically nonzero at any
finite `N`.

**Verdict:** Strategy 3 recovers the asymptotic (already known) and
does not produce exact equality.

---

## 5. Classification of the obstruction

**Fundamental, not technical.** The exact identity
`δ_N = 0 eventually` is *mathematically false* on the
`IsCanonicalFormBNT` surface in general — see the concrete witness in
§3 (taking `V(B_1)` to be a non-trivial linear combination of
`V(A_0), V(A_1)` while still admitting a proportional MPV identity).
No re-statement on the same surface, and no additional analytic
control, can rescue it: more hypotheses are needed.

The hypotheses that *would* close it are exactly the matched-FT
conclusion (`V(B_k) = ξ_k^N · V(A_{σ(k)})` for `k ≠ 0`, with
`σ : Fin (rB - 1) ↪ Fin (rA - 1)` and unit `ξ_k`). That is what the
peeling induction is trying to *produce*; it cannot be assumed at the
peel step. Equivalently, the gauge-phase pairing of *all* blocks (not
only the leading pair) would suffice, but that is the full content of
the FT itself.

The single-family BNT linear independence available at this surface
sees `Σ_k (μB k)^N V(B_k)` only through its A-basis coordinates, and
those coordinates pick up off-leading-pair contributions
`[V(B_k)]_{A_0}` that asymptotically vanish but do not vanish at finite
`N`. The path α induction's peeling step requires *exact* leading
cancellation; this is incompatible with the geometric off-diagonal
contributions that the BNT separation surface admits.

---

## 6. Status of this PR

No new lemma was added to the codebase. The probe is
conclusive — the gateway sub-lemma of path α as formulated in
`audits/2026-05-13_cpsv16_ft_sorry_discharge_plan.md` §4.3 is *not*
provable from `IsCanonicalFormBNT` (`StrictAnti`/one-copy-per-sector)
hypotheses plus the dominant phase relation.

`lake build` is unchanged from the new-`main` baseline.

---

## 7. Recommendation: pursue path β

Path β is the structural refactor outlined in
`audits/2026-05-13_cpsv16_ft_bridge_gap.md` §"Resolution" — split
`IsCanonicalFormBNT` into the two layers used by CPSV16:

* outer layer: spectral sector index `j` with strictly decreasing
  `‖λ_j‖` (the equivalent of the existing `mu_strict_anti`);
* inner layer: within-sector multiplicity `q ∈ Fin (r_j)` with
  unit-modulus weights `μ_{j,q}` (the missing data in
  `IsCanonicalFormBNT`).

Plan C (already in the codebase, see
`TNLean/MPS/FundamentalTheorem/SectorDecomposition/`) provides the
algebraic skeleton on `SectorDecomposition` + `HasBNTSectorData` +
unit-modulus weights:

* `fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_sectorDecomp`
  and its left counterpart in
  `SectorDecomposition/HNoCancelDischarge.lean`;
* `IsBNTCanonicalFormSD` wrapper in
  `SectorDecomposition/IsBNTCanonicalFormSD.lean`.

The path-β follow-up workstream is to (i) bridge
`IsCanonicalFormBNT` to `IsBNTCanonicalFormSD` (existing
`exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks` is the natural
foundation), and (ii) use the `_sectorDecomp` discharge lemmas to
retire the two `_CFBNT` sorries in
`TNLean/MPS/FundamentalTheorem/Full/NondecayingOverlap.lean`.

The path-β content of the proof is the per-block projection of CPSV16
applied at the *sector* level, where the unit-modulus weights inside
each sector make the inner-product self-term `Σ_q μ_{j,q}^N` an
almost-periodic sequence (does not tend to zero), which closes the
contradiction directly without needing exact leading-coefficient
cancellation.

Concretely, the next PR should:

1. Provide an unconditional construction of `IsBNTCanonicalFormSD`
   from `IsCanonicalFormBNT` (the trivial multiplicity-1 instance — every
   sector has a single weight `μ_j`, automatically unit modulus only if
   `‖μ_j‖ = 1`, which holds for `j = 0` after normalization but not for
   `j ≥ 1`). This direct lift is therefore the same blocker noted in
   `cpsv16_ft_bridge_gap.md`; producing it requires retiring
   `mu_strict_anti` as the *only* sector-level ordering, replacing it
   with a two-layer `λ`-strict-anti + per-sector unit-modulus pair.

2. Alternatively, construct an `IsBNTCanonicalFormSD` from the
   *upstream* irreducible-TP-primitive block data via
   `exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks`
   (`CanonicalForm/PhaseClassSectorData.lean`); this is unconditional
   and avoids re-using the `IsCanonicalFormBNT` shim.

3. Rewrite the two `_CFBNT` callers in `NondecayingOverlap.lean` to
   consume the new sector-decomposition discharge lemmas through this
   bridge.

This is the *substantive* (300–500 LoC) refactor referenced in the
"Plan B path-β" arm of the workplan. Path α as currently formulated is
not viable; path β is the correct next step.

---

## 8. References

* arXiv:1606.00608, Theorem `thm1`, lines 1170–1192 (per-block
  projection argument).
* arXiv:2011.12127, Definition 4.2 (two-layer BNT canonical form).
* `audits/2026-05-13_cpsv16_ft_bridge_gap.md` (`IsCanonicalFormBNT` ↔
  sector-decomposition bridge gap).
* `audits/2026-05-13_cpsv16_ft_sorry_discharge_plan.md` §4.3
  (path α gateway sub-lemma; this probe is its outcome).
* `TNLean/MPS/FundamentalTheorem/Full/ProportionalDominant.lean:388`
  (`exists_dominant_phase_adjusted_scalar_tendsto_one_*` — the
  asymptotic input that was hoped to upgrade to the exact identity).
* `TNLean/MPS/FundamentalTheorem/Full/ProportionalExpansion.lean:434`
  (`eventuallyNonzeroProportionalMPV₂_tail_succ_of_total_and_selected`
   — the downstream consumer requiring the exact identity).
* `TNLean/MPS/BNT/Basic.lean:172`
  (`coefficient_eventually_eq_of_eventually_linearIndependent` — the
  LI coefficient-matching tool, applicable only to a single LI family).
* `TNLean/MPS/FundamentalTheorem/SectorDecomposition/` (path β
  infrastructure already in place).
