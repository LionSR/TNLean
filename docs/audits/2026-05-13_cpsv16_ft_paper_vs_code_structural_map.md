# CPSV16 Fundamental Theorem of MPV: Paper vs. Code Structural Map

**Scope.** This audit verifies the claims in
`blueprint/comments202605/cpsv16_fundamental_theorem_analysis.md` against the
actual Lean code in `TNLean/MPS/FundamentalTheorem/Full/`. It compares the
proof of the Fundamental Theorem of MPV in CPSV16 (arXiv:1606.00608v4,
Appendix A, p. 32) — both in its **equal-MPV form** (`SameMPV₂`) and its
**proportional-MPV form** (`EventuallyNonzeroProportionalMPV₂`) — to the
corresponding Lean scaffolding. The deliverable is a paper-step↔Lean-lemma
correspondence, an inventory of structural deviations, and an assessment of
whether the strict-modulus restriction in `IsCanonicalFormBNT.mu_strict_anti`
justifies the deviation observed in the proportional case.

The audit is read-only: source files are inspected via `grep`, `read_file`,
and direct path inspection; nothing is modified.

---

> **Note on file:line citations.** This memo was written against the *pre-deletion* tree (commit `40c1c6f9` on `main`). Several lemmas and entire files cited below were retired in PR #1639; see `audits/2026-05-13_cpsv16_ft_deletion_candidates_and_archaeology.md` for the deletion list and `audits/2026-05-13_cpsv16_ft_sorry_discharge_plan.md` for the post-deletion roadmap.

---

## 0. Paper-side proof outline (recap; for the per-step table below)

CPSV16 Appendix A, p. 32, proof of the Fundamental Theorem (verbatim, with
labels assigned by the analysis memo §4.1–§4.2):

1. **Step 1 (per-block non-decay).** Fix a block `B_k`. It is impossible that
   ⟨V^(N)(B_k) | V^(N)(A_j)⟩ → 0 for **all** `j`. The argument uses Corollary
   `Lem1` / Lemma A.4 (the family `{V^(N)(B_k')}_{k'}` becomes pairwise
   asymptotically orthonormal, with non-vanishing weighted coefficients
   `∑_q ν_{k,q}^N`, which lets one project the proportionality identity and
   derive a contradiction from the supposed full decay).
2. **Step 2 (overlap → 1 ⇒ exact phase).** By Lemma A.2 the limit of
   |⟨V^(N)(B_k) | V^(N)(A_j)⟩| is 0 or 1; Step 1 forces it to be 1 for some
   `j_k`. Corollary A.3 then upgrades this to the exact length-by-length
   equality `V^(N)(B_k) = e^{iφ_k N} V^(N)(A_{j_k})`.
3. **Step 3 (gauge-phase equivalence at the tensor level).** Lemma A.2's
   second clause yields the matrix `X_k` with
   `B^i_k = e^{iφ_k} X_k A^i_{j_k} X_k^{-1}`.
4. **Step 4 (injectivity from BNT minimality).** The map `k ↦ j_k` is
   injective: two `B`-blocks mapped to the same `A_j` would be
   phase-equivalent, contradicting BNT minimality (Definition 2.6 (ii) +
   Prop. 2.7 (ii)). This gives `g_a ≥ g_b`.
5. **Step 5 (symmetric swap).** Exchange A and B in Steps 1–4 to get
   `g_b ≥ g_a`. Conclude `g_a = g_b`.

**Crucially:** the paper proof is a *one-shot, per-block existence statement
plus a separate (minimality) injectivity argument*. It does **not** recurse
on a shrinking pair of families and never introduces combined-family linear
independence as an intermediate hypothesis. The linear-independence facts it
uses are:

- BNT-LI of `{V^(N)(A_j)}_j` *alone* (internal to A);
- BNT-LI of `{V^(N)(B_k)}_k` *alone* (internal to B);
- Corollary `Lem1` / Lemma A.4 in its actual content: a family of NMPVs whose
  pairwise overlaps tend to δ-orthonormality is LI for large enough N. This
  is used **once**, with one of the families being a *single* fixed block on
  the opposite side, i.e., LI of "all of side X together with one fixed block
  on side Y" — *not* LI of the full combined family.

---

## 1. Paper vs. code: Step-by-step map (equal-MPV case)

The equal case (`SameMPV₂`) is what would be the literal target of Steps
1–5. The Lean entry points are
`exists_nondecaying_overlap_of_sameMPV₂_CFBNT` (Steps 1–2, the matching) and
`blocks_match_of_sameMPV₂_CFBNT` (Steps 3–5, the gauge-phase output and
injectivity assembly).

| Paper step | Paper claim | Lean lemma (file:line) | Notes |
|---|---|---|---|
| Step 1 | For each `B_k`, ∃ `j` with ⟨V^(N)(B_k), V^(N)(A_j)⟩ ↛ 0 | `exists_nondecaying_overlap_of_sameMPV₂_CFBNT` (`NondecayingOverlap.lean:82`) | **Differs from paper.** The Lean proof is *not* the per-block projection argument: it uses dominant-weight contradiction on `b0` (line 191, `dominant_B_contra`), peels the matched leading pair, and then **strong-induction on `rA + rB`** for non-leading blocks (`termination_by rA + rB`, line 632). See §3 below for the LI usage. |
| Step 2 | Overlap ↛ 0 ⇒ overlap → 1 in modulus ⇒ exact phase equality | `unique_left_nondecaying_overlap_partner_CFBNT`, `gaugePhaseEquiv_of_nondecaying_overlap_CFBNT`, `exists_phase_mpvState_eq_smul_of_nondecaying_overlap_CFBNT` (`NondecayingPartnerUnique.lean:145, 63, 100`); also `mpvOverlap_self_scale_of_mpv_eq_pow_mul`, `norm_eq_one_of_selfOverlap_scale` (per-pair dichotomy / norm-one phase) | Direct correspondence to Lemma A.2 + Corollary A.3 input. Used inside `exists_nondecaying_overlap_of_sameMPV₂_CFBNT` to extract `ζ`, `‖ζ‖ = 1`. |
| Step 3 | Tensor-level GPE `B_k = e^{iφ_k} X_k A_{j_k} X_k^{-1}` | `gaugePhaseEquiv_of_nondecaying_overlap_CFBNT` and the `GaugePhaseEquiv` packaging in `blocks_match_of_sameMPV₂_CFBNT` (`BlocksMatch.lean:148–155`, calling `mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left`) | Direct correspondence to Lemma A.2 second clause. |
| Step 4 | `k ↦ j_k` injective from BNT minimality | `hfA_inj`, `hgB_inj` inside `blocks_match_of_sameMPV₂_CFBNT` (`BlocksMatch.lean:160–264`) | The injectivity is proved by *contradiction with `hA_cross` / `hB_cross`* (the pairwise asymptotic orthogonality inside one family), using the same cross-overlap-norm-one calculation. This is mathematically equivalent to BNT minimality. |
| Step 5 | Symmetric swap | The pair `(fA, gB)` constructions in `blocks_match_of_sameMPV₂_CFBNT` (`BlocksMatch.lean:135, 269`), giving `rA ≤ rB` and `rB ≤ rA`, hence `rA = rB`. | Direct correspondence to "we would obtain `g_b ≥ g_a`". |

### Question A: peeling vs. per-block projection vs. both, in the equal case

**Answer.** *Both.* `exists_nondecaying_overlap_of_sameMPV₂_CFBNT` uses

1. a **per-block projection** argument for the *dominant* (leading) pair —
   `dominant_A_contra` (lines 161–185) and `dominant_B_contra` (lines
   187–217), each contradicting "all overlaps with `a0`/`b0` decay" by
   projecting the `μA a0 / μB b0`-normalized identity; and
2. a **strong-induction peeling** on `rA + rB` for non-leading blocks
   (`termination_by rA + rB`, line 632; the recursive call is at lines
   587–597 in the A-direction and 615–625 in the B-direction).

So the Lean equal-case argument is a *hybrid*: it uses the paper's per-block
projection only for the leading pair, and replaces the paper's per-block
projection on non-leading pairs by an inductive descent that has already
matched and removed the leading pair.

### Question B: does the equal case use combined-family LI?

**Answer.** *No.* Every LI invocation in
`exists_nondecaying_overlap_of_sameMPV₂_CFBNT` and the lemmas it calls is a
**per-tensor BNT-LI**:

- Lines 545, 591 in `NondecayingOverlap.lean`: `hA.isBNT.eventually_li` and
  `hB.isBNT.eventually_li`, used in the `rB = 1` and `rA = 1` base cases to
  conclude that an empty-tail sum equals zero, forcing a coefficient
  contradiction.
- The two LI-from-orthonormality helpers
  `eventually_linearIndependent_all_left_single_right_of_all_overlaps_decay_CFBNT`
  and
  `eventually_linearIndependent_all_right_single_left_of_all_overlaps_decay_CFBNT`
  (lines 709 and 768) are *defined* in this file but are **only invoked by
  the proportional-case `FixedBlockSingleton.lean`** base lemmas. They are
  not used inside the equal case.

So the equal case is source-faithful with respect to combined-family LI:
*no combined-family LI hypothesis is introduced at any point.* The recursion
on smaller `(rA−1, rB−1)` works because subtracting the matched leading pair
from `SameMPV₂` yields another `SameMPV₂` on the tail (lines 438–449,
`hTailState`), and the tail BNT structure is propagated via
`IsCanonicalFormBNT.ofSeparatedData` (lines 545–565). The clean recursion
exploits the **exact** coefficient identity `μA a0 = μB b0 · ζ` derived at
lines 360–433.

---

## 2. Paper vs. code: Step-by-step map (proportional-MPV case)

The proportional case (`EventuallyNonzeroProportionalMPV₂`) introduces an
unknown scalar sequence `c_N` linking the two assembled tensors. The Lean
scaffolding is split across several files, with the top-level entry being
`exists_nondecaying_overlap_of_nonzeroProportionalMPV₂_CFBNT`
(`NondecayingOverlap.lean:969`) which delegates the two existential
contradictions to
`fixed_left_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT`
(line 934) and
`fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT`
(line 897). Both of those are presently `sorry`.

The dominant case **is** discharged for the leading-block `k₀ = b0` (or
`j₀ = a0`) via `fixed_*_leading_all_overlaps_decay_false_*` (lines 827, 859),
which forward to
`dominant_projection_contradictions_of_eventuallyNonzeroProportionalMPV₂_CFBNT`
in `ProportionalDominant.lean:850`. The non-leading-block cases are what
remain open.

| Paper step | Paper claim | Lean lemma (file:line) | Notes |
|---|---|---|---|
| Step 1 (leading block) | For leading `B_k = B_{b0}`, ∃ `j` with non-decaying overlap | `fixed_right_leading_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT` (`NondecayingOverlap.lean:827`) → `dominant_projection_contradictions_of_eventuallyNonzeroProportionalMPV₂_CFBNT` (`ProportionalDominant.lean:850`) | **Faithful to the paper's per-block argument** for the leading block, using `b0`-normalized projection. The `c_N (μB b0 / μA a0)^N` adjusted-scalar norm-one bound (`exists_dominant_adjusted_scalar_tendsto_norm_one_of_eventuallyNonzeroProportionalMPV₂_CFBNT`, `ProportionalDominant.lean:536`) plays the role the paper's `∑_q ν_{k,q}^N` non-vanishing plays. |
| Step 1 (non-leading block) | For arbitrary `B_{k₀}`, ∃ `j` with non-decaying overlap | `fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT` (`NondecayingOverlap.lean:897`) | **`sorry`.** Issue #1607. The scaffolding for closing this is in `LeadingTail`, `ProportionalTail`, `ProportionalDominant`, `ProportionalExpansion`, `ProportionalExpansionLeft`, `ProportionalResidualSpan`, `FixedBlockSingleton`. See §3. |
| Step 2 | Overlap ↛ 0 ⇒ exact phase | `exists_phase_mpvState_eq_smul_of_nondecaying_overlap_CFBNT` (`NondecayingPartnerUnique.lean:100`) | Same lemma as the equal case. Source-faithful. |
| Step 3 | Tensor-level GPE | `gaugePhaseEquiv_of_nondecaying_overlap_CFBNT` (`NondecayingPartnerUnique.lean:63`) | Same lemma as the equal case. |
| Step 4 | `k ↦ j_k` injective from BNT minimality | Not yet assembled (no proportional analogue of `blocks_match_of_sameMPV₂_CFBNT` exists in the tree). | Would be a thin wrapper once Step 1 (general k₀) is closed; the BNT-cross-overlap calculation in `BlocksMatch.lean:160–264` is independent of which side has the unknown `c_N`. |
| Step 5 | Symmetric swap | Same as Step 4: pending Step 1's closure. | The two directions are symmetric in the scaffolding, both `sorry`. |

### Question C: which proportional-case lemmas correspond to which paper steps, and which are in-Lean-only?

| Lean lemma | Paper analogue (if any) | In-Lean-only? |
|---|---|---|
| `dominant_projection_contradictions_of_eventuallyNonzeroProportionalMPV₂_CFBNT` (`ProportionalDominant.lean:850`) | Step 1 *for the leading block only* | Restricted-scope version of paper Step 1. |
| `exists_dominant_adjusted_scalar_tendsto_norm_one_of_eventuallyNonzeroProportionalMPV₂_CFBNT` (`ProportionalDominant.lean:536`) | Implicit in paper (the boundedness of λ_N) | **In-Lean-only bookkeeping.** No paper lemma names this; it is the asymptotic surrogate for "λ_N bounded" in the analysis memo §4.2. |
| `exists_dominant_phase_adjusted_scalar_tendsto_one_of_eventuallyNonzeroProportionalMPV₂_CFBNT` (`ProportionalDominant.lean:303`) | None | **In-Lean-only.** Asymptotic-only; never gives an exact coefficient identity. |
| `exists_dominant_selected_diff_tendsto_zero_of_eventuallyNonzeroProportionalMPV₂_CFBNT` (`ProportionalDominant.lean:431`) | None | **In-Lean-only.** Asymptotic surrogate for paper's "subtract the matched dominant summand". |
| `adjusted_scalar_factor_eq` (`ProportionalScalar.lean:278`) | None (algebra) | **In-Lean-only bookkeeping.** A purely algebraic factor manipulation. |
| `leading_right_nondecaying_partner_eq_leading_left_of_eventuallyNonzeroProportionalMPV₂_CFBNT` (`LeadingPartner.lean:39`) | Implicit: the analogue of "the matched A-block of B's leading block must also be a leading A-block" | **In-Lean-only**, but a *consequence* of strict-modulus restriction (see §5 below). Has no paper analogue because in CPSV16 there is no strict modulus to begin with. |
| `exists_leading_phase_tail_diff_tendsto_zero_of_eventuallyNonzeroProportionalMPV₂_CFBNT` (`LeadingTail.lean:47`) | None | **In-Lean-only.** Asymptotic tail-difference statement; not exact. Designed to mirror the equal-case `hTailState`, but for proportional. |
| `exists_dominant_tail_diff_tendsto_zero_of_eventuallyNonzeroProportionalMPV₂_CFBNT` (`ProportionalTail.lean:41`) | None | **In-Lean-only.** As above. |
| `fixed_*_leading_all_overlaps_decay_false_*` (`NondecayingOverlap.lean:827, 859`) | Step 1 specialized to `k₀ = b0` (or `j₀ = a0`) | Restricted-scope versions of paper Step 1; thin wrappers around `dominant_projection_contradictions_*`. |
| `fixed_*_all_overlaps_decay_false_*` (`NondecayingOverlap.lean:897, 934`) | Step 1 for **arbitrary** `k₀` | These are the paper-Step-1 obligations. Currently `sorry`. |
| `fixed_*_all_overlaps_decay_false_*_finOne` (`FixedBlockSingleton.lean:45, 128`) | Step 1 for the **base case** when the fixed side has only one block | **In-Lean-only.** No paper analogue (the paper does not split on family size). |
| `eventually_linearIndependent_all_left_single_right_of_all_overlaps_decay_CFBNT` and `_all_right_single_left_*` (`NondecayingOverlap.lean:709, 768`) | Exactly Corollary `Lem1` / Lemma A.4 in the form actually used by the paper: LI of "all of one side + one fixed block on the other side" | **Faithful** to the paper's actual use of Corollary `Lem1`. |
| `selected_notMem_residual_span_of_linearIndependent_option`, `eventually_selected_notMem_residual_span_of_linearIndependent_option`, `selected_coefficient_eq_of_residual_span`, `eventually_selected_coefficient_eq_of_residual_span` (`ProportionalResidualSpan.lean:40, 79, 109, 143`) | None | **In-Lean-only.** These are pure linear-algebra coefficient-extraction lemmas. Their LI/residual-span hypothesis is *not* a paper hypothesis. The lemma docstrings explicitly state: "In a source-faithful application it must be derived from the BNT separation argument, or replaced by the equivalent residual-span exclusion supplied by that argument." (`ProportionalResidualSpan.lean:34–39`) |
| `eventuallyNonzeroProportionalMPV₂_tail_succAbove_of_phase_sum_li` (`ProportionalExpansion.lean:698`) | None | **In-Lean-only.** Postulates a residual two-family LI; the docstring (lines 686–697) explicitly flags the scope-restriction discrepancy: "CPSV16 Lemma `Lem1` gives this kind of independence only for the family in which all off-diagonal overlaps tend to zero. In the fixed-block step of Theorem `thm1`, lines 1181–1185, the local application gives independence for all blocks on one side together with **one** fixed block on the other side, not for the whole remaining tail appearing in this lemma." |
| `eventuallyNonzeroProportionalMPV₂_tail_succAbove_of_phase_sum_li_left` (`ProportionalExpansionLeft.lean:47`) | None | **In-Lean-only.** Same as the previous, with the role of A and B swapped. Same scope-restriction note in the docstring. |
| `eventually_selected_coefficient_eq_of_eventually_linearIndependent_sum` (`ProportionalExpansion.lean:305`) | None | **In-Lean-only.** Same shape: needs `LinearIndependent ℂ (Sum.elim v w)` where `v` is *all* of one side and `w` is the *remaining tail* of the other side. The docstring (lines 291–304) explicitly notes that CPSV16 Lemma `Lem1` does not directly supply this two-family residual LI. |

### Question D: precise statement of the flagged hypotheses, and why they fail

Let `nA, nB : ℕ`, `a0 : Fin (nA+1)`, `b0 : Fin (nB+1)`, with two BNT
families `A : (j : Fin (nA+1)) → MPSTensor d (dimA j)` and
`B : (k : Fin (nB+1)) → MPSTensor d (dimB k)`.

**(D.1) `_phase_sum_li` hypothesis** (`ProportionalExpansion.lean:710–713`):

```
hLI : ∀ᶠ N in atTop,
        LinearIndependent ℂ
          (Sum.elim
            (fun j : Fin (nA + 1) => mpvState (d := d) (A j) N)
            (fun k : Fin nB    => mpvState (d := d) (B (b0.succAbove k)) N))
```

i.e., eventual LI of the combined family

  `{V^(N)(A_j) : j = 0,…,nA} ∪ {V^(N)(B_k) : k ∈ {0,…,nB}∖{b0}}`.

This is **the full A-family plus the B-tail with b0 removed**.

**(D.2) `_phase_sum_li_left` hypothesis** (`ProportionalExpansionLeft.lean:60–64`):

```
hLI : ∀ᶠ N in atTop,
        LinearIndependent ℂ
          (Sum.elim
            (fun k : Fin (nB + 1) => mpvState (d := d) (B k) N)
            (fun j : Fin nA    => mpvState (d := d) (A (a0.succAbove j)) N))
```

i.e., LI of `{V^(N)(B_k) : k = 0,…,nB} ∪ {V^(N)(A_j) : j ∈ {0,…,nA}∖{a0}}`.

**(D.3) `_residual_span` hypothesis** (`ProportionalResidualSpan.lean:48`, in
the eventual form at lines 88, 151): given a family `u : κ → E` and a
singled-out vector `v₀ : E`, the lemmas need

```
v₀ ∉ Submodule.span ℂ (Set.range u)
```

(and the `Option κ` LI form on lines 43–47 that gives it). In the
fixed-block application this becomes "`V^(N)(A_{j₀})` not in the span of
`{V^(N)(B_k) : k ∈ {0,…,nB}}`" or its mirror — i.e., the *singled-out
selected block on one side is not in the span of all blocks on the other
side*. The Option-LI form on line 43 unfolds, after passing through
`Sum.elim`, to a special case of the combined two-family LI of (D.1)/(D.2).

#### Why all three generally fail in the FT regime

The analysis memo §3 toy example (taking `A := C`, `B := C` with `C` any
normal tensor) shows the issue at its sharpest, but the same phenomenon is
generic in the regime where the Fundamental Theorem **applies**:

- The conclusion of FT is precisely that, after a permutation `π`, for each
  `k` there is a phase `φ_k` with `V^(N)(B_k) = e^{iφ_k N} V^(N)(A_{π(k)})`
  for all `N`. So at the very conclusion of the theorem, every `B_k` is in
  the span of `{V^(N)(A_j)}_j` (and vice versa). The combined family is
  **maximally dependent** as a *consequence* of FT.
- Therefore (D.1), (D.2), (D.3) generically *fail in the regime FT is about*.
  They are not redundant hypotheses on the input — they are constraints that
  *exclude* the situations FT proves things about.
- This is consistent with the analysis memo §5(a): "the hypothesis `hLI` on
  the combined family fails for the actual situation the theorem is about.
  The lemma is vacuously vacuous, in a bad way."

Concretely: even at the **first peel** (no recursion yet, no induction
hypothesis used), if `g_a = g_b = g ≥ 2` and FT's conclusion holds, then
`V^(N)(B_k) − e^{iφ_k N} V^(N)(A_{π(k)}) = 0` for **every** `k`, including
`k ≠ b0`. So among the combined family of (D.1), the `nB` non-b0 B-vectors
are each in the span of the A-family. The combined family is dependent for
*every* `N`. (D.1) and (D.2) hence fail for the input FT applies to,
*independently of any peeling or induction*. They cannot be discharged by
the BNT structure on A and B alone.

What CPSV16 Corollary `Lem1` (= Lemma A.4) actually delivers is the much
weaker

  `LinearIndependent ℂ ({V^(N)(A_j)}_j ∪ {V^(N)(B_{k₀})})`,

i.e., one fixed block of the other side. This **is** consistent with the
FT-applicable regime (it says only that B_{k₀} is not in span of the A-family
— which is exactly the conclusion-to-be-contradicted "all overlaps decay").
The two LI hypotheses in `eventually_linearIndependent_all_left_single_right_of_all_overlaps_decay_CFBNT` and
`_all_right_single_left_*` (`NondecayingOverlap.lean:709, 768`) are this form
and *are* source-faithful.

---

## 3. The proportional case as a port of the equal-case template

### Question E: can the proportional case be done with the same architecture?

The equal-case proof closes because of the chain

  Step A (dominant norm equality) → Step B (dominant match)
  → exact `μA a0 = μB b0 · ζ` (line 360)
  → exact tail identity `hTailState` (line 438)
  → SameMPV₂ on (rA−1, rB−1) tails (line 491, `hEqual_tail`)
  → strong induction.

The critical line is the **exact** coefficient identity `μA a0 = μB b0 · ζ`,
established in `NondecayingOverlap.lean:359–434`:

```
have hμ_eq : μA a0 = μB b0 * ζ := by
  ...
  have h_ratio_tendsto : Tendsto (fun N => ratio ^ N) atTop (nhds 1) := ...
  exact eq_one_of_pow_tendsto_nhds_one h_ratio_tendsto
```

(Here `ratio := μB b0 · ζ / μA a0`; the `eq_one_of_pow_tendsto_nhds_one`
hammer at line 433 — `DominantWeight.lean:72` — converts the Tendsto into
an exact equality.) From this, `hTailState` at line 438 reads literally
`∑_{j≠a0} μA j^N • V_A(N,j) = ∑_{k≠b0} μB k^N • V_B(N,k)`, which is again a
`SameMPV₂` on the tails after weight-and-block reindexing.

In the proportional case, the analogous identity would be

  `c_N · μB b0^N · ζ^N = μA a0^N`

(equivalently `c_N · (μB b0 · ζ / μA a0)^N = 1`) **for every sufficiently
large N**, not just in the limit. Such an exact identity would let the
analogous tail-state subtraction yield another `EventuallyNonzeroProportionalMPV₂`
on (rA−1, rB−1) with the same scalar sequence `c_N`, ready for recursion.

### What the code actually proves

Searching the proportional scaffolding for the exact identity above:

- `adjusted_scalar_factor_eq` (`ProportionalScalar.lean:278`): purely
  algebraic; says `(μ^N)⁻¹ · c = (c · (ν/μ)^N) · (ν^N)⁻¹`. Not an identity
  on `c_N` at all.
- `exists_dominant_adjusted_scalar_tendsto_norm_one_of_eventuallyNonzeroProportionalMPV₂_CFBNT`
  (`ProportionalDominant.lean:536`): conclusion is
  ``Tendsto (fun N => ‖c N * (μB b0 / μA a0) ^ N‖) atTop (nhds 1)`` — only
  **norm-one in the limit**.
- `exists_dominant_phase_adjusted_scalar_tendsto_one_of_eventuallyNonzeroProportionalMPV₂_CFBNT`
  (`ProportionalDominant.lean:303`): conclusion is
  ``Tendsto (fun N => c N * ((μB b0 · ζ) / μA a0) ^ N) atTop (nhds 1)`` —
  the value-one limit, but still **only asymptotic**, with no
  identity-for-large-N upgrade.
- `exists_dominant_selected_diff_tendsto_zero_of_eventuallyNonzeroProportionalMPV₂_CFBNT`
  (`ProportionalDominant.lean:431`): conclusion is
  ``Tendsto (fun N => ‖(μA a0^N)⁻¹ · (μA a0^N · V_A(N,a0) − c_N · μB b0^N · V_B(N,b0))‖) atTop (nhds 0)`` —
  the **norm-of-the-difference goes to zero**, not an identity.

**Conclusion.** *No exact coefficient identity `c_N · μB b0^N · ζ^N = μA a0^N`
is established anywhere in the present code*. Every relevant statement is
asymptotic (`Tendsto … (nhds 1)`, or norm of difference `Tendsto … 0`).

There is no equal-case-style `eq_one_of_pow_tendsto_nhds_one` analogue
applicable to `c_N · (μB b0 · ζ / μA a0)^N`, because `c_N` is a **free
sequence**, not of the form `ratio^N` for some constant `ratio`. The
equal-case trick relied essentially on the form `ratio^N` to extract an
exact identity from a limit; once `c_N` is a free sequence, the limit gives
norm one but no length-by-length identity.

### Why this is the obstruction

The inductive step in the equal case **strips the leading pair exactly**:
the tail identity `hTailState` is literally an equation of vectors at every
`N`. In the proportional case, the analogous tail identity would have to be
literally

  `∑_{j≠a0} μA j^N · V_A(N,j) = c_N · ∑_{k≠b0} μB k^N · V_B(N,k)`

for sufficiently large `N`. This is what would let the recursion start with
the same `c_N` on the (rA−1, rB−1) tails (so the **same**
`EventuallyNonzeroProportionalMPV₂` predicate continues to hold). Without the
exact coefficient identity, all the current code produces is

  `‖(μA a0^N)⁻¹ · [(∑_{j≠a0} μA j^N · V_A(N,j)) − c_N · (∑_{k≠b0} μB k^N · V_B(N,k))]‖ → 0`

(line 64 of `LeadingTail.lean`, the asymptotic-only conclusion of
`exists_leading_phase_tail_diff_tendsto_zero_of_eventuallyNonzeroProportionalMPV₂_CFBNT`),
which is **not** `EventuallyNonzeroProportionalMPV₂` on the tails and cannot
be fed back into the recursion.

This is the actual obstruction to closing the proportional case via the
equal-case template. The `_phase_sum_li` / `_residual_span` helpers were
introduced as a *workaround*: under the (vacuous-in-the-FT-regime) hypothesis
that the residual combined family is LI for large `N`, the coefficient
extraction at lines 332 / 376 of `ProportionalExpansion.lean` would pin
`c_N · μB b0^N` to `μA a0^N · (ζ^N)⁻¹` exactly (as in
`ProportionalExpansionLeft.lean:88–122`). But that LI hypothesis is the very
hypothesis the analysis memo (and the lemma docstrings themselves) identify
as not derivable from the BNT data, and as failing for the input the
theorem applies to.

---

## 4. Discrepancies & wrong turns

In priority order:

1. **Combined residual-family LI hypotheses** (D.1, D.2 above):
   `eventuallyNonzeroProportionalMPV₂_tail_succAbove_of_phase_sum_li`
   (`ProportionalExpansion.lean:698`) and `_left` (`ProportionalExpansionLeft.lean:47`).
   These postulate eventual LI of the full opposite-side family plus the
   side-tail-with-fixed-block-removed. This **is** the combined-family LI
   the analysis memo flags as not implied by BNT and as failing in the
   FT-applicable regime.
   - **The lemmas' own docstrings acknowledge this scope mismatch.** Both
     contain explicit notes pointing to
     `docs/paper-gaps/cpsv16_fixed_block_cancellation.tex`.
2. **`selected_*_residual_span` family in `ProportionalResidualSpan.lean`.**
   These are purely linear-algebraic and correct as stated, but their `hLI`
   / `v₀ ∉ Submodule.span ℂ (Set.range u)` hypotheses are not paper
   hypotheses — they are intermediate conditions which, in any
   source-faithful application, would need to be derived from BNT separation,
   and they are precisely the residual-span exclusions equivalent to (D.1)
   / (D.2). The lemma docstrings explicitly state this (`ProportionalResidualSpan.lean:34–39, 74–78, 104–107, 139–142`).
3. **Peeling architecture in the equal case is a stylistic deviation from
   the paper but does not introduce combined-family LI.** The equal case
   uses strong induction on `rA + rB` instead of the paper's one-shot
   per-block argument. This is consistent with the paper's mathematics — the
   per-block Step 1 argument *is* what the dominant projection
   `dominant_A_contra` / `dominant_B_contra` does at the leading block; the
   induction is then used to defer the non-leading blocks. The only LI used
   is per-tensor BNT-LI. So this deviation is structural but harmless: it is
   *not* the wrong turn the analysis memo flags.
4. **`leading_right_nondecaying_partner_eq_leading_left_*` (`LeadingPartner.lean:39`)**
   is an in-Lean-only step that exists because of `mu_strict_anti`. The
   paper does not need it; in CPSV16 all canonical-form blocks share
   spectral radius 1, so there is no notion of "the leading B-block matches
   the leading A-block". This is a structural difference between the Lean
   restricted canonical form and CPSV16's canonical form. See §5.
5. **Asymptotic-only conclusions throughout the proportional scaffolding.**
   `exists_dominant_adjusted_scalar_tendsto_norm_one_*`,
   `_phase_adjusted_scalar_tendsto_one_*`,
   `_selected_diff_tendsto_zero_*`,
   `exists_leading_phase_tail_diff_tendsto_zero_*`,
   `exists_dominant_tail_diff_tendsto_zero_*` all produce `Tendsto`
   statements with limit value 1 or limit norm 0, but never an
   exact-for-large-N identity. This is the root cause of the architecture
   gap with the equal case (where `eq_one_of_pow_tendsto_nhds_one` upgrades
   the analogous limit to an exact identity).
6. **`fixed_*_all_overlaps_decay_false_*` are `sorry`** at
   `NondecayingOverlap.lean:897, 934`. The leading-block versions at lines
   827, 859 are discharged; the non-leading-`k₀` versions remain open.
   Issue #1607.

---

## 5. What the strict-modulus restriction changes

The Lean `IsCanonicalFormBNT` carries `mu_strict_anti : StrictAnti (‖μ ·‖)`
(`TNLean/MPS/BNT/Construction.lean:106`). This is strictly stronger than
CPSV16's CF, where all blocks have transfer-operator spectral radius 1.
The defense (paraphrasing the candidate argument in the prompt) is:

> "We always peel the leading block, never an arbitrary one. So the
> per-block projection only needs to handle the leading block, and the
> non-leading blocks come back via recursion on the smaller tail BNT family
> — which by induction has all the BNT-LI it needs. Combined-family LI is
> never required."

This defense **does** hold for the equal case: it is precisely the route
taken by `exists_nondecaying_overlap_of_sameMPV₂_CFBNT`, and the LI usage
audit (Question B) confirms that only per-tensor BNT-LI ever appears.

For the proportional case, the defense **partially holds but breaks at the
recursion step**, for the reason analyzed in §3:

1. **For the leading block, strict modulus helps.** The dominant projection
   `dominant_projection_contradictions_of_eventuallyNonzeroProportionalMPV₂_CFBNT`
   (`ProportionalDominant.lean:850`) is genuinely the paper's per-block
   Step 1 argument applied to the leading block. The supporting
   `exists_dominant_adjusted_scalar_tendsto_norm_one_*` works only because
   strict modulus forces `|μA j / μA a0| < 1` for all `j ≠ a0`, so the
   normalized geometric sums collapse to the diagonal — this is the
   `tendsto_norm_normalized_weighted_mpvState_sum_of_dominant` step at
   `ProportionalDominant.lean:565–598`. Under CPSV16's equal-modulus CF
   this collapse would not happen (the off-diagonal terms would not vanish
   under `μA a0^N` normalization), and the paper would instead need to
   project against the BNT element directly using the
   pairwise-orthonormality-in-the-limit produced by Lemma A.2 applied to
   the BNT family of one side.
2. **For non-leading blocks, the strict-modulus normalization is the wrong
   normalization.** If `k₀ ≠ b0` and one tries to repeat the dominant
   argument by normalizing against `μB k₀^N`, the term
   `‖μA j / μB k₀‖` can be **greater than 1** for `j` with
   `‖μA j‖ > ‖μB k₀‖`. (This is generically possible: under the FT regime
   the conclusion is `‖μA a0‖ = ‖μB b0‖`, but strict ordering on each side
   permits `‖μA j‖` for small `j` to exceed `‖μB k₀‖` for non-leading `k₀`.)
   The corresponding term in the normalized identity is then *unbounded*
   in `N`, and the diagonal-collapse argument fails. So under
   `IsCanonicalFormBNT.mu_strict_anti`, the **per-block projection of the
   paper does not transfer to non-leading `k₀`** directly. The leading-only
   peel is therefore *mandatory* under this hypothesis.
3. **But the leading-only peel still does not give the exact coefficient
   identity needed for clean recursion.** Even if we accept "we always peel
   the leading block", the recursion would need to feed an
   `EventuallyNonzeroProportionalMPV₂` on (rA−1, rB−1) tails with the same
   scalar sequence `c_N`, which requires the exact identity
   `c_N · μB b0^N · ζ^N = μA a0^N` for sufficiently large `N`. This exact
   identity is **not** proved anywhere in the code: only asymptotic versions
   exist (`exists_dominant_adjusted_scalar_tendsto_norm_one_*`,
   `exists_dominant_phase_adjusted_scalar_tendsto_one_*`,
   `exists_dominant_selected_diff_tendsto_zero_*` — all `Tendsto`
   statements). The equal-case `eq_one_of_pow_tendsto_nhds_one` trick does
   not apply because `c_N` is a free sequence, not of the form `ratio^N`.

**Net conclusion.** The strict-modulus restriction `mu_strict_anti` does
two things:

- It **legitimately** allows the equal case to avoid combined-family LI by
  the leading-only-peel + tail induction.
- It does **not** rescue the proportional case from needing the exact
  coefficient identity for recursion. The `_phase_sum_li` and
  `_residual_span` workarounds are an attempt to supply the exact
  identity *by hypothesis* (via residual-family LI plus coefficient
  extraction), but those hypotheses are vacuous in the FT-applicable regime,
  per the analysis memo §5(a) and Question D above.

So the candidate defense ("strict-modulus + leading-only peel ⇒ tail BNT-LI
suffices") is correct for the equal case but **fails to bridge to the
proportional case** because the proportional case needs an *exact*
coefficient identity (not just LI) at the peel step. That identity is
the missing piece; the LI hypotheses introduced in `_phase_sum_li` and
`_residual_span` are a way of *postulating* the exact identity at large
`N`, not deriving it.

### Recommended fix (as per the analysis memo §6, transposed to the proportional case)

Either:

- **(a)** Restate the proportional version of Step 1 in the paper's
  per-block-projection form, *for an arbitrary `k₀` directly* (not via
  recursion on a peeled tail). Under `IsCanonicalFormBNT.mu_strict_anti`
  this requires a more careful normalization: instead of dividing by
  `μA a0^N` or `μB b0^N`, project the proportionality identity against
  `V^(N)(B_{k₀})` itself and use the BNT-cross-orthogonality of B (the
  `hB_cross` field of `IsCanonicalFormBNT`) to isolate the `k₀`-coefficient
  in the B-side sum, exactly as the analysis memo's reformulation of Step 1
  in §4.2 does. This route uses only per-tensor BNT-LI / cross-overlap-decay
  and the bounded-norm boundedness of `c_N` (which would have to be
  established separately, but the existing
  `exists_dominant_adjusted_scalar_tendsto_norm_one_*` is a starting point);
  or
- **(b)** Establish the **exact** identity
  `∃ N₀, ∀ N ≥ N₀, c_N · μB b0^N · ζ^N = μA a0^N` (or equivalently
  `c_N · (μB b0 · ζ / μA a0)^N = 1` for large `N`) by some non-asymptotic
  argument — e.g., by going from `c_N · …^N → 1` to the eventual-equality
  by using the fact that `c_N` is a coefficient sequence determined by the
  proportionality, not an arbitrary sequence (this requires a separate
  algebraic uniqueness argument and is the harder route).

Route (a) mirrors the equal case's structure most directly and is what the
analysis memo recommends. Route (b) would salvage the current peel-induction
architecture but requires a genuinely new lemma. Neither route requires
combined-family LI on the (full-A ∪ tail-B) configuration of `_phase_sum_li`.

---

## 6. Summary table

| Aspect | Equal-MPV case (`SameMPV₂`) | Proportional-MPV case (`EventuallyNonzeroProportionalMPV₂`) |
|---|---|---|
| Top-level matching lemma | `blocks_match_of_sameMPV₂_CFBNT` (proved) | (no analogue assembled) |
| Step 1 (non-decay existence) | `exists_nondecaying_overlap_of_sameMPV₂_CFBNT` (proved, hybrid: per-block + induction) | `exists_nondecaying_overlap_of_nonzeroProportionalMPV₂_CFBNT` (proved modulo `sorry` in `fixed_*_all_overlaps_decay_false_*`) |
| Step 1 for leading block | covered by `dominant_*_contra` (per-block projection) | covered by `dominant_projection_contradictions_*` (per-block projection, leading only) |
| Step 1 for non-leading block | covered by strong induction on `rA + rB` | **`sorry`** — issue #1607 |
| Steps 2, 3 (Lemma A.2 + Corollary A.3) | `exists_phase_mpvState_eq_smul_of_nondecaying_overlap_CFBNT`, `gaugePhaseEquiv_of_nondecaying_overlap_CFBNT` (shared) | same shared lemmas |
| Step 4 (injectivity) | proved (`hfA_inj`, `hgB_inj` inside `blocks_match_of_sameMPV₂_CFBNT`) | not yet assembled |
| Step 5 (symmetric swap) | proved | not yet assembled |
| Recursion enabler | exact `μA a0 = μB b0 · ζ` (`NondecayingOverlap.lean:360`) and exact tail identity (`hTailState`, line 438) | only **asymptotic** versions exist (`Tendsto … (nhds 1)`, `… norm-one`, `norm-of-diff → 0`) — no exact identity |
| LI used (per-tensor BNT-LI only?) | **Yes**, only `hA.isBNT.eventually_li` / `hB.isBNT.eventually_li` | Mixed: per-tensor BNT-LI **plus** `_phase_sum_li` / `_residual_span` postulates of combined residual-family LI (not paper-faithful; flagged by lemma docstrings) |
| Source-faithfulness of Step 1 | source-faithful (only per-tensor BNT-LI invoked) | source-faithful for **leading block only**; non-leading-`k₀` step relies on the flagged `_phase_sum_li` / `_residual_span` workarounds |

---

## 7. Verdict

The analysis memo's claim is **substantially confirmed by direct code
inspection**:

- The equal-MPV case is source-faithful: no combined-family LI hypothesis is
  ever introduced; every LI invocation is per-tensor BNT-LI. The stylistic
  deviation (strong induction on `rA + rB` instead of the paper's one-shot
  per-block matching) is harmless because the leading-only peel allows the
  argument to repackage non-leading blocks via the recursion.
- The proportional-MPV case introduces combined-residual-family LI
  hypotheses (`_phase_sum_li`, `_phase_sum_li_left`,
  `selected_*_residual_span`) at the non-leading-`k₀` peel step. These
  hypotheses are exactly the ones the memo flags as not implied by the BNT
  data and as failing in the regime the Fundamental Theorem applies to.
  The lemma docstrings themselves acknowledge the scope mismatch.
- The underlying reason combined-family LI got introduced is that the
  proportional case never establishes the exact coefficient identity
  `c_N · μB b0^N · ζ^N = μA a0^N` for sufficiently large `N` that the
  equal case obtains for free from `eq_one_of_pow_tendsto_nhds_one`. The
  `_phase_sum_li` / `_residual_span` route is an attempt to recover this
  exact identity by postulating residual-family LI plus coefficient
  extraction — but that postulate is precisely the missing piece, not a
  consequence of the BNT data.
- The `IsCanonicalFormBNT.mu_strict_anti` strict-modulus restriction does
  legitimize the leading-only peel strategy (and does so essentially for
  the equal case), but does **not** supply the exact coefficient identity
  the proportional case needs to close the recursion cleanly. The
  candidate defense "we always peel the leading block, so combined-family
  LI is never needed — only tail BNT-LI suffices" is correct for the equal
  case but breaks at the recursive step for the proportional case.

The two recommended fixes are restated in §5: either reformulate Step 1
directly per-block (memo §6.1 transposed to the proportional setting),
which is what the analysis memo recommends, or establish the exact
coefficient identity by a separate non-asymptotic argument. Either way,
the `_phase_sum_li` and `_residual_span` hypotheses should be retired.
