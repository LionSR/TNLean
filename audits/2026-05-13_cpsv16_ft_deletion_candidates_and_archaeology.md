# CPSV16 Fundamental Theorem (Proportional Case): Deletion Candidates + PR Archaeology

**Date:** 2026-05-13
**Scope.** Identify every declaration in `TNLean/` whose existence is justified
solely by the wrong-direction *combined-family linear-independence* /
*residual-span exclusion* hypothesis (per `audits/2026-05-13_cpsv16_ft_paper_vs_code_structural_map.md`
and `blueprint/comments202605/cpsv16_fundamental_theorem_analysis.md`). Then
reconstruct how the wrong-direction scaffolding got built, PR by PR.

Read-only audit; no source files changed.

---

## §1 Deletion-candidates table

All file:line references are against the current `main` (HEAD = `40c1c6f9`).

### 1.A. The three "hypothesis shapes" the analysis memo flags

For brevity below:

* **CFLI** = the *combined-family* eventual linear-independence hypothesis on
  `Sum.elim (all of one side) (tail of other side)`. The two concrete forms
  are `(D.1)` in the structural map: `LinearIndependent ℂ (Sum.elim
  (fun j : Fin (nA+1) => mpvState (A j) N) (fun k : Fin nB => mpvState (B
  (b0.succAbove k)) N))` and its left mirror `(D.2)`. Vacuous in the FT
  regime.
* **RSE** = the *residual-span exclusion* hypothesis `v₀ ∉ Submodule.span ℂ
  (Set.range u)` and its eventual / Option-LI repackagings. Equivalent to a
  special case of CFLI under `Sum.elim` (per structural map §2 D.3).
* **PURE** = the declaration is pure linear algebra without any FT-specific
  semantics in its statement (could be reusable elsewhere in principle).

### 1.B. Direct wrong-direction declarations (the prompt's named starting list)

| Declaration | File:Line | Hypothesis shape | Used by (Lean code only) | Status |
|---|---|---|---|---|
| `eventually_selected_coefficient_eq_of_eventually_linearIndependent_sum` | `ProportionalExpansion.lean:305` | **CFLI** (PURE) | `eventually_selected_weighted_mpvState_eq_smul_of_phase_sum_and_li` (`ProportionalExpansion.lean:402`); `eventuallyNonzeroProportionalMPV₂_tail_succAbove_of_phase_sum_li_left` (`ProportionalExpansionLeft.lean:85`) | **DELETE** (only consumers are wrong-direction siblings; pure algebra but currently only feeds dying consumers) |
| `eventually_selected_weighted_mpvState_eq_smul_of_phase_and_coeff` | `ProportionalExpansion.lean:343` | PURE (consumes `μA^N = c·(μB·ζ)^N`) | `eventually_selected_weighted_mpvState_eq_smul_of_phase_sum_and_li` (`ProportionalExpansion.lean:422`) | **DELETE** (sole consumer is wrong-direction; bridge purely for CFLI workflow) |
| `eventually_selected_weighted_mpvState_eq_smul_of_phase_sum_and_li` | `ProportionalExpansion.lean:376` | **CFLI** | `eventuallyNonzeroProportionalMPV₂_tail_succAbove_of_phase_sum_li` (`ProportionalExpansion.lean:750`) | **DELETE** |
| `eventuallyNonzeroProportionalMPV₂_tail_succAbove_of_phase_sum_li` | `ProportionalExpansion.lean:698` | **CFLI** | *No Lean consumer* (only blueprint refs in `blueprint/src/chapter/ch11_fundamental_theorem_proof.tex:446` and `blueprint/web/ch-ft_proof.html:1625`) | **DELETE** (orphan + wrong hypothesis) |
| `eventuallyNonzeroProportionalMPV₂_tail_succAbove_of_phase_sum_li_left` | `ProportionalExpansionLeft.lean:47` | **CFLI** | *No Lean consumer* (only blueprint refs at `blueprint/src/chapter/ch11_fundamental_theorem_proof.tex:479`) | **DELETE** + delete the file (this lemma is the only public content in `ProportionalExpansionLeft.lean`) |
| `selected_notMem_residual_span_of_linearIndependent_option` | `ProportionalResidualSpan.lean:40` | **RSE** (PURE) | `eventually_selected_notMem_residual_span_of_linearIndependent_option` (`ProportionalResidualSpan.lean:90`) | **DELETE** (only consumer is wrong-direction sibling) |
| `eventually_selected_notMem_residual_span_of_linearIndependent_option` | `ProportionalResidualSpan.lean:79` | **RSE** | *No Lean consumer* | **DELETE** (orphan) |
| `selected_coefficient_eq_of_residual_span` | `ProportionalResidualSpan.lean:109` | **RSE** (PURE) | `eventually_selected_coefficient_eq_of_residual_span` (`ProportionalResidualSpan.lean:154`) | **DELETE** (only consumer is wrong-direction sibling) |
| `eventually_selected_coefficient_eq_of_residual_span` | `ProportionalResidualSpan.lean:143` | **RSE** | *No Lean consumer* | **DELETE** (orphan) |

**Whole-file deletions implied by §1.B alone:**

* `TNLean/MPS/FundamentalTheorem/Full/ProportionalExpansionLeft.lean` (142
  lines, one lemma, no other content)
* `TNLean/MPS/FundamentalTheorem/Full/ProportionalResidualSpan.lean` (158
  lines, four lemmas, no other content)

`ProportionalExpansion.lean` loses 4 of its 25 lemmas (lines 305–428, 698–759
≈ 230 lines + docstrings) but the file as a whole still hosts source-faithful
helpers and must remain.

### 1.C. Orphan scaffolding consumed only by §1.B-tagged lemmas (or by nothing)

These take no `hLI` / residual-span hypothesis themselves, but exist solely
to feed the wrong-direction subgraph or are completely unused:

| Declaration | File:Line | Role | Used by | Status |
|---|---|---|---|---|
| `fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT` | `NondecayingOverlap.lean:897` (`sorry`) | Public obligation paired with #1607 | `exists_nondecaying_overlap_of_nonzeroProportionalMPV₂_CFBNT` (`:994`) | **AMBIGUOUS** — the *statement* is paper-faithful (the obligation of paper Step 1 for arbitrary `k₀`); its body is `sorry`. Its **dispatcher** (the public top-level lemma `exists_nondecaying_overlap_of_nonzeroProportionalMPV₂_CFBNT` at `:969`) is itself not consumed anywhere in `TNLean/`. Keep the obligation; replace it with the per-block-projection proof recommended by the structural map §5 route (a). |
| `fixed_left_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT` | `NondecayingOverlap.lean:934` (`sorry`) | symmetric to above | `exists_nondecaying_overlap_of_nonzeroProportionalMPV₂_CFBNT` (`:989`) | **AMBIGUOUS** (same as above) |
| `exists_nondecaying_overlap_of_nonzeroProportionalMPV₂_CFBNT` | `NondecayingOverlap.lean:969` | Public top-level proportional Step 1 | *No Lean consumer* (only blueprint at `blueprint/lean_decls:903` and `ch11_fundamental_theorem_proof.tex:1346`) | **AMBIGUOUS** — currently an orphan public entry, but its *statement* is the correct paper-Step-1 destination for the proportional case. Keep the statement; delete the body (which is just a dispatch to the two `sorry` lemmas above) only after the per-block-projection proof is in. |
| `fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT_finOne` | `FixedBlockSingleton.lean:45` | "no-tail base case" for the (never-built) peel induction | *No Lean consumer* (only blueprint at `ch11_fundamental_theorem_proof.tex:1279`) | **DELETE** — base case of an induction strategy that the structural map and `cpsv16_fixed_block_cancellation.tex` explicitly retire. The lemma uses `eventually_linearIndependent_all_left_single_right_of_all_overlaps_decay_CFBNT` (source-faithful) and `coefficient_eventually_eq_of_eventually_linearIndependent` directly (not via the wrong-direction selector), so it is mathematically correct, but as a *base case for an abandoned induction* it is orphan scaffolding. |
| `fixed_left_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT_finOne` | `FixedBlockSingleton.lean:128` | symmetric | *No Lean consumer* | **DELETE** (same as above) |
| `leading_right_nondecaying_partner_eq_leading_left_of_eventuallyNonzeroProportionalMPV₂_CFBNT` | `LeadingPartner.lean:39` | Peel-induction support | `LeadingTail.lean:88` (only) | **DELETE** — consumer is orphan; in-Lean-only artifact of `mu_strict_anti`, no paper analogue (structural map Question C). |
| `exists_dominant_tail_diff_tendsto_zero_of_eventuallyNonzeroProportionalMPV₂_CFBNT` | `ProportionalTail.lean:41` | Peel-induction support | `LeadingTail.lean:97` (only) | **DELETE** — consumer is orphan. |
| `exists_leading_phase_tail_diff_tendsto_zero_of_eventuallyNonzeroProportionalMPV₂_CFBNT` | `LeadingTail.lean:47` | Peel-induction "tail asymptotic" | *No Lean consumer* (only blueprint at `ch11_fundamental_theorem_proof.tex:1092` and `cpsv16_fixed_block_cancellation.tex:97`) | **DELETE** — orphan, asymptotic-only conclusion never used; explicitly flagged in the paper-gap doc as "insufficient for the missing arbitrary fixed-block cancellation". |
| `exists_dominant_selected_diff_tendsto_zero_of_eventuallyNonzeroProportionalMPV₂_CFBNT` | `ProportionalDominant.lean:431` | feeds `ProportionalTail.lean:74` | `ProportionalTail.lean:74` (only) | **DELETE** (transitively orphan) |
| `exists_dominant_phase_adjusted_scalar_tendsto_one_of_eventuallyNonzeroProportionalMPV₂_CFBNT` | `ProportionalDominant.lean:303` | feeds 431 | `ProportionalDominant.lean:464` (only) | **DELETE** (transitively orphan) |
| `exists_nondecaying_overlap_dominant_of_eventuallyNonzeroProportionalMPV₂_CFBNT` | `ProportionalDominant.lean:920` | repackages leading-block contradiction | *No Lean consumer* (only blueprint at `ch11_fundamental_theorem_proof.tex:1017`) | **DELETE** — public wrapper that subsumes nothing; its conclusion is already implied by `dominant_projection_contradictions_*_CFBNT`. |
| `exists_adjusted_scalar_norm_and_inner_sequence_of_eventuallyNonzeroProportionalMPV₂` | `ProportionalProjection.lean:39` | Asymptotic packaging | *No Lean consumer* | **DELETE** — orphan packaging that does not advance the proof; structurally it is the "we have a scalar tending to norm 1 in a projected family" statement, useful only if the peel-induction architecture is kept. |
| `fixed_right_leading_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT` | `NondecayingOverlap.lean:827` | Leading-only fixed-right contradiction | `LeadingTail.lean:84` (only) | **DELETE** — public statement is source-faithful (paper Step 1 for the leading block, which is correctly proved here), but its only consumer is the orphan `exists_leading_phase_tail_diff_*`. Note: the same content remains available as `(dominant_projection_contradictions_of_eventuallyNonzeroProportionalMPV₂_CFBNT _ _ _ _ _ _ _).1`. **AMBIGUOUS** if a future per-block-projection route wants a named hook. |
| `fixed_left_leading_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT` | `NondecayingOverlap.lean:859` | symmetric | *No Lean consumer* | **DELETE** (same; raw orphan, never even called by `LeadingTail.lean`). |

**Whole-file deletions implied by §1.C:**

* `TNLean/MPS/FundamentalTheorem/Full/LeadingPartner.lean` (230 lines, one
  lemma, no other content)
* `TNLean/MPS/FundamentalTheorem/Full/LeadingTail.lean` (103 lines, one lemma)
* `TNLean/MPS/FundamentalTheorem/Full/ProportionalTail.lean` (138 lines, one
  lemma)
* `TNLean/MPS/FundamentalTheorem/Full/ProportionalProjection.lean` (98 lines,
  one lemma)
* `TNLean/MPS/FundamentalTheorem/Full/FixedBlockSingleton.lean` (198 lines,
  two lemmas)

`ProportionalDominant.lean` loses 3 of its 9 lemmas (lines 303–429,
431–533, 920–949 ≈ 250 lines, mostly the "phase_adjusted_scalar tendsto
one" / "selected diff tendsto zero" / "nondecaying overlap dominant"
chain). The remaining 6 lemmas (the dominant-projection contradictions and
their normalized-form helpers, lines 36–301, 536–617–905) are source-faithful
per the structural map and are needed by the recommended fix (Route (a) of
§5).

### 1.D. AMBIGUOUS / KEEP

These are paper-faithful, source-cited helpers in the proportional-case
subtree that *currently* have no live consumers but are exactly the
pieces a per-block-projection (Route-(a)) reproof would re-consume.
Recommended status: **KEEP** with a note that they survive the deletion.

| Declaration | File:Line | Reason to keep |
|---|---|---|
| `dominant_projection_contradictions_of_eventuallyNonzeroProportionalMPV₂_CFBNT` | `ProportionalDominant.lean:850` | Paper Step 1 for the leading block (source-faithful per structural map Q.C). |
| `dominant_projection_contradictions_of_normalized_proportional_inner` | `ProportionalDominant.lean:617` | Pure-LP form of the above; consumed by 850. |
| `exists_dominant_adjusted_scalar_tendsto_norm_one_of_eventuallyNonzeroProportionalMPV₂_CFBNT` | `ProportionalDominant.lean:536` | Asymptotic bound on `c_N`; needed for Route (a). |
| `tendsto_norm_normalized_weighted_mpvState_sum_of_dominant` | `ProportionalScalar.lean:247` | Pure LP, dominant normalization. Reusable. |
| `tendsto_norm_weighted_mpvState_sum_of_dominant_ratio` | `ProportionalScalar.lean:150` | Pure LP, reusable elsewhere. |
| `adjusted_scalar_factor_eq` | `ProportionalScalar.lean:278` | Pure algebra; reused at three sites including `LeadingPartner.lean:99` (which is going away) and `ProportionalDominant.lean:386, 902` (which are KEEP). |
| `tendsto_norm_scalar_of_*`, `tendsto_norm_weighted_mpvState_scalar_of_*`, `tendsto_norm_adjusted_weighted_mpvState_scalar_of_*`, `tendsto_geometric_smul_of_tendsto_norm_one`, `normalized_weighted_mpvInner_eq_mul_adjusted_of_eq_mul`, all other helpers in `ProportionalScalar.lean` | `ProportionalScalar.lean:35–423` | Generic asymptotic / normalization helpers, mostly pure LP. |
| `eventuallyNonzeroProportionalMPV₂_tail_succAbove_of_total_and_selected` and the family at `ProportionalExpansion.lean:432–693` (`weighted_mpvState_tail_eq_smul_sequence_of_total_and_selected`, `weighted_mpvState_sum_erase_zero_eq_sum_succ`, `weighted_mpvState_sum_erase_eq_sum_succAbove`, `eventuallyNonzeroProportionalMPV₂_tail_succ_of_total_and_selected`, `eventuallyNonzeroProportionalMPV₂_tail_succAbove_of_total_and_selected`) | `ProportionalExpansion.lean` | These take an *exact* selected-summand identity as hypothesis (the genuine output of the per-block argument in the equal-MPV case), not a CFLI hypothesis. They are paper-faithful packaging and would survive any Route-(a) reproof. **KEEP.** |
| `eventually_linearIndependent_all_left_single_right_of_all_overlaps_decay_CFBNT` and `_all_right_single_left_*` | `NondecayingOverlap.lean:709, 768` | Source-faithful CPSV16 `Lem1` inputs. **KEEP** (used by `FixedBlockSingleton.lean` even after the latter is deleted? — actually only `FixedBlockSingleton.lean` consumes them; *but* `cpsv16_fixed_block_cancellation.tex` explicitly designates these as the building blocks for the planned per-block-projection proof, so they must stay.) |

### 1.E. Summary count

**Files candidate for whole-file deletion: 6**

| File | Lines | Lemmas killed | Reason |
|---|---:|---:|---|
| `TNLean/MPS/FundamentalTheorem/Full/ProportionalExpansionLeft.lean` | 142 | 1 | wrong-direction (CFLI) |
| `TNLean/MPS/FundamentalTheorem/Full/ProportionalResidualSpan.lean` | 158 | 4 | wrong-direction (RSE ≡ CFLI) |
| `TNLean/MPS/FundamentalTheorem/Full/LeadingPartner.lean` | 230 | 1 | orphan peel-induction step |
| `TNLean/MPS/FundamentalTheorem/Full/LeadingTail.lean` | 103 | 1 | orphan peel-induction package |
| `TNLean/MPS/FundamentalTheorem/Full/ProportionalTail.lean` | 138 | 1 | orphan peel-induction asymptotic |
| `TNLean/MPS/FundamentalTheorem/Full/ProportionalProjection.lean` | 98 | 1 | orphan asymptotic packaging |
| `TNLean/MPS/FundamentalTheorem/Full/FixedBlockSingleton.lean` | 198 | 2 | orphan base cases of abandoned induction |
| **Total whole files** | **1067** | **11** | |

**Partial-file deletions:**

| File | Lines killed (≈) | Lemmas killed | Surviving fraction |
|---|---:|---:|---|
| `TNLean/MPS/FundamentalTheorem/Full/ProportionalExpansion.lean` | ≈ 230 | 4 (of 25) | `eventually_selected_coefficient_eq_of_eventually_linearIndependent_sum`, `eventually_selected_weighted_mpvState_eq_smul_of_phase_and_coeff`, `eventually_selected_weighted_mpvState_eq_smul_of_phase_sum_and_li`, `eventuallyNonzeroProportionalMPV₂_tail_succAbove_of_phase_sum_li` — all wrong-direction (CFLI). 21/25 lemmas survive. |
| `TNLean/MPS/FundamentalTheorem/Full/ProportionalDominant.lean` | ≈ 250 | 3 (of 9) | `exists_dominant_phase_adjusted_scalar_tendsto_one_*`, `exists_dominant_selected_diff_tendsto_zero_*`, `exists_nondecaying_overlap_dominant_*` — orphan peel-induction support. 6/9 survive. |
| `TNLean/MPS/FundamentalTheorem/Full/NondecayingOverlap.lean` | ≈ 100 (lines 827–891) | 2 (`fixed_*_leading_all_overlaps_decay_false_*`) | The two `sorry`s at 897, 934 are kept as the **correct paper-Step-1 obligations** awaiting a per-block-projection reproof. |
| **Total partial** | **≈ 580** | **9** | |

**Grand total:** ≈ 1650 lines, 20 declarations, 6 entire files, in 9 files
touched, all in `TNLean/MPS/FundamentalTheorem/Full/`. No other directory is
affected (per the grep audit: `EventuallyNonzeroProportionalMPV₂` is referenced
*only* inside `Full/` plus its definition in `MPS/Defs.lean`).

After the cull, the proportional-case subtree retains exactly:

* `ProportionalScalar.lean` (full)
* the source-faithful parts of `ProportionalExpansion.lean` (21 lemmas)
* the source-faithful parts of `ProportionalDominant.lean` (6 lemmas, the
  dominant-projection contradiction at line 850, plus its supporting layer)
* the source-faithful `Lem1`-input lemmas in `NondecayingOverlap.lean` plus
  the two unsolved obligations at 897, 934.

That is **exactly** the scaffolding Route (a) of the structural map §5 would
re-consume.

---

## §2 PR / branch archaeology

All commit hashes verified by `git show`; PR numbers from commit messages.
Times are in commit timezones (Europe).

### 2.0 The plan-of-record that prescribed the wrong architecture

Before the first PR landed, the plan was already locked in. Two GitHub
issues (both `state:OPEN` as of audit time) set the architecture explicitly:

* **Issue #1559** (umbrella, "Tracking: paper-faithful proportional MPV
  Fundamental Theorem (CPSV16 §II)"). The dependency chain it sets is
  `#1563 (Stage C) → #1566 → #1562`. Status snapshot at
  `/tmp/issue1559-body.md` says, for Stage C:

  > "5. Apply the same non-decaying-overlap statement recursively to the two
  > tail BNT families.
  > 6. Combine with the dominant contradictions from #1578 to cover all
  > blocks in both directions."

  i.e., **peel-induction was the plan**, transplanted from the equal-MPV
  case.

* **Issue #1563** ("Stage C of #1559", `/tmp/issue1563-body.md`). It opens
  with the missing-step description and then lists the exact stages "match
  the dominant pair, subtract, reindex, recurse". This is the equal-MPV
  architecture verbatim. The instruction at the bottom — *"The
  implementation should not reintroduce the deleted
  `ProportionalDecompositionData` / coefficient-array branch"* — is the
  *previous* wrong-direction that had already been deleted, telling agents
  not to relitigate it, but it does not warn about the *new* wrong direction
  (combined-family LI) that the peel architecture inevitably needs.

So the architectural drift was *executed*, not improvised: the helpers were
built to fulfil a plan that did not anticipate that the peel step requires
an exact coefficient identity (`c_N · μB b0^N · ζ^N = μA a0^N` for large
`N`) that the equal-MPV case obtained for free from
`eq_one_of_pow_tendsto_nhds_one` but the proportional case cannot obtain
without combined-family LI.

### 2.1 The chronological PR sequence

All commit hashes are from `git log --all`; dates are commit dates.

| PR # | SHA | Date | Author | Title | What it adds | Wrong-direction content? |
|---|---|---|---|---|---|---|
| #1595 | `03024536` | May 11 17:54 | Ray | `feat(MPS/FT): add selected weighted summand helper` | `eventually_selected_weighted_mpvState_eq_smul_of_phase_and_coeff` (algebra bridge from `μA^N = c·(μB·ζ)^N` to the selected-summand identity) | No (pure algebra; ostensibly innocuous). |
| #1596 | `aaca9803` | May 11 18:06 | Ray | `feat(MPS/FT): add arbitrary tail reindex package` | tail-reindex packaging | No. |
| #1598 | `02410d8e` | May 11 18:29 | Ray | `feat(MPS/FT): extract selected coefficient from LI relation` | **`eventually_selected_coefficient_eq_of_eventually_linearIndependent_sum`** introduced. Docstring (verbatim): *"Lemma `Lem1` supplies eventual linear independence for the remaining two-family list."* | **Yes — first wrong-direction CFLI lemma** in the tree. |
| #1599 | `63278843` | May 11 18:39 | Ray | `feat(MPS/FT): derive selected summand from LI relation` | **`eventually_selected_weighted_mpvState_eq_smul_of_phase_sum_and_li`** introduced. Docstring (verbatim): *"Lemma `Lem1` gives eventual linear independence of the family obtained by replacing that selected block by its phase-matched partner."* | **Yes — second wrong-direction CFLI lemma.** Docstring asserts Lem1 supplies it. |
| #1600 | `191ae589` | May 11 18:46 | Ray | `feat(MPS/FT): package tail proportionality after phase substitution` | **`eventuallyNonzeroProportionalMPV₂_tail_succAbove_of_phase_sum_li`** introduced. Original docstring: *"Eventual proportionality of tails from phase substitution and Lemma `Lem1`."* — making the false claim explicitly part of the lemma's title. | **Yes — third wrong-direction CFLI lemma** (the "top" of the chain in `ProportionalExpansion.lean`). |
| #1601 | `4a3aafa6` | May 11 20:08 | Ray | `feat(MPS/FT): add symmetric tail phase wrapper` | **`eventuallyNonzeroProportionalMPV₂_tail_succAbove_of_phase_sum_li_left`** — symmetric mirror; creates whole new file `ProportionalExpansionLeft.lean`. | **Yes — fourth wrong-direction CFLI lemma.** |
| #1604 | `ee97b6ac` | May 11 21:01 | Ray | `doc(MPS/FT): mark tail LI helpers conditional` | **First retrospective acknowledgement.** Docstring changes: title "Eventual proportionality of tails from phase substitution and Lemma `Lem1`" → "Tail proportionality from phase substitution and a Lemma `Lem1` input"; adds disclaimer *"The assumption is that the displayed combined MPV family is linearly independent for all sufficiently large lengths. In the proof of Theorem `thm1` this assumption is supplied by the fixed-block application of Lemma `Lem1` at the current peeling step."* The disclaimer still **incorrectly** says Lem1 supplies it. | (Doc-only; reduces visible severity but does not retract the false claim.) |
| #1605 | `251e9367` | May 11 21:16 | Ray | `feat(MPS/FT): add fixed-block Lem1 input` | `eventually_linearIndependent_all_left_single_right_of_all_overlaps_decay_CFBNT`. **Source-faithful** — supplies LI of `{A_j} ∪ {one B_k}`, exactly what Lem1 actually gives. | No (this is the *correct* Lem1 application; ironically it shows by contrast that the `_phase_sum_li` hypotheses ask for more). |
| #1606 | `4bde687a` | May 11 21:26 | Ray | `feat(MPS/FT): add symmetric fixed-block Lem1 input` | Symmetric `_all_right_single_left_*`. | No (source-faithful). |
| #1608 | `96a600c9` | May 11 21:38 | Ray | `feat(MPS/FT): name fixed-block contradiction obligations` | Adds the two `sorry`s (`fixed_right/left_all_overlaps_decay_false_*_CFBNT`); **adds `docs/paper-gaps/cpsv16_fixed_block_cancellation.tex`**. The new gap doc says explicitly: *"It must not assume global linear independence of all remaining blocks, since that is not a consequence of the BNT hypotheses once a block on one side may be phase-equivalent to a block on the other."* | **This is the moment the wrong-direction was identified in writing**, ~3 h after PR #1600 landed. But the wrong-direction lemmas were not deleted; only the missing step was named as an open obligation. |
| #1609 | `c3e70432` (merge `10562780`) | May 11 21:49 | Sirui | `feat(MPS/FT): prove singleton fixed-block cancellation` | `FixedBlockSingleton.lean` with `_finOne` base cases. Uses `eventually_linearIndependent_all_left_single_right_*` (source-faithful) directly, not the wrong-direction selector. | No, but conceptually it is a base case of the abandoned peel induction, so the lemma becomes orphan scaffolding. |
| #1611 | (merge `36ee0131`) | May 11 22:28 | Sirui | `feat(MPS/FT): record leading fixed-block cancellation` (`2da53dd7`) | `fixed_*_leading_all_overlaps_decay_false_*_CFBNT` thin wrappers around `dominant_projection_contradictions_*`. | No (paper-faithful for the leading block), but consumer is dying. |
| #1621 | `2a093a93` (merge `df838763`) | May 12 01:48 | Sirui | `doc(MPS/FT): mark residual LI peeling conditional` | **Second, stronger retrospective acknowledgement.** Title changes from "Tail proportionality from phase substitution and a Lemma `Lem1` input" → "Tail proportionality from phase substitution and a linear-independence hypothesis"; the disclaimer is rewritten to **drop the false claim that Lem1 supplies it**: *"CPSV16 Lemma `Lem1` gives this kind of independence only for the family in which all off-diagonal overlaps tend to zero. In the fixed-block step of Theorem `thm1`, lines 1181–1185, the local application gives independence for all blocks on one side together with **one fixed block** on the other side, not for the whole remaining tail appearing in this lemma. This conditional helper must therefore **not** be used as the source-faithful discharge of fixed-block cancellation."* Cites the gap doc explicitly. | (Doc-only.) |
| #1630 | `c3b38a68` (merge `163fc3b3`) | May 12 05:55 | Sirui | `feat(MPS/FT): record leading tail peeling data` | `LeadingTail.lean` (and previously `LeadingPartner.lean`, `ProportionalTail.lean`). Asymptotic-only conclusions. | Conceptually wrong-direction (the peel architecture is what produces the CFLI need), but takes no CFLI hypothesis itself. Orphan now. |
| #1633 | (merge `630ebeee`) | May 12 06:20+ | Sirui | `feat(MPS/FT): isolate selected coefficient by residual span` (`4be2bd62`) plus follow-ups `d410aadf`, `6cf31fab`, `66837b27`, `7600bc99`, `618786ae`, `d71bf882` | Creates `ProportionalResidualSpan.lean`; introduces the four RSE lemmas; exposes the module from `Full.lean`. | **Yes — fifth/sixth/seventh/eighth wrong-direction lemmas.** Even with docstrings flagged conditional from the start, this attempts to *bypass* CFLI by stating the same combined dependency as an RSE hypothesis; the analysis memo notes the two are equivalent (structural map §2 D.3). |

After PR #1633, the residual-span branch `feat/mps-ft-residual-span-exclusion`
continued (not yet merged to `main`):

* `01c6bc90` (May 12 08:58) `feat: derive residual span exclusion from
  independence` — tries to *derive* RSE from a (still wrong-direction) LI
  input.
* `69bdc1b2` (May 12 10:15) `feat: derive Lem1 residual span exclusions` —
  source-faithful `Lem1`-form RSEs (the all-A + one-B variant).
* `dd8323fd` (May 12 10:49) `feat: extract selected terms from residual
  spans`.
* `b5c6428d` (May 12 10:57) `feat: peel tails from residual span
  exclusions` — RSE-flavoured peel.
* `61f733dc` (May 12 11:12) `feat: add left residual span tail peeling`.
* `504715db` (May 12 12:02) `doc: retarget fixed-block cancellation tracker`.
* `29ce5688` (May 12 14:45) `feat(MPS/FT): close fixed-block cancellation` —
  **the smoking-gun "close"**: tries to discharge the two `sorry`s by
  reducing fixed-right to fixed-left and vice versa, i.e., calling each
  `sorry` from the other. The reduction is mathematically sound (swap A↔B,
  invert `c_N`), but since both functions are `sorry` it is a **circular
  call**: each function's body forwards to the other, and the recursion has
  no terminating base case. Lean's termination checker accepts it because
  the call is from one lemma to a different lemma (different definitional
  name) and there is no decreasing measure required for non-recursive
  definitions; the body just type-checks as if both were proved. The
  apparent "discharge" is in fact a no-op: the obligation is unchanged.
* `a5dcc273` (May 12 15:11) `fix(MPS/FT): use residual span for fixed
  block` — **silently reverts the circular discharge back to `sorry`** and
  introduces two new `eventually_fixed_right/left_notMem_*_span_*_CFBNT`
  helpers that translate the source-faithful all-A+one-B LI into the
  *narrow* RSE (only the one fixed B-block is excluded from the A-span).
  This RSE is paper-faithful — but it is not strong enough to feed
  `eventually_selected_coefficient_eq_of_residual_span` at line 143, which
  needs the *combined* residual span (all-A + tail-B). So the circular
  proof attempt failed and the residual-span direction stalled.
* `ed5b2fd2` (May 12 15:19) `refactor: split fixed-block residual span` —
  cosmetic file split.
* `c45f01ae` (May 12 15:37) `doc: cite fixed-block residual span lemmas` —
  cosmetic.

Per `git log --oneline main..feat/mps-ft-residual-span-exclusion`, none of
these post-`#1633` commits is merged. The two `sorry`s persist on `main`.

### 2.2 Were the docstrings flagging suspicious before-the-fact?

No. The chronology of the docstring drift inside the same files is:

1. **PR #1598, #1599, #1600 (May 11 18:29–18:46)**: docstrings affirm
   *"Lemma `Lem1` supplies / gives"* the combined-family LI. False claim,
   stated as positive fact.
2. **PR #1604 (May 11 21:01, +2h 15min)**: title softened to "a Lemma `Lem1`
   input"; disclaimer added saying the assumption is *supplied* by the
   fixed-block application. **Still incorrect** but less assertive.
3. **PR #1608 (May 11 21:38)**: the *paper-gap doc*
   `docs/paper-gaps/cpsv16_fixed_block_cancellation.tex` is born and
   correctly identifies the gap. The wrong-direction lemma docstrings are
   not updated in the same PR.
4. **PR #1621 (May 12 01:48)**: docstrings finally retracted — now
   *"CPSV16 Lemma `Lem1` gives this kind of independence only for [the
   single-block family]"*, with explicit "must not be used as the
   source-faithful discharge". This is the final form on `main` and
   matches the analysis memo's diagnosis.
5. **PR #1633's `ProportionalResidualSpan.lean` (May 12 06:20+)**: the four
   RSE lemmas are *born* with the conditional disclaimer already present
   (docstring at e.g. `:34–39`, `:74–78`, `:104–107`, `:139–142`).

So the docstrings drifted from "this is the proof" (#1598–#1600) → "this is
conditional but Lem1 supplies it" (#1604) → "this is conditional and Lem1
does **not** supply it" (#1621). The retroactive correction took **~7 hours**
to land after the wrong claim was first asserted, and the *workaround*
(residual-span branch) was already underway by then.

### 2.3 Were there earlier audit memos catching this?

No.

* `audits/scouting_1606.00608.md` (March 2026): general scouting; no mention
  of `phase_sum_li` or residual-span.
* `audits/2026-05-01_issue1093_non_gemma_ft_reorganization_scout.md`: focused
  on `CommonSectorRelabelingHypothesis` etc.; the "BlockedNormalFormHypotheses"
  framework it praises is a different proportional-FT branch (subsequently
  deleted in PR #1574 per `/tmp/issue1559-body.md`). No mention of
  combined-family LI.
* `audits/lean_spaghetti_*.md`, `audits/2026-02-19_proof_structure_audit_memo.md`:
  "peeling" appears in these but refers to *block-separation / CFSep
  exponential bound* peeling — a completely different argument in
  `PiAlgebra/CanonicalFormSepAux.lean`.

The earliest documents that diagnose the wrong-direction subgraph are:

* `blueprint/comments202605/cpsv16_fundamental_theorem_analysis.md` (untracked
  in `git status`; analysis memo by an external reviewer that the user fed
  into the audit session).
* `audits/2026-05-13_cpsv16_ft_paper_vs_code_structural_map.md` (the
  predecessor of this memo).
* `audits/2026-05-13_cpsv16_ft_sorry_discharge_plan.md` (sibling memo, same
  day).
* `docs/paper-gaps/cpsv16_fixed_block_cancellation.tex` (created **May 11 in
  PR #1608**, three hours after the first wrong-direction PR landed; updated
  through the chain — its current form mentions
  `exists_leading_phase_tail_diff_*` as "insufficient" and the
  `_phase_sum_li` family as "not faithful replacements for the source
  sentence", confirming the wrong-direction without naming it as
  *deletable*).

### 2.4 Agent-session evidence

`~/.claude/projects/-Users-siruilu-Local-agentFormalization-TNLean/`:

* `df012803-44f9-4a46-8c8f-591a8df88c2b.jsonl` (May 10 17:55 → May 10 21:59).
  User prompt: *"audti the stauts of the issues #1542 #1541 #1543 #1526.
  Need to audit if all the lemmas/theorems have been formalized in the
  1606 and the 2007 paper and if so do they introduce extra assumptions
  or hypothesis"*. This session was the original *meta*-audit triggered
  by #1526 / #1559 cleanup. It did **not** catch the wrong-direction
  hypothesis. It triaged PRs as they landed.
* `c2df58f8-547c-4463-ac0a-f7a7e1a96ee3.jsonl` (May 12 12:22). User
  prompt: *"in #1544-1555 we found a huge deviations of the formalization
  from the paper 1606 and that is missed in #1526 […] this is horrible,
  horrible, because all the formalization effort would be wasted and fake
  if key definitions such as this do not match the original paper!!! we
  need to audit, very hard, with subagents, also after getting the
  results reflect and check"*. This session **deleted** "5 proportional
  FT wrapper cascade" decls (per its summary at line 12; quote: *"The
  proportional FT wrapper cascade — delete 5 of them"*) — these were the
  `ProportionalDecompositionData`-era artifacts, *not* the wrong-direction
  combined-LI hypotheses. The session detected the *outer* wrappers were
  unfaithful but did not drill into `_phase_sum_li`.
* `5242f7cc-b63c-4619-b07e-65c575fead2e.jsonl` (May 12 17:16). User
  prompt: *"there is something wrong with the curretn formalization of
  the fundamental theorem with respect to CPSV16. there are a lot of
  things that were not in the paper getting proven but are likely wrong
  or not leading to the conclusion. scout the situations, also read
  blueprint/comments202605/cpsv16_fundamental_theorem_analysis.md"*. This
  is the session that produced the structural-map memo (or its precursor)
  with the explicit per-step paper-vs-code table.

So the audit chain was: (i) May 10 cleanup audit fails to catch the issue;
(ii) PRs #1595–#1633 land May 11–12 building the wrong-direction subgraph
while the audit session triages; (iii) May 12 morning the user re-audits
the PRs and deletes outer wrappers; (iv) May 12 afternoon the user invokes
the analysis memo and triggers the structural-map audit, which is the first
written diagnosis of the actual root cause.

### 2.5 `/tmp/` orchestrator-output evidence

Six progress-stub files at `/tmp/issue1559-after-{1580,1581,1582}.md`,
`/tmp/issue1563-{body,reopen-comment,after-1580,after-1581,after-1582,reopen-after-1580}.md`.
The `issue1563-body.md` issue-body draft (quoted in §2.0) is the most
informative: it states explicitly that the closure plan is to "use #1579 to
form the proportional tail hypothesis, and then lift the #1578 dominant
contradictions to arbitrary blocks **by tail reduction**, without
reintroducing coefficient-array hypotheses." The "tail reduction" phrase
is the peel-induction architecture that requires CFLI; the warning is
against the *previous* coefficient-array deviation, not against CFLI.

### 2.6 GitHub issue evidence

`gh issue view 1607` (CLOSED) — the proof obligation for the wrong-direction
discharge — its body says:

> "Do not assume global linear independence of all remaining blocks. If a
> stronger hypothesis appears necessary, record it as a paper gap instead
> of marking the source theorem formalized."

`gh issue view 1603` (OPEN) — parent of #1607, opened *after* PR #1600
landed (the issue cites the lemma `_phase_sum_li` directly):

> "These lemmas are useful after a selected phase relation and the
> corresponding eventual linear-independence input are already available.
> Their linear-independence hypotheses **must not be treated as automatic
> global consequences of the BNT hypotheses**: if a remaining block on one
> side is phase/gauge equivalent to a block on the other side, the combined
> family is dependent."

Both issue bodies correctly articulate the policy constraint that the
PRs subsequently violated. The disconnect is between *policy as stated in
the issue* and *code as built in the PR cascade* over the following six
hours.

---

## §3 Root-cause diagnosis

**The root cause is a plan-of-record (issue #1559 / #1563) that prescribed
peel-induction on tail BNT families as the proportional-case Step 1
architecture, transplanted unchanged from the equal-MPV case without
recognising that the proportional case lacks the
`eq_one_of_pow_tendsto_nhds_one` upgrade from "limit-one" to
"exact-for-large-N" for the free scalar sequence `c_N`.** Each agent PR
#1595 → #1601 was a small, plausible-looking helper on the way to the
recursive call, but at PR #1599 (the coefficient-extraction step from a
combined-family LI hypothesis) the design choice that should have flagged
"this is asking for more than `Lem1` supplies" instead chose to claim
"`Lem1` supplies this". That claim, baked into the docstrings of
`eventually_selected_coefficient_eq_of_eventually_linearIndependent_sum`
(PR #1598) and `_phase_sum_and_li` (PR #1599) and the lemma names
themselves (`_of_phase_sum_li` literally encodes the wrong hypothesis), is
the wrong turn. PRs #1600, #1601, #1611, #1630, #1633 then built on top of
it. The structural map's diagnosis (§3): *"the proportional case never
establishes the exact coefficient identity… The `_phase_sum_li` /
`_residual_span` route is an attempt to recover this exact identity by
postulating residual-family LI plus coefficient extraction"* matches the
PR timeline: each PR is locally plausible, the architecture as a whole is
not.

Contributing factors, in order of impact:

1. **Plan-of-record drift.** The Stage-C plan in issue #1563 mandated
   "recurse on tail BNT families" with no caveat about the coefficient
   identity. The agents executed the plan literally.
2. **The `_finOne` base case is genuinely provable** (PR #1609) using only
   the source-faithful `Lem1` input — which "trained" the agents to think
   the inductive step would also factor through `Lem1`, when in fact only
   the no-tail case does.
3. **Docstring momentum.** The wrong claim *"Lemma Lem1 gives eventual
   linear independence"* propagated through PRs #1598 → #1599 → #1600
   verbatim before any reviewer flagged it. The retraction in PR #1604
   only softened "gives" to "is supplied by", and the real retraction
   (PR #1621) took until May 12 01:48.
4. **The retrospective gap doc (`cpsv16_fixed_block_cancellation.tex`,
   PR #1608) was created at the *right* time** (~3 hours after the wrong
   claim landed) and explicitly said *"It must not assume global linear
   independence of all remaining blocks"* — but it did **not** mandate
   deletion of the wrong-direction lemmas, only opened issue #1607 to
   "discharge" them. The branch that responded (`feat/mps-ft-residual-span-exclusion`)
   tried to rephrase the same wrong hypothesis as residual-span exclusion
   instead of deleting the lemmas and switching to the per-block-projection
   route.
5. **Two prior audit sessions (`df012803`, `c2df58f8`) did not drill into
   `_phase_sum_li`.** They focused on outer wrappers and the previously
   deleted coefficient-array branch. Only the May-12-evening audit
   (`5242f7cc`, seeded with the external analysis memo) finally diagnosed
   the wrong-direction subgraph in writing.

This was **not** a mis-reading of the paper: every individual citation to
"lines 1181–1185" is correct, and the gap doc correctly transcribes what
`Lem1` supplies. It was **not** a single agent run going off-script: a
dozen PRs over two days, three authors (Ray, Sirui, texra-ai), each PR
small and plausible. It is the textbook profile of *opportunistic
helper-PRs each plausible in isolation, building out an architecture
whose viability was never re-checked at the level of the architecture*.

The fix is the deletion list of §1 plus a Route-(a) per-block-projection
proof of the two `sorry`s at `NondecayingOverlap.lean:897, 934`, as
recommended in the structural-map memo §5.

---

*Audit produced by the deletion-candidates scout, 2026-05-13.*
