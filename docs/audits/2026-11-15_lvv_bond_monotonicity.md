# LVV bond-bound monotonicity

Base: `eb588dc15332a3798431015e6c27ecbaf329b2d1`; implements rank 13 of the comprehensive audit in #10637.
Four cut-rank reconstructions now use the existing `IsOpenMPS.mono` from `OpenMPSCutRank.lean`.
`FinalMPS` shrinks 87→85 lines, `SuccessiveApproximation` 118→109, and `SampledSuccessiveConstruction` 434→430: **net −15 Lean lines**.
All 12 public declaration headers, imports, arithmetic bounds, chosen vectors and Blueprint anchors are unchanged.
The 34 open PR file lists and relevant branch-name/issue searches showed no competing edited-file ownership.
The higher-ranked compact-gap item remains with its assigned owner and existing `codex/10598-compact-directed-cover-candidate` branch.
Public-header equality, unchanged-import, prose, line-length, forbidden-token and whitespace checks passed against exact current-main source copies.
Local Lean/Lake/cache remain unavailable; hosted compilation of this new slice is pending. Required: the three changed module builds, the root build and strict changed-file checks.
Earlier drafts #10637, #10639 and #10642 passed full Lean builds, strict checks, declaration checks, module policies, Blueprint web and compilation-time checks at their recorded heads; PDF jobs were skipped.
No new lemma, tactic, test fixture, assumption, CI rerun or merge is introduced by this slice.
