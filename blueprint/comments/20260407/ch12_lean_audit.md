# ch12 semigroup audit

Scope checked:
- `blueprint/src/chapter/ch12_semigroup.tex` (full)
- all files under `TNLean/Channel/Semigroup/`
- `TNLean/Channel/Schwarz/OperatorConvexity.lean`

Baseline:
- All 85 `\lean{...}` tags in `ch12_semigroup.tex` resolve to existing declarations.
- `TNLean/Channel/Semigroup/` has no live `sorry`/`admit`; the `rg` hits there are stale comments/docstrings only.

## Issues

1. Stale `\notready` remark after Prop. 7.5 setup.
   - Blueprint: `blueprint/src/chapter/ch12_semigroup.tex:842`
   - The remark says there is a “remaining gap in the semigroup irreducible/primitive equivalence”.
   - That is no longer true in the actual Lean code: the fraction-slice lemmas are present and proved in
     `TNLean/Channel/Semigroup/Primitivity/IrreducibleAnalysis.lean:377,416,437,533,562`,
     and the two main theorems are proved in
     `TNLean/Channel/Semigroup/Primitivity/MainTheorem.lean:39,74`.
   - Recommendation: remove or rewrite the remark; its `\notready` status is stale.

2. Liouvillian-kernel section overstates hypotheses relative to Lean.
   - Blueprint:
     `blueprint/src/chapter/ch12_semigroup.tex:940`
     `blueprint/src/chapter/ch12_semigroup.tex:969`
   - Lean declarations:
     `TNLean/Channel/Semigroup/LiouvillianKernel.lean:407`
     `TNLean/Channel/Semigroup/LiouvillianKernel.lean:475`
   - The Lean theorems only assume a `LindbladForm` plus
     `HasFaithfulStationaryState F.toLinearMap`.
   - The blueprint states “Let `L` be a GKSL generator in Lindblad form...” and includes `def:is_gksl_generator` in `\uses`.
   - This is not a status error, but it is statement drift: the GKSL semigroup assumption is stronger than what Lean actually uses.

3. Cor. 7.2(3) statement/proof drift around Kossakowski rank.
   - Blueprint:
     `blueprint/src/chapter/ch12_semigroup.tex:1267-1280`
   - Lean declarations:
     `TNLean/Channel/Semigroup/RelaxationConditions.lean:831`
     `TNLean/Channel/Semigroup/RelaxationConditions.lean:893`
   - Lean proves `not_isReducible_of_kossakowski_rank_ge` from the hypothesis
     `kossakowskiRank F.toLinearMap + D ≥ D ^ 2 + 1`.
   - The blueprint theorem instead says `\rank(C) > d^2 - d`, but no Kossakowski form / matrix `C` is introduced in that theorem.
   - The proof also says “apply the formal result”, which is blueprint-inappropriate formalization-speak.
   - Recommendation: restate the theorem in terms of `kossakowskiRank`, or explicitly quantify a Kossakowski form/matrix `C`; also remove “formal result”.

4. `OperatorConvexity.lean` still has real `sorry`s, but they do not currently invalidate ch12 tags.
   - File: `TNLean/Channel/Schwarz/OperatorConvexity.lean:94,113,131`
   - The three unfinished declarations are:
     `IsPositiveMap.rpow_concave_jensen`,
     `IsPositiveMap.rpow_convex_jensen`,
     `IsPositiveMap.log_concave_jensen`.
   - These are consumed by `TNLean/Channel/Schwarz/OperatorMonotone.lean`, not by any file under `TNLean/Channel/Semigroup/`.
   - So this is real unfinished infrastructure, but not a blocker for the chapter’s current semigroup `\leanok` tags.

## Verified upgrades

- `\lean{irreducible_semigroup_implies_primitive}\leanok` is correct.
  The theorem exists at `TNLean/Channel/Semigroup/Primitivity/MainTheorem.lean:39`, and the supporting semigroup files are sorry-free.

- `\lean{qds_irreducible_iff_primitive}\leanok` is correct.
  The theorem exists at `TNLean/Channel/Semigroup/Primitivity/MainTheorem.lean:74`, and the proof is present.
