# QICLean bump to 8f05f840: square-root Hölder bound

Date: 2026-10-07. PR: chore(lake): bump QICLean to 8f05f840.

## Removed declaration

- `CFC.norm_sqrt_sub_sqrt_le` in `TNLean/Algebra/CStarSqrtHolder.lean`:
  `‖√a - √b‖ ≤ √‖a - b‖` for positive elements of a unital C⋆-algebra.

## Replacement

- `CFC.norm_sqrt_sub_sqrt_le` in `QICLean/Analysis/SqrtHolder.lean` (QICLean
  `8f05f840`, added by LionSR/QICLean#579), with the same statement, the same
  instance assumptions `[CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]`
  and the same hypotheses `(ha : 0 ≤ a) (hb : 0 ≤ b)`.

Both declarations have the same fully qualified name, so keeping the TNLean copy
would make the root module fail to load once the bumped QICLean is imported.
`TNLean/Algebra/CStarSqrtHolder.lean` now imports `QICLean.Analysis.SqrtHolder`;
its only consumer, `TNLean/Algebra/CStarSqrtLipschitz.lean`, resolves the name to
the QICLean declaration unchanged. The blueprint tag
`\lean{CFC.norm_sqrt_sub_sqrt_le}` in `ch32_log_depth_preparation.tex` keeps
resolving, now to the QICLean declaration with the same name and statement. The
other declarations of `CStarSqrtHolder.lean` are kept.
