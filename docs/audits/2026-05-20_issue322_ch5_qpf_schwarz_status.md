# Issue #322 status audit: QPF and Schwarz chapters

Date: 2026-05-20.

This audit refreshes issue #322 against current `main`
(`465dfc171c64274d03e698bb3bb0aa75f9a66b7c`).  The older comments on the
issue were useful at the time, but several of their concrete findings have
since changed.

## QPF chapter

The QPF source files are still the four files under `TNLean/QPF/`, and they
are free of `sorry` and `axiom`.

The Chapter 5a blueprint already recorded the injective-tensor QPF theorem and
the positive-definite fixed-point and uniqueness ingredients.  This audit adds
the two remaining irreducible-transfer-map variants that were identified in the
April 2026 audit comments:

- `MPSTensor.posSemidef_fixedPoint_unique_of_irreducible`;
- `MPSTensor.quantum_perron_frobenius_irreducible`.

Both are statement-level and proof-level complete in Lean.

## Schwarz chapter

The Schwarz source area has expanded beyond the older 12-file count.  Current
`TNLean/Channel/Schwarz/` contains 21 Lean files, counting the split
`PositiveOnAbelian/` subdirectory.

Current status:

- The Kadison--Schwarz, two-positive, Douglas factorization, multiplicative
  domain, normal/subnormal Schwarz, positive-map order, and Wolf Example 5.3
  entries are still recorded in `blueprint/src/chapter/ch05_schwarz.tex`.
- `PositiveOnAbelian.lean` is no longer a 1042-line monolith.  The public
  synopsis file has 46 lines, and the proof is split across
  `PositiveOnAbelian/Basic.lean`, `PositiveOnAbelian/Characterization.lean`,
  and `PositiveOnAbelian/Consequences.lean`.
- The operator Jensen, trace convexity, and Lieb concavity material is no
  longer missing from the blueprint.  It is now collected in
  `blueprint/src/chapter/ch17_operator_convexity.tex`, which is imported by
  `blueprint/src/content.tex`, and Chapter 5b explicitly points the reader to
  that chapter.

The remaining inputs in this area that are not proved from Mathlib alone are
not `sorry` proofs in `TNLean/Channel/Schwarz/OperatorMonotone.lean`.  They
are the four explicit axioms in `TNLean/Axioms/OperatorConvexity.lean`:

- `posMap_rpow_concave_jensen`;
- `posMap_rpow_convex_jensen`;
- `posMap_log_concave_jensen`;
- `lieb_concavity_axiom`.

The corresponding source statements are marked `\notready` in
`blueprint/src/chapter/ch17_operator_convexity.tex`.  The map-form corollaries
in the Schwarz namespace are statement-level `\leanok`, but their proofs depend
on these cited inputs.

## Tracker status

Issue #322 can now be closed as a Chapter 5 audit issue after this refresh is
merged.  The mathematical proof obligations that remain are more accurately
tracked by:

- #138, for the Wolf Chapter 5 operator-convexity and monotonicity route;
- #21, for the broader Wolf Chapter 5 Schwarz tracking issue.

The old requests to add missing operator-convexity blueprint entries and to
split `PositiveOnAbelian.lean` have both been superseded by current repository
state.
