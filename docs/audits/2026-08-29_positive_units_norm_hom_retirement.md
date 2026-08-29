# Positive-unit norm homomorphism retirement

This audit records the removal of `PositiveUnits.normMonoidHom` from
`TNLean/Algebra/PositiveGeneralizedCocycle.lean`. Its sole non-Archive use was
the adjacent definition `PositiveUnits.norm`, and no blueprint declaration tag
named it.

The exact replacement is Mathlib's `nnnormHom.toMonoidHom`: both maps send a
complex number `z` to its nonnegative norm ‖z‖₊ and preserve multiplication.
`PositiveUnits.norm` now passes that map directly to `Units.map`. No
compatibility alias is retained, in accordance with
`docs/project_conventions.md` §Style.
