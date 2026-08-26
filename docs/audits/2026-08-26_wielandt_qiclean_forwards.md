# Wielandt QICLean forward audit (2026-08-26)

Audited at TNLean `e091784dec9f7c478a2802ec741637456da436e0`, with QICLean pinned at
`edc008646e6fdd002c37b3849ca3ce33f4571da4`.

The project pass-through exception applies: each declaration is a literal
forward to its QICLean owner, every non-Archive consumer is migrated, and no
Blueprint tag names it.

| Removed declaration | Single source of truth | Migrated consumer |
|---|---|---|
| `MPSTensor.rectSpan_nilpIndex_finrank_constant'` | `Kraus.rectSpan_nilpIndex_finrank_constant'` | none (`RectangularSpan/Universality` already called the QICLean name) |
| `MPSTensor.vectorSpreadSpan_eq_top_of_wordSpan_eq_top` | `Kraus.vectorSpreadSpan_eq_top_of_wordSpan_eq_top` | `Wielandt/Primitivity/EasyDirections` (two call sites) |
| `MPSTensor.wielandt_lemma2b_conditional` | `Kraus.wielandt_lemma2b_conditional` | `Wielandt/RectangularSpan/Basic` (`wielandt_blocked_assembly`) |

Docstring mentions in `Wielandt/Primitivity/EasyDirections` and
`MPS/CanonicalForm/SectorComparison/TPPrimitiveReduction` were re-pointed to the
`Kraus` names in the same change.

The three defining modules remain because their other results are MPS-specific:
`RectangularSpan/Universality` keeps the two normality capstones,
`Primitivity/EasyDirections` keeps the paper-primitivity direction and the index
bound, and `RectangularSpan/Basic` keeps the blocking theory and the blocked
fixed-length spanning assembly.
