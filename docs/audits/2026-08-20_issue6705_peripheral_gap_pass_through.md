# Issue #6705: peripheral-gap pass-through deletion audit

This cleanup uses the repository-local exact pass-through exception in
`docs/MATHLIB_style.md` §Deprecation. The removed declarations had no independent
mathematical content:

| Removed declaration | Canonical replacement |
|---|---|
| `MPSTensor.wordSpan_one_eq_span_range` | `Kraus.wordSpan_one` |
| `MPSTensor.hasEventuallyFullKrausRank_of_injective` | `(MPSTensor.hasEventuallyFullKrausRank_iff_isNormal A).2 hA.isNormal` |

The first theorem forwarded exactly to the Kraus word-span theorem. The second
named a one-step proof of eventual full Kraus rank from injectivity. Its three
local consumers now use the established equivalence with normality directly;
no private replacement helper was introduced.

Exact-name scans of the repository, including `TNLean/Archive` and the blueprint,
found no remaining occurrence of either removed declaration. The declarations
therefore qualify for immediate removal without a deprecation period under the
repository-local exception.
