# Remove the conditional one-copy periodic equal case

Issue: #7733. Source: arXiv:1708.00029, Theorem 3.8 (`thm:bdequal`),
`Papers/1708.00029/main.tex:643–655` (the theorem allows matrix-valued
multiplicities).

Removed `MPSTensor.fundamentalTheorem_periodic_equalCase_matching` and
`MPSTensor.fundamentalTheorem_periodic_equalCase`. The first only repackaged
conditional block matching; the second additionally assumed weight-power
identities and treated one-dimensional multiplicity spaces. Neither had a
Lean consumer outside this pair on main at `fafa75e42`.

The source result remains
`MPSTensor.fundamentalTheorem_periodic_equalCase_derivedPeriods` in
`TNLean/MPS/Periodic/IrreducibleFormPeriods.lean`, with its existing blueprint
entry `thm:periodic_ft`. The two obsolete conditional blueprint entries had
no incoming references outside the removed pair and are deleted together.
The scalar power-sum and Z-gauge helpers remain unchanged.

The docstring of `PeriodicEqualCaseFT` now distinguishes the existing
blockwise theorem from its own explicit global-gauge hypothesis. No new
implication to that hypothesis is claimed.

No compatibility aliases are retained: TNLean has no stable public API,
and neither deleted declaration had a remaining consumer.
