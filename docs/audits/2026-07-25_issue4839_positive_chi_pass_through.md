# Issue #4839: positive-$\chi$ pass-through deletion audit

This cleanup uses the repository-local exact pass-through exception in
`docs/MATHLIB_style.md`.

## Removed declarations and replacements

| Removed declaration | Direct replacement |
|---|---|
| `MPOTensor.BNTFusionIsometryFamily.toPositiveChiWitness` | `MPOTensor.PositiveBNTLabelChiTracePowerForm.ofChi Fam.chi Fam.posEntries` |
| `MPOTensor.BNTFusionCoisometryFamily.toPositiveChiWitness` | `MPOTensor.PositiveBNTLabelChiTracePowerForm.ofChi Fam.chi Fam.posEntries` |

Both removed definitions were exact forwards to the listed constructor. They
carried no additional hypotheses, equations, or mathematical conclusion. Their
only non-Archive Lean consumers were the adjacent `toBNTAlgebraClause`
constructors, which now call the common constructor directly. The sole blueprint
tag on the isometry wrapper was removed; the common constructor remains tagged
where the positive diagonal $\chi$ data are defined.

A repository-wide exact-name search after the migration found no remaining
non-Archive Lean use or blueprint tag for either removed declaration.
