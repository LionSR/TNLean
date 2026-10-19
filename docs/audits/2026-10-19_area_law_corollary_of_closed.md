# The area law as a corollary of its explicit form

Theorem 1.1 of the two-dimensional area-law manuscript, `uniformAreaLaw` in
`TNLean/PEPS/AreaLaw/AreaLawTheorem.lean`, is now proved from `uniformAreaLaw_closed` with the
closed-form constant `uniformAreaLawConstantClosed q R J Δ`. Before this change it chose a
safe-box constant and filter-locality constants by existence statements and applied an
intermediate bound whose truncation and transport constants were also existential.

## Import order

`TNLean.PEPS.AreaLaw.AreaLawExplicitConstant` used to import
`TNLean.PEPS.AreaLaw.AreaLawTheorem`. It now imports the four modules that `AreaLawTheorem`
imported, and `AreaLawTheorem` imports `AreaLawExplicitConstant`. No declaration moved
between files; `uniformAreaLaw` and its corollaries keep their names and file.

## Removed declarations

| Removed | File | Reason | Replacement |
|---|---|---|---|
| `TNLean.PEPS.AreaLaw.uniformAreaLawConstant` | `TNLean/PEPS/AreaLaw/AreaLawTheorem.lean` | Its only user was the removed theorem below | `uniformAreaLawConstantClosed` (`AreaLawExplicitConstant.lean`) |
| `TNLean.PEPS.AreaLaw.exists_regionalEntropy_le_uniformAreaLawConstant` | `TNLean/PEPS/AreaLaw/AreaLawTheorem.lean` | Its only user was the old proof of `uniformAreaLaw` | `uniformAreaLaw_closed` (`AreaLawExplicitConstant.lean`) |

Both were auxiliary results: their blueprint entries, the definition
`def:area_law_named_constant` and the theorem `thm:area_law_named_constant` of
`blueprint/src/chapter/ch24_peps_area_law_explicit_constant.tex`, were not source-labelled
formalizations, and they are removed with the declarations. The axiom test
`TNLeanTest/PEPS/AreaLaw/AreaLawTheoremAxioms.lean` no longer lists the removed theorem.
No compatibility alias is kept.

## Kept declarations

`Scan.exists_boxEntropy_le_boxError` and the companion-library statement
`SpectralFilter.exists_norm_positiveConstraint_sub_map_le` keep other users in
`TNLean/PEPS/AreaLaw` and the blueprint, and are not removed.
