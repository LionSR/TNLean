# PEPS torus edge-absorbed scalar-condition rung retirement

This audit records the repository-local pass-through exception
(`docs/project_conventions.md` §Style) for the removal of
`TNLean.PEPS.lambda_pow_card_torus_eq_one_of_edgeAbsorbed` from
`TNLean/PEPS/TorusFundamentalTheorem.lean`.

## Why

The module carried a three-rung hypothesis ladder for the torus scalar condition
of Theorem 3 of arXiv:1804.04964 (lines 1449--1471 of
`Papers/1804.04964/paper_normal.tex`). The top rung took the bare-edge absorbed
equality, ran `twoBlockProportional_of_edgeAbsorbed` at the two one-site-different
comparison regions `R_v` and `insert v R_v`, and handed the resulting pair of
two-block proportionalities to the rung below it. That assembly is performed
directly, and with its own choice of comparison regions, inside the unconditional
torus theorem `fundamentalTheorem_normalTorusPEPS_unconditional`
(`TNLean/PEPS/TorusFundamentalTheorem2.lean`); the packaged rung was never
called. It is a proof step now written at the use site, which is exactly the
pass-through case.

The rung below it, `lambda_pow_card_torus_eq_one_of_twoBlockProportional`, is
kept: it is cited by a `\lean{...}` tag at
`blueprint/src/chapter/ch24_peps_ft_torus_staircase_geometry_and_ft.tex:306`
and survives on that tag.

## Zero-consumer evidence

At the audited head the removed theorem had no non-`Archive` Lean consumer; no
`\lean{...}` tag under `blueprint/src/` names it; the single prose reference was
one `\leanid{}` entry in `docs/paper-gaps/peps_normal_ft_section3_route.tex`,
reworded in the same change to point at the unconditional torus theorem that
performs the assembly.

## Removed declarations with replacements

| Removed declaration | Replacement |
|---|---|
| `TNLean.PEPS.lambda_pow_card_torus_eq_one_of_edgeAbsorbed` | the hand assembly inside `TNLean.PEPS.fundamentalTheorem_normalTorusPEPS_unconditional`: `twoBlockProportional_of_edgeAbsorbed` at `R_v` and at `insert v (R_v)`, then `lambda_pow_card_torus_eq_one_of_twoBlockProportional` |

## Import consequence

`import TNLean.PEPS.RegionBlock.ProportionalityFromAbsorbed` was the removed
theorem's only reason to be in the module and went with it. This frees no
compile cone: the seven modules below it remain in the root build through their
other importers.
