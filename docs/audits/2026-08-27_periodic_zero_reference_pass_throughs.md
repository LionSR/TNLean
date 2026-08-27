# Two zero-reference periodic pass-throughs

This audit records the repository-local pass-through exception of
`docs/project_conventions.md` §Style for two specializations in the periodic
layer that forwarded to a general theorem with an identical argument list and
had no consumer anywhere in the tree. It is an execution slice of open ledger
entry S2 in `docs/proof_debt_ledger.md` (zero-reference declarations), not a new
find: the 2026-08-26 periodic sweep passed over both.

| Removed | Replacement |
|---|---|
| `MPSTensor.gaugeEquiv_of_sameMPV_rotatePhysical` (`TNLean/MPS/Periodic/Applications.lean`) | `MPSTensor.fundamentalTheorem_singleBlock` (`TNLean/MPS/FundamentalTheorem/Basic.lean`) |
| `MPSTensor.perBlock_zgauge_of_power_eq` (`TNLean/MPS/Periodic/FundamentalTheorem.lean`) | `MPSTensor.zgauge_construction` (same file) |

## What was checked

`gaugeEquiv_of_sameMPV_rotatePhysical` took an injectivity hypothesis and a
same-matrix-product-vector hypothesis for a tensor and its physical-leg rotation
and returned gauge equivalence; its proof was
`fundamentalTheorem_singleBlock hA hSym`, with the rotation appearing only
through the hypothesis. Specializing the general theorem at the rotated tensor
is what a caller writes anyway, so the declaration named a proof step rather
than a result.

`perBlock_zgauge_of_power_eq` restated `zgauge_construction` with the index type
fixed to `Fin r`. The general theorem is stated for an arbitrary finite
decidable index type, so the specialization is obtained by instantiation; its
proof was `zgauge_construction m μ ν hpow hν`.

Neither name occurred anywhere outside its own declaration and the module
docstring that advertised it: not in `TNLean`, not in `blueprint/src`, not in
`docs`, and not in `blueprint/lean_decls`, so no `\lean{}` tag is affected and
the declaration list needed no regeneration. Both module docstrings were
rewritten to describe what survives — the physical-index rotation and its
matrix-product-vector expansion in `Applications.lean`, and `zgauge_construction`
alone in `FundamentalTheorem.lean`. The `zgauge_construction` mention is kept
deliberately: it survives and is blueprint-tagged.

## Verification

Root `lake build` completes successfully with the package lean options.
`check_forbidden_lean_tokens.py`, `check_reader_facing_prose.py`,
`check_numbered_lean_files.py`, `check_oversized_lean_files.py` and
`generate_import_aggregators.py --check` are clean; no file was added or
deleted, so no aggregator changed.
