# A QICLean power-sum shadow in the periodic fundamental theorem

This audit records the repository-local pass-through exception of
`docs/project_conventions.md` §Style for one theorem in
`TNLean/MPS/Periodic/FundamentalTheorem.lean` that restated a QICLean theorem
with the index type narrowed.

| Removed | Replacement |
|---|---|
| `MPSTensor.weight_multisets_eq_of_power_sums_eq` (`TNLean/MPS/Periodic/FundamentalTheorem.lean`) | `Matrix.sum_pow_eq_implies_multiset_eq` (`QICLean.Algebra.ScalarPowerSumIdentity`) |

## What was checked

The removed theorem said that two families of scalar multiplicity entries with
equal power sums at every positive exponent determine the same multiset — the
Newton–Girard recovery statement. Its hypotheses and conclusion were those of
the QICLean theorem with the index type fixed to `Fin r`, and its proof was
`Matrix.sum_pow_eq_implies_multiset_eq μ ν h`. The QICLean statement is already
in the form the caller needs, so the narrowing bought nothing.

There was one call site, inside `equalCase_zgauge_of_power_sums` in the same
file, which now names the QICLean theorem directly. No import or `open` change
was needed: `QICLean.Algebra.ScalarPowerSumIdentity` is in the import closure
because the deleted body called into it, and the call site sits in the same
`namespace MPSTensor` — `ZGaugeConstruction` is a `section`, not a namespace — so
the fully-qualified `Matrix.` spelling resolves exactly as it did inside the
deleted proof.

The removed name carried no blueprint `\lean{}` tag and appeared nowhere in
`blueprint/src`, `blueprint/lean_decls` or `docs`.

## Verification

Root `lake build` completes successfully with the package lean options.
`check_forbidden_lean_tokens.py`, `check_reader_facing_prose.py`,
`check_numbered_lean_files.py`, `check_oversized_lean_files.py` and
`generate_import_aggregators.py --check` are clean.
