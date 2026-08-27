# Martingale coordinate specializations: two pass-throughs retired

This audit records the repository-local pass-through exception of
`docs/project_conventions.md` §Style for two coordinate-space specializations in
the parent-Hamiltonian martingale layer. Each forwarded, with an identical
argument list, to the finite-dimensional statement that carries the proof; the
finite-dimensional statement subsumes the coordinate-space one because
`EuclideanSpace ℂ ι` over a `Fintype` is a finite-dimensional inner-product
space and its instances are found by synthesis at every call site.

| Removed | Replacement |
|---|---|
| `FrustrationFree.spectralGap_of_martingale` (`TNLean/MPS/ParentHamiltonian/Martingale/AbstractCriterion.lean`) | `FrustrationFree.spectralGap_of_martingale_of_finiteDimensional` in the same file, of which the removed name was a one-line term-mode forward |
| `MPSTensor.spectralGap_of_martingale_anticommutator_rowCol` (`TNLean/MPS/ParentHamiltonian/Martingale/Reduction.lean`) | `MPSTensor.spectralGap_of_martingale_anticommutator_rowCol_of_finiteDimensional` in the same file, which the removed name reached after a decidability-instance shuffle only |

## What was checked

Both names arose as backward-compatibility wrappers when the underlying
statements were generalized from the coordinate space `EuclideanSpace ℂ ι` to an
arbitrary finite-dimensional complex inner-product space. Neither bare name is
cited by any `\lean{...}` tag in `blueprint/src`, so no blueprint node was
redirected and no declaration reference had to move.

`FrustrationFree.spectralGap_of_martingale` had exactly one caller,
`MPSTensor.parentHamiltonianES_norm_bound_of_quadratic_form` in
`TNLean/MPS/ParentHamiltonian/Martingale/Reduction.lean`. The call now names the
finite-dimensional statement; the explicit `(ι := Cfg d N)` ascription is dropped
because the ambient space is determined by the type of `parentHamiltonianES A L N`.

`MPSTensor.spectralGap_of_martingale_anticommutator_rowCol` had no caller
anywhere outside its own declaration. Its body only replaced the ambient
`DecidableEq` instance by the classical one before applying the surviving
statement, which is unnecessary work for a caller that can supply hypotheses
against whatever instance it already has.

Three module docstrings named the removed abstract criterion and now name its
replacement: the module header and the docstring of
`parentHamiltonianES_norm_bound_of_quadratic_form` in `Martingale/Reduction.lean`,
and the component list in `Martingale.lean`. The tracking entry PH-4a in
`docs/audits/PARENT_HAMILTONIAN_ISSUES.md` was repointed for the same reason, so
that the document names a declaration that exists.

## Verification

Root `lake build` completes successfully with the package lean options, which is
the oracle that proves the row-and-column wrapper dead: a module-target build
compiles a file's dependencies, not its importers.
`check_forbidden_lean_tokens.py`, `check_reader_facing_prose.py`,
`check_numbered_lean_files.py`, `check_oversized_lean_files.py` and
`generate_import_aggregators.py --check` are clean, and `leanblueprint checkdecls`
resolves every tag.
