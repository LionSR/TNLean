# Parent-Hamiltonian slice: four zero-reference simp lemmas and one import scope

Two small cleanups in the parent-Hamiltonian layer, recorded together because
neither redirects a blueprint tag and both are proved by the root build.

## Zero-reference simp lemmas

Four `@[simp]` lemmas had no reference anywhere in the repository, in the
blueprint, or in the documentation, and none of them fired inside a bare `simp`
in any surviving proof: the root build is clean without them. They are deleted
outright rather than de-attributed, so no orphan statement is left behind. Each
was a definitional unfolding available by `rfl` or by unfolding the definition at
the use site, so no replacement declaration is needed.

| Removed | Replacement |
|---|---|
| `MPSTensor.productPairWindow_apply` (`TNLean/MPS/ParentHamiltonian/ProductPair.lean`) | none needed; the equation holds by `rfl` and `productPairWindow` unfolds directly |
| `MPSTensor.productPairState_zero` (`TNLean/MPS/ParentHamiltonian/ProductPair.lean`) | none needed; the empty product is discharged by `simp [productPairState]` at any use site |
| `MPSTensor.reindexSites_symm_apply` (`TNLean/MPS/ParentHamiltonian/RestrictTransport.lean`) | none needed; the equation holds by `rfl` |
| `MPSTensor.reindexSites_rfl` (`TNLean/MPS/ParentHamiltonian/RestrictTransport.lean`) | none needed; the equation holds by `rfl` |

The neighbouring lemmas `productPairWindow_one`, `productPairState_one`,
`reindexSites_apply` and `reindexSites_groundSpaceMap` are load-bearing and are
untouched.

## Import scope of the periodic-boundary reduction

`TNLean/MPS/ParentHamiltonian/PeriodicBoundaryReduction.lean` imported five
modules whose contents it never names; the identifiers they supply are used by
its single downstream consumer,
`TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean`, which reached them through
the reduction module. The five imports moved to the consumer, which now names
each of them directly:

* `BoundaryClosingAuxiliary` for the auxiliary boundary-product closure property;
* `CyclicTranslation` for the cyclic translation of configurations and states and
  its ground-space membership and append lemmas;
* `ExtendRight` for the right-extension of the ground space under block
  injectivity;
* `Nonvanishing` for nonvanishing of the matrix-product vector under block
  injectivity;
* `RestrictTransport` for site reindexing, its ground-space membership, and the
  window-restriction transport lemmas.

The generated aggregator `TNLean/MPS/ParentHamiltonian.lean` already imports all
five modules directly, so its content is unchanged and
`generate_import_aggregators.py --check` stays clean. The change is net zero in
lines; it narrows the reduction module's environment, which is where an unused
import is most likely to have been supplying an instance or a simp lemma
silently, and the root build confirms it was not.

## Verification

Root `lake build` completes successfully with the package lean options, which
exercises every importer of both edited modules. `check_forbidden_lean_tokens.py`,
`check_reader_facing_prose.py`, `check_numbered_lean_files.py`,
`check_oversized_lean_files.py` and `generate_import_aggregators.py --check` are
clean.
