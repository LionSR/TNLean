# Exact square-grid state transport

## Scope and source

This extends the core in PR #8783 at `a1d91d4c8fbe03c682f4a158cb80871f2aa8853a`. The core source definitions, edge/incidence equivalences and coefficient proofs are retained unchanged. The additional results compare Euclidean vectors, preserve every bond dimension and the maximum, transport nonzero normalization and the complete minimizing-phase predicate, and identify every regional reduced matrix, spectral entropy and crossing-boundary cardinality.

The selected OpenAI revision is `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Source declarations come from `PEPSFilters/Basic.lean` and `TensorNetwork/VectorColumn.lean`. Adapted definitions and the short normalization calculation are distinguished from original comparison proofs in module notices and declaration-level ledger fragments. No OpenAI package dependency is added.

## Mathematical boundaries

- Physical-first coefficient/vector equalities permit arbitrary site tensors, edge-dependent dimensions, zero dimensions, empty lattices and zero physical dimension.
- The virtual-first source structure alone carries positive bond dimensions.
- Individual dimensions are unchanged. The natural maximum on an empty edge set is zero; real per-edge bounds remain universally quantified and may be vacuous on an empty graph.
- Unit normalization is asserted only for a proved nonzero contraction. Regional matrices are explicitly unnormalized; their spectral entropy is the physical state entropy when the global vector is unit. Natural logarithms and zero logarithmic terms agree with QICLean.
- There are no injectivity, periodicity, parent-interaction, Hamiltonian, gap, or uniform-bond assumptions.
- The native approximation-predicate integration belongs to #8738. This change supplies its exact conjunction-level transport and leaves #8740 open for that integration. No approximation existence or area-law theorem is claimed.

## Checked local source snapshot

Toolchain: Lean `v4.35.0-rc3`; Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`; QICLean `8d5389d23c8e675a0117442e1a0d2c683a4bad41`. Every dependency checkout was verified clean at the manifest pin. Official prebuilt Mathlib was already present. Sixty-four native/QIC dependency modules were compiled from exact source with serialized 90-second limits, then reused only after matching source and artifact SHA-256 values. No Lake trace or hash was rewritten.

The following commands completed successfully with `-j1 -Dpp.unicode.fun=true -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 -Dlinter.mathlibStandardSet=true -DwarningAsError=true`; tests additionally use `-DautoImplicit=false`. The axiom test disables only the hash-command style warning so its intentional kernel dependency commands can run.

- `python3 peps-square-grid-extension-validation/check.py TNLean.PEPS.Approximation.SquareGridSource`: exit 0, 2.18 seconds; source SHA-256 `23c3bb180f87421469dc8c2a69b027ba984bff044093a25ebb72a96d0e4765f8`.

- `python3 peps-square-grid-extension-validation/check.py TNLean.PEPS.Approximation.SquareGridContraction`: exit 0, 2.53 seconds; source SHA-256 `1d4b0812723aac57fcc31dd84c2ae01819c2b7fef93ec7adc771532a09f499e4`.

- `python3 peps-square-grid-extension-validation/check.py TNLeanTest.SquareGridContraction`: exit 0, 2.26 seconds; source SHA-256 `a8c88a5dd96890606cba6a5e57f272e071494d2cd774989b38fe7f4178bc1739`.

- `python3 peps-square-grid-extension-validation/check.py TNLean.PEPS.Approximation.SquareGridBounds`: exit 0, 3.44 seconds; source SHA-256 `23c2b21d0328a1b340671b1665397b307392fedbaba37d0410a72ac97b24f2a7`.

- `python3 peps-square-grid-extension-validation/check.py TNLean.PEPS.Approximation.RegionalStates`: exit 0, 2.35 seconds; source SHA-256 `bb3803ef6fdf127a51aabcf2104aceac014d852be89fd26bad0c949fdcfe4d89`.

- `python3 peps-square-grid-extension-validation/check.py TNLeanTest.SquareGridStateTransport`: exit 0, 3.11 seconds; source SHA-256 `c783e755e0210fada89554bced55e7813b21c2d3ab028b35a0531877ce7d2537`.

- `python3 peps-square-grid-extension-validation/check.py TNLeanTest.SquareGridStateTransportAxioms`: exit 0, 2.11 seconds; source SHA-256 `bf288c7b7cae29432bf12459d02eb9e76b1f19b811425373652c5f2cbb9a42e4`.


The regression covers a bond-one product contraction; arbitrary heterogeneous local tensors with dimensions two and three at one corner; `L=0` including `q=0`; `L=1` maximum zero; `q=0` on a nonempty grid; a zero-dimensional bond forcing zero contraction; unequal source parameter values `q=3,L=2`; and empty/full boundary cardinalities. All 25 new named declarations have guarded kernel-axiom checks, permitting only `propext`, `Classical.choice` and `Quot.sound`.

## Documentation and remaining checks

The native tenkz diagram was rendered using exact companion revision `08a6493f3605dcf2ca5b512823ccb2698dfc027b`, structurally audited, and visually inspected. It has four local tensors, four individually labelled virtual bonds, four physical legs, and no open virtual boundary. The audit also checks label collisions and equation boundary signatures. The complete new section renders successfully in isolation.

The import generator, file-size/numbered-file/forbidden-token guards, YAML parsing and whitespace checks pass. The diagram and strict Lean regression/audit commands are registered in CI. The tactic-pattern survey yielded no new three-occurrence pattern requiring promotion.

The repository-wide blueprint source-sync check reports 524 existing unresolved dependency declarations both on the untouched `a1d91d4c` baseline and on the extension. New-section declaration links are checked separately against actual compiled declarations. A full `lake build TNLean` and `leanblueprint checkdecls` have not run locally. The environment has no installed `leanblueprint`, plasTeX or texra-blueprint; no package-install retry was made. These aggregate checks remain CI requirements.


Committed-revision build and printed-axiom evidence will be added after the source snapshot is published and its actual remote revision is known. Until then, new ledger rows remain planned.

## Assistance

OpenAI Codex assisted source comparison, implementation, regression tests and documentation. The human author remains responsible for mathematical review.
