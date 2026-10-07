# Blueprint verification

Both changed fragments were verified in a disposable copy of the blueprint.
All sixty new declarations occur exactly once, and full source synchronization
passes with the pinned QICLean sources available. The complete dependency
graph contains no cycles or duplicate labels. The focused PDF and web builds,
mathematical-text checks, and desktop/mobile reader checks pass. The reader
check covered four pages and 460 typeset expressions. The pinned indentation
check passes after whitespace-only corrections to the two fragments.

The imported Lean audit proves the existence and axiom dependencies of all
sixty newly referenced declarations. Full compiled `checkdecls` is a separate
CI check, not claimed as a local result here.

Final fragment SHA256 hashes:

- `blueprint/src/chapter/ch24_peps_source_preparation.tex`: `6eeeb29f7cdaaf39906667997848c7361ba7df765ed07ea9bc42a6126b22de2e`
- `blueprint/src/chapter/ch24_peps_pair_effects.tex`: `ad929f1bdf7762e30a34e061b9e6db12a175f2c4eac257892b11fef37245e709`
