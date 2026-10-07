# Published regional embedding verification

The three current adapter records identify public source commit
`bdaa988c4cf11aa6c5b5b9e6af6cfb4945a63be7`. Its complete tree
`f9c47755e594c742e64d1b039a67bad676a1977a` is identical to the actual local
execution revision `22452861589bfb0717cad045c390736147ee94d7`.
The compiler ran at the local revision; publishing those exact bytes is not
a new compiler execution. [identity.json](identity.json) records both identities,
the source and dependency hashes, and the original-to-retained manifest mapping.

[checks.json](checks.json) retains the native module and approximation aggregate
build (3,205 jobs), strict adapter production check, both adapter and encoder consumer and
axiom-guard checks, and raw axiom checks for three adapter and twenty-two encoder
declarations. All eight commands passed. Every raw declaration uses only
`propext`, `Classical.choice`, and `Quot.sound`. Seven logs are byte-identical.
The native build log replaces only its prior private cache-source path with
`<prior-local-qiclean-source>`; both hashes are recorded in the identity file.

These checks used QICLean `83fdc804bb0ce258a41d32ecb1063e0c7fa8b84c`,
inherited from main #8811. The author checkpoint and earlier `8602b340c`
integration checks used `8d5389d23c8e675a0117442e1a0d2c683a4bad41`.
Lean, Mathlib, and all other pins are unchanged.

The [original ledger](../historical/author-checkpoint-ledger.json) preserves
its local author revision and original commands exactly. All original evidence
remains unchanged in the parent directory. The encoder's twenty-two ledger rows
continue to identify their original public source at `d92310cca`; this packet
adds the new-pin integration evidence without overwriting those earlier runs.

The metadata migration changes no Lean proof, test, import, workflow or pin.
The final branch head still needs its own remote CI results; local targeted
checks and the earlier public head's CI do not establish that result.
