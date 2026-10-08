# Physical output after auxiliary-register exchange

Four modules establish the literal output exchange, finite-dimensionality of each retained auxiliary register, and the physical partial-trace identity. Exact source operators in the actual physical-first replacement recover its replacement density, with the original gate-count error budget ε/2. These statements are auxiliary results from the proof of polynomial-PEPS Theorem 5.2; they do not establish the global sampled operator-network contraction or the unrestricted compression theorem.

The actual physical register dimensions are preserved. The proofs assume individual finite-dimensionality only for the original discarded private registers, and impose no numerical bound on their dimensions. All 43 named public declarations were audited; their only axioms are `propext`, `Classical.choice`, and `Quot.sound`.

The checks used the approved read-only canonical source/resource and physical artifact environment, with new outputs in an independent temporary package. `direct-checks.json` records the production and checked-source hashes, generated artifact hashes, audit inventories, options and baseline. Production differs from the checked source only by the recorded import-prefix substitution. Raw checks used all package options with warnings as errors. They are not a canonical Lake build. Canonical Lake, blueprint declaration validation, full-library audit and manuscript generation are deferred to the coordinating integration branch.

The focused tactic scan reports only patterns already recorded in the approximation ledger. Tensor comparison uses the existing pure-tensor extension lemmas, and partial-trace invariance reuses the existing equivalence-reindexing theorem.

All check logs and the tactic-scan output are stored as deterministic gzip files, preserving the exact original bytes.
