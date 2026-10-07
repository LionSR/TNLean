# Two-family entropy integration

The generic theorem and physical regional-density proofs belong to QICLean.
This consumer builds on the finite-domain/model branch from issue 8738, reviewed
at `158bc6bb178ee53a2c981ba751fadf6e7a3ff0a2` (PR 8788), and uses its existing
`OrderedTwoFamilyPartition`, `earlierSameFamily`, `reducedState`, and `regionalEntropy`.

`regionalEntropy_le_residual_add_half_sum` formalizes the exact source
[area-law Lemma 11.1](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/10-geometry.tex#L26-L69).
It takes a normalized pure state, the existing labelled disjoint partition and
one information bound per piece, against the entire exterior-plus-earlier-same-
family region. Its conclusion is `S(A) ≤ S(D) + (1/2) ∑ i, ε i`.
No Hamiltonian, gap, geometry, nonempty-set or error-sign hypothesis is added.

The generic adapter `OrderedTwoFamilyPartition.entropy_le_residual_add_half_sum`
also accepts dependent local dimensions. The finite-domain specialization then
identifies the already-defined regional entropy with QICLean's construction.
Neither model data nor generic entropy proofs are duplicated.

All source code is independently written from the paper and existing library
APIs. The issue 8760 provenance shard lists only this repository's declarations;
QICLean owns its own source and verification evidence.

The shuffled-label regression uses three singleton pieces in a four-site system,
with family labels `1,0,1`, a nonempty exterior, and the true same-family past
`{0}` for piece `2`. It exercises the full exterior-plus-past estimate.

Publication requires the reviewed companion QICLean revision to be available and
pinned together with the consumer. The local verification uses a source-audited
private artifact overlay; it is not a substitute for the registered linter-bearing
Lake targets, complete repository CI, or full blueprint `checkdecls`.

The companion pin is the accepted QICLean PR 560 merge
`e0d95bff81c11eab7db872a927d1d69f820d4f47`. Root and docbuild manifests use
the same revision. Its entropy modules, imported proof-source closure, toolchain
and dependency configuration match the checked snapshot. The accepted main tree
additionally contains independent operator-mean modules outside this closure.
