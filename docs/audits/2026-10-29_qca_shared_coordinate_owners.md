# Shared interval-coordinate declaration owners

A source/Blueprint duplicate audit of the combined actual-MPU/QCA branches
found two full Lean names declared twice against main. This is a concrete
integration blocker even though each mathematical statement is correct.

`SpinChain.translateRegion_finiteChainRegion` already existed in
ParentHamiltonian/LocalObservableTranslationInvariance. The new QCA declaration
had the same name with the integer arguments reversed. Move the established
anchor-then-displacement declaration unchanged to QCA/IntervalTranslation,
remove the duplicate and update the new QCA/MPU calls to that established order.
The old parent-Hamiltonian consumer imports the shared QCA owner.

`SpinChain.quasiLocalIntervalObservable_chainWindowOperator` already existed
with the general nonwrapping-window statement in QuasiLocalCommutatorLocality.
The new MPU helper had the same name for a special padded-window statement.
Move the existing general declaration and its bulk-inclusion prerequisite
unchanged to ParentHamiltonian/QuasiLocalWindowCoordinates, remove the duplicate
MPU helper, and let both consumers use that owner. The actual four-block output
now directly applies the established general window API.

Both established public names, signatures and proof bodies are retained; no
compatibility aliases or parallel predicate families are introduced. Keep their
existing parent-Hamiltonian Blueprint anchors and readiness, and remove the
duplicate links from the new MPU nodes, recording the dependency instead.

Native validation: internal import graph is acyclic; one declaration per full
name; generated aggregators; Blueprint synchronization and duplicate tags;
roles; prose; project ChkTeX; diff checks. No local Lean/Lake/build/checkdecls.
The newly dependent MPU results retain their separate hosted acceptance gates.
