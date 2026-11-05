# Shared coordinates in the native regional energy estimate

The two private regional-operator coordinate calculations are removed from
RegionalEnergyEstimate.lean. The existing consumer now calls the explicit
exterior-first conjugation identity in QICLean's new
Entropy/RegionalOperatorCoordinates.lean. Its public theorem statement is
byte-identical, including its original candidate-loss bound; no energy or
generation claim changes. The same generic coordinate proof is now available
for the actual canonical tensor coordinates used by improving families.

The new generic module and this actual consumer passed fresh strict checking
against immutable TNLean e2706cbe715c49745d4399d37dabe3d2559cc494 and its own
QICLean de8a9d1286709f39d8c37d4d52d6e336925863e5. The imported audit covers
both new public coordinate forms and this unchanged public estimate, with
only the standard three foundations. Sources, imported objects, root inputs
and prebuilt Mathlib hashes were guarded. New objects and temporary audit
commands are confined to /tmp; the source worktree has no .lake. No provider
or cache was changed and no Mathlib source was compiled. The manifest records
exact source hashes and verification evidence. Ordinary combined and compiled
blueprint checks remain required after adoption.
