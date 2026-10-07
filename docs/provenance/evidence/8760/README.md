# Issue 8760 exact-source verification

Source repository: `LionSR/TNLean`.
Published immutable source revision: `4295513f99a80a2fec33dadae29ac67fd785c593`.

Each recorded module was checked by a real direct Lean invocation with the
package options, Mathlib standard linter set, warnings-as-errors, one thread and
a 90-second timeout. The module logs contain actual invocation metadata and the
unmodified compiler output. The axiom log is the unmodified printed output for
all declarations in this repository's issue 8760 shard. All dependencies are
limited to `propext`, `Classical.choice`, and `Quot.sound`.

This is strict direct elaboration evidence, not a claim that a linter-bearing
Lake build, whole-repository CI, or full blueprint `checkdecls` has completed.
Those gates are registered in CI. TNLean's consumer additionally requires the
reviewed QICLean companion revision to be pinned before publication is complete.

Validation reused only artifacts with matching recorded source/artifact hashes
and an unchanged Lean/Mathlib/package-option configuration. Missing project
prerequisites were compiled serially. No Mathlib source build, forged cache trace,
custom axiom, proof hole, or native kernel bypass was used.

QIC source revision used by the private integration overlay: `e0d95bff81c11eab7db872a927d1d69f820d4f47`.
TN model base: `158bc6bb178ee53a2c981ba751fadf6e7a3ff0a2`.

The locally checked source snapshot `6d13ef7fa70538fd7329ef22a8ab2b89866d8ef7` and the published source
have exactly the same Git tree; see the explicit tree attestation. All five
root/docbuild pin values in that source refer to the accepted QICLean merge.
The QIC merge additionally includes unrelated operator-mean modules; it is not
claimed to have the same complete tree as the earlier PR head. The entire
entropy/import proof closure and configuration are byte-identical, as checked
in `pin-update-audit.json`. The model delta from the prior checked base affects
only blueprint formatting, with no Lean source/API changes.
