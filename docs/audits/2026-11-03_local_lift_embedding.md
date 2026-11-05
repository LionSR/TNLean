# Regional lifts and inclusion of sites

The local lift of a matrix on a finite region is its placement along the inclusion of that region. `QuantumCircuit.localLift_eq_embedOp`, in `Circuit/EntropySupport.lean`, states this coordinate identity once. Its proof is the existing calculation formerly nested in the converse support characterization. The statement includes empty regions and zero physical dimension.

The converse support characterization and the singleton selected-middle calculation now use the same identity. All five existing public theorem signatures in the two changed source files are byte-for-byte unchanged. The mathematical blueprint correspondence is the supported-operator entry `thm:area_law_supported_identity`; its statement now explicitly includes the placement identity.

The repeated calculation was identified while preparing the native middle soft-MPO construction. That separate construction is not established by this refactor.

## Verification

The checked dependency pair is TNLean `88ab31ce57bdbc4bcb65be00055d1db50df4f259` and QICLean `e817ea0a8a46440eddc361d41cc46b9e61ba10f4`. All checks used the guarded private checker and wrote objects only under `/tmp`. No dependency source or build cache was changed.

The owner passed strict checking in 5.699 seconds. Its affected selected importers `SupportedSchmidtRank`, `LeftSupportedSchmidtRank`, and `ThreeRegionSupport` were freshly checked before the changed `SelectedMiddleData` consumer, which passed in 42.116 seconds. This last timing exceeds the 25-second warning threshold and is recorded without a timing-only repeat. The six-name imported foundation audit passed in 23.857 seconds; every declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`. The temporary audit commands were deleted.

The final production-module check will use fresh overrides for every selected importer of the changed owner. Canonical ordinary build and compiled whole-library blueprint checks remain integration gates.
