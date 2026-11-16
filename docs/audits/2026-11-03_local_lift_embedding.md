# Regional lifts and inclusion of sites

The local lift of a matrix on a finite region is its placement along the inclusion of that region. `QuantumCircuit.localLift_eq_embedOp`, in `Circuit/EntropySupport.lean`, states this coordinate identity once. Its proof is the existing calculation formerly nested in the converse support characterization. The statement includes empty regions and zero physical dimension.

The converse support characterization and the singleton selected-middle calculation now use the same identity. All five existing public theorem signatures in the two changed source files are byte-for-byte unchanged. The mathematical blueprint correspondence is the supported-operator entry `thm:area_law_supported_identity`; its statement now explicitly includes the placement identity.

The repeated calculation was identified while preparing the native middle soft-MPO construction. That separate construction is not established by this refactor.
