/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegionOperatorEmbedding

/-!
# Raw axiom audit for regional operator embeddings

Print all three public declarations independently of their guarded tests.
-/

set_option linter.hashCommand false

#print axioms TNLean.PEPS.agreeOff_region_iff
#print axioms TNLean.PEPS.regionLocalTerm_eq_embedOp
#print axioms TNLean.PEPS.dependentRegionOperatorLift_eq_reindex_embedOp
