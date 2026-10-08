/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegionOperatorEmbedding

/-!
# Axiom guards for regional operator embeddings

All three public declarations use only the standard logical axioms recorded
by the independent raw audit.
-/

set_option linter.hashCommand false

/-- info: 'TNLean.PEPS.agreeOff_region_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TNLean.PEPS.agreeOff_region_iff

/-- info: 'TNLean.PEPS.regionLocalTerm_eq_embedOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TNLean.PEPS.regionLocalTerm_eq_embedOp

/-- info: 'TNLean.PEPS.dependentRegionOperatorLift_eq_reindex_embedOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TNLean.PEPS.dependentRegionOperatorLift_eq_reindex_embedOp
