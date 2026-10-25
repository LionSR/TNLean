/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.SequentialTruncation
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Axiom audits for the projection mass identity, sequential rank and error estimates,
their spectral threshold consequence, and the leading-eigenvector truncation. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``Entropy.norm_sq_toEuclideanLin_localLift_eq_trace,
      ``TNLean.MPS.AreaLaw.norm_sub_sequentialTruncation_le,
      ``TNLean.MPS.AreaLaw.norm_sub_sequentialTruncation_sq_le,
      ``TNLean.MPS.AreaLaw.norm_sequentialTruncation_leadingEigenprojection_sub_sq_le,
      ``TNLean.MPS.AreaLaw.rank_cutMatrix_sequentialTruncation_le,
      ``TNLean.MPS.AreaLaw.exists_sequentialTruncation,
      ``TNLean.MPS.AreaLaw.prefixBasisProjection,
      ``TNLean.MPS.AreaLaw.isOpenMPS_sequentialTruncation_prefixBasisProjection,
      ``TNLean.MPS.AreaLaw.isOpenMPS_sequentialTruncation_leadingEigenprojection] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
