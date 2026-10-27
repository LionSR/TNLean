/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.Basic
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
The public viable-set results are present and depend only on the three standard axioms.
The span projection retains its original definition and explicit linear-equivalence rewrites.
-/

open TNLean.MPS.AreaLaw

variable {L q k : ℕ}

example (S : Set (LeftBlockVector L q k)) :
    spanProjection S = Matrix.toEuclideanLin.symm
      (Submodule.span ℂ S).starProjection.toLinearMap := rfl

example (S : Set (LeftBlockVector L q k)) :
    spanProjection S = (Submodule.span ℂ S).starProjectionMatrix := rfl

example (S : Set (LeftBlockVector L q k)) :
    Matrix.toEuclideanLin (spanProjection S) =
      (Submodule.span ℂ S).starProjection.toLinearMap := by
  rw [spanProjection, LinearEquiv.apply_symm_apply]

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``TNLean.MPS.AreaLaw.spanProjection,
    ``TNLean.MPS.AreaLaw.toEuclideanLin_spanProjection,
    ``TNLean.MPS.AreaLaw.isStarProjection_spanProjection,
    ``TNLean.MPS.AreaLaw.isHermitian_spanProjection,
    ``TNLean.MPS.AreaLaw.spanProjection_mul_self,
    ``TNLean.MPS.AreaLaw.spanProjection_mul_cutMatrix_eq_iff,
    ``TNLean.MPS.AreaLaw.spanProjection_mul_regionState_eq_iff,
    ``TNLean.MPS.AreaLaw.leftApply_spanProjection_cutVector_eq_iff,
    ``TNLean.MPS.AreaLaw.isViable_iff_le_norm_starProjection,
    ``TNLean.MPS.AreaLaw.IsViable.forall_mem_span_singleton,
    ``TNLean.MPS.AreaLaw.isViable_iff_forall_mem_span_singleton,
    ``TNLean.MPS.AreaLaw.IsOpenMPS.snoc,
    ``TNLean.MPS.AreaLaw.card_extend_le,
    ``TNLean.MPS.AreaLaw.leftSupportSubmodule_le_extend,
    ``TNLean.MPS.AreaLaw.IsViable.extend,
    ``TNLean.MPS.AreaLaw.IsLeftOpenMPS.extendSite,
    ``TNLean.MPS.AreaLaw.IsViableMPS.extend] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
