/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.OpenMPSCutRank
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Axiom checks and boundary cases for the open-boundary cut-rank characterization. -/

open TNLean.MPS.AreaLaw

-- Empty and one-site chains have no internal bonds, even at bond bound zero.
example {q : ℕ} (ψ : EuclideanSpace ℂ (Fin 0 → Fin q)) :
    IsOpenMPS 0 q 0 (fun x ↦ ψ x) := by
  apply (isOpenMPS_iff_internal_cutMatrix_rank_le ψ).mpr
  omega

example {q : ℕ} (ψ : EuclideanSpace ℂ (Fin 1 → Fin q)) :
    IsOpenMPS 1 q 0 (fun x ↦ ψ x) := by
  apply (isOpenMPS_iff_internal_cutMatrix_rank_le ψ).mpr
  omega

-- At a genuine internal cut, zero bond bound forces rank zero, not merely rank at most one.
example {L q : ℕ} {ψ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hψ : IsOpenMPS L q 0 (fun x ↦ ψ x)) {k : ℕ} (hk0 : 0 < k) (hkL : k < L) :
    (cutMatrix ψ k).rank = 0 :=
  Nat.eq_zero_of_le_zero (hψ.rank_cutMatrix_le hk0 hkL)

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let names := #[
    ``TNLean.MPS.AreaLaw.rank_cutMatrix_le_bondDim,
    ``TNLean.MPS.AreaLaw.IsOpenMPS.rank_cutMatrix_le,
    ``TNLean.MPS.AreaLaw.isOpenMPS_iff_internal_cutMatrix_rank_le]
  for decl in names do
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
