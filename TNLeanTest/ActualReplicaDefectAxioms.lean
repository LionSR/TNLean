/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.PEPS.AreaLaw.Scan.ActualReplicaDefect
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom checks for normalization and the actual charge low-defect estimate. -/

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``norm_filteredVector_actualChargeData,
      ``actualChargeScanRound_globalLowDefectProjection_mass_ge] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

end TNLean.PEPS.AreaLaw.Scan.CollarScan
