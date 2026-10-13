/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.PEPS.AreaLaw.Scan.ActualGlobalReplicaEnergy
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom checks for the actual fill and charge rounds' global replica energy. -/

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``actualFillScanRound_meanEnergy_eq_globalReplicaMeanHamiltonian,
      ``actualChargeScanRound_meanEnergy_eq_globalReplicaMeanHamiltonian] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

end TNLean.PEPS.AreaLaw.Scan.CollarScan
