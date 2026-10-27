/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalIntervalTransport
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Exact declaration dependencies for PhysicalIntervalTransport -/

run_cmd do
  let env ← Lean.getEnv
  let expectations : Array (Lean.Name × Array Lean.Name) := #[
    (``MPOTensor.identityExtendInterval,
      #[``propext, ``Classical.choice, ``Quot.sound]),
    (``TNLean.MPS.AreaLaw.intervalShiftOrderIso,
      #[``propext, ``Classical.choice, ``Quot.sound]),
    (``TNLean.MPS.AreaLaw.intervalShiftOrderIso_mem_subinterval,
      #[``propext, ``Classical.choice, ``Quot.sound]),
    (``TNLean.MPS.AreaLaw.intervalShift_subinterval_length_le,
      #[``propext, ``Quot.sound]),
    (``TNLean.MPS.AreaLaw.intervalComplementEquiv,
      #[``propext, ``Classical.choice, ``Quot.sound]),
    (``TNLean.MPS.AreaLaw.exists_retainedMatrix_of_physical_localLift,
      #[``propext, ``Classical.choice, ``Quot.sound]),
    (``MPOTensor.trace_identityExtendInterval_nested_natural,
      #[``propext, ``Classical.choice, ``Quot.sound])]
  for (decl, expected) in expectations do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let actual ← Lean.collectAxioms decl
    unless actual.size == expected.size && actual.all (expected.contains ·) do
      throwError "Unexpected axioms for {decl}: {actual}"
