/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.TraceCoreSlices
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Exact declaration dependencies for TraceCoreSlices -/

run_cmd do
  let env ← Lean.getEnv
  let expectations : Array (Lean.Name × Array Lean.Name) := #[
    (``TNLean.MPS.AreaLaw.isOpenMPS_trace_closed_chain,
      #[``propext, ``Classical.choice, ``Quot.sound]),
    (``TNLean.MPS.AreaLaw.orderedProduct_partition_interval,
      #[``propext]),
    (``MPOTensor.interiorMatrixSlice,
      #[``propext, ``Classical.choice, ``Quot.sound]),
    (``MPOTensor.stackClosingMatrix,
      #[``propext, ``Classical.choice, ``Quot.sound]),
    (``MPOTensor.sum_word_slices_eq_trace_stackedTensor,
      #[``propext, ``Classical.choice, ``Quot.sound])]
  for (decl, expected) in expectations do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let actual ← Lean.collectAxioms decl
    unless actual.size == expected.size && actual.all (expected.contains ·) do
      throwError "Unexpected axioms for {decl}: {actual}"
