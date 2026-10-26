import TNLean.Algebra.CoreWordCoefficients
import Lean.Elab.Command
import Lean.Util.CollectAxioms

run_cmd do
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``Matrix.coreWordCoeff, ``Matrix.prod_coreStep_eq_sum] do
    let axioms ← Lean.collectAxioms decl
    unless axioms.size == expected.size && axioms.all (expected.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
