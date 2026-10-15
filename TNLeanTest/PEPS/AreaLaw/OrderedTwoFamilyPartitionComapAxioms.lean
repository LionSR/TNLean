import TNLean.PEPS.AreaLaw.Geometry.OrderedTwoFamilyPartitionComap
import Lean.Elab.Command
import Lean.Util.CollectAxioms

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[
    ``TNLean.PEPS.AreaLaw.Geometry.OrderedTwoFamilyPartition.comap,
    ``TNLean.PEPS.AreaLaw.Geometry.OrderedTwoFamilyPartition.earlierSameFamily_comap,
    ``TNLean.PEPS.AreaLaw.Geometry.OrderedTwoFamilyPartition.card_residual_comap_le]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
