import TNLean.MPS.AreaLaw.DGEntropyParameters
import TNLean.MPS.AreaLaw.PhysicalDGEntropy
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Public declarations and standard foundations for physical ground-space entropy bounds. -/

run_cmd do
  let env ← Lean.getEnv
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
      ``Entropy.probabilityEntropy_le_of_logarithmic_rank_tail_bounds,
      ``Real.dg_entropy_coefficient_bound,
      ``TNLean.MPS.AreaLaw.exists_physical_dg_interval_entropy_bound] do
    unless env.contains decl do
      throwError "Missing public entropy declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.size == expected.size && axioms.all (expected.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
