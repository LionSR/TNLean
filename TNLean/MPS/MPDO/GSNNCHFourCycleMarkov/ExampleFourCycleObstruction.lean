/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CPSVExample412FourCycleEntropy
import TNLean.MPS.MPDO.GSNNCHFourCycleMarkov.FourCycle

/-!
# The four-cycle obstruction in CPSV16 Example 4.12

This file identifies the tripartite coordinates of the literal four-site
entropy calculation with the generic four-cycle regrouping, and concludes
that the tensor in CPSV16 Example 4.12 is not GSNNCH.
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

namespace MPOTensor.CPSVExample412Literal

/-- The basis regrouping used in the literal entropy calculation is exactly
the specialization of the general four-cycle regrouping to binary sites.

This identifies the coordinate boundary used for CPSV16, arXiv:1606.00608,
Example 4.12, lines 932--938, with the one used for the four-site consequence
of Definition 4.8, lines 829--850. -/
private theorem fourCycleTripartiteEquiv_eq_generic :
    fourCycleTripartiteEquiv = MPOTensor.fourCycleTripartiteEquiv 2 := by
  apply Equiv.symm_bijective.injective
  apply Equiv.ext
  intro σ
  rfl

/-- The tripartite state used in the literal entropy calculation is the
binary specialization of the general four-cycle regrouping.

This identifies the normalized state in CPSV16, arXiv:1606.00608,
Example 4.12, lines 932--938, with the four-site coordinate boundary derived
from Definition 4.8, lines 829--850. -/
theorem fourCycleTripartiteState_eq_generic :
    fourCycleTripartiteState =
      MPOTensor.fourCycleTripartiteState (normalizedMPO M 4) := by
  ext x y
  simp only [fourCycleTripartiteState, MPOTensor.fourCycleTripartiteState,
    Matrix.reindex_apply, Equiv.symm_symm]
  rw [fourCycleTripartiteEquiv_eq_generic]

/-- The tensor in CPSV16 Example 4.12 is not GSNNCH.

The four-site specialization of Definition 4.8 would force equality in
strong subadditivity for (A={0}), (B={1,3}), (C={2}), whereas the
literal four-site entropy calculation is strict.

Source conclusion: CPSV16, arXiv:1606.00608, Example 4.12, lines 932--938. -/
theorem M_not_isGSNNCH : ¬ IsGSNNCH M := by
  intro hGSNNCH
  have hSSA := MPOTensor.isSSAEquality_fourCycle_of_isGSNNCHAt
    (hGSNNCH 4 (by decide))
  apply fourCycleTripartiteState_not_isSSAEquality
  simpa only [IsSSAEquality, ← fourCycleTripartiteState_eq_generic] using hSSA

end MPOTensor.CPSVExample412Literal
