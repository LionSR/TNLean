/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.SupportProjectionOrder
import TNLean.Circuit.SiteExpectationOrder
import TNLean.Circuit.EntropySupport

/-!
# The range projection of a supported Hermitian operator

Functional calculus preserves the sites on which a Hermitian operator acts.
In particular, replacement by its range projection preserves its physical
support. This is the local support assertion in the range-projection reduction
of ALVV, arXiv:1602.08828v2, Section 6.1, lines 1457–1460.
-/

namespace QuantumCircuit

variable {q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [NeZero q]

/-- The range projection acts on the same sites as the original Hermitian
operator. ALVV, arXiv:1602.08828v2, Section 6.1, lines 1457–1460. -/
theorem supportProj_mem_supportedOperators (K : Finset ι)
    {A : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hA : A.IsHermitian)
    (hK : A ∈ supportedOperators q (K : Set ι)) :
    hA.supportProj ∈ supportedOperators q (K : Set ι) := by
  rw [hA.supportProj_eq_cfc]
  exact mem_supportedOperators_of_forall_commute K fun Y hY ↦
    (commute_of_mem_supportedOperators disjoint_compl_right hK hY).cfc_real _

end QuantumCircuit
