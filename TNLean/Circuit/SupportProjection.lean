/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.SupportProjectionOrder
import TNLean.Circuit.SiteEmbedding
import TNLean.Circuit.SupportedMatrixElements
import QICLean.Entropy.RegionUnion
import QICLean.ManyBody.Sites.Twirl

/-!
# The range projection of a supported Hermitian operator

Functional calculus preserves the sites on which a Hermitian operator acts.
In particular, replacement by its range projection preserves its physical
support. This is the local support assertion in the range-projection reduction
of ALVV, arXiv:1602.08828v2, Section 6.1, lines 1457–1460.
-/

namespace QuantumCircuit

variable {q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The range projection acts on the same sites as the original Hermitian
operator. ALVV, arXiv:1602.08828v2, Section 6.1, lines 1457–1460. -/
theorem supportProj_mem_supportedOperators (K : Finset ι)
    {A : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hA : A.IsHermitian)
    (hK : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) K) :
    hA.supportProj ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) K := by
  rw [hA.supportProj_eq_cfc]
  refine ManyBody.mem_supportedOperators_iff_forall_commute.mpr fun Y hY ↦ ?_
  have hY' : Y ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) Kᶜ := by
    simpa only [Finset.coe_compl] using hY
  exact (ManyBody.commute_of_mem_supportedOperators_of_disjoint hK hY'
      disjoint_compl_right).cfc_real _

end QuantumCircuit
