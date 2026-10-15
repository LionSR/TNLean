/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DistributedOperatorContraction
import Mathlib.Data.Fintype.BigOperators

/-! # Gate-label sums on the universal active set

When every gate occurrence is active, the active-gate subtype is canonically
the original gate type. The finite sum over its dependent label assignments
is therefore the original label sum. The identification retains each label
at its original occurrence and chooses no additional label values.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 565–579.
-/

namespace TNLean.PEPS.Approximation.DistributedOperatorContraction

variable {G : Type} [Fintype G] {Label : G → Type}
variable [∀ g, Fintype (Label g)] {m n : Type}

open Classical in
/-- Reindex the original finite label sum by labels on the universal active
set. The matrix summand is arbitrary, and its row and column types need not
be finite. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`,
lines 565–579. -/
theorem sum_eq_sum_gateLabels_univ
    (K : ((g : G) → Label g) → Matrix m n ℂ) :
    (∑ η : (g : G) → Label g, K η) =
      ∑ ξ : GateLabels (Finset.univ : Finset G) Label,
        K (fun g ↦ ξ ⟨g, Finset.mem_univ g⟩) := by
  let e := Equiv.piCongrLeft
    (fun g : ActiveGate (Finset.univ : Finset G) ↦ Label g.1)
    (Equiv.subtypeUnivEquiv (fun g : G ↦ Finset.mem_univ g)).symm
  exact (e.symm.sum_comp K).symm

end TNLean.PEPS.Approximation.DistributedOperatorContraction
