/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Defs
import TNLean.MPS.Core.Transfer
import TNLean.Channel.Stinespring

/-!
# Pure-state renormalization fixed point (RFP) — definitions

This file defines the notion of a **renormalization fixed point** (RFP) for a
pure MPS tensor, following arXiv:1606.00608 §3.1
(Cirac–Pérez-García–Schuch–Verstraete).

The key definition is `IsRFP A`, which says that the completely positive map
(CPM) associated to the MPS tensor `A` is **idempotent**: composing the
transfer map with itself yields the same transfer map.
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- An MPS tensor `A` is a **renormalization fixed point** (RFP) when its
transfer map is idempotent as a linear map, i.e. `E_A ∘ E_A = E_A`.
See arXiv:1606.00608, Definition 3.2. -/
def IsRFP (A : MPSTensor d D) : Prop :=
  transferMap A ∘ₗ transferMap A = transferMap A

/-- The RFP condition is equivalent to a Kraus-level condition: there exists
an isometry `U` on the physical index such that `A^{i₁} A^{i₂} = Σ_j U_{(i₁,i₂),j} A^j`.
This follows from Stinespring: two Kraus representations of the same CPM
are related by an isometry on the physical index.
See arXiv:1606.00608, Theorem 3.1.

TODO: state the Kraus-level condition precisely and prove the equivalence. -/
theorem isRFP_iff_kraus (A : MPSTensor d D) :
    IsRFP A ↔ ∃ _U : Matrix (Fin (d * d)) (Fin d) ℂ, True := by
  sorry

end MPSTensor
