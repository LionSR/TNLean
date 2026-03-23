/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Semigroup.ReducibleQDS

/-!
# Wolf Corollary 7.2 — Honest partial formalization

This file records the currently proved part of Wolf Corollary 7.2 in a way
that matches the available infrastructure.

At present, we formalize a **single sufficient criterion for non-reducibility**:
if a GKSL generator admits no nontrivial block-upper-triangular Lindblad
representation, then the associated QDS is not reducible.

This does **not** yet formalize full relaxation (primitivity / convergence to a
unique full-rank stationary state), which additionally depends on the
irreducibility ↔ primitivity bridge.
-/

open scoped Matrix ComplexOrder BigOperators NNReal MatrixOrder
open Matrix Finset

noncomputable section

attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

variable {D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/--
If a GKSL generator has no block-upper-triangular Lindblad decomposition,
then the generated quantum dynamical semigroup is not reducible.

This is the contrapositive of Wolf Prop 7.6 `(3) → (4)`.
-/
theorem not_isReducibleQDS_of_no_blockUpperTriangular_lindblad
    {L : Mat →ₗ[ℂ] Mat}
    (hGKSL : IsGKSLGenerator L)
    (hNoBlockUT : ¬ HasBlockUpperTriangularLindblad L) :
    ¬ IsReducibleQDS L := by
  intro hReducible
  exact hNoBlockUT (wolf_prop_7_6_three_implies_four hGKSL hReducible)

/--
Rephrasing of `not_isReducibleQDS_of_no_blockUpperTriangular_lindblad` with
the assumptions in the opposite order.
-/
theorem no_blockUpperTriangular_lindblad_implies_not_isReducibleQDS
    {L : Mat →ₗ[ℂ] Mat}
    (hNoBlockUT : ¬ HasBlockUpperTriangularLindblad L)
    (hGKSL : IsGKSLGenerator L) :
    ¬ IsReducibleQDS L :=
  not_isReducibleQDS_of_no_blockUpperTriangular_lindblad hGKSL hNoBlockUT

end -- noncomputable section
