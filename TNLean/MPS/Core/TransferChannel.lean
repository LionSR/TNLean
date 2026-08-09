/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Irreducible.TraceAdjoint
import TNLean.Channel.KrausMap
import TNLean.MPS.Core.Transfer

/-!
# Channel compatibility for MPS transfer maps

This adapter identifies the matrix-product-state transfer-map notation with the generic
finite Kraus-map API. Generic channel developments should use `Kraus.map` and `Kraus.mapLM`
directly.

## Main declarations

* `Kraus.isChannel_transferMap`: the MPS transfer map of a trace-preserving Kraus family is
  a channel.
* `trace_mul_transferMap_adjoint`: the generic Kraus trace-adjoint identity in MPS
  transfer-map notation.
-/

open scoped Matrix ComplexOrder BigOperators
open Matrix Finset

variable {D : ℕ}

namespace Kraus

variable {d : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- The MPS transfer map of a trace-preserving finite Kraus family is a quantum channel. -/
theorem isChannel_transferMap (K : Fin d → Mat) (h_tp : IsTP K) :
    IsChannel (MPSTensor.transferMap (d := d) (D := D) K) := by
  have hmap : MPSTensor.transferMap (d := d) (D := D) K = mapLM K := by
    apply LinearMap.ext
    intro X
    simp [MPSTensor.transferMap_apply]
  rw [hmap]
  exact isChannel_mapLM K h_tp

end Kraus
