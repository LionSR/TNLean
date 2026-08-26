/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.Wielandt.Primitivity.VectorSpreadPositivity
import QICLean.Kraus.InvariantProjection
import TNLean.Wielandt.Primitivity.Definitions

/-!
# Fixed-length vector spreading: MPS formulations

This file states the positivity and irreducibility consequences of fixed-length
vector spreading in transfer-map notation. Their finite-Kraus proofs are provided
by `QICLean.Kraus.Wielandt.Primitivity.VectorSpreadPositivity`.

These results form the first part of Proposition 3, direction (a) to (c), of
Sanz, Pérez-García, Wolf, and Cirac, arXiv:0909.5347.
-/

open scoped Matrix ComplexOrder BigOperators
open Matrix Module

namespace MPSTensor

variable {d D : ℕ}

/-- Paper-primitivity implies that the tensor has no nontrivial invariant
orthogonal projection. -/
theorem isIrreducibleTensor_of_isPrimitivePaper
    (A : MPSTensor d D)
    (hPrim : IsPrimitivePaper A) :
    Kraus.IsIrreducibleFamily A := by
  obtain ⟨q, _, hq⟩ := hPrim
  exact Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM A
    (Kraus.isIrreducibleMap_mapLM_of_vectorSpreadSpan_eq_top A hq)

end MPSTensor
