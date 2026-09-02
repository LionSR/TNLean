/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FixedSubmodule

/-!
# Common fixed submodule

This file defines the common fixed submodule of an arbitrary family of linear
endomorphisms and gives its elementary membership and dimension properties.
No commutativity assumption is needed.
-/

namespace LinearMap

variable {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]

/-- The intersection of the fixed submodules of a family of endomorphisms. -/
def commonFixedSubmodule {ι : Sort*} (f : ι → V →ₗ[R] V) : Submodule R V :=
  ⨅ i, (f i).fixedSubmodule

@[simp]
theorem mem_commonFixedSubmodule_iff {ι : Sort*} {f : ι → V →ₗ[R] V} {v : V} :
    v ∈ commonFixedSubmodule f ↔ ∀ i, f i v = v := by
  simp only [commonFixedSubmodule, Submodule.mem_iInf, mem_fixedSubmodule_iff]

variable {K W : Type*} [DivisionRing K] [AddCommGroup W] [Module K W]
  [Module.Finite K W]

/-- A common nonzero fixed vector ensures that the common fixed submodule has
finrank at least one. -/
theorem one_le_finrank_commonFixedSubmodule {ι : Sort*} (f : ι → W →ₗ[K] W) {v : W}
    (hv : v ∈ commonFixedSubmodule f) (hv0 : v ≠ 0) :
    1 ≤ Module.finrank K (commonFixedSubmodule f) := by
  rw [Submodule.one_le_finrank_iff]
  exact (Submodule.ne_bot_iff _).mpr ⟨v, hv, hv0⟩

end LinearMap
