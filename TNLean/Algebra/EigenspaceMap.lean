/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Images of eigenspaces

An endomorphism acts on its `μ`-eigenspace as multiplication by `μ`.  When
`μ ≠ 0` that action is invertible, so the eigenspace is mapped *onto* itself
and not merely into itself.

## Main results

* `Module.End.map_eigenspace_of_ne_zero`: `f (ker (f - μ)) = ker (f - μ)` for
  `μ ≠ 0`.
-/

namespace Module.End

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- An eigenspace for a **nonzero** eigenvalue is mapped *onto* itself: on the
`μ`-eigenspace the endomorphism acts as multiplication by `μ`, which is
invertible when `μ ≠ 0`. -/
theorem map_eigenspace_of_ne_zero (f : Module.End K V) {μ : K} (hμ : μ ≠ 0) :
    Submodule.map f (f.eigenspace μ) = f.eigenspace μ := by
  refine le_antisymm ?_ fun y hy ↦ ?_
  · rintro _ ⟨x, hx, rfl⟩
    rw [Module.End.mem_eigenspace_iff.mp hx]
    exact (f.eigenspace μ).smul_mem μ hx
  · refine ⟨μ⁻¹ • y, (f.eigenspace μ).smul_mem _ hy, ?_⟩
    rw [map_smul, Module.End.mem_eigenspace_iff.mp hy, smul_smul, inv_mul_cancel₀ hμ,
      one_smul]

end Module.End
