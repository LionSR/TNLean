import TNLean.MPS.ParentHamiltonian.Defs
import TNLean.MPS.ParentHamiltonian.Basic
import TNLean.MPS.ParentHamiltonian.UniqueGroundState
import TNLean.MPS.ParentHamiltonian.IntersectionProperty

/-!
# Martingale-method spectral-gap scaffolding for parent Hamiltonians

This file introduces a first formal scaffold for the martingale approach to proving
that MPS parent Hamiltonians are gapped.

The intended proof route is:
1. frustration-freeness (`parentHamiltonian_frustrationFree`),
2. local projector gap (`parentInteraction`/`localTerm` as orthogonal projections),
3. intersection property (`groundSpace_intersection`),
4. a martingale estimate (Nachtergaele / Kastoryano–Lucia).

The final quantitative assembly is left as future work.
-/

namespace MPSTensor

open scoped BigOperators

variable {d D : ℕ}
variable (L N : ℕ)

/-- Ground-space submodule for the finite-size parent Hamiltonian. -/
noncomputable def parentHamiltonianGroundSpace (A : MPSTensor d D) : Submodule ℂ (NSiteSpace d N) :=
  LinearMap.ker (parentHamiltonian A L N)

/--
A norm-form spectral-gap statement for the parent Hamiltonian.

This is the endpoint produced by the martingale method: vectors orthogonal to the
ground space are uniformly penalized by the Hamiltonian.
-/
theorem parentHamiltonian_gapped
    (A : MPSTensor d D) (hA : IsInjective A) (hL : 1 < L) (hLN : L ≤ N) :
    ∃ γ > 0, ∀ v, v ∉ parentHamiltonianGroundSpace (L := L) (N := N) A →
      ‖parentHamiltonian A L N v‖ ≥ γ * ‖v‖ := by
  -- Ingredients available on `main`:
  -- * `groundSpace_intersection`
  -- * frustration-freeness of parent Hamiltonians on MPS vectors
  -- * projector structure of local terms
  -- The quantitative martingale estimate still needs to be assembled.
  sorry

end MPSTensor
