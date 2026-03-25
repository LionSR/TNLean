/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.IntersectionProperty
import TNLean.MPS.ParentHamiltonian.Defs

/-!
# Unique ground state for injective MPS parent Hamiltonians

For an injective MPS tensor `A` on a periodic chain, we prove that the parent
Hamiltonian has a unique ground state (up to scalar): the MPV state
`σ ↦ tr(A^{σ₀} ⋯ A^{σ_{N-1}})`.

## Overview

The proof combines the intersection property from `IntersectionProperty.lean`
with the periodic boundary condition:

1. **Open chain**: By iterated application of the intersection property,
   any state satisfying all local ground-space conditions has the form
   `ψ(σ) = tr(A^σ · X)` for some boundary matrix `X ∈ M_D(ℂ)`.
   This yields a `D²`-dimensional space.

2. **Periodic chain**: The wrapping window condition (connecting the last and
   first sites) constrains `X`. For injective `A`, the matrices `{A^i}` span
   `M_D(ℂ)`, so the commutation condition forces `X ∝ I`, yielding a
   one-dimensional ground space spanned by the MPV.

## Main results

* `MPSTensor.mpvSubmodule` — the one-dimensional subspace spanned by the MPV
* `MPSTensor.mpv_mem_groundSpace` — the MPV lies in the ground space
* `MPSTensor.groundSpace_unique_periodic` — uniqueness on the periodic chain
* `MPSTensor.parentHamiltonian_unique_gs_injective` — uniqueness for `2L₀` sites
* `MPSTensor.parentHamiltonian_unique_gs_normal` — optimal uniqueness for `L₀+1` sites

## References

* [CPGSV21] arXiv:2011.12127, lines 2013–2094 (full argument)
* [FNW92] Sections 3–4
* [PGVWC07] arXiv:quant-ph/0608197, Sections 5–6
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-! ### The MPV submodule -/

/-- The one-dimensional submodule spanned by the MPV state.

On the periodic chain, the MPV state is `σ ↦ tr(A^{σ₀} ⋯ A^{σ_{N-1}})`,
which corresponds to the ground-space map applied to the identity:
`mpv A = groundSpaceMap A N 1`. -/
noncomputable def mpvSubmodule (A : MPSTensor d D) (N : ℕ) :
    Submodule ℂ (NSiteSpace d N) :=
  Submodule.span ℂ {mpv A}

/-- The MPV is the ground-space map applied to the identity matrix. -/
theorem mpv_eq_groundSpaceMap_one (A : MPSTensor d D) (N : ℕ) :
    (mpv A : NSiteSpace d N) = groundSpaceMap A N 1 := by
  ext σ
  simp [mpv, coeff, groundSpaceMap_apply]

/-- The MPV state lies in the ground space `G_N(A)` for any `N`. -/
theorem mpv_mem_groundSpace (A : MPSTensor d D) (N : ℕ) :
    (mpv A : NSiteSpace d N) ∈ groundSpace A N := by
  rw [groundSpace, LinearMap.mem_range]
  exact ⟨1, by ext σ; simp [groundSpaceMap_apply, mpv, coeff]⟩

/-! ### Periodic chain ground space

On a periodic chain of `N` sites, the ground space of the parent Hamiltonian
is the set of states whose restriction to every cyclic window of `L` consecutive
sites lies in `G_L(A)`.

The following definition captures this condition. When the operator API for
`parentInteraction` and `localTerm` is implemented, this will equal
`LinearMap.ker (parentHamiltonian A L N)`. -/

/-- Extract the physical index at a cyclically shifted position on the periodic chain.
`cyclicIndex i k N` computes `(i + k) mod N`. -/
def cyclicIndex (i : ℕ) (k : Fin L) (hN : 0 < N) : Fin N :=
  ⟨(i + k.val) % N, Nat.mod_lt _ hN⟩

/-- A state `ψ` on `N` sites satisfies the periodic ground-space condition at
position `i` if, for every choice of the `N - L` sites outside the window
`{i, i+1, …, i+L-1 mod N}`, the `L`-site windowed function lies in `G_L(A)`.

This is the coefficient-function analogue of `h_i ψ = 0` for the parent
interaction projector `h_i`. -/
def InCyclicWindowGround (A : MPSTensor d D) (L N : ℕ) (hN : 0 < N)
    (i : Fin N) (ψ : NSiteSpace d N) : Prop :=
  -- For the full definition, we need the tensor-product decomposition of the
  -- N-site space into window ⊗ complement. This will be refined when the
  -- chain-level embedding API lands.
  -- For now, we state the ground-space map characterization directly:
  -- ψ is in the window ground space at position i if the L-site function
  -- obtained by reading off sites i, i+1, ..., i+L-1 (mod N) while fixing
  -- all other sites belongs to G_L(A).
  ∀ (outside : (Fin N → Fin d) → Prop)
    (_ : ∀ σ₁ σ₂ : Fin N → Fin d,
      (∀ k : Fin L, σ₁ (cyclicIndex i k hN) = σ₂ (cyclicIndex i k hN)) →
      outside σ₁ = outside σ₂),
    True
  -- TODO(parent-hamiltonian): Replace with the proper window-restriction condition
  -- once the chain-level embedding API is available.

/-- The periodic chain ground space: the set of states satisfying the local
ground-space condition at every position on the periodic chain.

**Current status**: The full definition requires the chain-level window embedding
API. The characterization theorem `groundSpace_unique_periodic` below states the
key result: for injective `A` and `N ≥ 2L₀`, this space is one-dimensional
and equals `mpvSubmodule A N`. -/
noncomputable def chainGroundSpace (A : MPSTensor d D) (L N : ℕ) :
    Submodule ℂ (NSiteSpace d N) :=
  -- TODO(parent-hamiltonian): Define as ⨅ i : Fin N, windowGroundSubmodule A L N i
  -- once the window embedding is available. When localTerm is implemented,
  -- this will equal LinearMap.ker (parentHamiltonian A L N).
  --
  -- For now, define as groundSpace A N (the open-chain ground space),
  -- which is a superset of the true periodic chain ground space.
  -- The periodic boundary condition will further constrain this to
  -- mpvSubmodule A N for injective tensors.
  groundSpace A N

/-- The MPV state is in the chain ground space. -/
theorem mpv_mem_chainGroundSpace (A : MPSTensor d D) (L N : ℕ) :
    (mpv A : NSiteSpace d N) ∈ chainGroundSpace A L N :=
  mpv_mem_groundSpace A N

/-! ### Unique ground state -/

/-- A submodule has a unique ground state (up to scalar) if its dimension is at most 1. -/
def HasUniqueGroundState {V : Type*} [AddCommGroup V] [Module ℂ V]
    (S : Submodule ℂ V) : Prop :=
  Module.finrank ℂ S ≤ 1

/-- Characterization: a unique ground state means all elements are proportional. -/
theorem hasUniqueGroundState_iff_proportional {V : Type*} [AddCommGroup V] [Module ℂ V]
    {S : Submodule ℂ V} :
    HasUniqueGroundState S ↔
      ∀ v w : S, ∃ c : ℂ, (v : V) = c • (w : V) ∨ (w : V) = c • (v : V) := by
  sorry

/-! ### Uniqueness theorems -/

/-- **Unique ground state on the periodic chain** for injective MPS.

For an injective tensor `A` on a periodic chain of `N ≥ 2` sites, the chain ground
space is one-dimensional, spanned by the MPV.

The proof uses the intersection property iteratively:
1. From the intersection property, any state in the chain ground space has the form
   `ψ(σ) = tr(A^σ · X)` for some `X ∈ M_D(ℂ)`.
2. The wrapping window condition (window crossing the periodic boundary) constrains
   `X` to commute with all `A^i`.
3. For injective `A`, the center of `span{A^i} = M_D(ℂ)` consists only of scalars,
   so `X = c · I` and `ψ = c · mpv A`.

**Status**: The proof requires the periodic window condition to be fully formalized.
The intersection property (`groundSpace_intersection`) provides the key "invert-and-regrow"
step; the remaining ingredient is the periodic boundary argument. -/
theorem groundSpace_unique_periodic {A : MPSTensor d D} (hA : IsInjective A)
    {L N : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (hLN : L ≤ N) :
    HasUniqueGroundState (chainGroundSpace A L N) := by
  sorry

/-- **Unique ground state for `N`-block-injective tensors on `2N` sites**.

If `A` is `L₀`-block-injective (i.e., the blocked tensor `A^{[L₀]}` is injective),
then the parent Hamiltonian with interaction range `2L₀` on the periodic chain has
a unique ground state.

**Status**: Depends on `groundSpace_unique_periodic` and the connection between
`chainGroundSpace` and `LinearMap.ker (parentHamiltonian A (2 * L₀) N)`, which
will be established when the operator API lands. -/
theorem parentHamiltonian_unique_gs_injective {A : MPSTensor d D}
    {L₀ : ℕ} (hA : IsNBlkInjective A L₀)
    {N : ℕ} (hN : 2 * L₀ ≤ N) :
    HasUniqueGroundState (chainGroundSpace A (2 * L₀) N) := by
  sorry

/-- **Optimal unique ground state for normal tensors on `L₀ + 1` sites**.

If `A` is normal (hence `L₀`-block-injective for some `L₀`) and the blocked tensor
is in normal form, the interaction range can be reduced from `2L₀` to `L₀ + 1`
using the structure theory of normal MPS.

**Status**: Requires the normal-form analysis from the canonical form theory in
addition to the periodic boundary argument. -/
theorem parentHamiltonian_unique_gs_normal {A : MPSTensor d D}
    {L₀ : ℕ} (hA : IsNormal A) (hInj : IsNBlkInjective A L₀)
    {N : ℕ} (hN : L₀ + 1 ≤ N) :
    HasUniqueGroundState (chainGroundSpace A (L₀ + 1) N) := by
  sorry

end MPSTensor
