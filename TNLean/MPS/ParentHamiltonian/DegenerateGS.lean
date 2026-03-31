/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.UniqueGroundState
import TNLean.MPS.BNT.Construction
import TNLean.MPS.CanonicalForm.Assembly
import TNLean.MPS.FundamentalTheorem.Multi

/-!
# Degenerate ground space = BNT span (block-injective parent Hamiltonians)

This file formalizes the declaration-level interface for the block-injective case:
for a canonical-form/BNT decomposition, the periodic parent-Hamiltonian ground
space equals the span of the BNT states.

The detailed proof is split conceptually into two inclusions:

* `⊇`: each BNT block-state is in the parent-Hamiltonian ground space;
* `⊆`: every ground state decomposes into block components, and injective-block
  uniqueness (from `UniqueGroundState`) forces each component to be proportional
  to the block MPV state.
-/

namespace MPSTensor

open scoped Matrix

variable {d r : ℕ} {dim : Fin r → ℕ} {μ : Fin r → ℂ}

/-- Parent-Hamiltonian ground space for a CF/BNT block family, represented via
`chainGroundSpace` of the assembled tensor. -/
noncomputable def parentHamiltonianGroundSpace
    (A : (j : Fin r) → MPSTensor d (dim j)) (L N : ℕ) :
    Submodule ℂ (NSiteSpace d N) :=
  chainGroundSpace (toTensorFromBlocks μ A) L N

/-- Span of BNT block MPV states (as `N`-site coefficient functions). -/
noncomputable def bntSpan
    (A : (j : Fin r) → MPSTensor d (dim j)) (N : ℕ) :
    Submodule ℂ (NSiteSpace d N) :=
  Submodule.span ℂ (Set.range fun j : Fin r => (mpv (A j) : NSiteSpace d N))

/-- `⊇` direction helper: each BNT block MPV lies in the parent-Hamiltonian
ground space of the assembled tensor. -/
theorem bnt_mem_groundSpace
    (hCF : IsCanonicalFormBNT μ A) {L N : ℕ} (hN : N ≥ L + 1)
    (j : Fin r) :
    (mpv (A j) : NSiteSpace d N) ∈ parentHamiltonianGroundSpace (μ := μ) A L N := by
  -- Planned route:
  -- 1. use the open-chain / cyclic-window argument blockwise,
  -- 2. transport to the assembled tensor,
  -- 3. conclude membership in `chainGroundSpace`.
  --
  -- This theorem is introduced as the dedicated interface point for the `⊇`
  -- inclusion in `parentHamiltonian_gs_eq_bnt_span`.
  sorry

/-- **Degenerate ground space = span of BNT states** for block-injective parent
Hamiltonians (declaration-level theorem).

Main statement requested in PR #5/5: the periodic parent-Hamiltonian ground
space of a canonical-form/BNT tensor equals the span of the individual BNT
block MPV states.
-/
theorem parentHamiltonian_gs_eq_bnt_span
    (A : (j : Fin r) → MPSTensor d (dim j))
    (hCF : IsCanonicalFormBNT μ A) {L N : ℕ} (hN : N ≥ L + 1) :
    parentHamiltonianGroundSpace (μ := μ) A L N = bntSpan A N := by
  -- `⊇`: every BNT block state is a ground state.
  -- `⊆`: decompose an arbitrary ground state into canonical-form blocks and use
  -- injective-block uniqueness (`UniqueGroundState`) on each block.
  --
  -- Final assembly of these two inclusions is deferred to the forthcoming
  -- blockwise decomposition lemmas.
  sorry

end MPSTensor
