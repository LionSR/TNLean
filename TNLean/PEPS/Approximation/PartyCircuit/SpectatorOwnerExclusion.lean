/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Circuit.Party.Syntax.CoarsenLocal

/-!
# Spectators at an excluded owner

A source-free composition read on blocks whose parties all lie outside a fixed
block acts on that block as the scalar identity: its basis has one element and
every entry of the party operation is one. Running the composition beside
spectator registers therefore leaves the spectators of the block unchanged. These
spectators need not be empty, and their spaces are arbitrary.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 233–267, 351–381, 409–434 and 565–588.
-/

noncomputable section

open Matrix ManyBody
open scoped Kronecker

namespace QuantumCircuit.Party.Word

/-- A block outside the range of the owner map retains only its spectator
registers, on which the source-free composition read on blocks is the identity. The
source-free composition and the spectator registers may be arbitrary.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 233–267,
351–381, 409–434 and 565–588. -/
theorem partyOp_frame_coarsen_apply_of_forall_ne {C P : Type} [Fintype C] [DecidableEq C]
    [DecidableEq P] (owner : C → P) (p : P) {X Y : C → Type} [∀ c, Fintype (X c)]
    [∀ c, DecidableEq (X c)] (u : Word X Y) (hs : u.sources = []) (howner : ∀ c, owner c ≠ p)
    (W : P → Type) [∀ q, Fintype (W q)] [∀ q, DecidableEq (W q)]
    (a b : W p) (y : blockSystem owner Y p) (x : blockSystem owner X p) :
    ((u.coarsen owner).frame W).partyOp p (a, y) (b, x) = (1 : Matrix (W p) (W p) ℂ) a b := by
  rw [PartyCircuit.partyOp_frame, kroneckerMap_apply,
    partyOp_coarsen_apply_of_forall_ne owner u ((isLocal_iff_sources_eq_nil u).mpr hs) howner,
    mul_one]

end QuantumCircuit.Party.Word
