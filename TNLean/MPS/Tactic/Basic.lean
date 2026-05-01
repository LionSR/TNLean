/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic

/-!
# Tactics for tensor-network proofs

This file provides small custom `simp` attribute sets and thin tactic wrappers
for recurring proof patterns in MPS / channel / overlap files.

## Custom simp attributes

* `mps_block_words` : direct/iterated blocking maps, `wordOfBlock` expressions
* `mps_transfer` : transfer map unfoldings, basic trace/scalar identities
* `mps_zero_tail` : zero-tail MPV terms

## Tactic wrappers

* `mpv_ext` : introduce `N`, `σ` for `SameMPV₂` or `N`, `hN`, `σ` for `SameMPV₂Pos`
* `block_words` : normalize direct/iterated blocking maps and `wordOfBlock` expressions
* `transfer_simp` : unfold transfer maps and simplify trace/scalar side conditions
* `zero_tail_simp` : simplify zero-tail MPV terms after the length case is chosen

## Design

The tactics are intentionally simple. They do not search; when the normal form does
not apply, they leave clear unsolved goals. The `simp` attribute sets are the primary
mechanism; the tactic wrappers are thin sugar over the attributes.
-/

/-! ### Custom simp attribute sets -/

/-- Simp set for direct/iterated blocking maps and `wordOfBlock` normal forms. -/
register_simp_attr mps_block_words

/-- Simp set for transfer map unfoldings and trace/scalar identities. -/
register_simp_attr mps_transfer

/-- Simp set for zero-tail MPV term simplification. -/
register_simp_attr mps_zero_tail

/-! ### Tactic wrappers -/

/--
Introduce MPV length and word variables for `SameMPV₂` or `SameMPV₂Pos` goals.

For `SameMPV₂ A B` (i.e. `∀ N σ, mpv A σ = mpv B σ`), `mpv_ext` reduces the goal to
`mpv A σ = mpv B σ` by introducing `N` and `σ` as fresh variables.

For `SameMPV₂Pos A B` (i.e. `∀ N, 0 < N → ∀ σ, mpv A σ = mpv B σ`), `mpv_ext` also
introduces a name for the positivity hypothesis.

If the goal does not match either pattern, `mpv_ext` does nothing.
-/
macro "mpv_ext" : tactic => `(tactic|
  first
    | intro N hN σ
    | intro N σ
    | skip
)

/--
Normalize direct/iterated blocking maps and `wordOfBlock` expressions.

Uses the lemmas tagged with `@[mps_block_words]`.  After `block_words`:
* `directIteratedBlockEquiv d m n i` is rewritten to `directToIteratedBlockIndex d m n i`
* iterated-blocking dimension identities are unfolded
* word-of-block normal forms are applied
* grouped index equalities are reduced to flattened-index equalities

The tactic does not rewrite general matrix multiplication or common MPS tensor identities;
it only normalises the block-word presentation.
-/
macro "block_words" : tactic => `(tactic| simp [mps_block_words])

/--
Unfold transfer maps and simplify trace/scalar side conditions.

Uses the lemmas tagged with `@[mps_transfer]`.  After `transfer_simp`:
* `transferMap A X` is unfolded to `∑ i, A i * X * (A i)ᴴ`
* basic `Multiplicative.ofAdd` conversions (if any) are resolved

The tactic avoids broad `simp` over matrix multiplication, since that tends to
make goals harder to read.
-/
macro "transfer_simp" : tactic => `(tactic| simp [mps_transfer])

/--
Simplify zero-tail MPV terms.

Uses the lemmas tagged with `@[mps_zero_tail]`.  After `zero_tail_simp`:
* at positive length `N > 0`, `mpv (zeroMPSTensor d D) σ` simplifies to `0`
* at length zero `N = 0`, `mpv (zeroMPSTensor d D) σ` simplifies to `(D : ℂ)`

Call `zero_tail_simp` only after fixing the length case.
-/
macro "zero_tail_simp" : tactic => `(tactic| simp [mps_zero_tail])
