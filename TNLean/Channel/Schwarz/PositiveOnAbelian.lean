/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Schwarz.PositiveOnAbelian.Basic
import TNLean.Channel.Schwarz.PositiveOnAbelian.Characterization
import TNLean.Channel.Schwarz.PositiveOnAbelian.Consequences

/-!
# Positive maps on commuting / abelian matrix domains

Thin module collecting the positive-on-abelian Schwarz development from three
focused sub-modules.

* `TNLean.Channel.Schwarz.PositiveOnAbelian.Basic` — core block-positivity
  definitions and the diagonal-family Schwarz inequality.
* `TNLean.Channel.Schwarz.PositiveOnAbelian.Characterization` — the main block
  positivity result for positive maps on commuting families.
* `TNLean.Channel.Schwarz.PositiveOnAbelian.Consequences` — the normal-input
  Schwarz consequence used later in the project.

## Main definitions

* `BlockPositive` — quadratic-form positivity for block matrices.
* `PairwiseCommuteImages` — pairwise commutativity of block images.
* `blockQuadraticForm` — the block quadratic form after applying a linear map.
* `IsPositiveOnCommuting` — positivity on commuting block families.

## Main statements

* `diagonal_family_schwarz_le` — the diagonal / finite-spectrum Schwarz
  inequality.
* `quadraticForm_nonneg_of_isPositiveMap_of_commuting_images` — positivity on
  commuting block families for positive maps.
* `map_conjTranspose_mul_map_le_of_normal_of_subunital` — the normal-input
  Schwarz inequality for positive subunital maps.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Proposition 1.6 and
  Proposition 5.1][Wolf2012QChannels]

## Tags

positive map, commuting family, Schwarz inequality, normal operator
-/
