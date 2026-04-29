/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Determinant.Basic
import TNLean.Channel.Determinant.Bound
import TNLean.Channel.Determinant.HilbertSchmidt
import TNLean.Channel.Determinant.HeisenbergDual
import TNLean.Channel.Determinant.UnitaryCharacterization

/-!
# Determinants of quantum channels

Thin module assembling the determinant development for quantum channels from
five focused sub-modules.

The split follows the same review-oriented pattern as the earlier `Full/` and
`Growth/` refactors:

* `TNLean.Channel.Determinant.Basic` — determinant definitions and unitary
  channels.
* `TNLean.Channel.Determinant.Bound` — Wolf Theorem 6.1(1), the determinant
  bound for positive trace-preserving maps.
* `TNLean.Channel.Determinant.HilbertSchmidt` — spectral and Hilbert--Schmidt
  auxiliary lemmas for the rigidity argument.
* `TNLean.Channel.Determinant.HeisenbergDual` — Heisenberg-dual
  multiplicativity from determinant saturation.
* `TNLean.Channel.Determinant.UnitaryCharacterization` — Wolf Theorem 6.1(2)
  for CPTP maps.

## Main definitions

* `channelMatrix` — the matrix representation of a channel.
* `channelDet` — the determinant of that matrix representation.
* `unitaryChannel` — conjugation by a unitary matrix.

## Main statements

* `channelDet_eq_linearMap_det` — `channelDet` agrees with `LinearMap.det`.
* `channelDet_norm_le_one_of_positive_tracePreserving` — Wolf Theorem 6.1(1).
* `channelDet_norm_eq_one_iff_exists_unitaryChannel` — Wolf Theorem 6.1(2)
  for CPTP maps.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, §6.1.1][Wolf2012QChannels]

## Tags

quantum channel, determinant, unitary channel, Wolf theorem
-/
