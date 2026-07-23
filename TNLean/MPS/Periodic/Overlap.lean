/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.Overlap.SelfOverlap
import TNLean.MPS.Periodic.Overlap.SelfOverlapNonrep
import TNLean.MPS.Periodic.Overlap.DifferentPeriod
import TNLean.MPS.Periodic.Overlap.NoSectorMatch
import TNLean.MPS.Periodic.Overlap.SectorMatch
import TNLean.MPS.Periodic.Overlap.Dichotomy

/-!
# Periodic overlap dichotomy

This module keeps the historical import path `TNLean.MPS.Periodic.Overlap`
while the periodic-overlap development is split by Appendix-A case boundaries.

The supporting modules are:

* `TNLean.MPS.Periodic.Overlap.SelfOverlap` — cyclic-sector setup and
  self-overlap.
* `TNLean.MPS.Periodic.Overlap.SelfOverlapNonrep` — the spectral
  non-repetition crux (off-diagonal vanishing).
* `TNLean.MPS.Periodic.Overlap.DifferentPeriod` — different periods imply orthogonality.
* `TNLean.MPS.Periodic.Overlap.NoSectorMatch` — equal period with no sector match
  implies orthogonality.
* `TNLean.MPS.Periodic.Overlap.SectorMatch` — equal period with a sector match yields
  repeated blocks.
* `TNLean.MPS.Periodic.Overlap.Dichotomy` — the source proposition
  `equal-or-orthogonal-generalized` and eventual linear independence.

## References

* De las Cuevas, Cirac, Schuch, Perez-Garcia,
  *Irreducible forms of Matrix Product States: Theory and Applications*,
  arXiv:1708.00029, proposition `equal-or-orthogonal-generalized`
  and Appendix A.
-/
