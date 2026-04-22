/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Periodic.Overlap.SelfOverlap
import TNLean.MPS.Periodic.Overlap.Case1
import TNLean.MPS.Periodic.Overlap.Case2
import TNLean.MPS.Periodic.Overlap.Case3
import TNLean.MPS.Periodic.Overlap.Dichotomy

/-!
# Periodic overlap dichotomy

This module keeps the historical import path `TNLean.MPS.Periodic.Overlap`
while the periodic-overlap development is split by Appendix-A case boundaries.

The supporting modules are:

* `TNLean.MPS.Periodic.Overlap.SelfOverlap` — cyclic-sector setup and
  self-overlap.
* `TNLean.MPS.Periodic.Overlap.Case1` — different periods imply orthogonality.
* `TNLean.MPS.Periodic.Overlap.Case2` — equal period with no sector match
  implies orthogonality.
* `TNLean.MPS.Periodic.Overlap.Case3` — equal period with a sector match yields
  repeated blocks.
* `TNLean.MPS.Periodic.Overlap.Dichotomy` — Proposition 3.3 and eventual
  linear independence.

## References

* De las Cuevas, Cirac, Schuch, Perez-Garcia,
  *Irreducible forms of Matrix Product States: Theory and Applications*,
  arXiv:1708.00029, Proposition 3.3 and Appendix A.
-/
