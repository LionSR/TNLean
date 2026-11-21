/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.AreaLawTheorem
import TNLean.PEPS.AreaLaw.FrustrationFree.Model

/-!
# The frustration-free area law from the general theorem

The goal `eq:goal` of the frustration-free area-law note holds as a special case of Theorem 1.1,
`uniformAreaLaw`. This checks the statement `FrustrationFreeAreaLaw` against the general
theorem. Its proof passes through the time-filtered constraints of the general route; the
shorter route of the note is assembled separately in this directory.

## Main statements

* `TNLean.PEPS.AreaLaw.FrustrationFree.frustrationFreeAreaLaw_of_uniformAreaLaw`.

## References

* Reading note *Entanglement across a cut in two-dimensional frustration-free ground states*,
  November 18, 2026, `docs/audits/2026-11-18_finite_range_frustration_free_area_law.tex`,
  `eq:goal`: "This is the frustration-free specialization of Theorem 1.1".
-/

namespace TNLean.PEPS.AreaLaw.FrustrationFree

/-- **The frustration-free area law, as a special case of Theorem 1.1** (`eq:goal` of the
frustration-free area-law note). -/
theorem frustrationFreeAreaLaw_of_uniformAreaLaw : FrustrationFreeAreaLaw :=
  uniformAreaLaw.frustrationFreeAreaLaw

end TNLean.PEPS.AreaLaw.FrustrationFree
