/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Tensor.Torus.TorusSiteTensor
import Mathlib.Data.Fin.VecNotation

/-!
# Coordinates on the four native torus bonds

The top, right, down and left bonds determine every incident-edge label on
an actual square torus. This geometry is shared by regular-tensor entropy
and the constrained boundary of the CZX example.

**Scope restriction (simple torus graph):** both periods are at least three,
so the four native bonds are distinct; see
`docs/paper-gaps/rmp_peps_examples_small_torus.tex`.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807), Definition 6.1.
-/

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The four native virtual labels of a site, in top, right, down, left order. -/
def torusIncidentCoordinates (v : TorusVertex width height)
    (η : IncidentEdge (torusGraph width height) v → G) : G × G × G × G :=
  (η (torusTopLeg v), η (torusRightLeg v), η (torusDownLeg v), η (torusLeftLeg v))

omit [Group G] [Fintype G] [DecidableEq G] in
/-- The four native coordinates determine every incident-edge label. -/
theorem torusIncidentCoordinates_injective (v : TorusVertex width height) :
    Function.Injective (torusIncidentCoordinates (G := G) v) := by
  intro η θ h
  have ht := congrArg (fun p : G × G × G × G => p.1) h
  have hr := congrArg (fun p : G × G × G × G => p.2.1) h
  have hb := congrArg (fun p : G × G × G × G => p.2.2.1) h
  have hl := congrArg (fun p : G × G × G × G => p.2.2.2) h
  funext f
  obtain ⟨i, rfl⟩ := torusIncidentLeg_surjective v f
  fin_cases i
  · exact ht
  · exact hr
  · exact hb
  · exact hl

end TNLean.PEPS
