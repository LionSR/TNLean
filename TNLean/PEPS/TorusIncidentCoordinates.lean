/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusSiteTensor
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

private theorem torusIncidentEdge_eq_leg (v : TorusVertex width height)
    (f : IncidentEdge (torusGraph width height) v) :
    f = torusTopLeg v ∨ f = torusRightLeg v ∨ f = torusDownLeg v ∨ f = torusLeftLeg v := by
  obtain ⟨z, hz⟩ := torusEdgeEquiv.surjective f.1
  rcases z with p | p
  · change torusRightEdge p = f.1 at hz
    have hi := f.2
    rw [← hz] at hi
    have hep := Edge.ofAdj_endpoints (torusGraph_adj_right p.1 p.2)
    have hp : p = v ∨ (p.1 + 1, p.2) = v := by
      rcases hep with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hi with hi | hi
      · exact Or.inl (h1.symm.trans hi)
      · exact Or.inr (h2.symm.trans hi)
      · exact Or.inr (h1.symm.trans hi)
      · exact Or.inl (h2.symm.trans hi)
    rcases hp with rfl | hp
    · exact Or.inr (Or.inl (Subtype.ext hz.symm))
    · have hp' : p = (v.1 - 1, v.2) := by
        have hx := congrArg Prod.fst hp
        have hy := congrArg Prod.snd hp
        exact Prod.ext ((eq_sub_iff_add_eq).mpr hx) hy
      exact Or.inr (Or.inr (Or.inr (Subtype.ext (by rw [← hz, hp']; rfl))))
  · change torusUpEdge p = f.1 at hz
    have hi := f.2
    rw [← hz] at hi
    have hep := Edge.ofAdj_endpoints (torusGraph_adj_up p.1 p.2)
    have hp : p = v ∨ (p.1, p.2 + 1) = v := by
      rcases hep with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hi with hi | hi
      · exact Or.inl (h1.symm.trans hi)
      · exact Or.inr (h2.symm.trans hi)
      · exact Or.inr (h1.symm.trans hi)
      · exact Or.inl (h2.symm.trans hi)
    rcases hp with rfl | hp
    · exact Or.inl (Subtype.ext hz.symm)
    · have hp' : p = (v.1, v.2 - 1) := by
        have hx := congrArg Prod.fst hp
        have hy := congrArg Prod.snd hp
        exact Prod.ext hx ((eq_sub_iff_add_eq).mpr hy)
      exact Or.inr (Or.inr (Or.inl (Subtype.ext (by rw [← hz, hp']; rfl))))

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
  rcases torusIncidentEdge_eq_leg v f with rfl | rfl | rfl | rfl
  · exact ht
  · exact hr
  · exact hb
  · exact hl

/-- The four native legs enumerate the incident edges of a vertex.
Source: SCP10, square-lattice virtual legs in Definition 6.1. -/
def torusIncidentLeg (v : TorusVertex width height) :
    Fin 4 → IncidentEdge (torusGraph width height) v :=
  ![torusTopLeg v, torusRightLeg v, torusDownLeg v, torusLeftLeg v]

/-- No incident torus edge is omitted by the four native legs.
Source: SCP10, square-lattice construction at lines 1935–1990. -/
theorem torusIncidentLeg_surjective (v : TorusVertex width height) :
    Function.Surjective (torusIncidentLeg v) := by
  apply (Function.injective_comp_right_iff_surjective (γ := Bool)).mp
  intro η θ h
  apply torusIncidentCoordinates_injective (G := Bool) v
  have h0 := congrFun h (0 : Fin 4)
  have h1 := congrFun h (1 : Fin 4)
  have h2 := congrFun h (2 : Fin 4)
  have h3 := congrFun h (3 : Fin 4)
  exact Prod.ext h0 (Prod.ext h1 (Prod.ext h2 h3))

/-- The four native virtual legs are distinct when both periods are at least
three. Source: SCP10, square-lattice construction at lines 1935–1990. -/
theorem torusIncidentLeg_injective (v : TorusVertex width height) :
    Function.Injective (torusIncidentLeg v) := by
  have htr : torusTopLeg v ≠ torusRightLeg v := by
    intro h
    exact torusRightEdge_ne_torusUpEdge v v (congrArg Subtype.val h).symm
  have htl : torusTopLeg v ≠ torusLeftLeg v := by
    intro h
    exact torusRightEdge_ne_torusUpEdge (v.1 - 1, v.2) v (congrArg Subtype.val h).symm
  have hrd : torusRightLeg v ≠ torusDownLeg v := by
    intro h
    exact torusRightEdge_ne_torusUpEdge v (v.1, v.2 - 1) (congrArg Subtype.val h)
  have hdl : torusDownLeg v ≠ torusLeftLeg v := by
    intro h
    exact torusRightEdge_ne_torusUpEdge (v.1 - 1, v.2) (v.1, v.2 - 1)
      (congrArg Subtype.val h).symm
  have htd : torusTopLeg v ≠ torusDownLeg v := by
    intro h
    have hy := congrArg Prod.snd (torusUpEdge_injective (congrArg Subtype.val h))
    exact one_ne_zero (α := ZMod height)
      (add_left_cancel (by simpa only [add_zero] using eq_sub_iff_add_eq.mp hy))
  have hrl : torusRightLeg v ≠ torusLeftLeg v := by
    intro h
    have hx := congrArg Prod.fst (torusRightEdge_injective (congrArg Subtype.val h))
    exact one_ne_zero (α := ZMod width)
      (add_left_cancel (by simpa only [add_zero] using eq_sub_iff_add_eq.mp hx))
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [torusIncidentLeg]

/-- Numbering the four actual incident bonds in top, right, down, left order.
Source: SCP10, square-lattice virtual legs in Definition 6.1. -/
noncomputable def torusIncidentLegEquiv (v : TorusVertex width height) :
    Fin 4 ≃ IncidentEdge (torusGraph width height) v :=
  Equiv.ofBijective (torusIncidentLeg v)
    ⟨torusIncidentLeg_injective v, torusIncidentLeg_surjective v⟩

end TNLean.PEPS
