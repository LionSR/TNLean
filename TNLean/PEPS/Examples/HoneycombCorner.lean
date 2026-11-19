/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Examples.GraphStateCutConverse

/-! Two distinct outgoing bonds at one site obstruct graph-state region injectivity. -/

namespace TNLean.PEPS.HoneycombCorner
open ManyBody (Edge)
variable {V : Type*} [LinearOrder V] {G : SimpleGraph V} {R : Finset V}

private def edge {v w : V} (h : G.Adj v w) : Edge G :=
  if hv : v < w then ⟨(v,w),hv,h⟩
  else ⟨(w,v),lt_of_le_of_ne (le_of_not_gt hv) h.ne.symm,h.symm⟩

private def cross {v w : V} (hv : v ∈ R) (hw : w ∉ R) (h : G.Adj v w) :
    GraphStateCut.Crossing G R :=
  ⟨edge h, by unfold edge; split
              · exact Or.inl ⟨hv,hw⟩
              · exact Or.inr ⟨hw,hv⟩⟩

private theorem read {v w : V} (hv : v ∈ R) (hw : w ∉ R) (h : G.Adj v w) :
    (GraphStateCut.inside G R (cross hv hw h)).1 = v := by
  simp [GraphStateCut.inside,cross,edge]
  split <;> simp_all

theorem obstruction [Fintype V] [DecidableRel G.Adj] {v w z : V}
    (hv : v ∈ R) (hw : w ∉ R) (hz : z ∉ R) (hne : w ≠ z)
    (a : G.Adj v w) (b : G.Adj v z) :
    ¬ Function.Injective (openRegionMap (graphStatePEPS G) R) := by
  intro inj
  have eq := (GraphStateCut.injective_iff G R).1 inj
    (Subtype.ext ((read hv hw a).trans (read hv hz b).symm))
  have p : (edge a).1 = (edge b).1 := congrArg (fun e : GraphStateCut.Crossing G R => e.1.1) eq
  unfold edge at p
  split at p <;> split at p <;> simp_all

theorem horizontal_corner {W H : ℕ} [NeZero W] [NeZero H] [Fact (1 < W)] [Fact (1 < H)]
    (R : Finset (TorusVertex W H)) (v : TorusVertex W H) (hv : v ∈ R)
    (hl : (v.1 - 1,v.2) ∉ R) (hr : (v.1 + 1,v.2) ∉ R) (hd : v.1 - 1 ≠ v.1 + 1) :
    ¬ Function.Injective (openRegionMap (honeycombClusterPEPS W H) R) := by
  apply obstruction hv hl hr (fun eq => hd (congrArg Prod.fst eq))
  · exact Or.inl ⟨rfl, Or.inr (by simp)⟩
  · exact Or.inl ⟨rfl, Or.inl rfl⟩

end TNLean.PEPS.HoneycombCorner
