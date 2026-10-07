/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularTorusGram
import TNLean.PEPS.RegularTwistedRegion
import TNLean.PEPS.RegularRegionEntropy

/-!
# Graph contraction of actual regular torus closures

The four virtual arguments of a torus site are its top, right, down, and left
incident edges. The graph convention orients each bond toward its larger
endpoint. A horizontal seam reverses the native rightward orientation, so its
operator at the ordered head is the inverse horizontal closure element. The
vertical seam carries the vertical closure element at the ordered head.

This identifies the actual closure network with the existing graph tensor and
its physical cut; no second notion of torus state is introduced. Source:
Schuch, Cirac, and Pérez-García, arXiv:1001.3807,
`eq:2d:peps-with-ug-uh` and proof of Theorem 6.9, lines 1935–1990.

**Scope restriction (simple torus graph):** Width and height are at least three,
so the four virtual legs are distinct graph edges. Smaller periodic networks
require parallel bonds; see `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]

local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

variable {G : Type*} [Group G] {d : ℕ}

/-- A four-leg site coefficient expressed on the actual incident graph edges.
Source: SCP10, Definition 6.1 and `eq:2d:peps-with-ug-uh`. -/
def torusIncidentSite (a : G → G → G → G → Fin d → ℂ)
    (v : TorusVertex width height) (η : IncidentEdge (torusGraph width height) v → G)
    (s : Fin d) : ℂ :=
  a (η (torusTopLeg v)) (η (torusRightLeg v))
    (η (torusDownLeg v)) (η (torusLeftLeg v)) s

/-- Closure operators in the ordered-edge convention. A horizontal seam is
reversed and hence carries the inverse horizontal element at its ordered head.
Source: SCP10, `eq:2d:peps-with-ug-uh`. -/
noncomputable def torusClosureEdgeAssignment (g h : G)
    (f : Edge (torusGraph width height)) : G :=
  match torusEdgeEquiv.symm f with
  | Sum.inl v => (torusHorizontalClosureElement h v)⁻¹
  | Sum.inr v => torusVerticalClosureElement g v

/-- The horizontal edge value of the closure assignment. -/
theorem torusClosureEdgeAssignment_right (g h : G) (v : TorusVertex width height) :
    torusClosureEdgeAssignment g h (torusRightEdge v) =
      (torusHorizontalClosureElement h v)⁻¹ := by
  change (match torusEdgeEquiv.symm (torusEdgeEquiv (Sum.inl v)) with
    | Sum.inl z => (torusHorizontalClosureElement h z)⁻¹
    | Sum.inr z => torusVerticalClosureElement g z) = _
  rw [Equiv.symm_apply_apply]

/-- The vertical edge value of the closure assignment. -/
theorem torusClosureEdgeAssignment_up (g h : G) (v : TorusVertex width height) :
    torusClosureEdgeAssignment g h (torusUpEdge v) =
      torusVerticalClosureElement g v := by
  change (match torusEdgeEquiv.symm (torusEdgeEquiv (Sum.inr v)) with
    | Sum.inl z => (torusHorizontalClosureElement h z)⁻¹
    | Sum.inr z => torusVerticalClosureElement g z) = _
  rw [Equiv.symm_apply_apply]

/-- The ordered head of a horizontal seam is its native rightward origin. -/
theorem torusRightEdge_head_of_wrap (v : TorusVertex width height) (hv : v.1 + 1 = 0) :
    (torusRightEdge v).1.2 = v := by
  have hv0 : v.1 ≠ 0 := by
    intro h
    simp [h] at hv
  have hcmp : ((v.1 + 1, v.2) : TorusVertex width height) < v := by
    change toLex ((v.1 + 1).val, v.2.val) < toLex (v.1.val, v.2.val)
    rw [Prod.Lex.toLex_lt_toLex, hv, ZMod.val_zero]
    exact Or.inl (ZMod.val_pos.mpr hv0)
  rw [torusRightEdge, Edge.ofAdj_of_gt (torusGraph_adj_right v.1 v.2) hcmp]

/-- The ordered head of a vertical seam is its native upward origin. -/
theorem torusUpEdge_head_of_wrap (v : TorusVertex width height) (hv : v.2 + 1 = 0) :
    (torusUpEdge v).1.2 = v := by
  have hv0 : v.2 ≠ 0 := by
    intro h
    simp [h] at hv
  have hcmp : ((v.1, v.2 + 1) : TorusVertex width height) < v := by
    change toLex (v.1.val, (v.2 + 1).val) < toLex (v.1.val, v.2.val)
    rw [Prod.Lex.toLex_lt_toLex, hv, ZMod.val_zero]
    exact Or.inr ⟨rfl, ZMod.val_pos.mpr hv0⟩
  rw [torusUpEdge, Edge.ofAdj_of_gt (torusGraph_adj_up v.1 v.2) hcmp]

/-- Horizontal and vertical regular labels describe each actual torus edge once. -/
noncomputable def torusRegularBondConfigEquiv :
    ((TorusVertex width height → G) × (TorusVertex width height → G)) ≃
      (Edge (torusGraph width height) → G) :=
  (Equiv.sumArrowEquivProdArrow _ _ _).symm.trans
    (Equiv.arrowCongr torusEdgeEquiv (Equiv.refl G))

/-- The graph label on a horizontal seam is the native head label. This change
of variable absorbs the reversal of the horizontal seam orientation.
Source: SCP10, `eq:2d:peps-with-ug-uh`. -/
noncomputable def torusClosureBondConfigEquiv (h : G) :
    ((TorusVertex width height → G) × (TorusVertex width height → G)) ≃
      (Edge (torusGraph width height) → G) :=
  (Equiv.prodCongr
    (Equiv.piCongrRight fun v => Equiv.mulLeft (torusHorizontalClosureElement h v))
    (Equiv.refl _)).trans torusRegularBondConfigEquiv

/-- The graph label on a right edge after the seam change of variable. -/
theorem torusClosureBondConfigEquiv_right (h : G)
    (hb vb : TorusVertex width height → G) (v : TorusVertex width height) :
    torusClosureBondConfigEquiv h (hb, vb) (torusRightEdge v) =
      torusHorizontalClosureElement h v * hb v := by
  change torusClosureBondConfigEquiv h (hb, vb) (torusEdgeEquiv (Sum.inl v)) = _
  simp [torusClosureBondConfigEquiv, torusRegularBondConfigEquiv,
    Equiv.arrowCongr_apply]

/-- Vertical graph labels need no seam change of variable. -/
theorem torusClosureBondConfigEquiv_up (h : G)
    (hb vb : TorusVertex width height → G) (v : TorusVertex width height) :
    torusClosureBondConfigEquiv h (hb, vb) (torusUpEdge v) = vb v := by
  change torusClosureBondConfigEquiv h (hb, vb) (torusEdgeEquiv (Sum.inr v)) = _
  simp [torusClosureBondConfigEquiv, torusRegularBondConfigEquiv,
    Equiv.arrowCongr_apply]

/-- The top leg has the actual vertical closure label. -/
theorem torusClosureTwistedLabels_top (g h : G)
    (hb vb : TorusVertex width height → G) (v : TorusVertex width height) :
    regularTwistedLabels (torusClosureEdgeAssignment g h) v
        (fun f => torusClosureBondConfigEquiv h (hb, vb) f.1) (torusTopLeg v) =
      torusVerticalClosureElement g v * vb v := by
  simp only [regularTwistedLabels, torusTopLeg, torusClosureEdgeAssignment_up,
    torusClosureBondConfigEquiv_up]
  by_cases hv : v.2 + 1 = 0
  · simp only [torusUpEdge_head_of_wrap v hv, ite_true]
  · simp [torusVerticalClosureElement, hv]

/-- The right leg has the native horizontal tail label. -/
theorem torusClosureTwistedLabels_right (g h : G)
    (hb vb : TorusVertex width height → G) (v : TorusVertex width height) :
    regularTwistedLabels (torusClosureEdgeAssignment g h) v
        (fun f => torusClosureBondConfigEquiv h (hb, vb) f.1) (torusRightLeg v) = hb v := by
  simp only [regularTwistedLabels, torusRightLeg, torusClosureEdgeAssignment_right,
    torusClosureBondConfigEquiv_right]
  by_cases hv : v.1 + 1 = 0
  · simp [torusRightEdge_head_of_wrap v hv]
  · simp [torusHorizontalClosureElement, hv]

/-- The down leg has the native vertical tail label. -/
theorem torusClosureTwistedLabels_down (g h : G)
    (hb vb : TorusVertex width height → G) (v : TorusVertex width height) :
    regularTwistedLabels (torusClosureEdgeAssignment g h) v
        (fun f => torusClosureBondConfigEquiv h (hb, vb) f.1) (torusDownLeg v) =
      vb (v.1, v.2 - 1) := by
  simp only [regularTwistedLabels, torusDownLeg, torusDownEdge,
    torusClosureEdgeAssignment_up, torusClosureBondConfigEquiv_up]
  by_cases hv : (v.2 - 1) + 1 = 0
  · have hne : v ≠ (v.1, v.2 - 1) := by
      intro he
      exact one_ne_zero (sub_eq_self.mp (congrArg Prod.snd he).symm)
    simp only [torusUpEdge_head_of_wrap (v.1, v.2 - 1) hv, hne, ite_false]
  · have hv0 : v.2 ≠ 0 := by simpa only [sub_add_cancel] using hv
    simp [torusVerticalClosureElement, hv0]

/-- The left leg has the native horizontal head label. -/
theorem torusClosureTwistedLabels_left (g h : G)
    (hb vb : TorusVertex width height → G) (v : TorusVertex width height) :
    regularTwistedLabels (torusClosureEdgeAssignment g h) v
        (fun f => torusClosureBondConfigEquiv h (hb, vb) f.1) (torusLeftLeg v) =
      torusHorizontalClosureElement h (v.1 - 1, v.2) * hb (v.1 - 1, v.2) := by
  simp only [regularTwistedLabels, torusLeftLeg, torusLeftEdge,
    torusClosureEdgeAssignment_right, torusClosureBondConfigEquiv_right]
  by_cases hv : (v.1 - 1) + 1 = 0
  · have hne : v ≠ (v.1 - 1, v.2) := by
      intro he
      exact one_ne_zero (sub_eq_self.mp (congrArg Prod.fst he).symm)
    simp only [torusRightEdge_head_of_wrap (v.1 - 1, v.2) hv, hne, ite_false]
  · have hv0 : v.1 ≠ 0 := by simpa only [sub_add_cancel] using hv
    simp [torusHorizontalClosureElement, hv0]

variable [Fintype G] [DecidableEq G]

/-- Source: SCP10, `eq:2d:peps-with-ug-uh`. The actual regular torus closure
is the coefficient of the ordinary graph tensor with the closure operators
inserted at ordered heads. The inverse horizontal seam is accounted for by a
bijection of the summed regular labels. -/
theorem torusGClosure_eq_stateCoeff_twisted
    (a : G → G → G → G → Fin d → ℂ) (g h : G)
    (σ : TorusVertex width height → Fin d) :
    torusGClosure (leftRegularMatrix G) a g h σ =
      stateCoeff (groupBondTensor
        (regularTwistedSite (torusIncidentSite a) (torusClosureEdgeAssignment g h))) σ := by
  classical
  have hH : torusHorizontalClosure (leftRegularMatrix G) h =
      fun (v : TorusVertex width height) => Matrix.permMatrixHom (R := ℂ)
        (MulAction.toPermHom G G (torusHorizontalClosureElement h v)) := by
    funext v
    rw [torusHorizontalClosure_eq_map_element]
    rfl
  have hV : torusVerticalClosure (leftRegularMatrix G) g =
      fun (v : TorusVertex width height) => Matrix.permMatrixHom (R := ℂ)
        (MulAction.toPermHom G G (torusVerticalClosureElement g v)) := by
    funext v
    rw [torusVerticalClosure_eq_map_element]
    rfl
  unfold torusGClosure
  rw [hH, hV, torusBondNetwork_perm]
  symm
  let A : (v : TorusVertex width height) →
      (IncidentEdge (torusGraph width height) v → G) → Fin d → ℂ :=
    regularTwistedSite (torusIncidentSite a) (torusClosureEdgeAssignment g h)
  let E : (Edge (torusGraph width height) → G) ≃ VirtualConfig (groupBondTensor A) :=
    Equiv.piCongrRight fun _ => Fintype.equivFin G
  unfold stateCoeff
  rw [← Equiv.sum_comp E]
  simp only [groupBondTensor, E, Equiv.piCongrRight_apply, Pi.map_apply,
    Equiv.symm_apply_apply]
  rw [← Equiv.sum_comp (torusClosureBondConfigEquiv h), Fintype.sum_prod_type]
  apply Finset.sum_congr₂
  intro hb _ vb _
  apply Finset.prod_congr rfl
  intro v _
  simp only [regularTwistedSite, torusIncidentSite,
    torusClosureTwistedLabels_top, torusClosureTwistedLabels_right,
    torusClosureTwistedLabels_down, torusClosureTwistedLabels_left,
    torusPermutationSiteLabels, MulAction.toPermHom_apply, MulAction.toPerm_apply,
    smul_eq_mul]

/-- The physical cut coefficient of the actual native closure is the existing
cut matrix of the twisted graph tensor. Source: SCP10, the two-block partition
`eq:iso:L-shape-scenario`, lines 1935–1957. -/
theorem torusGClosure_assembleRegion_eq_regularPhysicalCutMatrix
    (a : G → G → G → G → Fin d → ℂ) (g h : G)
    (R : Finset (TorusVertex width height))
    (σ : RegionPhysicalConfig (d := d) R)
    (τ : RegionPhysicalConfig (d := d) (Finset.univ \ R)) :
    torusGClosure (leftRegularMatrix G) a g h (assembleRegionσ R σ τ) =
      regularPhysicalCutMatrix
        (regularTwistedSite (torusIncidentSite a) (torusClosureEdgeAssignment g h)) R σ τ :=
  torusGClosure_eq_stateCoeff_twisted a g h (assembleRegionσ R σ τ)

/-- Expressing an actual native closure in the two sets of physical coordinates
identifies it with the existing twisted regular physical cut state.
Source: SCP10, `eq:iso:L-shape-scenario`, lines 1935–1957. -/
theorem torusGClosure_cut_eq_regularPhysicalCutState
    (a : G → G → G → G → Fin d → ℂ) (g h : G)
    (R : Finset (TorusVertex width height)) :
    (fun p : RegionPhysicalConfig (d := d) R ×
        RegionPhysicalConfig (d := d) (Finset.univ \ R) =>
      torusGClosure (leftRegularMatrix G) a g h (assembleRegionσ R p.1 p.2)) =
      regularPhysicalCutState
        (regularTwistedSite (torusIncidentSite a) (torusClosureEdgeAssignment g h)) R := by
  funext p
  exact torusGClosure_assembleRegion_eq_regularPhysicalCutMatrix a g h R p.1 p.2

end TNLean.PEPS
