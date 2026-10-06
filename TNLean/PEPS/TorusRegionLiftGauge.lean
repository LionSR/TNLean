/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularTorusCut
import TNLean.PEPS.RegularRegionTreeGauge
import Mathlib.Algebra.Group.Commute.Basic

/-!
# Native torus closure gauges on integer-lifted regions

An integer lift of a region assigns a point of the square lattice to each native
torus vertex, projects to the original vertex, and preserves every internal
horizontal and vertical unit step. For commuting closure labels, its integer
deck coordinates give an explicit vertex gauge removing every internal closure
operator, including operators on the original seams.

**Scope restriction (supplied integer lift):** This is an auxiliary algebraic
consequence of a geometric lift, not a definition of a disk or a formalization of
SCP10 Theorem 6.9. Establishing such lifts from the topology of arbitrary disk
regions, and removing the sector-dependent boundary transport by operations on
the complement, remain separate steps. See
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, seam deformation
in `eq:2d:move-strings` and the disentangling proof of Theorem 6.9,
local source lines 1622–1647 and 1935–2072. Torus dimensions are at least three,
as required by the existing simple-graph realization of the native bonds.
-/

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]

local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

variable {G : Type*} [Group G]

/-- A supplied square-lattice lift of native region vertices. The conditions
are integer projection and unit-step equations, independent of any group or
closure operator. They do not assert that the region is a disk. -/
def IsTorusRegionIntegerLift (R : Finset (TorusVertex width height))
    (L : {v // v ∈ R} → ℤ × ℤ) : Prop :=
  (∀ v, (((L v).1 : ZMod width), ((L v).2 : ZMod height)) = v.1) ∧
    (∀ (v : {v // v ∈ R}) (he : (v.1.1 + 1, v.1.2) ∈ R),
      L ⟨(v.1.1 + 1, v.1.2), he⟩ = ((L v).1 + 1, (L v).2)) ∧
    (∀ (v : {v // v ∈ R}) (hn : (v.1.1, v.1.2 + 1) ∈ R),
      L ⟨(v.1.1, v.1.2 + 1), hn⟩ = ((L v).1, (L v).2 + 1))

/-- A rightward integer step changes its deck coordinate exactly at the native
periodic seam. This is the arithmetic transition used in SCP10 seam deformation,
lines 1622–1647. -/
theorem int_ediv_step_eq_add_seam_indicator {n : ℕ} [NeZero n]
    (x : ℤ) (z : ZMod n) (hx : (x : ZMod n) = z) :
    (x + 1) / (n : ℤ) = x / (n : ℤ) + if z + 1 = 0 then 1 else 0 := by
  have hn : (n : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hr : (z.val : ℤ) = x % n := by
    rw [← hx]
    exact ZMod.val_intCast x
  have hd : (x + 1) / (n : ℤ) = x / (n : ℤ) + ((z.val : ℤ) + 1) / n := by
    calc
      _ = ((z.val : ℤ) + 1 + (n : ℤ) * (x / n)) / n := by
        congr 1
        rw [hr]
        have h := Int.emod_add_mul_ediv x (n : ℤ)
        omega
      _ = _ := by rw [Int.add_mul_ediv_left _ _ hn, add_comm]
  have hz := ZMod.val_lt z
  have hc : ((z.val + 1 : ℕ) : ZMod n) = z + 1 := by simp
  by_cases hw : z + 1 = 0
  · have hdvd : n ∣ z.val + 1 := (ZMod.natCast_eq_zero_iff _ _).mp (hc.trans hw)
    have hle := Nat.le_of_dvd (Nat.succ_pos z.val) hdvd
    have hlast : z.val + 1 = n := by omega
    have hlast' : (z.val : ℤ) + 1 = n := by exact_mod_cast hlast
    rw [hd, hlast', Int.ediv_self hn, ite_eq_left hw]
  · have hlast : z.val + 1 ≠ n := by
      intro h
      apply hw
      rw [← hc, h, ZMod.natCast_self]
    have hlt : (z.val : ℤ) + 1 < n := by exact_mod_cast (by omega : z.val + 1 < n)
    rw [hd, Int.ediv_eq_zero_of_lt (by omega) hlt]
    simp [hw]

/-- The explicit closure gauge associated with a supplied integer lift. The
horizontal power is positive and the vertical power negative, in accordance
with the ordered-head native closure convention. -/
def torusRegionLiftGauge (R : Finset (TorusVertex width height))
    (L : {v // v ∈ R} → ℤ × ℤ) (g h : G) (v : {v // v ∈ R}) : G :=
  h ^ ((L v).1 / (width : ℤ)) * (g⁻¹) ^ ((L v).2 / (height : ℤ))

omit [NeZero width] [NeZero height] [Fact (2 < width)] [Fact (2 < height)] in
/-- The supplied integer projection makes the lift injective on native vertices. -/
theorem IsTorusRegionIntegerLift.injective {R : Finset (TorusVertex width height)}
    {L : {v // v ∈ R} → ℤ × ℤ} (hL : IsTorusRegionIntegerLift R L) :
    Function.Injective L := by
  intro v w hvw
  apply Subtype.ext
  rw [← hL.1 v, ← hL.1 w, hvw]

omit [NeZero height] [Fact (2 < width)] [Fact (2 < height)] in
/-- A rightward unit step increases the horizontal deck power exactly at the
native horizontal seam. -/
theorem torusRegionLiftGauge_right {R : Finset (TorusVertex width height)}
    {L : {v // v ∈ R} → ℤ × ℤ} (hL : IsTorusRegionIntegerLift R L)
    (g h : G) (v : {v // v ∈ R}) (he : (v.1.1 + 1, v.1.2) ∈ R) :
    torusRegionLiftGauge R L g h ⟨(v.1.1 + 1, v.1.2), he⟩ =
      torusHorizontalClosureElement h v.1 * torusRegionLiftGauge R L g h v := by
  have hx := congrArg Prod.fst (hL.1 v)
  have hd := int_ediv_step_eq_add_seam_indicator (L v).1 v.1.1 hx
  simp only [torusRegionLiftGauge, hL.2.1 v he, hd,
    torusHorizontalClosureElement]
  split_ifs with hw
  · rw [add_comm _ (1 : ℤ), zpow_one_add]
    exact mul_assoc _ _ _
  · simp

omit [NeZero width] [Fact (2 < width)] [Fact (2 < height)] in
/-- An upward unit step increases the negative vertical deck power exactly at
the native vertical seam. Commutativity permits the vertical power to pass the
horizontal power. -/
theorem torusRegionLiftGauge_up {R : Finset (TorusVertex width height)}
    {L : {v // v ∈ R} → ℤ × ℤ} (hL : IsTorusRegionIntegerLift R L)
    (g h : G) (hgh : Commute g h) (v : {v // v ∈ R})
    (hn : (v.1.1, v.1.2 + 1) ∈ R) :
    torusRegionLiftGauge R L g h ⟨(v.1.1, v.1.2 + 1), hn⟩ =
      (torusVerticalClosureElement g v.1)⁻¹ * torusRegionLiftGauge R L g h v := by
  have hy := congrArg Prod.snd (hL.1 v)
  have hd := int_ediv_step_eq_add_seam_indicator (L v).2 v.1.2 hy
  simp only [torusRegionLiftGauge, hL.2.2 v hn, hd,
    torusVerticalClosureElement]
  split_ifs with hw
  · rw [add_comm _ (1 : ℤ), zpow_one_add, ← mul_assoc,
      ← (hgh.inv_left.zpow_right ((L v).1 / (width : ℤ))).eq, mul_assoc]
  · simp

/-- The lift gauge has exactly the native closure operator as its gradient on
every internal edge. No condition on cycles or group-valued flatness is assumed;
the conclusion follows from the supplied integer unit-step equations. -/
theorem torusRegionLiftGauge_gradient {R : Finset (TorusVertex width height)}
    {L : {v // v ∈ R} → ℤ × ℤ} (hL : IsTorusRegionIntegerLift R L)
    (g h : G) (hgh : Commute g h)
    (e : {e : Edge (torusGraph width height) // e.1.1 ∈ R ∧ e.1.2 ∈ R}) :
    torusRegionLiftGauge R L g h ⟨e.1.1.2, e.2.2⟩ *
      (torusRegionLiftGauge R L g h ⟨e.1.1.1, e.2.1⟩)⁻¹ =
        torusClosureEdgeAssignment g h e.1 := by
  rcases e with ⟨e, he⟩
  obtain ⟨p, rfl⟩ := torusEdgeEquiv.surjective e
  rcases p with v | v
  · change (torusRightEdge v).1.1 ∈ R ∧ (torusRightEdge v).1.2 ∈ R at he
    change torusRegionLiftGauge R L g h ⟨(torusRightEdge v).1.2, he.2⟩ *
      (torusRegionLiftGauge R L g h ⟨(torusRightEdge v).1.1, he.1⟩)⁻¹ =
        torusClosureEdgeAssignment g h (torusRightEdge v)
    rw [torusClosureEdgeAssignment_right]
    rcases Edge.ofAdj_endpoints (torusGraph_adj_right v.1 v.2) with ⟨ht, hh⟩ | ⟨ht, hh⟩
    · change (torusRightEdge v).1.1 = v at ht
      change (torusRightEdge v).1.2 = (v.1 + 1, v.2) at hh
      have hv : v ∈ R := ht ▸ he.1
      have hn : (v.1 + 1, v.2) ∈ R := hh ▸ he.2
      have hs := torusRegionLiftGauge_right hL g h ⟨v, hv⟩ hn
      by_cases hw : v.1 + 1 = 0
      · have hc := torusRightEdge_head_of_wrap v hw
        exact False.elim ((torusGraph_adj_right v.1 v.2).ne (hh.symm.trans hc).symm)
      · simp only [ht, hh]
        rw [hs]
        simp [torusHorizontalClosureElement, hw]
    · change (torusRightEdge v).1.1 = (v.1 + 1, v.2) at ht
      change (torusRightEdge v).1.2 = v at hh
      have hv : v ∈ R := hh ▸ he.2
      have hn : (v.1 + 1, v.2) ∈ R := ht ▸ he.1
      have hs := torusRegionLiftGauge_right hL g h ⟨v, hv⟩ hn
      simp only [ht, hh]
      rw [hs]
      group
  · change (torusUpEdge v).1.1 ∈ R ∧ (torusUpEdge v).1.2 ∈ R at he
    change torusRegionLiftGauge R L g h ⟨(torusUpEdge v).1.2, he.2⟩ *
      (torusRegionLiftGauge R L g h ⟨(torusUpEdge v).1.1, he.1⟩)⁻¹ =
        torusClosureEdgeAssignment g h (torusUpEdge v)
    rw [torusClosureEdgeAssignment_up]
    rcases Edge.ofAdj_endpoints (torusGraph_adj_up v.1 v.2) with ⟨ht, hh⟩ | ⟨ht, hh⟩
    · change (torusUpEdge v).1.1 = v at ht
      change (torusUpEdge v).1.2 = (v.1, v.2 + 1) at hh
      have hv : v ∈ R := ht ▸ he.1
      have hn : (v.1, v.2 + 1) ∈ R := hh ▸ he.2
      have hs := torusRegionLiftGauge_up hL g h hgh ⟨v, hv⟩ hn
      by_cases hw : v.2 + 1 = 0
      · have hc := torusUpEdge_head_of_wrap v hw
        exact False.elim ((torusGraph_adj_up v.1 v.2).ne (hh.symm.trans hc).symm)
      · simp only [ht, hh]
        rw [hs]
        simp [torusVerticalClosureElement, hw]
    · change (torusUpEdge v).1.1 = (v.1, v.2 + 1) at ht
      change (torusUpEdge v).1.2 = v at hh
      have hv : v ∈ R := hh ▸ he.2
      have hn : (v.1, v.2 + 1) ∈ R := ht ▸ he.1
      have hs := torusRegionLiftGauge_up hL g h hgh ⟨v, hv⟩ hn
      simp only [ht, hh]
      rw [hs]
      group

/-- All internal native closure residuals vanish for the explicit lift gauge. -/
theorem regularRegionGaugeResidual_torusRegionLiftGauge {R : Finset (TorusVertex width height)}
    {L : {v // v ∈ R} → ℤ × ℤ} (hL : IsTorusRegionIntegerLift R L)
    (g h : G) (hgh : Commute g h)
    (e : {e : Edge (torusGraph width height) // e.1.1 ∈ R ∧ e.1.2 ∈ R}) :
    regularRegionGaugeResidual R (torusRegionLiftGauge R L g h)
      (torusClosureEdgeAssignment g h) e = 1 := by
  unfold regularRegionGaugeResidual
  rw [← torusRegionLiftGauge_gradient hL g h hgh e]
  group

/-- Right normalization at a root preserves every native edge gradient. -/
def torusRegionLiftRootGauge (R : Finset (TorusVertex width height))
    (L : {v // v ∈ R} → ℤ × ℤ) (g h : G) (o : {v // v ∈ R}) :
    RootedGroupLabels (G := G) o :=
  ⟨fun v => torusRegionLiftGauge R L g h v * (torusRegionLiftGauge R L g h o)⁻¹,
    by simp⟩

/-- Root normalization does not change the native closure gradient. -/
theorem torusRegionLiftRootGauge_gradient {R : Finset (TorusVertex width height)}
    {L : {v // v ∈ R} → ℤ × ℤ} (hL : IsTorusRegionIntegerLift R L)
    (g h : G) (hgh : Commute g h) (o : {v // v ∈ R})
    (e : {e : Edge (torusGraph width height) // e.1.1 ∈ R ∧ e.1.2 ∈ R}) :
    (torusRegionLiftRootGauge R L g h o).1 ⟨e.1.1.2, e.2.2⟩ *
      ((torusRegionLiftRootGauge R L g h o).1 ⟨e.1.1.1, e.2.1⟩)⁻¹ =
        torusClosureEdgeAssignment g h e.1 := by
  change (_ * _) * (_ * _)⁻¹ = _
  calc
    _ = torusRegionLiftGauge R L g h ⟨e.1.1.2, e.2.2⟩ *
        (torusRegionLiftGauge R L g h ⟨e.1.1.1, e.2.1⟩)⁻¹ := by group
    _ = _ := torusRegionLiftGauge_gradient hL g h hgh e

/-- On any spanning tree the native normalized tree gauge equals the explicit
normalized integer-lift gauge. Hence the result applies to the gauge used in
the actual spanning-tree contraction formula. -/
theorem regularRegionTreeGauge_eq_torusRegionLiftRootGauge [Fintype G]
    {R : Finset (TorusVertex width height)} {L : {v // v ∈ R} → ℤ × ℤ}
    (hL : IsTorusRegionIntegerLift R L)
    (T : SimpleGraph {v : TorusVertex width height // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ (torusGraph width height).induce (R : Set (TorusVertex width height)))
    (htree : T.IsTree) (o : {v // v ∈ R}) (g h : G) (hgh : Commute g h) :
    regularRegionTreeGauge R T hT htree o (torusClosureEdgeAssignment g h) =
      torusRegionLiftRootGauge R L g h o := by
  apply (rootedTreeGradientEquiv T htree o).injective
  funext f
  change (regularRegionTreeGauge R T hT htree o (torusClosureEdgeAssignment g h)).1 f.1.2 *
      ((regularRegionTreeGauge R T hT htree o (torusClosureEdgeAssignment g h)).1 f.1.1)⁻¹ =
    (torusRegionLiftRootGauge R L g h o).1 f.1.2 *
      ((torusRegionLiftRootGauge R L g h o).1 f.1.1)⁻¹
  let e : {e : Edge (torusGraph width height) // e.1.1 ∈ R ∧ e.1.2 ∈ R} :=
    ⟨⟨(f.1.1.1, f.1.2.1), f.2.1, hT f.2.2⟩, f.1.1.2, f.1.2.2⟩
  exact (regularRegionTreeGauge_gradient R T hT htree o
    (torusClosureEdgeAssignment g h) e f.2.2).trans
      (torusRegionLiftRootGauge_gradient hL g h hgh o e).symm

/-- Every cycle residual in the actual native spanning-tree coordinates is the
identity for commuting closures on a supplied integer-lifted region. -/
theorem regularRegionTreeCycleResidual_torusClosure_eq_one [Fintype G]
    {R : Finset (TorusVertex width height)} {L : {v // v ∈ R} → ℤ × ℤ}
    (hL : IsTorusRegionIntegerLift R L)
    (T : SimpleGraph {v : TorusVertex width height // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ (torusGraph width height).induce (R : Set (TorusVertex width height)))
    (htree : T.IsTree) (o : {v // v ∈ R}) (g h : G) (hgh : Commute g h)
    (e : {e : {e : Edge (torusGraph width height) // e.1.1 ∈ R ∧ e.1.2 ∈ R} //
      ¬ T.Adj ⟨e.1.1.1, e.2.1⟩ ⟨e.1.1.2, e.2.2⟩}) :
    regularRegionTreeCycleResidual R T hT htree o (torusClosureEdgeAssignment g h) e = 1 := by
  unfold regularRegionTreeCycleResidual
  rw [regularRegionTreeGauge_eq_torusRegionLiftRootGauge hL T hT htree o g h hgh]
  unfold regularRegionGaugeResidual
  rw [← torusRegionLiftRootGauge_gradient hL g h hgh o e.1]
  group

end TNLean.PEPS
