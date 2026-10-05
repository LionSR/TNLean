/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusParallelSection
import TNLean.PEPS.RegularWalkHolonomy
import TNLean.PEPS.RegularTorusCut

/-!
# Reduction of a flat torus connection to two commuting seams

A flat group-valued connection on a discrete torus can be gauged to the identity
away from one horizontal and one vertical seam. The two seam holonomies commute;
no trivial-holonomy hypothesis is imposed.

This is the group-valued form of the closure-string deformation in
Schuch, Cirac, and Pérez-García, arXiv:1001.3807, `eq:2d:move-strings`.
-/

namespace TNLean.PEPS

variable {G : Type*} [Group G]

/-- Cutting a cycle at zero leaves its full holonomy on the wrapping edge. -/
theorem zmodTransport_step {n : ℕ} [NeZero n] (c : ZMod n → G) (x : ZMod n) :
    c x * zmodTransport c x.val =
      zmodTransport c (x + 1).val * if x + 1 = 0 then zmodTransport c n else 1 := by
  obtain ⟨k, hk, rfl⟩ : ∃ k < n, (k : ZMod n) = x :=
    ⟨x.val, x.val_lt, ZMod.natCast_zmod_val x⟩
  rw [ZMod.val_natCast_of_lt hk, ← zmodTransport_succ, ← Nat.cast_succ]
  rcases Nat.lt_or_ge (k + 1) n with h | h
  · have hn : ((k + 1 : ℕ) : ZMod n) ≠ 0 := by
      intro hz
      have := congrArg ZMod.val hz
      rw [ZMod.val_natCast_of_lt h, ZMod.val_zero] at this
      omega
    rw [ite_eq_right hn, ZMod.val_natCast_of_lt h, mul_one]
  · have hkn : k + 1 = n := le_antisymm hk h
    simp only [Nat.succ_eq_add_one, hkn, ZMod.natCast_self, ZMod.val_zero,
      zmodTransport_zero, ite_true, one_mul]

variable {width height : ℕ}
variable {a b : TorusVertex width height → G}

/-- Flatness identifies the transports along the two sides of any rectangle. -/
theorem IsTorusFlat.zmodTransport_rectangle (hab : IsTorusFlat a b) (m n : ℕ) :
    zmodTransport (fun y => b ((m : ZMod width), y)) n *
        zmodTransport (fun x => a (x, 0)) m =
      zmodTransport (fun x => a (x, (n : ZMod height))) m *
        zmodTransport (fun y => b (0, y)) n := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [zmodTransport_succ, zmodTransport_succ, Nat.cast_succ, ← mul_assoc,
      hab.zmodTransport_column_mul, mul_assoc, ih, ← mul_assoc]

/-- The two based holonomies of a flat torus connection commute. -/
theorem IsTorusFlat.commute_holonomies (hab : IsTorusFlat a b) :
    Commute (zmodTransport (fun x => a (x, 0)) width)
      (zmodTransport (fun y => b (0, y)) height) := by
  have h := hab.zmodTransport_rectangle width height
  change _ * _ = _ * _
  simpa only [ZMod.natCast_self] using h.symm

variable [NeZero width] [NeZero height]

/-- Transport from the origin first along the bottom row, then up the column. -/
def torusTreeGauge (a b : TorusVertex width height → G) (v : TorusVertex width height) : G :=
  zmodTransport (fun y => b (v.1, y)) v.2.val *
    zmodTransport (fun x => a (x, 0)) v.1.val

/-- The tree gauge concentrates horizontal transport on the wrapping seam. -/
theorem IsTorusFlat.torusTreeGauge_right (hab : IsTorusFlat a b)
    (v : TorusVertex width height) :
    (torusTreeGauge a b (v.1 + 1, v.2))⁻¹ * a v * torusTreeGauge a b v =
      if v.1 + 1 = 0 then zmodTransport (fun x => a (x, 0)) width else 1 := by
  have hs := zmodTransport_step (fun x => a (x, 0)) v.1
  have hc := hab.zmodTransport_column_mul v.1 v.2.val
  rw [ZMod.natCast_zmod_val] at hc
  apply (mul_left_cancel_iff (a := torusTreeGauge a b (v.1 + 1, v.2))).mp
  simp only [mul_assoc, mul_inv_cancel_left]
  simp only [torusTreeGauge]
  calc
    a v * (zmodTransport (fun y => b (v.1, y)) v.2.val *
        zmodTransport (fun x => a (x, 0)) v.1.val) =
      zmodTransport (fun y => b (v.1 + 1, y)) v.2.val *
        (a (v.1, 0) * zmodTransport (fun x => a (x, 0)) v.1.val) := by
          rw [← mul_assoc, ← hc, mul_assoc]
    _ = _ := by rw [hs, ← mul_assoc]

/-- The tree gauge concentrates vertical transport on the wrapping seam. -/
theorem IsTorusFlat.torusTreeGauge_up (hab : IsTorusFlat a b)
    (v : TorusVertex width height) :
    (torusTreeGauge a b (v.1, v.2 + 1))⁻¹ * b v * torusTreeGauge a b v =
      if v.2 + 1 = 0 then zmodTransport (fun y => b (0, y)) height else 1 := by
  have hs := zmodTransport_step (fun y => b (v.1, y)) v.2
  have hc := hab.zmodTransport_rectangle v.1.val height
  simp only [ZMod.natCast_self, ZMod.natCast_zmod_val] at hc
  apply (mul_left_cancel_iff (a := torusTreeGauge a b (v.1, v.2 + 1))).mp
  simp only [mul_assoc, mul_inv_cancel_left]
  simp only [torusTreeGauge]
  rw [← mul_assoc, hs, mul_assoc]
  split_ifs with hv
  · rw [hc, ← mul_assoc]
  · simp only [one_mul, mul_one]

/-! ### Native graph connections -/

section Native

variable [Fact (2 < width)] [Fact (2 < height)]

local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

/-- Native rightward transport of an ordered torus bond assignment. -/
def torusNativeRightTransport (u : Edge (torusGraph width height) → G)
    (v : TorusVertex width height) : G :=
  regularDirectedTransport u (torusGraph_adj_right v.1 v.2)

/-- Native upward transport of an ordered torus bond assignment. -/
def torusNativeUpTransport (u : Edge (torusGraph width height) → G)
    (v : TorusVertex width height) : G :=
  regularDirectedTransport u (torusGraph_adj_up v.1 v.2)

/-- The horizontal native seam transport is the horizontal closure element. -/
theorem torusNativeRightTransport_closure (g h : G) (v : TorusVertex width height) :
    torusNativeRightTransport (torusClosureEdgeAssignment g h) v =
      if v.1 + 1 = 0 then h else 1 := by
  unfold torusNativeRightTransport regularDirectedTransport
  change (if v < (v.1 + 1, v.2) then
    torusClosureEdgeAssignment g h (torusRightEdge v) else
    (torusClosureEdgeAssignment g h (torusRightEdge v))⁻¹) = _
  rw [torusClosureEdgeAssignment_right]
  by_cases hv : v.1 + 1 = 0
  · have hlt : ¬v < (v.1 + 1, v.2) := by
      intro he
      have hh := torusRightEdge_head_of_wrap v hv
      rw [torusRightEdge, Edge.ofAdj_of_lt (torusGraph_adj_right v.1 v.2) he] at hh
      exact (ne_of_lt he) hh.symm
    rw [ite_eq_right hlt]
    simp [torusHorizontalClosureElement, hv]
  · simp [torusHorizontalClosureElement, hv]

/-- The vertical native seam transport is the inverse vertical closure element. -/
theorem torusNativeUpTransport_closure (g h : G) (v : TorusVertex width height) :
    torusNativeUpTransport (torusClosureEdgeAssignment g h) v =
      if v.2 + 1 = 0 then g⁻¹ else 1 := by
  unfold torusNativeUpTransport regularDirectedTransport
  change (if v < (v.1, v.2 + 1) then
    torusClosureEdgeAssignment g h (torusUpEdge v) else
    (torusClosureEdgeAssignment g h (torusUpEdge v))⁻¹) = _
  rw [torusClosureEdgeAssignment_up]
  by_cases hv : v.2 + 1 = 0
  · have hlt : ¬v < (v.1, v.2 + 1) := by
      intro he
      have hh := torusUpEdge_head_of_wrap v hv
      rw [torusUpEdge, Edge.ofAdj_of_lt (torusGraph_adj_up v.1 v.2) he] at hh
      exact (ne_of_lt he) hh.symm
    rw [ite_eq_right hlt]
    simp [torusVerticalClosureElement, hv]
  · simp [torusVerticalClosureElement, hv]

/-- Rightward and upward transports determine every ordered torus bond. -/
theorem torusEdgeAssignment_ext {u u' : Edge (torusGraph width height) → G}
    (hr : ∀ v, torusNativeRightTransport u v = torusNativeRightTransport u' v)
    (hu : ∀ v, torusNativeUpTransport u v = torusNativeUpTransport u' v) : u = u' := by
  funext e
  obtain ⟨v | v, rfl⟩ := torusEdgeEquiv.surjective e
  · have hv := hr v
    unfold torusNativeRightTransport regularDirectedTransport at hv
    change (if v < (v.1 + 1, v.2) then u (torusRightEdge v) else
      (u (torusRightEdge v))⁻¹) =
      (if v < (v.1 + 1, v.2) then u' (torusRightEdge v) else
        (u' (torusRightEdge v))⁻¹) at hv
    split_ifs at hv
    · exact hv
    · exact inv_injective hv
  · have hv := hu v
    unfold torusNativeUpTransport regularDirectedTransport at hv
    change (if v < (v.1, v.2 + 1) then u (torusUpEdge v) else
      (u (torusUpEdge v))⁻¹) =
      (if v < (v.1, v.2 + 1) then u' (torusUpEdge v) else
        (u' (torusUpEdge v))⁻¹) at hv
    split_ifs at hv
    · exact hv
    · exact inv_injective hv

/-- Every flat native torus connection is gauge equivalent to two commuting
closure seams. This is the group-valued seam reduction used in SCP10,
`eq:2d:move-strings`; its holonomies need not be trivial. -/
theorem exists_regularVertexGauge_eq_torusClosure
    (u : Edge (torusGraph width height) → G)
    (hu : IsTorusFlat (torusNativeRightTransport u) (torusNativeUpTransport u)) :
    ∃ (k : TorusVertex width height → G) (g h : G),
      Commute g h ∧ regularVertexGaugeOperators k u = torusClosureEdgeAssignment g h := by
  refine ⟨torusTreeGauge (torusNativeRightTransport u) (torusNativeUpTransport u),
    (zmodTransport (fun y => torusNativeUpTransport u (0, y)) height)⁻¹,
    zmodTransport (fun x => torusNativeRightTransport u (x, 0)) width,
    hu.commute_holonomies.symm.inv_left, ?_⟩
  apply torusEdgeAssignment_ext
  · intro v
    rw [torusNativeRightTransport_closure]
    exact (regularDirectedTransport_gauge _ _ _).trans (hu.torusTreeGauge_right v)
  · intro v
    rw [torusNativeUpTransport_closure, inv_inv]
    exact (regularDirectedTransport_gauge _ _ _).trans (hu.torusTreeGauge_up v)

variable [Fintype G] {d : ℕ}

/-- A flat insertion into a locally invariant regular torus network gives the
same physical state as a commuting two-seam closure. No injectivity or
isometry assumption is required for this equality. Source: SCP10,
`eq:2d:move-strings`. -/
theorem exists_sameState_torusClosure_of_isTorusFlat
    (a : (v : TorusVertex width height) →
      (IncidentEdge (torusGraph width height) v → G) → Fin d → ℂ)
    (ha : ∀ g v η s, a v (fun e => g * η e) s = a v η s)
    (u : Edge (torusGraph width height) → G)
    (hu : IsTorusFlat (torusNativeRightTransport u) (torusNativeUpTransport u)) :
    ∃ g h : G, Commute g h ∧
      SameState (groupBondTensor (regularTwistedSite a u))
        (groupBondTensor (regularTwistedSite a (torusClosureEdgeAssignment g h))) := by
  obtain ⟨k, g, h, hgh, hk⟩ := exists_regularVertexGauge_eq_torusClosure u hu
  refine ⟨g, h, hgh, ?_⟩
  rw [← hk]
  exact sameState_regularVertexGauge a ha k u

/-- For a four-leg regular tensor, a flat insertion is an actual commuting
closure in the source's horizontal and vertical conventions. Source: SCP10,
`eq:2d:peps-with-ug-uh` and `eq:2d:move-strings`. -/
theorem exists_stateCoeff_eq_torusGClosure_of_isTorusFlat [DecidableEq G]
    (a : G → G → G → G → Fin d → ℂ)
    (ha : ∀ g t r b l s, a (g * t) (g * r) (g * b) (g * l) s = a t r b l s)
    (u : Edge (torusGraph width height) → G)
    (hu : IsTorusFlat (torusNativeRightTransport u) (torusNativeUpTransport u)) :
    ∃ g h : G, Commute g h ∧
      ∀ σ, stateCoeff (groupBondTensor (regularTwistedSite (torusIncidentSite a) u)) σ =
        torusGClosure (leftRegularMatrix G) a g h σ := by
  obtain ⟨g, h, hgh, hs⟩ := exists_sameState_torusClosure_of_isTorusFlat
    (torusIncidentSite a) (fun g v η s => ha g _ _ _ _ s) u hu
  refine ⟨g, h, hgh, fun σ => ?_⟩
  rw [torusGClosure_eq_stateCoeff_twisted]
  exact hs σ

end Native

end TNLean.PEPS
