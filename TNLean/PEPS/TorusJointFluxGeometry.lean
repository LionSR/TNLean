/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusTranslatedFluxMove

/-!
# The outer walk and joint flux of two adjacent torus plaquettes

The six-step counterclockwise outer walk traverses the boundary of the actual
translated two-plaquette block. Directed upward transports `(a * b)⁻¹` on its
left side and `b⁻¹` on its middle bond give left and right plaquette holonomies
`a` and `b`, and outer holonomy `a * b`. Ordered-edge coefficients are inverted
at the vertical seam, so these identities hold at every position.

Source: SCP10, arXiv:1001.3807, joint flux measurement in the braiding passage,
lines 2380–2415.

**Scope restriction (regular six-site geometry):** Horizontal periods are at
least four and vertical periods at least three. The result is the geometric
joint-measurement step; it asserts neither braiding nor parent-Hamiltonian
membership. See `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (3 < width)] [Fact (2 < height)]
local instance jointFluxWidthTwo : Fact (2 < width) :=
  ⟨by have := Fact.out (p := 3 < width); omega⟩
local instance jointFluxWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 3 < width); omega⟩
local instance jointFluxHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height

/-- The counterclockwise outer boundary of the actual translated two-plaquette
block. Source: SCP10, joint flux measurement, lines 2380–2415. -/
def torusTwoPlaquetteOuterWalk (v : X) : (Γₜ).Walk v v :=
  .cons (torusGraph_adj_right v.1 v.2)
    (.cons (torusGraph_adj_right (v.1 + 1) v.2)
      (.cons (torusGraph_adj_up (v.1 + 1 + 1) v.2)
        (.cons (torusGraph_adj_right (v.1 + 1) (v.2 + 1)).symm
          (.cons (torusGraph_adj_right v.1 (v.2 + 1)).symm
            (.cons (torusGraph_adj_up v.1 v.2).symm .nil)))))

private theorem vertex_coordinates (v : X) :
    translatedTwoPlaquetteVertex v =
      ![v, (v.1 + 1, v.2), (v.1 + 1 + 1, v.2), (v.1 + 1 + 1, v.2 + 1),
        (v.1 + 1, v.2 + 1), (v.1, v.2 + 1)] := by
  rcases v with ⟨x, y⟩
  funext i
  fin_cases i
  · change (((0 : ℕ) : ZMod width) + x, ((0 : ℕ) : ZMod height) + y) = (x, y)
    simp
  · change (((1 : ℕ) : ZMod width) + x, ((0 : ℕ) : ZMod height) + y) = (x + 1, y)
    simp [add_comm]
  · change (((2 : ℕ) : ZMod width) + x, ((0 : ℕ) : ZMod height) + y) = (x + 1 + 1, y)
    simp [add_comm]
    ring
  · change (((2 : ℕ) : ZMod width) + x, ((1 : ℕ) : ZMod height) + y) = (x + 1 + 1, y + 1)
    simp [add_comm]
    ring
  · change (((1 : ℕ) : ZMod width) + x, ((1 : ℕ) : ZMod height) + y) = (x + 1, y + 1)
    simp [add_comm]
  · change (((0 : ℕ) : ZMod width) + x, ((1 : ℕ) : ZMod height) + y) = (x, y + 1)
    simp [add_comm]

/-- The outer walk visits exactly the six sites of the translated block.
Auxiliary to SCP10, joint flux measurement, lines 2380–2415. -/
theorem torusTwoPlaquetteOuterWalk_support (v : X) :
    (torusTwoPlaquetteOuterWalk v).support.toFinset = translatedTwoPlaquetteRegion v := by
  simp only [torusTwoPlaquetteOuterWalk, SimpleGraph.Walk.support, List.toFinset_cons,
    List.toFinset_nil, translatedTwoPlaquetteRegion, vertex_coordinates]
  ext x
  simp only [Finset.mem_insert, Finset.notMem_empty, or_false, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
    · exact ⟨0, rfl⟩
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp

variable {G : Type*} [Group G]
private def orderedUp (v : X) (g : G) : G :=
  if v.2.val < (v.2 + 1).val then g else g⁻¹

/-- The literal routed assignment with upward transports `(a * b)⁻¹` and
`b⁻¹` on the left and middle vertical bonds, respectively. All other bonds
carry the identity. Source: SCP10, joint flux measurement, lines 2380–2415. -/
def torusJointFluxAssignment (v : X) (a b : G) (e : Edge Γₜ) : G :=
  if e = Edge.ofAdj (torusGraph_adj_up v.1 v.2) then orderedUp v (a * b)⁻¹
  else if e = Edge.ofAdj (torusGraph_adj_up (v.1 + 1) v.2) then orderedUp v b⁻¹
  else 1

private theorem up_endpoints_fst (x : ZMod width) (y : ZMod height) :
    (Edge.ofAdj (torusGraph_adj_up x y)).1.1.1 = x ∧
      (Edge.ofAdj (torusGraph_adj_up x y)).1.2.1 = x := by
  rcases Edge.ofAdj_endpoints (torusGraph_adj_up x y) with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;>
    simp only [h₁, h₂, and_self]

private theorem up_edge_eq_iff (x x' : ZMod width) (y : ZMod height) :
    Edge.ofAdj (torusGraph_adj_up x y) = Edge.ofAdj (torusGraph_adj_up x' y) ↔ x = x' := by
  constructor
  · intro h
    have hx := (up_endpoints_fst x y).1
    rw [h, (up_endpoints_fst x' y).1] at hx
    exact hx.symm
  · rintro rfl
    rfl

private theorem horizontal_ne_vertical (x a : ZMod width) (y b : ZMod height) :
    Edge.ofAdj (torusGraph_adj_right x y) ≠ Edge.ofAdj (torusGraph_adj_up a b) := by
  intro h
  have hv := up_endpoints_fst a b
  rw [← h] at hv
  rcases Edge.ofAdj_endpoints (torusGraph_adj_right x y) with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · simp only [h₁, h₂] at hv
    exact (show x ≠ x + 1 by simp) (hv.1.trans hv.2.symm)
  · simp only [h₁, h₂] at hv
    exact (show x + 1 ≠ x by simp) (hv.1.trans hv.2.symm)

omit [Fact (3 < width)] [Fact (2 < height)] in
private theorem up_lt_iff (x : ZMod width) (y : ZMod height) :
    ((x, y) : X) < (x, y + 1) ↔ y.val < (y + 1).val := by
  change toLex (x.val, y.val) < toLex (x.val, (y + 1).val) ↔ _
  simp [Prod.Lex.toLex_lt_toLex]

/-- The directed upward values of the joint assignment, including its seam
orientation. Source: SCP10, joint flux measurement, lines 2380–2415. -/
theorem regularDirectedTransport_torusJointFluxAssignment_up
    (v : X) (a b : G) (x : ZMod width) :
    regularDirectedTransport (torusJointFluxAssignment v a b)
      (torusGraph_adj_up x v.2) =
      if x = v.1 then (a * b)⁻¹ else if x = v.1 + 1 then b⁻¹ else 1 := by
  simp only [regularDirectedTransport, torusJointFluxAssignment, orderedUp,
    up_edge_eq_iff, up_lt_iff]
  split_ifs <;> simp_all

private theorem horizontal_transport (v : X) (a b : G)
    (x : ZMod width) (y : ZMod height) :
    regularDirectedTransport (torusJointFluxAssignment v a b)
      (torusGraph_adj_right x y) = 1 := by
  simp [regularDirectedTransport, torusJointFluxAssignment,
    horizontal_ne_vertical x v.1 y v.2, horizontal_ne_vertical x (v.1 + 1) y v.2]

omit [NeZero width] in
private theorem two_right_ne (x : ZMod width) : x + 1 + 1 ≠ x := by
  have htwo : (2 : ZMod width) ≠ 0 := by
    simpa using (ZMod.natCast_eq_zero_iff 2 width).not.mpr
      (Nat.not_dvd_of_pos_of_lt (by decide) (by have := Fact.out (p := 3 < width); omega))
  intro h
  exact htwo (add_left_cancel (by simpa only [add_assoc, one_add_one_eq_two, add_zero] using h))

/-- The actual left, right, and outer holonomies are `a`, `b`, and `a * b`.
Source: SCP10, joint flux measurement, lines 2380–2415. -/
theorem regularWalkHolonomy_torusJointFluxAssignment (v : X) (a b : G) :
    regularWalkHolonomy (torusJointFluxAssignment v a b) (torusPlaquetteWalk v) = a ∧
      regularWalkHolonomy (torusJointFluxAssignment v a b)
        (torusPlaquetteWalk (v.1 + 1, v.2)) = b ∧
      regularWalkHolonomy (torusJointFluxAssignment v a b)
        (torusTwoPlaquetteOuterWalk v) = a * b := by
  have hL := regularDirectedTransport_torusJointFluxAssignment_up v a b v.1
  have hM := regularDirectedTransport_torusJointFluxAssignment_up v a b (v.1 + 1)
  have hR := regularDirectedTransport_torusJointFluxAssignment_up v a b (v.1 + 1 + 1)
  simp only [Prod.mk.eta, ↓reduceIte, mul_inv_rev, add_eq_left, one_ne_zero,
    two_right_ne] at hL hM hR
  have hH := horizontal_transport v a b
  have hHr (x : ZMod width) (y : ZMod height) :
      regularDirectedTransport (torusJointFluxAssignment v a b)
        (torusGraph_adj_right x y).symm = 1 := by
    rw [regularDirectedTransport_symm _ (torusGraph_adj_right x y), hH, inv_one]
  have hLr : regularDirectedTransport (torusJointFluxAssignment v a b)
      (torusGraph_adj_up v.1 v.2).symm = a * b := by
    rw [regularDirectedTransport_symm _ (torusGraph_adj_up v.1 v.2), hL]
    group
  simp only [regularWalkHolonomy_torusPlaquetteWalk, torusTwoPlaquetteOuterWalk,
    regularWalkHolonomy, inv_one, inv_inv, mul_inv_rev,
    hHr, hLr, hH, hL, hM, hR, mul_one, one_mul]
  simp [mul_assoc]
end TNLean.PEPS
