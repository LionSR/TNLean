/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusSweptStringEndpointHolonomy
import TNLean.PEPS.RegularGaugedCyclePhysicalPermutation
import TNLean.PEPS.TorusTranslatedFluxMove

/-!
# The first rightward endpoint step in the two-string configuration

The continuing first string is retained literally. The first rightward endpoint
step changes only the middle upward bond transport from g to g h. Its clockwise
plaquette flux h moves from (1,1) to (2,1), relative to the source patch.

Source: SCP10, arXiv:1001.3807, physical movement in Theorem 6.16 and the
four-endpoint braiding figure, lines 2271–2305 and 2340–2423.

**Scope restriction (finite-torus elementary movement):** The horizontal period
is at least eight and the vertical period at least seven. This calculation
handles the first rightward step; it does not establish the complete prescribed
braid. See `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (7 < width)] [Fact (6 < height)]
local instance horizontalStepWidthSix : Fact (6 < width) :=
  ⟨by have := Fact.out (p := 7 < width); omega⟩
local instance horizontalStepHeightFive : Fact (5 < height) :=
  ⟨by have := Fact.out (p := 6 < height); omega⟩
local instance horizontalStepWidthFour : Fact (4 < width) :=
  ⟨by have := Fact.out (p := 7 < width); omega⟩
local instance horizontalStepWidthThree : Fact (3 < width) :=
  ⟨by have := Fact.out (p := 7 < width); omega⟩
local instance horizontalStepHeightThree : Fact (3 < height) :=
  ⟨by have := Fact.out (p := 6 < height); omega⟩
local instance horizontalStepWidthTwo : Fact (2 < width) :=
  ⟨by have := Fact.out (p := 7 < width); omega⟩
local instance horizontalStepHeightTwo : Fact (2 < height) :=
  ⟨by have := Fact.out (p := 6 < height); omega⟩
local instance horizontalStepWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 7 < width); omega⟩
local instance horizontalStepHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 6 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height
variable {G : Type*} [Group G]

/-- The literal new middle upward coefficient, with native seam inversion.
Source: SCP10, first horizontal movement in the route, lines 2340–2423. -/
def torusSweptStringRightStepOperators (v : X) (g h : G) (e : Edge Γₜ) : G :=
  let p : X := (v.1+2, v.2+1)
  if e = torusUpEdge p then
    if p.2.val < (p.2+1).val then g*h else (g*h)⁻¹
  else torusSweptStringInitialOperators v g h e

/-- The rightward table and hence the entire continuing second string is retained.
Source: SCP10, first horizontal endpoint movement, lines 2340–2423. -/
theorem torusSweptStringRightStepOperators_right_transport (v p : X) (g h : G) :
    regularDirectedTransport (torusSweptStringRightStepOperators v g h)
      (torusGraph_adj_right p.1 p.2) = torusSweptStringInitialRight v h p := by
  have he : torusSweptStringRightStepOperators v g h (torusRightEdge p) =
      torusSweptStringInitialOperators v g h (torusRightEdge p) := by
    simp only [torusSweptStringRightStepOperators,
      ite_eq_right (torusRightEdge_ne_torusUpEdge p (v.1+2,v.2+1))]
  change torusSweptStringRightStepOperators v g h
    (Edge.ofAdj (torusGraph_adj_right p.1 p.2)) =
      torusSweptStringInitialOperators v g h
        (Edge.ofAdj (torusGraph_adj_right p.1 p.2)) at he
  simpa only [regularDirectedTransport, he] using
    torusSweptStringInitialOperators_right_transport v p g h

/-- Exactly one directed upward transport changes, including either seam.
Source: SCP10, first horizontal endpoint movement, lines 2340–2423. -/
theorem torusSweptStringRightStepOperators_up_transport (v p : X) (g h : G) :
    regularDirectedTransport (torusSweptStringRightStepOperators v g h)
      (torusGraph_adj_up p.1 p.2) =
      if p = (v.1+2,v.2+1) then g*h else torusSweptStringInitialUp v g p := by
  by_cases hp : p = (v.1+2,v.2+1)
  · subst p
    have hlt : ((v.1+2,v.2+1) : X) < (v.1+2,v.2+1+1) ↔
        (v.2+1).val < (v.2+1+1).val := by
      change toLex ((v.1+2).val,(v.2+1).val) <
        toLex ((v.1+2).val,(v.2+1+1).val) ↔ _
      simp [Prod.Lex.toLex_lt_toLex]
    simp only [regularDirectedTransport, hlt, torusSweptStringRightStepOperators,
      torusUpEdge, eq_self, ite_true]
    split_ifs <;> simp
  · have he : torusSweptStringRightStepOperators v g h (torusUpEdge p) =
        torusSweptStringInitialOperators v g h (torusUpEdge p) := by
      simp only [torusSweptStringRightStepOperators,
        ite_eq_right ((torusUpEdge_injective (width := width) (height := height)).ne hp)]
    change torusSweptStringRightStepOperators v g h
      (Edge.ofAdj (torusGraph_adj_up p.1 p.2)) =
        torusSweptStringInitialOperators v g h
          (Edge.ofAdj (torusGraph_adj_up p.1 p.2)) at he
    simpa only [regularDirectedTransport, he, ite_eq_right hp] using
      torusSweptStringInitialOperators_up_transport v p g h

/-- The actual clockwise flux moves right while its partner string continues.
Source: SCP10, first physical endpoint step, lines 2340–2423. -/
theorem regularWalkHolonomy_torusSweptStringRightStep (v : X) (g h : G) :
    regularWalkHolonomy (torusSweptStringRightStepOperators v g h)
      (torusPlaquetteWalk (v.1+1,v.2+1)).reverse = 1 ∧
    regularWalkHolonomy (torusSweptStringRightStepOperators v g h)
      (torusPlaquetteWalk (v.1+2,v.2+1)).reverse = h := by
  have hw := Fact.out (p := 7 < width)
  have hh := Fact.out (p := 6 < height)
  have hx21 := mt (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt (n := width) 2 1
    (by norm_num; omega)).mp (by decide : (2 : ℤ) ≠ 1)
  have hx32 := mt (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt (n := width) 3 2
    (by norm_num; omega)).mp (by decide : (3 : ℤ) ≠ 2)
  have hy20 := mt (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt (n := height) 2 0
    (by norm_num; omega)).mp (by decide : (2 : ℤ) ≠ 0)
  have hy21 := mt (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt (n := height) 2 1
    (by norm_num; omega)).mp (by decide : (2 : ℤ) ≠ 1)
  have hy2n := mt (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt (n := height) 2 (-1)
    (by norm_num; omega)).mp (by decide : (2 : ℤ) ≠ -1)
  norm_num only at hx21 hx32 hy20 hy21 hy2n
  constructor
  · rw [regularWalkHolonomy_torusPlaquetteWalk_reverse,
      torusSweptStringRightStepOperators_right_transport v (v.1+1,v.2+1) g h,
      torusSweptStringRightStepOperators_up_transport v (v.1+1+1,v.2+1) g h,
      torusSweptStringRightStepOperators_right_transport v (v.1+1,v.2+1+1) g h,
      torusSweptStringRightStepOperators_up_transport v (v.1+1,v.2+1) g h]
    norm_num [torusSweptStringInitialRight, torusSweptStringInitialUp,
      add_assoc, sub_eq_add_neg, hx21, Ne.symm hx21, hy20, hy21, hy2n]
  · rw [regularWalkHolonomy_torusPlaquetteWalk_reverse,
      torusSweptStringRightStepOperators_right_transport v (v.1+2,v.2+1) g h,
      torusSweptStringRightStepOperators_up_transport v (v.1+2+1,v.2+1) g h,
      torusSweptStringRightStepOperators_right_transport v (v.1+2,v.2+1+1) g h,
      torusSweptStringRightStepOperators_up_transport v (v.1+2,v.2+1) g h]
    norm_num [torusSweptStringInitialRight, torusSweptStringInitialUp,
      add_assoc, sub_eq_add_neg, hx21, Ne.symm hx21, hx32, Ne.symm hx32,
      hy20, hy21, hy2n]

end TNLean.PEPS
