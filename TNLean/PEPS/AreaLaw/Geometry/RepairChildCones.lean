/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairStarModel

/-!
# The eight wedges about a child of a removal square

Let a parent at `v` have removal half-side `d > 0`, and let `c = v + d e` be a
child, `e ∈ {-1, 0, 1}²`. In the open square of half-side `d / 2` about `c`,
every wedge of the fan at `c` lies in one wedge of the parent fan at `v` and
lies either inside the removal square `v + [-d, d]²` or outside its interior.

Number the slots `0, …, 7` along the perimeter. A noncentral child lies on the
final ray of the parent slot `k`. Writing `r = t - k (mod 8)` for a child
slot `t`, the parent slot is `k + 1` for `r ∈ {1, 2, 3, 4}` and `k` otherwise;
the child wedge lies inside the square for `r ∈ {3, 4, 5, 6}` at a side
midpoint and for `r ∈ {4, 5}` at a corner. At the center all child wedges lie
inside, in the parent wedge of the same slot.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:repair-induction`, lines 497–514.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Written from the manuscript; no upstream Lean text is reused.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The slot at perimeter position `n mod 8`.
Auxiliary to area-law Section 11, lines 506–514. -/
def repairSlotOfCode (n : ℕ) : RepairFanSlot :=
  ⟨⟨n % 8 / 2, by omega⟩, ⟨n % 2, by simp [repairFanSplit]; omega⟩⟩

theorem repairSlotCode_slotOfCode (n : ℕ) : repairSlotCode (repairSlotOfCode n) = n % 8 := by
  simp only [repairSlotCode, repairSlotOfCode]
  omega

theorem repairSlotOfCode_code (s : RepairFanSlot) : repairSlotOfCode (repairSlotCode s) = s := by
  apply repairSlotCode_injective
  rw [repairSlotCode_slotOfCode, Nat.mod_eq_of_lt (repairSlotCode_lt s)]

theorem repairSlotOfCode_mod (n : ℕ) : repairSlotOfCode (n % 8) = repairSlotOfCode n := by
  apply repairSlotCode_injective
  rw [repairSlotCode_slotOfCode, repairSlotCode_slotOfCode, Nat.mod_mod]

theorem cellFanNext_repairSlotOfCode (n : ℕ) :
    cellFanNext (repairSlotOfCode n) = repairSlotOfCode (n + 1) := by
  apply repairSlotCode_injective
  rw [repairSlotCode_next, repairSlotCode_slotOfCode, repairSlotCode_slotOfCode]
  omega

theorem repairSlotOfCode_snd_val (n : ℕ) : ((repairSlotOfCode n).2 : ℕ) = n % 2 :=
  rfl

theorem repairSlotOfCode_fst (n : ℕ) : (repairSlotOfCode n).1 = ⟨n % 8 / 2, by omega⟩ :=
  rfl

/-- The initial directions of the slots, in perimeter order.
Auxiliary to area-law Section 11, lines 506–514. -/
def repairStartTable (n : ℕ) : ℝ × ℝ :=
  match n % 8 with
  | 0 => (1, -1)
  | 1 => (1, 0)
  | 2 => (1, 1)
  | 3 => (0, 1)
  | 4 => (-1, 1)
  | 5 => (-1, 0)
  | 6 => (-1, -1)
  | _ => (0, -1)

theorem repairFanStart_slotOfCode (n : ℕ) :
    repairFanStart (repairSlotOfCode n) = repairStartTable n := by
  have key : ∀ k : Fin 8, repairFanStart (repairSlotOfCode k.val) = repairStartTable k.val := by
    intro k
    rw [repairFanStart_eq, repairSlotOfCode_snd_val, repairSlotOfCode_fst]
    fin_cases k <;> norm_num [cellFanSideVector, repairStartTable]
  have ht : repairStartTable n = repairStartTable (n % 8) := by
    simp only [repairStartTable, Nat.mod_mod]
  rw [← repairSlotOfCode_mod, ht]
  exact key ⟨n % 8, Nat.mod_lt _ (by norm_num)⟩

theorem repairFanDirection_slotOfCode (n : ℕ) :
    repairFanDirection (repairSlotOfCode n) = repairStartTable (n + 1) := by
  rw [← repairFanStart_next, cellFanNext_repairSlotOfCode, repairFanStart_slotOfCode]

/-- The perimeter position of the parent slot whose final ray contains the
child with the given offset; the central child is assigned position zero.
Auxiliary to area-law Section 11, lines 506–514. -/
def repairChildRayCode : Fin 3 × Fin 3 → ℕ
  | (2, 1) => 0
  | (2, 2) => 1
  | (1, 2) => 2
  | (0, 2) => 3
  | (0, 1) => 4
  | (0, 0) => 5
  | (1, 0) => 6
  | (2, 0) => 7
  | _ => 0

/-- Whether the child wedge at perimeter position `n` lies inside the removal
square of the parent.
Source: area-law Section 11, `geometry:repair-induction`, lines 497–514. -/
def repairChildInside (e : Fin 3 × Fin 3) (n : ℕ) : Bool :=
  if e = (1, 1) then true
  else if repairChildRayCode e % 2 = 0 then
    decide (3 ≤ (n + 8 - repairChildRayCode e) % 8 ∧ (n + 8 - repairChildRayCode e) % 8 ≤ 6)
  else decide (4 ≤ (n + 8 - repairChildRayCode e) % 8 ∧ (n + 8 - repairChildRayCode e) % 8 ≤ 5)

/-- The perimeter position of the parent wedge containing the child wedge at
perimeter position `n`.
Source: area-law Section 11, `geometry:repair-induction`, lines 497–514. -/
def repairChildParentCode (e : Fin 3 × Fin 3) (n : ℕ) : ℕ :=
  if e = (1, 1) then n % 8
  else if 1 ≤ (n + 8 - repairChildRayCode e) % 8 ∧ (n + 8 - repairChildRayCode e) % 8 ≤ 4 then
    repairChildRayCode e + 1
  else repairChildRayCode e

/-- Consecutive child wedges of the same kind lie in the same or in
adjacent parent wedges.
Auxiliary to area-law Section 11, lines 497–514. -/
theorem repairChildParentCode_succ_of_inside_eq (e : Fin 3 × Fin 3) (m : Fin 8)
    (h : repairChildInside e ((m.val + 1) % 8) = repairChildInside e m.val) :
    repairChildParentCode e ((m.val + 1) % 8) % 8 = repairChildParentCode e m.val % 8 ∨
      repairChildParentCode e ((m.val + 1) % 8) % 8 = (repairChildParentCode e m.val + 1) % 8 ∨
      repairChildParentCode e m.val % 8 = (repairChildParentCode e ((m.val + 1) % 8) + 1) % 8 := by
  revert h
  revert m
  revert e
  decide

/-- Consecutive child wedges of different kinds lie in the same parent wedge.
Auxiliary to area-law Section 11, lines 497–514. -/
theorem repairChildParentCode_succ_of_inside_ne (e : Fin 3 × Fin 3) (m : Fin 8)
    (h : repairChildInside e ((m.val + 1) % 8) ≠ repairChildInside e m.val) :
    repairChildParentCode e ((m.val + 1) % 8) % 8 = repairChildParentCode e m.val % 8 := by
  revert h
  revert m
  revert e
  decide

/-- The wedges about a child in its open square of half-side `d/2`: each lies
in its parent wedge, and lies in the removal square or outside its interior
according to its kind. Here `y = x - v` and `x - c = y - d e`.
Source: area-law Section 11, `geometry:repair-induction`, lines 497–514. -/
def RepairChildConeFacts (e : Fin 3 × Fin 3) (m : ℕ) (d : ℝ) (y : ℝ × ℝ) : Prop :=
  (y - d • repairChildOffset e ∈ repairFanCone (repairSlotOfCode m) →
      y ∈ repairFanCone (repairSlotOfCode (repairChildParentCode e m))) ∧
    (y - d • repairChildOffset e ∈ repairFanOpenCone (repairSlotOfCode m) →
      y ∈ repairFanOpenCone (repairSlotOfCode (repairChildParentCode e m))) ∧
    (repairChildInside e m = true →
      y - d • repairChildOffset e ∈ repairFanCone (repairSlotOfCode m) → ‖y‖ ≤ d) ∧
    (repairChildInside e m = true →
      y - d • repairChildOffset e ∈ repairFanOpenCone (repairSlotOfCode m) → ‖y‖ < d) ∧
    (repairChildInside e m = false →
      y - d • repairChildOffset e ∈ repairFanCone (repairSlotOfCode m) → ¬‖y‖ < d) ∧
    (repairChildInside e m = false →
      y - d • repairChildOffset e ∈ repairFanOpenCone (repairSlotOfCode m) → ¬‖y‖ ≤ d)

/-- Unfold the child-wedge facts to linear inequalities and close them. -/
local macro "repair_child_cone_tac" : tactic => `(tactic| (
  intro m d hd y hy
  obtain ⟨y₁, y₂⟩ := y
  rw [Prod.norm_def, max_lt_iff] at hy
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    Real.norm_eq_abs, abs_lt] at hy
  obtain ⟨⟨h₁, h₂⟩, h₃, h₄⟩ := hy
  simp only [RepairChildConeFacts, repairFanCone, repairFanOpenCone, Set.mem_ofPred_eq,
    repairFanStart_slotOfCode, repairFanDirection_slotOfCode, Prod.norm_def, Real.norm_eq_abs,
    max_le_iff, max_lt_iff, abs_le, abs_lt, not_and]
  fin_cases m <;>
    norm_num [repairChildInside, repairChildParentCode, repairChildRayCode, repairStartTable,
      repairChildOffset, repairCross] at h₁ h₂ h₃ h₄ ⊢ <;>
    (repeat' (first | apply And.intro | intro _)) <;>
    linarith))

private theorem repairChildConeFacts_00 : ∀ (m : Fin 8) {d : ℝ}, 0 < d →
    ∀ y : ℝ × ℝ, ‖y - d • repairChildOffset (0, 0)‖ < d / 2 →
      RepairChildConeFacts (0, 0) m.val d y := by
  repair_child_cone_tac

private theorem repairChildConeFacts_01 : ∀ (m : Fin 8) {d : ℝ}, 0 < d →
    ∀ y : ℝ × ℝ, ‖y - d • repairChildOffset (0, 1)‖ < d / 2 →
      RepairChildConeFacts (0, 1) m.val d y := by
  repair_child_cone_tac

private theorem repairChildConeFacts_02 : ∀ (m : Fin 8) {d : ℝ}, 0 < d →
    ∀ y : ℝ × ℝ, ‖y - d • repairChildOffset (0, 2)‖ < d / 2 →
      RepairChildConeFacts (0, 2) m.val d y := by
  repair_child_cone_tac

private theorem repairChildConeFacts_10 : ∀ (m : Fin 8) {d : ℝ}, 0 < d →
    ∀ y : ℝ × ℝ, ‖y - d • repairChildOffset (1, 0)‖ < d / 2 →
      RepairChildConeFacts (1, 0) m.val d y := by
  repair_child_cone_tac

private theorem repairChildConeFacts_11 : ∀ (m : Fin 8) {d : ℝ}, 0 < d →
    ∀ y : ℝ × ℝ, ‖y - d • repairChildOffset (1, 1)‖ < d / 2 →
      RepairChildConeFacts (1, 1) m.val d y := by
  repair_child_cone_tac

private theorem repairChildConeFacts_12 : ∀ (m : Fin 8) {d : ℝ}, 0 < d →
    ∀ y : ℝ × ℝ, ‖y - d • repairChildOffset (1, 2)‖ < d / 2 →
      RepairChildConeFacts (1, 2) m.val d y := by
  repair_child_cone_tac

private theorem repairChildConeFacts_20 : ∀ (m : Fin 8) {d : ℝ}, 0 < d →
    ∀ y : ℝ × ℝ, ‖y - d • repairChildOffset (2, 0)‖ < d / 2 →
      RepairChildConeFacts (2, 0) m.val d y := by
  repair_child_cone_tac

private theorem repairChildConeFacts_21 : ∀ (m : Fin 8) {d : ℝ}, 0 < d →
    ∀ y : ℝ × ℝ, ‖y - d • repairChildOffset (2, 1)‖ < d / 2 →
      RepairChildConeFacts (2, 1) m.val d y := by
  repair_child_cone_tac

private theorem repairChildConeFacts_22 : ∀ (m : Fin 8) {d : ℝ}, 0 < d →
    ∀ y : ℝ × ℝ, ‖y - d • repairChildOffset (2, 2)‖ < d / 2 →
      RepairChildConeFacts (2, 2) m.val d y := by
  repair_child_cone_tac

/-- The child-wedge facts hold for every child, wedge and point of the open
square of half-side `d / 2` about the child.
Source: area-law Section 11, `geometry:repair-induction`, lines 497–514. -/
theorem repairChildConeFacts_holds (e : Fin 3 × Fin 3) (m : Fin 8) {d : ℝ} (hd : 0 < d)
    (y : ℝ × ℝ) (hy : ‖y - d • repairChildOffset e‖ < d / 2) :
    RepairChildConeFacts e m.val d y := by
  fin_cases e
  · exact repairChildConeFacts_00 m hd y hy
  · exact repairChildConeFacts_01 m hd y hy
  · exact repairChildConeFacts_02 m hd y hy
  · exact repairChildConeFacts_10 m hd y hy
  · exact repairChildConeFacts_11 m hd y hy
  · exact repairChildConeFacts_12 m hd y hy
  · exact repairChildConeFacts_20 m hd y hy
  · exact repairChildConeFacts_21 m hd y hy
  · exact repairChildConeFacts_22 m hd y hy

end TNLean.PEPS.AreaLaw.Geometry
