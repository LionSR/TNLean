/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ThreePlaquetteGeometry
import TNLean.PEPS.TorusJointFluxGeometry

/-!
# Literal transports and holonomies in a three-plaquette strip

Three directed vertical transports determine the left, middle, and right
plaquette holonomies. The ordered coefficients are inverted together at the
vertical seam. The literal assignment is identified with the three actual
non-tree coordinates of the prescribed eight-site tree. The outer boundary
walk of the middle and right plaquettes lies in this actual region.

Source: SCP10, arXiv:1001.3807, adjacent-flux joint measurement and the
braiding passage, lines 2380–2415. These formulas supply a finite geometry
for auxiliary operations on three flux coordinates.

**Scope restriction (three-plaquette transport):** The horizontal period is at
least five and the vertical period at least three; all positions are allowed,
including both seams. No identity with a physical string-crossing braid or
parent-Hamiltonian assertion is made. See
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (4 < width)] [Fact (2 < height)]
local instance threeFluxWidthThree : Fact (3 < width) :=
  ⟨by have := Fact.out (p := 4 < width); omega⟩
local instance threeFluxWidthTwo : Fact (2 < width) :=
  ⟨by have := Fact.out (p := 4 < width); omega⟩
local instance threeFluxWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 4 < width); omega⟩
local instance threeFluxHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height
variable {G : Type*} [Group G]

/-- The literal assignment with directed upward transports `t 0`, `t 1`, and
`t 2` on the three selected vertical bonds, and identity on all other bonds.
Auxiliary to SCP10, braiding passage, lines 2380–2415. -/
def torusThreePlaquetteFluxAssignment (v : X) (t : Fin 3 → G) (e : Edge Γₜ) : G :=
  let ordered := fun g : G => if v.2.val < (v.2 + 1).val then g else g⁻¹
  if e = Edge.ofAdj (torusGraph_adj_up v.1 v.2) then ordered (t 0)
  else if e = Edge.ofAdj (torusGraph_adj_up (v.1 + 1) v.2) then ordered (t 1)
  else if e = Edge.ofAdj (torusGraph_adj_up (v.1 + 2) v.2) then ordered (t 2)
  else 1

/-- The literal assignment is exactly the actual tree-cycle assignment.
The same seam-orientation flag determines all three ordered residuals.
Auxiliary to SCP10, braiding passage, lines 2380–2415. -/
theorem torusThreePlaquetteFluxAssignment_eq_treeCycleAssignment (v : X) (t : Fin 3 → G) :
    torusThreePlaquetteFluxAssignment v t =
      regularTreeCycleAssignment (translatedThreePlaquetteRegion v) (translatedThreePlaquetteTree v)
        (fun e =>
          let ordered := fun g : G => if v.2.val < (v.2 + 1).val then g else g⁻¹
          if e = translatedThreePlaquetteCycleBond v 0 then ordered (t 0)
          else if e = translatedThreePlaquetteCycleBond v 1 then ordered (t 1)
          else if e = translatedThreePlaquetteCycleBond v 2 then ordered (t 2)
          else 1) := by
  classical
  let c := translatedThreePlaquetteCycleBond v
  let k := fun g : G => if v.2.val < (v.2 + 1).val then g else g⁻¹
  symm
  change regularTreeCycleAssignment (translatedThreePlaquetteRegion v)
    (translatedThreePlaquetteTree v)
    (fun e => if e = c 0 then k (t 0) else if e = c 1 then k (t 1)
      else if e = c 2 then k (t 2) else 1) = torusThreePlaquetteFluxAssignment v t
  calc
    _ = (fun e => if e = (c 0).1.1 then k (t 0)
        else if e = (c 1).1.1 then k (t 1)
        else if e = (c 2).1.1 then k (t 2) else 1) := by
      funext e
      by_cases h₀ : e = (c 0).1.1
      · subst e
        simp [regularTreeCycleAssignment, (c 0).1.2.1, (c 0).1.2.2, (c 0).2]
      · by_cases h₁ : e = (c 1).1.1
        · subst e
          simp [regularTreeCycleAssignment, (c 1).1.2.1, (c 1).1.2.2, (c 1).2,
            Subtype.ext_iff, h₀]
        · by_cases h₂ : e = (c 2).1.1
          · subst e
            simp [regularTreeCycleAssignment, (c 2).1.2.1, (c 2).1.2.2, (c 2).2,
              Subtype.ext_iff, h₀, h₁]
          · simp only [regularTreeCycleAssignment]
            split_ifs <;> simp_all [Subtype.ext_iff]
    _ = torusThreePlaquetteFluxAssignment v t := by
      funext e
      simp [c, k, translatedThreePlaquetteCycleBond_eq_up, torusThreePlaquetteFluxAssignment]

omit [NeZero width] [NeZero height] [Fact (2 < height)] in
private theorem offset_injective (v : X) :
    Function.Injective (fun i : Fin 4 => v.1 + (i.val : ZMod width)) := by
  intro i j h
  apply Fin.ext
  have hc := (ZMod.natCast_eq_natCast_iff' i.val j.val width).mp (add_left_cancel h)
  have hi : i.val < width := by have := Fact.out (p := 4 < width); omega
  have hj : j.val < width := by have := Fact.out (p := 4 < width); omega
  simpa only [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using hc

/-- The three selected upward transports and the identity at the right boundary
are derived from the ordered assignment, including at a vertical seam.
Auxiliary to SCP10, braiding passage, lines 2380–2415. -/
theorem torusThreePlaquetteFluxAssignment_up_transport (v : X) (t : Fin 3 → G)
    (i : Fin 4) :
    regularDirectedTransport (torusThreePlaquetteFluxAssignment v t)
      (torusGraph_adj_up (v.1 + (i.val : ZMod width)) v.2) =
      ![t 0, t 1, t 2, 1] i := by
  have hup (x x' : ZMod width) :
      Edge.ofAdj (torusGraph_adj_up x v.2) = Edge.ofAdj (torusGraph_adj_up x' v.2) ↔
        x = x' := by
    constructor
    · intro h
      have h' : torusUpEdge (x, v.2) = torusUpEdge (x', v.2) := h
      exact congrArg Prod.fst (torusUpEdge_injective h')
    · rintro rfl
      rfl
  have h₀ : v.1 + (i.val : ZMod width) = v.1 ↔ i = 0 := by
    simpa using (offset_injective v).eq_iff (a := i) (b := 0)
  have h₁ : v.1 + (i.val : ZMod width) = v.1 + 1 ↔ i = 1 := by
    simpa using (offset_injective v).eq_iff (a := i) (b := 1)
  have h₂ : v.1 + (i.val : ZMod width) = v.1 + 2 ↔ i = 2 := by
    simpa using (offset_injective v).eq_iff (a := i) (b := 2)
  have hdir (x : ZMod width) :
      ((x, v.2) : X) < (x, v.2 + 1) ↔ v.2.val < (v.2 + 1).val := by
    change toLex (x.val, v.2.val) < toLex (x.val, (v.2 + 1).val) ↔ _
    simp [Prod.Lex.toLex_lt_toLex]
  simp only [regularDirectedTransport, torusThreePlaquetteFluxAssignment, hup, h₀, h₁, h₂, hdir]
  fin_cases i <;> split_ifs <;> simp_all

private theorem horizontal_transport (v : X) (t : Fin 3 → G)
    (x : ZMod width) (y : ZMod height) :
    regularDirectedTransport (torusThreePlaquetteFluxAssignment v t)
      (torusGraph_adj_right x y) = 1 := by
  have h₀ : Edge.ofAdj (torusGraph_adj_right x y) ≠
      Edge.ofAdj (torusGraph_adj_up v.1 v.2) := torusRightEdge_ne_torusUpEdge (x, y) v
  have h₁ : Edge.ofAdj (torusGraph_adj_right x y) ≠
      Edge.ofAdj (torusGraph_adj_up (v.1 + 1) v.2) :=
    torusRightEdge_ne_torusUpEdge (x, y) (v.1 + 1, v.2)
  have h₂ : Edge.ofAdj (torusGraph_adj_right x y) ≠
      Edge.ofAdj (torusGraph_adj_up (v.1 + 2) v.2) :=
    torusRightEdge_ne_torusUpEdge (x, y) (v.1 + 2, v.2)
  simp [regularDirectedTransport, torusThreePlaquetteFluxAssignment, h₀, h₁, h₂]

/-- The actual three plaquette holonomies and the middle-right outer holonomy
are respectively `t₀⁻¹ * t₁`, `t₁⁻¹ * t₂`, `t₂⁻¹`, and `t₁⁻¹`.
Auxiliary to SCP10, braiding passage, lines 2380–2415. -/
theorem regularWalkHolonomy_torusThreePlaquetteFluxAssignment (v : X) (t : Fin 3 → G) :
    regularWalkHolonomy (torusThreePlaquetteFluxAssignment v t) (torusPlaquetteWalk v) =
        (t 0)⁻¹ * t 1 ∧
      regularWalkHolonomy (torusThreePlaquetteFluxAssignment v t)
        (torusPlaquetteWalk (v.1 + 1, v.2)) = (t 1)⁻¹ * t 2 ∧
      regularWalkHolonomy (torusThreePlaquetteFluxAssignment v t)
        (torusPlaquetteWalk (v.1 + 2, v.2)) = (t 2)⁻¹ ∧
      regularWalkHolonomy (torusThreePlaquetteFluxAssignment v t)
        (torusTwoPlaquetteOuterWalk (v.1 + 1, v.2)) = (t 1)⁻¹ := by
  have h₀ : regularDirectedTransport (torusThreePlaquetteFluxAssignment v t)
      (torusGraph_adj_up v.1 v.2) = t 0 := by
    simpa using torusThreePlaquetteFluxAssignment_up_transport v t 0
  have h₁ : regularDirectedTransport (torusThreePlaquetteFluxAssignment v t)
      (torusGraph_adj_up (v.1 + 1) v.2) = t 1 := by
    simpa using torusThreePlaquetteFluxAssignment_up_transport v t 1
  have h₂ : regularDirectedTransport (torusThreePlaquetteFluxAssignment v t)
      (torusGraph_adj_up (v.1 + 2) v.2) = t 2 := by
    simpa using torusThreePlaquetteFluxAssignment_up_transport v t 2
  have h₃ : regularDirectedTransport (torusThreePlaquetteFluxAssignment v t)
      (torusGraph_adj_up (v.1 + 3) v.2) = 1 := by
    simpa using torusThreePlaquetteFluxAssignment_up_transport v t 3
  have hH := horizontal_transport v t
  have hx₂ : v.1 + 1 + 1 = v.1 + 2 := by ring
  have hx₃ : v.1 + 2 + 1 = v.1 + 3 := by ring
  have hHr (x : ZMod width) (y : ZMod height) :
      regularDirectedTransport (torusThreePlaquetteFluxAssignment v t)
        (torusGraph_adj_right x y).symm = 1 := by
    rw [regularDirectedTransport_symm _ (torusGraph_adj_right x y), hH, inv_one]
  have hDr (x : ZMod width) :
      regularDirectedTransport (torusThreePlaquetteFluxAssignment v t)
        (torusGraph_adj_up x v.2).symm =
        (regularDirectedTransport (torusThreePlaquetteFluxAssignment v t)
          (torusGraph_adj_up x v.2))⁻¹ :=
    regularDirectedTransport_symm _ (torusGraph_adj_up x v.2)
  simp only [regularWalkHolonomy_torusPlaquetteWalk, torusTwoPlaquetteOuterWalk,
    regularWalkHolonomy, inv_one,
    Prod.mk.eta, hHr, hDr, hH, mul_one, one_mul]
  simp only [hx₂, hx₃, h₀, h₁, h₂, h₃, mul_one, and_self]

/-- The native outer walk of the middle and right plaquettes stays inside
the actual eight-site strip.
Auxiliary to SCP10, braiding passage, lines 2380–2415. -/
theorem torusThreePlaquette_rightPairWalk_mem_region (v : X) :
    ∀ x ∈ (torusTwoPlaquetteOuterWalk (v.1 + 1, v.2)).support,
      x ∈ translatedThreePlaquetteRegion v := by
  have hsub : translatedTwoPlaquetteRegion (v.1 + 1, v.2) ⊆
      translatedThreePlaquetteRegion v := by
    intro w hw
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
    apply Finset.mem_image.mpr
    refine ⟨⟨i.val + 1, by omega⟩, Finset.mem_univ _, ?_⟩
    fin_cases i
    · change (((1 : ℕ) : ZMod width) + v.1, ((0 : ℕ) : ZMod height) + v.2) =
        (((0 : ℕ) : ZMod width) + (v.1 + 1), ((0 : ℕ) : ZMod height) + v.2)
      simp [add_comm]
    · change (((2 : ℕ) : ZMod width) + v.1, ((0 : ℕ) : ZMod height) + v.2) =
        (((1 : ℕ) : ZMod width) + (v.1 + 1), ((0 : ℕ) : ZMod height) + v.2)
      norm_num
      ring
    · change (((3 : ℕ) : ZMod width) + v.1, ((0 : ℕ) : ZMod height) + v.2) =
        (((2 : ℕ) : ZMod width) + (v.1 + 1), ((0 : ℕ) : ZMod height) + v.2)
      norm_num
      ring
    · change (((3 : ℕ) : ZMod width) + v.1, ((1 : ℕ) : ZMod height) + v.2) =
        (((2 : ℕ) : ZMod width) + (v.1 + 1), ((1 : ℕ) : ZMod height) + v.2)
      norm_num
      ring
    · change (((2 : ℕ) : ZMod width) + v.1, ((1 : ℕ) : ZMod height) + v.2) =
        (((1 : ℕ) : ZMod width) + (v.1 + 1), ((1 : ℕ) : ZMod height) + v.2)
      norm_num
      ring
    · change (((1 : ℕ) : ZMod width) + v.1, ((1 : ℕ) : ZMod height) + v.2) =
        (((0 : ℕ) : ZMod width) + (v.1 + 1), ((1 : ℕ) : ZMod height) + v.2)
      simp [add_comm]
  intro x hx
  apply hsub
  rw [← torusTwoPlaquetteOuterWalk_support]
  exact List.mem_toFinset.mpr hx

end TNLean.PEPS
