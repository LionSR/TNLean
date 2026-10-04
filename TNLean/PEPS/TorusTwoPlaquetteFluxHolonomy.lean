/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusPlaquetteFluxMeasurement
import TNLean.PEPS.RegularTwoCycleFluxMove
import TNLean.PEPS.TwoPlaquetteGeometry
import TNLean.PEPS.TorusTranslatedFluxMove

/-!
# Plaquette holonomies of a native local flux movement

The two insertion bonds of the six-site rectangle are ordered upward. The
positively oriented plaquette walk traverses the middle bond upward and the
left bond downward. Extending the insertion from the left bond to both bonds
therefore removes the left plaquette holonomy and transfers the same holonomy
to the right plaquette. These identities concern the literal native bond
assignments used by the fixed physical unitary, rather than prescribed
holonomy hypotheses.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Theorem 6.16,
local source lines 2270–2301.

**Scope restriction (native two-plaquette rectangle):** The results concern
this six-site rectangle on a finite torus of width at least four and height
at least three. They give the endpoint interpretation of the local operation,
not the unrestricted lattice statement. See
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (3 < width)] [Fact (2 < height)]
local instance twoPlaquetteHolonomyWidthGtTwo : Fact (2 < width) :=
  ⟨by have := Fact.out (p := 3 < width); omega⟩
local instance twoPlaquetteHolonomyWidthGtOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 3 < width); omega⟩
local instance twoPlaquetteHolonomyHeightGtOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 2 < height); omega⟩
variable {G : Type*} [Group G]
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height

/-- The initial or extended string on the two upward vertical bonds at horizontal
coordinates zero and one. Source: SCP10, Theorem 6.16, lines 2270–2301. -/
def torusTwoPlaquetteFluxAssignment (extend : Bool) (g : G) (e : Edge Γₜ) : G :=
  if e = Edge.ofAdj (torusGraph_adj_up (0 : ZMod width) (0 : ZMod height)) ∨
    (extend = true ∧ e = Edge.ofAdj (torusGraph_adj_up (1 : ZMod width) (0 : ZMod height)))
  then g else 1

private theorem small_coords_lt {x y : ℕ} (_hx : x < 3) (hy : y < 2) :
    ((x : ZMod width), (y : ZMod height)) < ((x : ZMod width), ((y + 1 : ℕ) : ZMod height)) := by
  have hw := Fact.out (p := 3 < width)
  have hh := Fact.out (p := 2 < height)
  change toLex ((x : ZMod width).val, (y : ZMod height).val) <
    toLex ((x : ZMod width).val, ((y+1 : ℕ) : ZMod height).val)
  rw [Prod.Lex.toLex_lt_toLex]
  right
  constructor
  · rfl
  · rw [ZMod.val_natCast_of_lt (show y < height by omega),
      ZMod.val_natCast_of_lt (show y+1 < height by omega)]
    omega

/-- The actual initial holonomies are `(g⁻¹, 1)`, and the extended holonomies are
`(1, g⁻¹)`, for the counterclockwise native walks. Source: SCP10, Theorem 6.16. -/
theorem torusTwoPlaquetteFluxAssignment_holonomy (extend : Bool) (g : G) :
    regularWalkHolonomy (torusTwoPlaquetteFluxAssignment (width := width) (height := height)
      extend g)
      (torusPlaquetteWalk (0 : X)) = (if extend then 1 else g⁻¹) ∧
    regularWalkHolonomy (torusTwoPlaquetteFluxAssignment (width := width) (height := height)
      extend g)
      (torusPlaquetteWalk ((1 : ZMod width), 0)) = (if extend then g⁻¹ else 1) := by
  classical
  have hs : torusTwoPlaquetteFluxAssignment (width := width) (height := height) extend g =
      torusTranslatedFluxAssignment (0 : X) extend g := by
    have hlt : ((0 : ZMod width), (0 : ZMod height)) < (0, 1) := by
      simpa using small_coords_lt (width := width) (height := height)
        (x := 0) (y := 0) (by decide) (by decide)
    have ht := (torusTranslatedFluxAssignment_up_transport (0 : X) extend g).1
    simp only [regularDirectedTransport, Prod.fst_zero, Prod.snd_zero, zero_add,
      ite_eq_left hlt] at ht
    simp only [torusTranslatedFluxAssignment, Prod.fst_zero, Prod.snd_zero, zero_add,
      eq_self, true_or, ite_true] at ht
    funext e
    simp only [torusTwoPlaquetteFluxAssignment, torusTranslatedFluxAssignment,
      Prod.fst_zero, Prod.snd_zero, zero_add, ht]
  have h := regularWalkHolonomy_torusTranslatedFluxAssignment (0 : X) extend g
  rw [← hs] at h
  have hbase : ((0 : X).1 + 1, (0 : X).2) = ((1 : ZMod width), 0) := by
    ext <;> simp
  rw [hbase] at h
  exact h

/-- The literal two vertical-bond insertion is precisely the native tree-cycle
assignment in the physical operation. Source: SCP10, Theorem 6.16. -/
theorem torusTwoPlaquetteFluxAssignment_eq_treeCycleAssignment
    (extend : Bool) (g : G) :
    torusTwoPlaquetteFluxAssignment (width := width) (height := height) extend g =
      regularTreeCycleAssignment twoPlaquetteTorusRegion twoPlaquetteTorusTree
        (fun e => if e = twoPlaquetteTorusCycleBond 0 ∨
          (extend = true ∧ e = twoPlaquetteTorusCycleBond 1) then g else 1) := by
  classical
  have hedge (i : Fin 2) :
      (twoPlaquetteTorusCycleBond (width := width) (height := height) i).1.1 =
        Edge.ofAdj (torusGraph_adj_up (i.val : ZMod width) (0 : ZMod height)) := by
    have hlt : ((i.val : ZMod width), (0 : ZMod height)) < ((i.val : ZMod width), 1) := by
      simpa using small_coords_lt (width := width) (height := height)
        (x := i.val) (y := 0) (by omega) (by decide)
    rw [Edge.ofAdj_of_lt (torusGraph_adj_up (i.val : ZMod width)
      (0 : ZMod height)) (by simpa only [zero_add] using hlt)]
    simpa only [zero_add] using Subtype.ext (Prod.ext
      (twoPlaquetteTorusCycleBond_endpoints i).1
      (twoPlaquetteTorusCycleBond_endpoints i).2)
  rw [regularTreeCycleAssignment_twoSupport]
  funext e
  simp [hedge, torusTwoPlaquetteFluxAssignment]

/-- The same actual tree-cycle assignments used by the unitary operation move
one plaquette holonomy one step to the right. Source: SCP10, Theorem 6.16. -/
theorem regularWalkHolonomy_twoPlaquetteTreeCycleAssignment
    (extend : Bool) (g : G) :
    let u := regularTreeCycleAssignment
      (twoPlaquetteTorusRegion (width := width) (height := height)) twoPlaquetteTorusTree
      (fun e => if e = twoPlaquetteTorusCycleBond 0 ∨
        (extend = true ∧ e = twoPlaquetteTorusCycleBond 1) then g else 1)
    regularWalkHolonomy u (torusPlaquetteWalk (0 : X)) = (if extend then 1 else g⁻¹) ∧
      regularWalkHolonomy u (torusPlaquetteWalk ((1 : ZMod width), 0)) =
        (if extend then g⁻¹ else 1) := by
  dsimp only
  rw [← torusTwoPlaquetteFluxAssignment_eq_treeCycleAssignment]
  exact torusTwoPlaquetteFluxAssignment_holonomy extend g
end TNLean.PEPS
