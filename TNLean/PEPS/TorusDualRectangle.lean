/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusDualHomotopy

/-!
# Finite rectangular dual patches

A bottom-row and vertical-column comb normalizes labelled unit-step paths.
Source: SCP10, arXiv:1001.3807v3, Lemma 6.14, lines 2199–2214.

**Scope restriction (embedded finite rectangles):** This is the finite bulk
case of string deformation, not arbitrary-region avoidance or equality across
winding classes. See `docs/paper-gaps/scp10_dual_flux_string_deformation.tex`.
-/

namespace TNLean.PEPS

variable {width height : ℕ}
local notation "X" => TorusVertex width height
local instance : Quiver X := torusDualQuiver width height

/-- A common initial path can be cancelled using elementary backtracks. -/
theorem TorusDualHomotopy.cancel_prefix {R : Set X} {r a b : X}
    (c : TorusDualPath r a) {p q : TorusDualPath a b}
    (h : TorusDualHomotopy R (c.comp p) (c.comp q)) : TorusDualHomotopy R p q := by
  have hc := TorusDualHomotopy.cancel_reverse R c.reverse
  simp only [Quiver.Path.reverse_reverse] at hc
  have hp := hc.comp (TorusDualHomotopy.refl p)
  have hq := hc.comp (TorusDualHomotopy.refl q)
  have hh := (TorusDualHomotopy.refl c.reverse).comp h
  rw [Quiver.Path.comp_assoc, Quiver.Path.nil_comp] at hp hq
  exact hp.symm.trans (hh.trans hq)

/-- Reverse an edge in a comb-edge identity by cancelling its backtrack. -/
theorem TorusDualHomotopy.reverse_edge {R : Set X} {r a b : X}
    {p : TorusDualPath r a} {q : TorusDualPath r b} (e : TorusDualStep a b)
    (h : TorusDualHomotopy R (p.cons e) q) :
    TorusDualHomotopy R (q.cons e.reverse) p := by
  have hh := h.symm.comp (TorusDualHomotopy.refl (Quiver.Hom.toPath e.reverse))
  exact hh.trans ((TorusDualHomotopy.refl p).comp (.backtrack e))

/-- Coordinates in the lifted nonnegative quadrant, translated by an arbitrary origin. -/
def torusRectCoord {n : ℕ} (x : ZMod n) : ℕ → ZMod n
  | 0 => x
  | i + 1 => torusRectCoord x i + 1

/-- The recursive coordinates are the usual translated integer coordinates. -/
theorem torusRectCoord_eq {n : ℕ} (x : ZMod n) (i : ℕ) :
    torusRectCoord x i = x + i := by
  induction i with
  | zero => simp [torusRectCoord]
  | succ i ih => simp [torusRectCoord, ih, Nat.cast_add, add_assoc]

/-- No two lifted coordinates below one period are identified. -/
theorem torusRectCoord_injective {n W : ℕ} (x : ZMod n) (hW : W < n)
    {i j : ℕ} (hi : i ≤ W) (hj : j ≤ W)
    (h : torusRectCoord x i = torusRectCoord x j) : i = j := by
  simp only [torusRectCoord_eq, add_left_cancel_iff] at h
  have hv := congrArg ZMod.val h
  simpa only [ZMod.val_natCast_of_lt (lt_of_le_of_lt hi hW),
    ZMod.val_natCast_of_lt (lt_of_le_of_lt hj hW)] using hv

/-- The upward column at a fixed horizontal coordinate. -/
def torusRectColumn (x : ZMod width) (y : ZMod height) :
    (j : ℕ) → TorusDualPath (x, y) (x, torusRectCoord y j)
  | 0 => .nil
  | j + 1 => (torusRectColumn x y j).cons (.north x (torusRectCoord y j))

/-- The bottom row followed by the column through the target vertex. -/
def torusRectComb (x : ZMod width) (y : ZMod height) :
    (i j : ℕ) → TorusDualPath (x, y) (torusRectCoord x i, torusRectCoord y j)
  | 0, j => torusRectColumn x y j
  | i + 1, j =>
    ((torusRectComb x y i 0).cons (.east (torusRectCoord x i) y)).comp
      (torusRectColumn (torusRectCoord x (i + 1)) y j)

/-- Interchange a column and its final east edge by sweeping exactly its adjacent squares. -/
theorem torusRectColumn_east (R : Set X) (x : ZMod width) (y : ZMod height)
    (j : ℕ) (hs : ∀ k < j, (x + 1, torusRectCoord y (k + 1)) ∈ R) :
    TorusDualHomotopy R
      ((torusRectColumn x y j).cons (.east x (torusRectCoord y j)))
      ((Quiver.Hom.toPath (TorusDualStep.east x y)).comp (torusRectColumn (x + 1) y j)) := by
  induction j with
  | zero => exact .refl _
  | succ j ih =>
    have hsq := (TorusDualHomotopy.refl (torusRectColumn x y j)).comp
      (TorusDualHomotopy.square x (torusRectCoord y j) (hs j (Nat.lt_succ_self j))).symm
    have hh := (ih (fun k hk => hs k (Nat.lt_succ_of_lt hk))).comp
      (TorusDualHomotopy.refl
        (Quiver.Hom.toPath (TorusDualStep.north (x + 1) (torusRectCoord y j))))
    exact hsq.trans hh

/-- Appending a north edge stays on the chosen column. -/
theorem torusRectComb_north (x : ZMod width) (y : ZMod height) (i j : ℕ) :
    (torusRectComb x y i j).cons
        (.north (torusRectCoord x i) (torusRectCoord y j)) =
      torusRectComb x y i (j + 1) := by
  cases i <;> rfl

/-- Appending an east edge is reduced to the comb by adjacent square moves. -/
theorem torusRectComb_east (R : Set X) (x : ZMod width) (y : ZMod height)
    (i j : ℕ) (hs : ∀ k < j,
      (torusRectCoord x (i + 1), torusRectCoord y (k + 1)) ∈ R) :
    TorusDualHomotopy R
      ((torusRectComb x y i j).cons
        (.east (torusRectCoord x i) (torusRectCoord y j)))
      (torusRectComb x y (i + 1) j) := by
  have hc : torusRectComb x y i j =
      (torusRectComb x y i 0).comp (torusRectColumn (torusRectCoord x i) y j) := by
    cases i with
    | zero => simp [torusRectComb, torusRectColumn, torusRectCoord]
    | succ i => rfl
  rw [hc]
  simpa only [torusRectComb, Quiver.Path.comp_assoc, Quiver.Path.comp_cons,
    Quiver.Path.comp_nil, Quiver.Hom.toPath, torusRectCoord] using
    (TorusDualHomotopy.refl (torusRectComb x y i 0)).comp
      (torusRectColumn_east R (torusRectCoord x i) y j hs)

/-- Labelled unit steps in the lifted closed rectangle `[0,W] × [0,H]`.
Distinct direction constructors retain the edge labels after projection to a torus. -/
inductive RectDualStep (W H : ℕ) : ℕ × ℕ → ℕ × ℕ → Type
  | east (i j : ℕ) (hi : i < W) (hj : j ≤ H) :
      RectDualStep W H (i, j) (i + 1, j)
  | west (i j : ℕ) (hi : i < W) (hj : j ≤ H) :
      RectDualStep W H (i + 1, j) (i, j)
  | north (i j : ℕ) (hi : i ≤ W) (hj : j < H) :
      RectDualStep W H (i, j) (i, j + 1)
  | south (i j : ℕ) (hi : i ≤ W) (hj : j < H) :
      RectDualStep W H (i, j + 1) (i, j)

/-- The finite rectangle's labelled step quiver, with isolated vertices outside it. -/
@[instance_reducible]
def rectDualQuiver (W H : ℕ) : Quiver (ℕ × ℕ) where
  Hom := RectDualStep W H

/-- Project a labelled lifted edge to its actual torus edge. -/
def RectDualStep.toTorus {W H : ℕ} (x : ZMod width) (y : ZMod height)
    {a b : ℕ × ℕ} (e : RectDualStep W H a b) :
    TorusDualStep (torusRectCoord x a.1, torusRectCoord y a.2)
      (torusRectCoord x b.1, torusRectCoord y b.2) :=
  match e with
  | .east i j _ _ => .east (torusRectCoord x i) (torusRectCoord y j)
  | .west i j _ _ => .west (torusRectCoord x i) (torusRectCoord y j)
  | .north i j _ _ => .north (torusRectCoord x i) (torusRectCoord y j)
  | .south i j _ _ => .south (torusRectCoord x i) (torusRectCoord y j)

/-- The swept primal sites are precisely the interiors of the dual unit squares. -/
def torusRectInterior (x : ZMod width) (y : ZMod height) (W H : ℕ) : Set X :=
  {v | ∃ i < W, ∃ j < H,
    v = (torusRectCoord x (i + 1), torusRectCoord y (j + 1))}

/-- Each of the four labelled edges satisfies the rooted comb identity. -/
theorem RectDualStep.comb {W H : ℕ} (x : ZMod width) (y : ZMod height)
    {a b : ℕ × ℕ} (e : RectDualStep W H a b) :
    TorusDualHomotopy (torusRectInterior x y W H)
      ((torusRectComb x y a.1 a.2).cons (e.toTorus x y))
      (torusRectComb x y b.1 b.2) := by
  have he (i j : ℕ) (hi : i < W) (hj : j ≤ H) :=
    torusRectComb_east (torusRectInterior x y W H) x y i j
      (fun k hk => ⟨i, hi, k, lt_of_lt_of_le hk hj, rfl⟩)
  cases e with
  | east i j hi hj => exact he i j hi hj
  | west i j hi hj => exact TorusDualHomotopy.reverse_edge _ (he i j hi hj)
  | north i j _hi _hj =>
    change TorusDualHomotopy _
      ((torusRectComb x y i j).cons
        (TorusDualStep.north (torusRectCoord x i) (torusRectCoord y j))) _
    rw [torusRectComb_north]
    exact .refl _
  | south i j _hi _hj =>
    apply TorusDualHomotopy.reverse_edge (.north (torusRectCoord x i) (torusRectCoord y j))
    rw [torusRectComb_north]
    exact .refl _

section Paths

variable {W H : ℕ}

/-- Projection of the lifted rectangle preserves the four direction labels. -/
def rectDualToTorus (x : ZMod width) (y : ZMod height) :
    @Prefunctor (ℕ × ℕ) (rectDualQuiver W H) X (torusDualQuiver width height) := by
  letI : Quiver (ℕ × ℕ) := rectDualQuiver W H
  exact { obj := fun a => (torusRectCoord x a.1, torusRectCoord y a.2)
          map := fun e => e.toTorus x y }

/-- Mathlib path projection with the rectangle quiver supplied explicitly.
Its dimensions cannot be recovered from the ambient type `ℕ × ℕ` alone. -/
abbrev rectDualPathToTorus (x : ZMod width) (y : ZMod height)
    {a b : ℕ × ℕ} (p : @Quiver.Path (ℕ × ℕ) (rectDualQuiver W H) a b) :
    TorusDualPath (torusRectCoord x a.1, torusRectCoord y a.2)
      (torusRectCoord x b.1, torusRectCoord y b.2) :=
  @Prefunctor.mapPath (ℕ × ℕ) (rectDualQuiver W H) X (torusDualQuiver width height)
    (rectDualToTorus x y) a b p

/-- Induction on an arbitrary labelled path reduces it to the rooted comb. -/
theorem rectDualPath_comb (x : ZMod width) (y : ZMod height)
    {a b : ℕ × ℕ} (p : @Quiver.Path (ℕ × ℕ) (rectDualQuiver W H) a b) :
    TorusDualHomotopy (torusRectInterior x y W H)
      ((torusRectComb x y a.1 a.2).comp (rectDualPathToTorus x y p))
      (torusRectComb x y b.1 b.2) := by
  induction p with
  | nil => exact .refl _
  | cons p e ih =>
    exact (ih.comp (.refl (Quiver.Hom.toPath (e.toTorus x y)))).trans (e.comb x y)

/-- Any two labelled unit-step paths in a finite rectangle with the same lifted
endpoints are related by supported squares and backtracks. No supplied homotopy,
gauge, or equality of crossing counts is assumed. Source: the finite rectangular
bulk case of SCP10, Lemma 6.14. -/
theorem rectDualPath_homotopy (x : ZMod width) (y : ZMod height)
    {a b : ℕ × ℕ} (p q : @Quiver.Path (ℕ × ℕ) (rectDualQuiver W H) a b) :
    TorusDualHomotopy (torusRectInterior x y W H)
      (rectDualPathToTorus x y p) (rectDualPathToTorus x y q) := by
  exact TorusDualHomotopy.cancel_prefix (torusRectComb x y a.1 a.2)
    ((rectDualPath_comb x y p).trans (rectDualPath_comb x y q).symm)

/-- An explicitly embedded finite rectangular patch. The side bounds forbid
identifying distinct lifted vertices through a periodic seam. -/
structure TorusDualRectangle (width height : ℕ) where
  /-- Lower-left dual plaquette. -/
  origin : TorusVertex width height
  /-- Horizontal number of unit squares. -/
  cols : ℕ
  /-- Vertical number of unit squares. -/
  rows : ℕ
  /-- The closed horizontal interval fits strictly within a period. -/
  cols_lt : cols < width
  /-- The closed vertical interval fits strictly within a period. -/
  rows_lt : rows < height

/-- The patch projection is injective on its closed lifted rectangle. -/
theorem TorusDualRectangle.injective (P : TorusDualRectangle width height)
    {a b : ℕ × ℕ} (ha : a.1 ≤ P.cols ∧ a.2 ≤ P.rows)
    (hb : b.1 ≤ P.cols ∧ b.2 ≤ P.rows)
    (he : (torusRectCoord P.origin.1 a.1, torusRectCoord P.origin.2 a.2) =
      (torusRectCoord P.origin.1 b.1, torusRectCoord P.origin.2 b.2)) : a = b := by
  exact Prod.ext
    (torusRectCoord_injective P.origin.1 P.cols_lt ha.1 hb.1 (congrArg Prod.fst he))
    (torusRectCoord_injective P.origin.2 P.rows_lt ha.2 hb.2 (congrArg Prod.snd he))

/-- The embedded finite-bulk homotopy theorem. Both paths have the same lifted
endpoints; equality of periodic endpoints alone is not a hypothesis. -/
theorem TorusDualRectangle.homotopy (P : TorusDualRectangle width height)
    {a b : ℕ × ℕ}
    (p q : @Quiver.Path (ℕ × ℕ) (rectDualQuiver P.cols P.rows) a b) :
    TorusDualHomotopy (torusRectInterior P.origin.1 P.origin.2 P.cols P.rows)
      (rectDualPathToTorus P.origin.1 P.origin.2 p)
      (rectDualPathToTorus P.origin.1 P.origin.2 q) :=
  rectDualPath_homotopy P.origin.1 P.origin.2 p q

end Paths

end TNLean.PEPS
