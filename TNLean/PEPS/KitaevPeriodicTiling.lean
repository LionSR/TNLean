/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.KitaevCheckerboardBlocking
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Disjoint periodic checkerboard tiling

The fine torus has twice each coarse period. Its sites are exactly the coarse
sites paired with one of the four clockwise corners. The coordinate equivalence
also respects the actual horizontal and vertical nearest-neighbor steps.
Source: SCP10, arXiv:1001.3807, Section 7.1, lines 2755–2827.
-/

noncomputable section
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
local notation "TV" => TorusVertex width height

/-- Clockwise corner coordinates, starting at the upper-right corner.
Source: SCP10, four-site checkerboard diagram, lines 2755–2794. -/
def kitaevCornerEquiv : Fin 4 ≃ Fin 2 × Fin 2 :=
  Equiv.ofBijective ![(1, 1), (1, 0), (0, 0), (0, 1)] (by decide)

/-- Division into pairs identifies a coarse periodic coordinate and a binary
corner coordinate with a fine periodic coordinate. -/
def kitaevDoubleCoordinateEquiv (n : ℕ) [NeZero n] :
    ZMod n × Fin 2 ≃ ZMod (n * 2) :=
  ((ZMod.finEquiv n).toEquiv.symm.prodCongr (Equiv.refl (Fin 2))).trans
    (finProdFinEquiv.trans (ZMod.finEquiv (n * 2)).toEquiv)

/-- The disjoint 2×2 blocks cover the torus with both periods doubled.
The corner order agrees with the source's checkerboard contraction. This is an
actual bijection, with no separately supplied covering or disjointness premise.
Source: SCP10, Section 7.1, lines 2755–2827. -/
def kitaevPeriodicTilingEquiv : TV × Fin 4 ≃ TorusVertex (width * 2) (height * 2) :=
  ((Equiv.refl TV).prodCongr kitaevCornerEquiv).trans
    ((Equiv.prodProdProdComm (ZMod width) (ZMod height) (Fin 2) (Fin 2)).trans
      ((kitaevDoubleCoordinateEquiv width).prodCongr
        (kitaevDoubleCoordinateEquiv height)))

/-- Explicit fine coordinate of a point in a two-site block. -/
theorem kitaevDoubleCoordinateEquiv_apply (n : ℕ) [NeZero n] (x : ZMod n) (b : Fin 2) :
    kitaevDoubleCoordinateEquiv n (x, b) = ((b.val + 2 * x.val : ℕ) : ZMod (n * 2)) := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    apply Fin.ext
    change b.val + 2 * x.val = (b.val + 2 * x.val) % ((n + 1) * 2)
    rw [Nat.mod_eq_of_lt]
    have hx := ZMod.val_lt x
    have hb := b.isLt
    omega

private theorem doubleCoordinate_step_zero (n : ℕ) [NeZero n] (x : ZMod n) :
    kitaevDoubleCoordinateEquiv n (x, 0) + 1 = kitaevDoubleCoordinateEquiv n (x, 1) := by
  simp only [kitaevDoubleCoordinateEquiv_apply, Fin.val_zero, Fin.val_one,
    Nat.cast_add, Nat.cast_one, zero_add]
  ring

private theorem doubleCoordinate_step_one (n : ℕ) [NeZero n] (x : ZMod n) :
    kitaevDoubleCoordinateEquiv n (x, 1) + 1 = kitaevDoubleCoordinateEquiv n (x + 1, 0) := by
  have hval : (x + 1).val = (x.val + 1) % n := by
    conv_lhs => rw [← ZMod.natCast_zmod_val x, ← Nat.cast_one, ← Nat.cast_add]
    exact ZMod.val_natCast _ _
  rw [kitaevDoubleCoordinateEquiv_apply, kitaevDoubleCoordinateEquiv_apply, hval]
  simp only [Fin.val_zero, Fin.val_one, zero_add]
  by_cases h : x.val + 1 < n
  · rw [Nat.mod_eq_of_lt h]
    push_cast
    ring
  · have heq : x.val + 1 = n := by have := ZMod.val_lt x; omega
    rw [heq, Nat.mod_self, mul_zero, Nat.cast_zero]
    calc
      ((1 + 2 * x.val : ℕ) : ZMod (n * 2)) + 1 =
          ((2 * (x.val + 1) : ℕ) : ZMod (n * 2)) := by push_cast; ring
      _ = 0 := by rw [heq, mul_comm]; exact ZMod.natCast_self _

/-- The right neighbor in the periodic four-corner tiling. -/
def kitaevTiledRight (p : TV × Fin 4) : TV × Fin 4 :=
  ![((p.1.1 + 1, p.1.2), 3), ((p.1.1 + 1, p.1.2), 2),
    (p.1, 1), (p.1, 0)] p.2

/-- The upper neighbor in the periodic four-corner tiling. -/
def kitaevTiledUp (p : TV × Fin 4) : TV × Fin 4 :=
  ![((p.1.1, p.1.2 + 1), 1), (p.1, 0), (p.1, 3),
    ((p.1.1, p.1.2 + 1), 2)] p.2

/-- The tiling's horizontal steps are the fine torus's actual nearest-neighbor
steps, including wraparound. -/
theorem kitaevPeriodicTilingEquiv_right (p : TV × Fin 4) :
    kitaevPeriodicTilingEquiv (kitaevTiledRight p) =
      ((kitaevPeriodicTilingEquiv p).1 + 1, (kitaevPeriodicTilingEquiv p).2) := by
  rcases p with ⟨v, i⟩
  fin_cases i <;>
    simp [kitaevPeriodicTilingEquiv, kitaevCornerEquiv, kitaevTiledRight,
      ← doubleCoordinate_step_zero, ← doubleCoordinate_step_one]

/-- The tiling's vertical steps are the fine torus's actual nearest-neighbor
steps, including wraparound. -/
theorem kitaevPeriodicTilingEquiv_up (p : TV × Fin 4) :
    kitaevPeriodicTilingEquiv (kitaevTiledUp p) =
      ((kitaevPeriodicTilingEquiv p).1, (kitaevPeriodicTilingEquiv p).2 + 1) := by
  rcases p with ⟨v, i⟩
  fin_cases i <;>
    simp [kitaevPeriodicTilingEquiv, kitaevCornerEquiv, kitaevTiledUp,
      ← doubleCoordinate_step_zero, ← doubleCoordinate_step_one]

/-- The left neighbor in the periodic four-corner tiling. -/
def kitaevTiledLeft (p : TV × Fin 4) : TV × Fin 4 :=
  ![(p.1, 3), (p.1, 2), ((p.1.1 - 1, p.1.2), 1),
    ((p.1.1 - 1, p.1.2), 0)] p.2

/-- The lower neighbor in the periodic four-corner tiling. -/
def kitaevTiledDown (p : TV × Fin 4) : TV × Fin 4 :=
  ![(p.1, 1), ((p.1.1, p.1.2 - 1), 0),
    ((p.1.1, p.1.2 - 1), 3), (p.1, 2)] p.2

omit [NeZero width] [NeZero height] in
/-- Left and right tile steps are inverses. -/
theorem kitaevTiledRight_left (p : TV × Fin 4) :
    kitaevTiledRight (kitaevTiledLeft p) = p := by
  rcases p with ⟨v, i⟩
  fin_cases i <;> simp [kitaevTiledRight, kitaevTiledLeft]

omit [NeZero width] [NeZero height] in
/-- Down and up tile steps are inverses. -/
theorem kitaevTiledUp_down (p : TV × Fin 4) :
    kitaevTiledUp (kitaevTiledDown p) = p := by
  rcases p with ⟨v, i⟩
  fin_cases i <;> simp [kitaevTiledUp, kitaevTiledDown]

/-- Left tile steps include the correct fine-torus wraparound. -/
theorem kitaevPeriodicTilingEquiv_left (p : TV × Fin 4) :
    kitaevPeriodicTilingEquiv (kitaevTiledLeft p) =
      ((kitaevPeriodicTilingEquiv p).1 - 1, (kitaevPeriodicTilingEquiv p).2) := by
  have h := kitaevPeriodicTilingEquiv_right (kitaevTiledLeft p)
  rw [kitaevTiledRight_left] at h
  exact Prod.ext (eq_sub_of_add_eq (congrArg Prod.fst h).symm)
    (congrArg Prod.snd h).symm

/-- Lower tile steps include the correct fine-torus wraparound. -/
theorem kitaevPeriodicTilingEquiv_down (p : TV × Fin 4) :
    kitaevPeriodicTilingEquiv (kitaevTiledDown p) =
      ((kitaevPeriodicTilingEquiv p).1, (kitaevPeriodicTilingEquiv p).2 - 1) := by
  have h := kitaevPeriodicTilingEquiv_up (kitaevTiledDown p)
  rw [kitaevTiledUp_down] at h
  exact Prod.ext (congrArg Prod.fst h).symm
    (eq_sub_of_add_eq (congrArg Prod.snd h).symm)

end TNLean.PEPS
