/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Tactic.Group
import TNLean.PEPS.TorusSiteTensor

/-!
# Group-valued transports on the torus and their parallel sections

Let `G` be a group. Assign to every site `v` of the `width × height` torus two elements
`a v, b v ∈ G`, the transports from `v` to its right neighbour `v + (1, 0)` and to its upper
neighbour `v + (0, 1)`. A function `f` from the sites to `G` is a parallel section of these
transports if `f (v + (1, 0)) = a v * f v` and `f (v + (0, 1)) = b v * f v` for every `v`.

Parallel sections are unique up to right multiplication by one group element, and they exist
exactly when the transports are flat, `b (v + (1, 0)) * a v = a (v + (0, 1)) * b v` around every
elementary square, and have trivial holonomy around one row and one column, the two
non-contractible cycles of the torus. Hence the number of parallel sections is `|G|` or `0`.

This is the combinatorial core of the statement that on the torus the differences of plaquette
colorings of the dual quantum-double network are the Gauss-law configurations of trivial
holonomy, arXiv:1001.3807, Section "Examples", "The double models",
`Papers/1001.3807/paper_v3.tex` lines 2914–2923
(`TNLean.PEPS.stateCoeff_quantumDoubleDualPEPS`).

## Main definitions

* `TNLean.PEPS.zmodTransport`: the ordered product `c (k - 1) ⋯ c 1 * c 0` along a cycle.
* `TNLean.PEPS.IsTorusParallelSection`: a parallel section of transports on the torus.
* `TNLean.PEPS.IsTorusFlat`: flatness of transports around every elementary square.

## Main results

* `TNLean.PEPS.IsTorusParallelSection.eq_mul_right`: uniqueness up to a right multiplication.
* `TNLean.PEPS.exists_isTorusParallelSection_iff`: existence exactly for flat transports with
  trivial holonomy around the row and the column through the origin.
* `TNLean.PEPS.card_isTorusParallelSection`: the number of parallel sections is `|G|` or `0`.
-/

open scoped BigOperators

namespace TNLean
namespace PEPS

variable {G : Type*} [Group G]

/-! ### Transport along a cycle -/

section Cycle

variable {n : ℕ}

/-- The transport along the first `k` steps of the cycle `ZMod n`, the ordered product
`c (k - 1) ⋯ c 1 * c 0`, where `c x` is the transport from `x` to `x + 1`. The holonomy around
the cycle is `zmodTransport c n`. -/
def zmodTransport (c : ZMod n → G) : ℕ → G
  | 0 => 1
  | k + 1 => c k * zmodTransport c k

@[simp] theorem zmodTransport_zero (c : ZMod n → G) : zmodTransport c 0 = 1 := rfl

theorem zmodTransport_succ (c : ZMod n → G) (k : ℕ) :
    zmodTransport c (k + 1) = c k * zmodTransport c k := rfl

/-- A function transported by `c` along the cycle is its value at `0` transported along the
first `k` steps. -/
theorem apply_natCast_eq_zmodTransport_mul (c f : ZMod n → G)
    (hf : ∀ x, f (x + 1) = c x * f x) (k : ℕ) :
    f k = zmodTransport c k * f 0 := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.cast_succ, hf, ih, zmodTransport_succ, mul_assoc]

/-- A function transported by `c` around the cycle forces trivial holonomy. -/
theorem zmodTransport_self_eq_one_of_apply_add_one (c f : ZMod n → G)
    (hf : ∀ x, f (x + 1) = c x * f x) : zmodTransport c n = 1 := by
  have h := apply_natCast_eq_zmodTransport_mul c f hf n
  rw [ZMod.natCast_self] at h
  exact (mul_eq_right.mp h.symm)

variable [NeZero n]

/-- For trivial holonomy, the transport to the representative of `x + 1` is one more step
than the transport to the representative of `x`, also when `x + 1` wraps around to `0`. -/
theorem zmodTransport_val_add_one {c : ZMod n → G} (hc : zmodTransport c n = 1)
    (x : ZMod n) : zmodTransport c (x + 1).val = c x * zmodTransport c x.val := by
  obtain ⟨k, hk, rfl⟩ : ∃ k < n, (k : ZMod n) = x := ⟨x.val, x.val_lt, ZMod.natCast_zmod_val x⟩
  rw [ZMod.val_natCast_of_lt hk, ← zmodTransport_succ, ← Nat.cast_succ]
  rcases Nat.lt_or_ge (k + 1) n with h | h
  · rw [ZMod.val_natCast_of_lt h]
  · have hkn : k + 1 = n := le_antisymm hk h
    rw [Nat.succ_eq_add_one, hkn, ZMod.natCast_self, ZMod.val_zero, zmodTransport_zero, hc]

end Cycle

/-! ### Parallel sections on the torus -/

variable {width height : ℕ}

/-- A function `f` from the sites of the torus to `G` is a parallel section of the horizontal
transports `a` and the vertical transports `b` if `f (x + 1, y) = a (x, y) * f (x, y)` and
`f (x, y + 1) = b (x, y) * f (x, y)` for every site. -/
def IsTorusParallelSection (a b f : TorusVertex width height → G) : Prop :=
  ∀ v : TorusVertex width height, f (v.1 + 1, v.2) = a v * f v ∧ f (v.1, v.2 + 1) = b v * f v

/-- The transports `a` and `b` are flat if around every elementary square the two paths from
`(x, y)` to `(x + 1, y + 1)` give the same transport,
`b (x + 1, y) * a (x, y) = a (x, y + 1) * b (x, y)`. -/
def IsTorusFlat (a b : TorusVertex width height → G) : Prop :=
  ∀ v : TorusVertex width height, b (v.1 + 1, v.2) * a v = a (v.1, v.2 + 1) * b v

variable {a b f : TorusVertex width height → G}

/-- Right multiplication by one group element maps parallel sections to parallel sections. -/
theorem IsTorusParallelSection.mul_right (hf : IsTorusParallelSection a b f) (g : G) :
    IsTorusParallelSection a b fun v => f v * g :=
  fun v => ⟨by simp only [(hf v).1, mul_assoc], by simp only [(hf v).2, mul_assoc]⟩

/-- The transports of a parallel section are flat. -/
theorem IsTorusParallelSection.isTorusFlat (hf : IsTorusParallelSection a b f) :
    IsTorusFlat a b := by
  intro v
  have h1 := (hf (v.1 + 1, v.2)).2
  have h2 := (hf (v.1, v.2 + 1)).1
  simp only at h1 h2
  rw [h2, (hf v).2, (hf v).1, ← mul_assoc, ← mul_assoc] at h1
  exact (mul_right_cancel h1).symm

/-- The transports of a parallel section have trivial holonomy around every row. -/
theorem IsTorusParallelSection.zmodTransport_row (hf : IsTorusParallelSection a b f)
    (y : ZMod height) : zmodTransport (fun x => a (x, y)) width = 1 :=
  zmodTransport_self_eq_one_of_apply_add_one _ (fun x => f (x, y)) fun x => (hf (x, y)).1

/-- The transports of a parallel section have trivial holonomy around every column. -/
theorem IsTorusParallelSection.zmodTransport_column (hf : IsTorusParallelSection a b f)
    (x : ZMod width) : zmodTransport (fun y => b (x, y)) height = 1 :=
  zmodTransport_self_eq_one_of_apply_add_one _ (fun y => f (x, y)) fun y => (hf (x, y)).2

/-- Flatness moves a vertical transport one column to the right, conjugated by the horizontal
transports at its two ends. -/
theorem IsTorusFlat.zmodTransport_column_mul (hab : IsTorusFlat a b) (x : ZMod width)
    (k : ℕ) :
    zmodTransport (fun y => b (x + 1, y)) k * a (x, 0) =
      a (x, k) * zmodTransport (fun y => b (x, y)) k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [zmodTransport_succ, zmodTransport_succ, mul_assoc, ih, ← mul_assoc, hab (x, k),
      Nat.cast_succ, mul_assoc]

variable [NeZero width] [NeZero height]

/-- Two parallel sections differ by right multiplication by one group element, fixed by their
values at the origin. -/
theorem IsTorusParallelSection.eq_mul_right {f' : TorusVertex width height → G}
    (hf : IsTorusParallelSection a b f) (hf' : IsTorusParallelSection a b f') :
    f' = fun v => f v * ((f 0)⁻¹ * f' 0) := by
  have key := torusVertex_apply_eq_apply_zero_of_shift (fun v => (f v)⁻¹ * f' v)
    (fun v => by simp only [(hf v).1, (hf' v).1]; group)
    (fun v => by simp only [(hf v).2, (hf' v).2]; group)
  funext v
  rw [← key v]
  group

omit [NeZero height] in
/-- For flat transports, trivial holonomy around one column gives trivial holonomy around every
column. -/
theorem IsTorusFlat.zmodTransport_column_eq_one (hab : IsTorusFlat a b)
    (h0 : zmodTransport (fun y => b (0, y)) height = 1) (x : ZMod width) :
    zmodTransport (fun y => b (x, y)) height = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, (k : ZMod width) = x := ⟨x.val, ZMod.natCast_zmod_val x⟩
  induction k with
  | zero => simpa using h0
  | succ k ih =>
    have h := hab.zmodTransport_column_mul (k : ZMod width) height
    rw [ih, mul_one, ZMod.natCast_self] at h
    rw [Nat.cast_succ]
    simpa using h

/-- Parallel sections exist exactly for flat transports with trivial holonomy around the row
and the column through the origin. A section is built by transporting along the row through the
origin and then up the columns. -/
theorem exists_isTorusParallelSection_iff :
    (∃ f, IsTorusParallelSection a b f) ↔
      IsTorusFlat a b ∧ zmodTransport (fun x => a (x, 0)) width = 1 ∧
        zmodTransport (fun y => b (0, y)) height = 1 := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨hf.isTorusFlat, hf.zmodTransport_row 0, hf.zmodTransport_column 0⟩
  · rintro ⟨hab, hrow, hcol⟩
    refine ⟨fun v => zmodTransport (fun y => b (v.1, y)) v.2.val *
      zmodTransport (fun x => a (x, 0)) v.1.val, fun v => ⟨?_, ?_⟩⟩
    · simp only
      rw [zmodTransport_val_add_one hrow, ← mul_assoc, hab.zmodTransport_column_mul,
        ZMod.natCast_zmod_val, mul_assoc]
    · simp only
      rw [zmodTransport_val_add_one (hab.zmodTransport_column_eq_one hcol v.1), mul_assoc]

open Classical in
/-- The number of parallel sections is `|G|` if there is one and `0` otherwise: they form one
orbit of the free action of `G` by right multiplication. -/
theorem card_isTorusParallelSection [Fintype G] (a b : TorusVertex width height → G) :
    Fintype.card {f // IsTorusParallelSection a b f} =
      if ∃ f, IsTorusParallelSection a b f then Fintype.card G else 0 := by
  split_ifs with h
  · obtain ⟨f₀, hf₀⟩ := h
    refine Fintype.card_congr
      { toFun := fun f => (f₀ 0)⁻¹ * f.1 0
        invFun := fun g => ⟨fun v => f₀ v * g, hf₀.mul_right g⟩
        left_inv := fun f => Subtype.ext (hf₀.eq_mul_right f.2).symm
        right_inv := fun g => by simp }
  · exact Fintype.card_eq_zero_iff.mpr ⟨fun f => h ⟨f.1, f.2⟩⟩

end PEPS
end TNLean
