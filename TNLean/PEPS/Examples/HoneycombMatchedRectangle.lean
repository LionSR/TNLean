/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Examples.HoneycombCorner

/-! Nonwrapping rectangles of vertical pairs along the two downward diagonal axes. -/

namespace TNLean.PEPS.HoneycombCorner
variable {W H : ℕ} [NeZero W] [NeZero H] [Fact (1 < W)] [Fact (1 < H)]

def point (x y i j k : ℕ) : TorusVertex W H := (↑(x+i-j), ↑(y-(i+j)+k))

def region (x y m n : ℕ) : Finset (TorusVertex W H) :=
  (((Finset.range (m+1)).product (Finset.range (n+1))).product (Finset.range 2)).image
    fun p => point x y p.1.1 p.1.2 p.2

omit [NeZero W] [NeZero H] in
theorem vertical_pair {x y m n i j : ℕ} (hx : n ≤ x) (hw : x+m < W)
    (hy : m+n ≤ y) (hh : y+1 < H) (hp : (x+y)%2 = 0) (hi : i ≤ m) (hj : j ≤ n) :
    (honeycombGraph W H).Adj (point x y i j 0) (point x y i j 1) := by
  apply Or.inr
  refine ⟨rfl, Or.inl ⟨?_,?_⟩⟩
  · simp [point]
  · change (((↑(x+i-j) : ZMod W).val + (↑(y-(i+j)+0) : ZMod H).val) % 2 = 0)
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt (show x+i-j < W by omega),
      Nat.mod_eq_of_lt (show y-(i+j)+0 < H by omega)]
    omega

theorem rectangle_obstruction {x y m n : ℕ} (hx : n ≤ x) (hw : x+m < W)
    (hy : m+n ≤ y) (hh : y+1 < H) (left : 0 < x) (right : x+1 < W) :
    ¬ Function.Injective (openRegionMap (honeycombClusterPEPS W H) (region x y m n)) := by
  let v : TorusVertex W H := (↑x, ↑(y+1))
  have top {t : ℕ} (ht : t < W) (hm : ((↑t, ↑(y+1)) : TorusVertex W H) ∈ region x y m n) :
      t = x := by
    obtain ⟨⟨⟨i,j⟩,k⟩, mem, eq⟩ := Finset.mem_image.mp hm
    change ((i,j),k) ∈ ((Finset.range (m+1)).product (Finset.range (n+1))).product (Finset.range 2) at mem
    obtain ⟨hij,hk⟩ := Finset.mem_product.mp mem
    obtain ⟨hi,hj⟩ := Finset.mem_product.mp hij
    have hi2 := Finset.mem_range.mp hi
    have hj2 := Finset.mem_range.mp hj
    have hk2 := Finset.mem_range.mp hk
    change i < m+1 at hi2
    change j < n+1 at hj2
    change k < 2 at hk2
    have ey := congrArg (fun z : TorusVertex W H => z.2.val) eq
    have ex := congrArg (fun z : TorusVertex W H => z.1.val) eq
    change (↑(y-(i+j)+k) : ZMod H).val = (↑(y+1) : ZMod H).val at ey
    change (↑(x+i-j) : ZMod W).val = (↑t : ZMod W).val at ex
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hh,
      Nat.mod_eq_of_lt (show y-(i+j)+k < H by omega)] at ey
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt ht,
      Nat.mod_eq_of_lt (show x+i-j < W by omega)] at ex
    omega
  have hv : v ∈ region x y m n := Finset.mem_image.mpr ⟨((0,0),1), by simp, by simp [point,v]⟩
  have l : (((x-1 : ℕ) : ZMod W), v.2) ∉ region x y m n := fun h => by
    have := top (t := x-1) (by omega) h
    omega
  have r : (((x+1 : ℕ) : ZMod W), v.2) ∉ region x y m n := fun h => by
    have := top right h
    omega
  apply obstruction hv l r
  · intro eq
    have e := congrArg (fun z : TorusVertex W H => z.1.val) eq
    change (↑(x-1) : ZMod W).val = (↑(x+1) : ZMod W).val at e
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt right, Nat.mod_eq_of_lt (show x-1<W by omega)] at e
    omega
  · apply Or.inl
    refine ⟨rfl, Or.inr ?_⟩
    change (↑x : ZMod W) = ↑(x-1) + 1
    rw [← Nat.cast_succ, show (x-1).succ=x by omega]
  · exact Or.inl ⟨rfl, Or.inl (by simp [v])⟩

end TNLean.PEPS.HoneycombCorner

namespace TNLean.PEPS.HoneycombCorner
private instance : Fact (1 < 4) := ⟨by decide⟩
example : ¬ Function.Injective (openRegionMap (honeycombClusterPEPS 4 4) (region 2 2 1 1)) :=
  rectangle_obstruction (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
example : ¬ ∃ x : ℕ, 0 < x ∧ x+1 < 2 := by omega
end TNLean.PEPS.HoneycombCorner
