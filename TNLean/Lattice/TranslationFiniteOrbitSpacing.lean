/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.TranslationSupercellSpacing

/-!
# Separated finite translation orbits

Suppose a lattice coordinate takes values in a circle of `n` cells, and one translation
advances it by one. If two sites initially have circular coordinate separation at most
`L/2`, then translation of the second by `kL` cells, for `1 ≤ k ≤ m`, separates them by at
least `L/2`, provided `2(m+1)L ≤ n`. This gives finitely many separated translates without
any assumption on ground-state momenta. It supplies the geometric step in the general
translation-invariant argument of Hastings, arXiv:cond-mat/0508554v3, lines 1644–1654.
-/

namespace TNLean.Lattice

/-- Every positive multiple up to `mL` carries a nearby coordinate at least `L/2` away.
Hastings, arXiv:cond-mat/0508554v3, lines 1644–1654. -/
theorem natAbs_valMinAbs_add_mul_ge_of_near {n L m : ℕ} [NeZero n]
    (hL : 0 < L) (hn : 2 * (m + 1) * L ≤ n)
    (a : ZMod n) (ha : a.valMinAbs.natAbs ≤ L / 2)
    {k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) :
    L / 2 ≤ (a + ((k * L : ℕ) : ZMod n)).valMinAbs.natAbs := by
  rw [ZMod.valMinAbs_natAbs_eq_min] at ha ⊢
  have hm : 2 * (m * L) + 2 * L ≤ n := by nlinarith only [hn]
  have hav := ZMod.val_lt a
  have hkl : L ≤ k * L := by nlinarith
  have hku : k * L ≤ m * L := Nat.mul_le_mul_right L hkm
  have hhalf : 2 * (L / 2) ≤ L := Nat.mul_div_le L 2
  have hval : (a + ((k * L : ℕ) : ZMod n)).val = (a.val + k * L) % n := by
    rw [ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod]
  rw [hval]
  rcases min_le_iff.mp ha with ha | ha
  · rw [Nat.mod_eq_of_lt (by nlinarith : a.val + k * L < n)]
    apply le_min <;> omega
  · have hge : n ≤ a.val + k * L := by omega
    have hlt : a.val + k * L - n < n := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt]
    apply le_min <;> omega

/-- The separated coordinates give graph separation for the same finite orbit.
Hastings, arXiv:cond-mat/0508554v3, lines 1644–1654. -/
theorem edist_pow_mul_ge_of_near {V Γ : Type*} [Group Γ] [MulAction Γ V]
    {n L m : ℕ} [NeZero n] (hL : 0 < L) (hn : 2 * (m + 1) * L ≤ n)
    (G : SimpleGraph V) (π : V → ZMod n)
    (hπ : ∀ u v, G.Adj u v → (π v - π u).valMinAbs.natAbs ≤ 1)
    (e : Γ) (he : ∀ v, π (e • v) = π v + 1) (x y : V)
    (hnear : (π y - π x).valMinAbs.natAbs ≤ L / 2)
    {k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) :
    ((L / 2 : ℕ) : ℕ∞) ≤ G.edist x (e ^ (k * L) • y) := by
  have hc := natAbs_valMinAbs_add_mul_ge_of_near hL hn (π y - π x) hnear hk hkm
  have hd := SimpleGraph.natAbs_valMinAbs_sub_le_edist (by decide : 0 < (1 : ℕ))
    π hπ x (e ^ (k * L) • y)
  rw [coordinate_pow_smul π e he] at hd
  have heq : π y - π x + ((k * L : ℕ) : ZMod n) =
      π y + ((k * L : ℕ) : ZMod n) - π x := by abel
  rw [heq] at hc
  simpa only [Nat.cast_one, one_mul] using (show
    ((L / 2 : ℕ) : ℕ∞) ≤
      ((π y + ((k * L : ℕ) : ZMod n) - π x).valMinAbs.natAbs : ℕ∞) by
        exact_mod_cast hc).trans hd

end TNLean.Lattice
