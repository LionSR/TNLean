/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Metric
import TNLean.Lattice.TranslationMomentum

/-!
# Supercell translations that carry a site far away

Hastings, *Solving gapped Hamiltonians locally* (arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 1620–1641), assumes that every momentum of a ground state is a rational multiple
`2πp/q` of `2π` whose denominator does not depend on the system size. Then translation by a
supercell of bounded size leaves every ground state unchanged, and such a translation can carry
any site to a distance of order the linear size of the system from any other site.

For a character this hypothesis reads `χ(g)^q = 1`. If it holds for every character with a
nonzero momentum sector, then every `q`-th power lies in the supercell
(`pow_mem_supercell`). On a ring of `n` sites, the rotations by multiples of `q` carry any site
`y` to distance more than `n / 2 - q` from any site `x` (`exists_lt_edist_add_cycleGraph`). So
some element of the supercell does this (`exists_mem_supercell_lt_edist_add`).

**Scope restriction (ring):** the source's system is a `d`-dimensional lattice (lines 1603–1612).
The geometric step here, that some supercell translation carries a site to distance of order the
linear size (`exists_lt_edist_add_cycleGraph`, `exists_mem_supercell_lt_edist_add`), is proved
for the rotations of a ring of sites, the one-dimensional case; `pow_mem_supercell` holds for any
abelian group. Documented in `docs/paper-gaps/hastings05_translation_supercell.tex`.

## Main results

* `TNLean.Lattice.pow_mem_supercell`: with momenta of denominator `q`, every `q`-th power lies in
  the supercell.
* `SimpleGraph.ringNorm_sub_le_edist_cycleGraph`: the graph distance on the ring is at least the
  circular distance `min(a, n - a)` of the displacement `a`.
* `SimpleGraph.exists_lt_edist_add_cycleGraph`: some rotation by a multiple of `q` carries `y` to
  distance more than `n / 2 - q` from `x`.
* `TNLean.Lattice.exists_mem_supercell_lt_edist_add`: for the rotations of a ring with momenta of
  denominator `q`, some element of the supercell carries `y` to distance more than `n / 2 - q`
  from `x`.
-/

open Matrix
open scoped Fin.NatCast

namespace SimpleGraph

/-- The circular distance `min(a, n - a)` from `0` to `a` on a ring of `n` sites. -/
def ringNorm {n : ℕ} (a : Fin n) : ℕ := min a.val (n - a.val)

private theorem exists_eq_succ (n : ℕ) [NeZero n] : ∃ m, n = m + 1 :=
  ⟨n - 1, (Nat.succ_pred_eq_of_pos (NeZero.pos n)).symm⟩

theorem ringNorm_zero {n : ℕ} [NeZero n] : ringNorm (0 : Fin n) = 0 := by simp [ringNorm]

theorem ringNorm_add_one_le {n : ℕ} [NeZero n] (a : Fin n) : ringNorm (a + 1) ≤ ringNorm a + 1 := by
  obtain ⟨m, rfl⟩ := exists_eq_succ n
  have ha := a.isLt
  simp only [ringNorm, Fin.val_add_one]
  split_ifs <;> omega

theorem ringNorm_le_add_one_add_one {n : ℕ} [NeZero n] (a : Fin n) :
    ringNorm a ≤ ringNorm (a + 1) + 1 := by
  obtain ⟨m, rfl⟩ := exists_eq_succ n
  have ha := a.isLt
  simp only [ringNorm, Fin.val_add_one]
  split_ifs with h
  · have : a.val = m := by rw [h]; rfl
    omega
  · omega

private theorem eq_one_of_val_eq_one {n : ℕ} [NeZero n] {a : Fin n} (h : a.val = 1) : a = 1 :=
  Fin.ext (by rw [h, Fin.val_one', Nat.mod_eq_of_lt (by have := a.isLt; omega)])

/-- Along an edge of the ring the circular distance to a fixed site changes by at most one. -/
theorem ringNorm_sub_le_of_adj {n : ℕ} [NeZero n] {u v : Fin n} (huv : (cycleGraph n).Adj u v)
    (x : Fin n) : ringNorm (v - x) ≤ ringNorm (u - x) + 1 := by
  rcases cycleGraph_adj'.mp huv with h | h
  · have hu : u - x = (v - x) + 1 := by rw [← eq_one_of_val_eq_one h]; abel
    rw [hu]; exact ringNorm_le_add_one_add_one _
  · have hv : v - x = (u - x) + 1 := by rw [← eq_one_of_val_eq_one h]; abel
    rw [hv]; exact ringNorm_add_one_le _

theorem ringNorm_sub_le_length {n : ℕ} [NeZero n] (x : Fin n) {u y : Fin n}
    (p : (cycleGraph n).Walk u y) : ringNorm (y - x) ≤ ringNorm (u - x) + p.length := by
  induction p with
  | nil => simp
  | cons h p ih =>
    rw [Walk.length_cons]
    have := ringNorm_sub_le_of_adj h x
    omega

/-- **Distance on a ring.** The graph distance from `x` to `y` on the ring of `n` sites is at
least the circular distance `min(a, n - a)` of the displacement `a = y - x`. -/
theorem ringNorm_sub_le_edist_cycleGraph {n : ℕ} [NeZero n] (x y : Fin n) :
    (ringNorm (y - x) : ℕ∞) ≤ (cycleGraph n).edist x y := by
  rcases eq_or_ne ((cycleGraph n).edist x y) ⊤ with h | h
  · simp [h]
  obtain ⟨p, hp⟩ := exists_walk_of_edist_ne_top h
  rw [← hp]
  have := ringNorm_sub_le_length x p
  rw [sub_self, ringNorm_zero, zero_add] at this
  exact_mod_cast this

/-- **Rotations by multiples of `q` reach far.** On a ring of `n` sites, for `q ≥ 1` and any
sites `x`, `y`, some rotation by a multiple of `q` carries `y` to graph distance more than
`n / 2 - q` from `x`. -/
theorem exists_lt_edist_add_cycleGraph {n : ℕ} [NeZero n] {q : ℕ} (hq : 0 < q) (x y : Fin n) :
    ∃ t : ℕ, ((n / 2 : ℕ) : ℕ∞) < (cycleGraph n).edist x (((q * t : ℕ) : Fin n) + y) + q := by
  suffices ∃ t : ℕ, n / 2 < ringNorm (((q * t : ℕ) : Fin n) + y - x) + q by
    obtain ⟨t, ht⟩ := this
    have h1 : ((n / 2 : ℕ) : ℕ∞) < (ringNorm (((q * t : ℕ) : Fin n) + y - x) : ℕ∞) + q := by
      exact_mod_cast ht
    exact ⟨t, h1.trans_le (add_le_add_left (ringNorm_sub_le_edist_cycleGraph x _) _)⟩
  have hn := NeZero.pos n
  set a := (y - x).val with ha
  have haL : a < n := (y - x).isLt
  set h := n / 2 with hh
  have hhn : h ≤ n - h := by omega
  have hval (t : ℕ) : (((q * t : ℕ) : Fin n) + y - x).val = (q * t + a) % n := by
    rw [add_sub_assoc, Fin.val_add, Fin.val_natCast, ha, Nat.mod_add_mod]
  by_cases hsmall : h < q
  · exact ⟨0, by omega⟩
  replace hsmall := not_lt.mp hsmall
  by_cases hah : a ≤ h
  · refine ⟨(h - a) / q, ?_⟩
    have h1 := Nat.div_mul_le_self (h - a) q
    have h2 := Nat.lt_div_mul_add (a := h - a) hq
    rw [mul_comm] at h1 h2
    rw [ringNorm, hval, Nat.mod_eq_of_lt (show q * ((h - a) / q) + a < n by omega)]
    omega
  · refine ⟨(n + h - a) / q, ?_⟩
    have h1 := Nat.div_mul_le_self (n + h - a) q
    have h2 := Nat.lt_div_mul_add (a := n + h - a) hq
    rw [mul_comm] at h1 h2
    set s := q * ((n + h - a) / q) + a
    have hs : s % n = s - n := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [ringNorm, hval, hs]
    omega

end SimpleGraph

namespace TNLean.Lattice

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Type*} [CommGroup G] [MulAction G V]
  {d : ℕ}

/-- **Momenta of denominator `q`.** If every character with a nonzero momentum sector satisfies
`χ(g)^q = 1`, then every `q`-th power lies in the supercell. For the translations of a lattice
these are the momenta `2πp/q` of Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 1620–1625, and `g^q` is a translation by whole supercells (lines 1626–1630). -/
theorem pow_mem_supercell {H : Matrix (V → Fin d) (V → Fin d) ℂ} {E₀ : ℝ} {q : ℕ}
    (hden : ∀ χ : G →* ℂ, momentumSector G d H E₀ χ ≠ ⊥ → ∀ g, χ g ^ q = 1) (g : G) :
    g ^ q ∈ supercell G d H E₀ := by
  simp only [supercell, Subgroup.mem_iInf, MonoidHom.mem_ker, map_pow]
  exact fun χ hχ ↦ hden χ hχ g

open scoped Fin.CommRing in
/-- **A supercell translation carries a site far away.** For the rotations of a ring of `n`
sites, an invariant `H`, and momenta of denominator `q ≥ 1`, any site `y` is carried by some
element of the supercell to graph distance more than `n / 2 - q` from any site `x`. Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1620–1641: "we can pick `x'` such that the
distance ... is of order the linear size of the system". -/
theorem exists_mem_supercell_lt_edist_add {n : ℕ} [NeZero n]
    {H : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ} {E₀ : ℝ} {q : ℕ} (hq : 0 < q)
    (hden : ∀ χ : Multiplicative (Fin n) →* ℂ,
      momentumSector (Multiplicative (Fin n)) d H E₀ χ ≠ ⊥ → ∀ g, χ g ^ q = 1)
    (x y : Fin n) :
    ∃ g ∈ supercell (Multiplicative (Fin n)) d H E₀,
      ((n / 2 : ℕ) : ℕ∞) < (SimpleGraph.cycleGraph n).edist x (g • y) + q := by
  obtain ⟨t, ht⟩ := SimpleGraph.exists_lt_edist_add_cycleGraph hq x y
  refine ⟨Multiplicative.ofAdd ((t : ℕ) : Fin n) ^ q, pow_mem_supercell hden _, ?_⟩
  convert ht using 3
  change (Multiplicative.ofAdd ((t : ℕ) : Fin n) ^ q).toAdd + y = _
  rw [toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, Nat.cast_mul]

end TNLean.Lattice
