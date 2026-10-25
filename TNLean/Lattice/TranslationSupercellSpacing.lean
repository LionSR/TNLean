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
lines 1603–1641), treats a translationally invariant system on a `d`-dimensional lattice, with
sites `(x, y)` for a unit cell `x` and a site `y` within it. He assumes that every momentum of a
ground state has components that are rational multiples `2πp/q` of `2π` with denominators that do
not depend on the system size. Then translation by a supercell, whose side in each direction is
the least common multiple of the denominators, leaves every ground state unchanged, and such a
translation can carry any site to a distance of order the linear size of the system from any
other site.

For a character this hypothesis reads `χ(g)^q = 1`, with `q` the common multiple of the
denominators. If it holds for every character with a nonzero momentum sector, then every `q`-th
power lies in the supercell (`pow_mem_supercell`). For the geometry, let `π : V → ℤ/n` be the
coordinate of the unit cell along one lattice direction, with `n` cells in that direction, such
that every edge of the graph joins cells whose coordinates differ by at most one, and let `e` be
the unit translation in that direction. Then the graph distance is at least the circular distance
`min(a, n - a)` of the coordinate difference `a`, and the translations `e^{qt}` carry any site
to distance more than `n / 2 - q` from any other (`exists_mem_supercell_lt_edist_add`). The ring
of `n` sites with its rotations is the case `π = id` (`exists_mem_supercell_lt_edist_add_ring`).

## Main results

* `TNLean.Lattice.pow_mem_supercell`: with momenta of denominator `q`, every `q`-th power lies in
  the supercell.
* `SimpleGraph.ringNorm_sub_le_edist`: the graph distance is at least the circular distance of
  the cell coordinates.
* `SimpleGraph.exists_lt_ringNorm_add`: some multiple of `q` added to a cell coordinate puts it
  at circular distance more than `n / 2 - q` from any other.
* `TNLean.Lattice.exists_mem_supercell_lt_edist_add`: with momenta of denominator `q`, some
  element of the supercell carries any site to graph distance more than `n / 2 - q` from any
  other.
* `TNLean.Lattice.exists_mem_supercell_lt_edist_add_ring`: the same for the rotations of a ring.
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

/-- A coordinate step of circular size at most one is `0`, `1` or `-1`. -/
private theorem eq_zero_or_eq_one_or_add_one_eq_zero {n : ℕ} [NeZero n] {a : Fin n}
    (ha : ringNorm a ≤ 1) : a = 0 ∨ a = 1 ∨ a + 1 = 0 := by
  have hn := NeZero.pos n
  have hlt := a.isLt
  rcases Nat.lt_or_ge a.val 2 with h | h
  · rcases Nat.lt_succ_iff.mp h |>.lt_or_eq with h | h
    · exact Or.inl (Fin.ext (by rw [Fin.val_zero]; omega))
    · exact Or.inr (Or.inl (eq_one_of_val_eq_one h))
  · have : a.val = n - 1 := by simp only [ringNorm] at ha; omega
    refine Or.inr (Or.inr (Fin.ext ?_))
    rw [Fin.val_add, this, Fin.val_one', Fin.val_zero]
    rcases Nat.lt_or_ge 1 n with h1 | h1
    · rw [Nat.mod_eq_of_lt h1, Nat.sub_add_cancel hn, Nat.mod_self]
    · omega

variable {V : Type*} {Γ : SimpleGraph V}

/-- Along an edge whose cell coordinates differ by at most one, the circular distance to a fixed
coordinate changes by at most one. -/
theorem ringNorm_sub_le_of_step {n : ℕ} [NeZero n] (π : V → Fin n) {u v : V}
    (h : ringNorm (π v - π u) ≤ 1) (c : Fin n) : ringNorm (π v - c) ≤ ringNorm (π u - c) + 1 := by
  rcases eq_zero_or_eq_one_or_add_one_eq_zero h with h | h | h
  · rw [sub_eq_zero.mp h]; omega
  · have : π v - c = (π u - c) + 1 := by rw [← h]; abel
    rw [this]; exact ringNorm_add_one_le _
  · have : π u - c = (π v - c) + 1 := by
      have := congrArg (· + (π u - c)) h
      simp only [zero_add] at this
      rw [← this]; abel
    rw [this]; exact ringNorm_le_add_one_add_one _

theorem ringNorm_sub_le_length {n : ℕ} [NeZero n] (π : V → Fin n)
    (hπ : ∀ u v, Γ.Adj u v → ringNorm (π v - π u) ≤ 1) (c : Fin n) {u y : V} (p : Γ.Walk u y) :
    ringNorm (π y - c) ≤ ringNorm (π u - c) + p.length := by
  induction p with
  | nil => simp
  | cons h p ih =>
    rw [Walk.length_cons]
    have := ringNorm_sub_le_of_step π (hπ _ _ h) c
    omega

/-- **Distance and cell coordinates.** If every edge of `Γ` joins sites whose cell coordinates
differ by at most one, the graph distance from `x` to `y` is at least the circular distance
`min(a, n - a)` of the coordinate difference `a = π y - π x`. -/
theorem ringNorm_sub_le_edist {n : ℕ} [NeZero n] (π : V → Fin n)
    (hπ : ∀ u v, Γ.Adj u v → ringNorm (π v - π u) ≤ 1) (x y : V) :
    (ringNorm (π y - π x) : ℕ∞) ≤ Γ.edist x y := by
  rcases eq_or_ne (Γ.edist x y) ⊤ with h | h
  · simp [h]
  obtain ⟨p, hp⟩ := exists_walk_of_edist_ne_top h
  rw [← hp]
  have := ringNorm_sub_le_length π hπ (π x) p
  rw [sub_self, ringNorm_zero, zero_add] at this
  exact_mod_cast this

theorem ringNorm_neg {n : ℕ} [NeZero n] (a : Fin n) : ringNorm (-a) = ringNorm a := by
  have := a.isLt
  simp only [ringNorm, Fin.val_neg]
  split_ifs with h
  · simp [h]
  · omega

/-- Every edge of the ring joins coordinates at circular distance one. -/
theorem ringNorm_sub_le_one_of_adj_cycleGraph {n : ℕ} [NeZero n] (u v : Fin n)
    (h : (cycleGraph n).Adj u v) : ringNorm (id v - id u) ≤ 1 := by
  simp only [id]
  rcases cycleGraph_adj'.mp h with h | h
  · rw [← neg_sub, ringNorm_neg, ringNorm, h]; omega
  · rw [ringNorm, h]; omega

/-- **Multiples of `q` reach far.** For `q ≥ 1` and coordinates `a`, `b` in `ℤ/n`, some
`b + qt` lies at circular distance more than `n / 2 - q` from `a`. -/
theorem exists_lt_ringNorm_add {n : ℕ} [NeZero n] {q : ℕ} (hq : 0 < q) (a b : Fin n) :
    ∃ t : ℕ, n / 2 < ringNorm (b + ((q * t : ℕ) : Fin n) - a) + q := by
  have hn := NeZero.pos n
  set c := (b - a).val with hc
  have hcL : c < n := (b - a).isLt
  set h := n / 2 with hh
  have hhn : h ≤ n - h := by omega
  have hval (t : ℕ) : (b + ((q * t : ℕ) : Fin n) - a).val = (q * t + c) % n := by
    rw [add_sub_right_comm, add_comm, Fin.val_add, Fin.val_natCast, hc, Nat.mod_add_mod]
  by_cases hsmall : h < q
  · exact ⟨0, by omega⟩
  replace hsmall := not_lt.mp hsmall
  by_cases hch : c ≤ h
  · refine ⟨(h - c) / q, ?_⟩
    have h1 := Nat.div_mul_le_self (h - c) q
    have h2 := Nat.lt_div_mul_add (a := h - c) hq
    rw [mul_comm] at h1 h2
    rw [ringNorm, hval, Nat.mod_eq_of_lt (show q * ((h - c) / q) + c < n by omega)]
    omega
  · refine ⟨(n + h - c) / q, ?_⟩
    have h1 := Nat.div_mul_le_self (n + h - c) q
    have h2 := Nat.lt_div_mul_add (a := n + h - c) hq
    rw [mul_comm] at h1 h2
    set s := q * ((n + h - c) / q) + c
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

/-- **A supercell translation carries a site far away.** Let an abelian group `Γ` act on the
sites, let `H` be invariant, and let every character with a nonzero momentum sector satisfy
`χ(g)^q = 1`, where `q ≥ 1`. Let `π` be the cell coordinate along one lattice direction, with
`n` cells, such that every edge of the graph `G` joins cells at circular distance at most one,
and let `e` translate by one cell in that direction. Then any site `y` is carried by some element
of the supercell to graph distance more than `n / 2 - q` from any site `x`. Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1620–1641: "By choosing `x'` correctly, we can
make the distance ... of order the linear size of the system". -/
theorem exists_mem_supercell_lt_edist_add {Γ : Type*} [CommGroup Γ] [MulAction Γ V]
    {H : Matrix (V → Fin d) (V → Fin d) ℂ} {E₀ : ℝ} {q : ℕ} (hq : 0 < q)
    (hden : ∀ χ : Γ →* ℂ, momentumSector Γ d H E₀ χ ≠ ⊥ → ∀ g, χ g ^ q = 1)
    (G : SimpleGraph V) {n : ℕ} [NeZero n] (π : V → Fin n)
    (hπ : ∀ u v, G.Adj u v → SimpleGraph.ringNorm (π v - π u) ≤ 1)
    (e : Γ) (he : ∀ v, π (e • v) = π v + 1) (x y : V) :
    ∃ g ∈ supercell Γ d H E₀, ((n / 2 : ℕ) : ℕ∞) < G.edist x (g • y) + q := by
  have hpow (k : ℕ) (v : V) : π (e ^ k • v) = π v + ((k : ℕ) : Fin n) := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', mul_smul, he, ih, Nat.cast_succ]; abel
  obtain ⟨t, ht⟩ := SimpleGraph.exists_lt_ringNorm_add hq (π x) (π y)
  refine ⟨(e ^ t) ^ q, pow_mem_supercell hden _, ?_⟩
  rw [← pow_mul, mul_comm]
  have hdist := SimpleGraph.ringNorm_sub_le_edist π hπ x (e ^ (q * t) • y)
  rw [hpow] at hdist
  have h1 : ((n / 2 : ℕ) : ℕ∞) < (SimpleGraph.ringNorm (π y + ((q * t : ℕ) : Fin n) - π x) : ℕ∞)
      + q := by exact_mod_cast ht
  exact h1.trans_le (add_le_add_left hdist _)

/-- **A supercell rotation of a ring carries a site far away.** The case of
`exists_mem_supercell_lt_edist_add` for the rotations of a ring of `n` sites. -/
theorem exists_mem_supercell_lt_edist_add_ring {n : ℕ} [NeZero n]
    {H : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ} {E₀ : ℝ} {q : ℕ} (hq : 0 < q)
    (hden : ∀ χ : Multiplicative (Fin n) →* ℂ,
      momentumSector (Multiplicative (Fin n)) d H E₀ χ ≠ ⊥ → ∀ g, χ g ^ q = 1)
    (x y : Fin n) :
    ∃ g ∈ supercell (Multiplicative (Fin n)) d H E₀,
      ((n / 2 : ℕ) : ℕ∞) < (SimpleGraph.cycleGraph n).edist x (g • y) + q :=
  exists_mem_supercell_lt_edist_add hq hden (SimpleGraph.cycleGraph n) id
    SimpleGraph.ringNorm_sub_le_one_of_adj_cycleGraph (Multiplicative.ofAdd 1)
    (fun v ↦ by change 1 + v = v + 1; abel) x y

end TNLean.Lattice
