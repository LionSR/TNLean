/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.ZMod.ValMinAbs
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

For a character, the momentum hypothesis is `χ g ^ q = 1`, where `q` is a common multiple of
the denominators. If it holds for every character with a nonzero momentum sector, then every
`q`-th power belongs to the supercell (`pow_mem_supercell`).

Let `π : V → ZMod n` be a cell coordinate, and let the positive integer `R` bound its circular
displacement along every graph edge. The circular displacement between two sites is at most `R`
times their graph distance. If `e` translates the coordinate by one, some translation
`g = (e ^ t) ^ q` in the supercell satisfies `n / 2 < R * d(x, g • y) + q`
(`exists_mem_supercell_lt_edist_add`). The rotations of a ring have `R = 1`
(`exists_mem_supercell_lt_edist_add_ring`).

## Main results

* `TNLean.Lattice.pow_mem_supercell`: with momenta of denominator `q`, every `q`-th power lies in
  the supercell.
* `SimpleGraph.natAbs_valMinAbs_sub_le_edist`: the circular displacement of the cell
  coordinate satisfies `|π y - π x| ≤ R * Γ.edist x y`.
* `TNLean.Lattice.exists_lt_natAbs_valMinAbs_add`: some multiple of `q` added to a residue puts it
  at circular distance more than `n / 2 - q` from any other.
* `TNLean.Lattice.exists_mem_supercell_lt_edist_add`: with momenta of denominator `q`, some
  element of the supercell carries any site to graph distance more than `(n / 2 - q) / R` from
  any other.
* `TNLean.Lattice.exists_mem_supercell_lt_edist`: if `l + q ≤ n / 2`, a supercell
  translate has distance greater than `l`, when each edge changes the coordinate by at most one.
* `TNLean.Lattice.exists_mem_supercell_lt_edist_add_ring`: the same for the rotations of a ring.
-/

open Matrix

namespace SimpleGraph

variable {V : Type*} {Γ : SimpleGraph V} {n R : ℕ}

/-- One step of the triangle inequality: crossing an edge changes the circular displacement
from a fixed site by at most \(R\). -/
private theorem natAbs_valMinAbs_sub_le_add_of_adj (π : V → ZMod n)
    (hπ : ∀ u v, Γ.Adj u v → (π v - π u).valMinAbs.natAbs ≤ R)
    (u w x : V) (h : Γ.Adj u w) :
    (π w - π x).valMinAbs.natAbs ≤ (π u - π x).valMinAbs.natAbs + R := by
  simpa only [add_comm (π u - π x) (π w - π u), sub_add_sub_cancel] using
    (ZMod.natAbs_valMinAbs_add_le (π u - π x) (π w - π u)).trans
      ((Int.natAbs_add_le _ _).trans (Nat.add_le_add_left (hπ u w h) _))

/-- Accumulating the one-edge step along a walk: the circular displacement grows by at most
\(R\) times the length of the walk. -/
private theorem natAbs_valMinAbs_sub_le_add_length_mul (π : V → ZMod n)
    (hπ : ∀ u v, Γ.Adj u v → (π v - π u).valMinAbs.natAbs ≤ R)
    (x : V) {u y : V} (p : Γ.Walk u y) :
    (π y - π x).valMinAbs.natAbs ≤
      (π u - π x).valMinAbs.natAbs + R * p.length := by
  induction p with
  | nil => simp
  | cons h p ih =>
    have hstep := natAbs_valMinAbs_sub_le_add_of_adj π hπ _ _ x h
    rw [SimpleGraph.Walk.length_cons, Nat.mul_succ]
    omega

/-- If each edge changes a cell coordinate by at most the positive integer \(R\), its
circular displacement is at most \(R\) times the graph distance. -/
theorem natAbs_valMinAbs_sub_le_edist (hR : 0 < R) (π : V → ZMod n)
    (hπ : ∀ u v, Γ.Adj u v → (π v - π u).valMinAbs.natAbs ≤ R) (x y : V) :
    ((π y - π x).valMinAbs.natAbs : ℕ∞) ≤ (R : ℕ∞) * Γ.edist x y := by
  rcases eq_or_ne (Γ.edist x y) ⊤ with h | h
  · simp [h, hR.ne']
  · obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top h
    rw [← hp]
    have hw := natAbs_valMinAbs_sub_le_add_length_mul π hπ x p
    simp only [sub_self, ZMod.valMinAbs_zero, Int.natAbs_zero, zero_add] at hw
    exact_mod_cast hw

end SimpleGraph

namespace TNLean.Lattice

/-- Translation by the `k`-th power advances a cell coordinate by `k`.
Hastings, arXiv:cond-mat/0508554v3, lines 1603–1618. -/
theorem coordinate_pow_smul {V Γ : Type*} [Group Γ] [MulAction Γ V]
    {n : ℕ} (π : V → ZMod n) (e : Γ) (he : ∀ v, π (e • v) = π v + 1)
    (k : ℕ) (v : V) : π (e ^ k • v) = π v + (k : ZMod n) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_smul, he, ih, Nat.cast_succ]; abel

/-- **Multiples of `q` reach far.** For `q ≥ 1` and residues `a`, `b` modulo `n`, some
`b + qt` lies at circular distance more than `n / 2 - q` from `a`. -/
theorem exists_lt_natAbs_valMinAbs_add {n : ℕ} [NeZero n] {q : ℕ} (hq : 0 < q)
    (a b : ZMod n) :
    ∃ t : ℕ, n / 2 < (b + ((q * t : ℕ) : ZMod n) - a).valMinAbs.natAbs + q := by
  have hn := NeZero.pos n
  set c := (b - a).val with hc
  have hcL : c < n := ZMod.val_lt (b - a)
  set h := n / 2 with hh
  have hhn : h ≤ n - h := by omega
  have hval (t : ℕ) : (b + ((q * t : ℕ) : ZMod n) - a).val = (q * t + c) % n := by
    rw [← ZMod.val_natCast, Nat.cast_add, hc, ZMod.natCast_zmod_val]
    congr 1
    abel
  simp only [ZMod.valMinAbs_natAbs_eq_min]
  by_cases hsmall : h < q
  · exact ⟨0, by omega⟩
  replace hsmall := not_lt.mp hsmall
  by_cases hch : c ≤ h
  · refine ⟨(h - c) / q, ?_⟩
    have h1 := Nat.div_mul_le_self (h - c) q
    have h2 := Nat.lt_div_mul_add (a := h - c) hq
    rw [mul_comm] at h1 h2
    rw [hval, Nat.mod_eq_of_lt (show q * ((h - c) / q) + c < n by omega)]
    omega
  · refine ⟨(n + h - c) / q, ?_⟩
    have h1 := Nat.div_mul_le_self (n + h - c) q
    have h2 := Nat.lt_div_mul_add (a := n + h - c) hq
    rw [mul_comm] at h1 h2
    set s := q * ((n + h - c) / q) + c
    have hs : s % n = s - n := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hval, hs]
    omega

/-- The coordinate of a site of the ring, as a residue: subtraction of sites is subtraction of
residues. -/
private theorem natCast_val_sub {n : ℕ} [NeZero n] (u v : Fin n) :
    (((v - u : Fin n) : ℕ) : ZMod n) = ((v : ℕ) : ZMod n) - ((u : ℕ) : ZMod n) := by
  rw [Fin.val_sub, ZMod.natCast_mod, Nat.cast_add, Nat.cast_sub u.isLt.le, ZMod.natCast_self]
  ring

/-- Every edge of the ring joins residues at circular distance one. -/
private theorem natAbs_valMinAbs_sub_le_one_of_adj_cycleGraph {n : ℕ} [NeZero n] (u v : Fin n)
    (h : (SimpleGraph.cycleGraph n).Adj u v) :
    (((v : ℕ) : ZMod n) - ((u : ℕ) : ZMod n)).valMinAbs.natAbs ≤ 1 := by
  have hone : ((1 : ZMod n)).valMinAbs.natAbs ≤ 1 := by
    rw [ZMod.valMinAbs_natAbs_eq_min]
    exact (min_le_left _ _).trans (by rw [ZMod.val_one_eq_one_mod]; exact Nat.mod_le 1 n)
  rcases SimpleGraph.cycleGraph_adj'.mp h with h | h
  · rw [← neg_sub, ZMod.natAbs_valMinAbs_neg, ← natCast_val_sub, h, Nat.cast_one]; exact hone
  · rw [← natCast_val_sub, h, Nat.cast_one]; exact hone

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

/-- **A supercell translation carries a site far away.** Let an abelian group act on the
sites, and suppose \(\chi(g)^q=1\) for every group element and every character with a nonzero
momentum sector, where \(q\ge1\). Let \(\pi\) be a cell coordinate with \(n\) cells, let
\(R\ge1\) bound its circular displacement along every edge, and let \(e\) translate it by
one. Then some supercell translation satisfies
\(\lfloor n/2\rfloor<R\,d(x,g\cdot y)+q\).

Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1620–1641, chooses a supercell
translation carrying a site to a distance of order the linear size of the system. -/
theorem exists_mem_supercell_lt_edist_add {Γ : Type*} [CommGroup Γ] [MulAction Γ V]
    {H : Matrix (V → Fin d) (V → Fin d) ℂ} {E₀ : ℝ} {q : ℕ} (hq : 0 < q)
    (hden : ∀ χ : Γ →* ℂ, momentumSector Γ d H E₀ χ ≠ ⊥ → ∀ g, χ g ^ q = 1)
    (G : SimpleGraph V) {n R : ℕ} [NeZero n] (hR : 0 < R) (π : V → ZMod n)
    (hπ : ∀ u v, G.Adj u v → (π v - π u).valMinAbs.natAbs ≤ R)
    (e : Γ) (he : ∀ v, π (e • v) = π v + 1) (x y : V) :
    ∃ g ∈ supercell Γ d H E₀, ((n / 2 : ℕ) : ℕ∞) < (R : ℕ∞) * G.edist x (g • y) + q := by
  obtain ⟨t, ht⟩ := exists_lt_natAbs_valMinAbs_add hq (π x) (π y)
  refine ⟨(e ^ t) ^ q, pow_mem_supercell hden _, ?_⟩
  rw [← pow_mul, Nat.mul_comm t q]
  have hdist := SimpleGraph.natAbs_valMinAbs_sub_le_edist hR π hπ x (e ^ (q * t) • y)
  rw [coordinate_pow_smul π e he] at hdist
  have h1 : ((n / 2 : ℕ) : ℕ∞) <
      ((π y + ((q * t : ℕ) : ZMod n) - π x).valMinAbs.natAbs : ℕ∞) + q := by
    exact_mod_cast ht
  exact h1.trans_le (add_le_add_left hdist _)

/-- If each edge changes the cell coordinate by at most one and
`l + q ≤ n / 2`, a supercell translation carries any site to graph distance
strictly greater than `l` from any other. This combines the geometric choice
with its distance consequence in Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 1634–1641. -/
theorem exists_mem_supercell_lt_edist {Γ : Type*} [CommGroup Γ] [MulAction Γ V]
    {H : Matrix (V → Fin d) (V → Fin d) ℂ} {E₀ : ℝ} {q : ℕ} (hq : 0 < q)
    (hden : ∀ χ : Γ →* ℂ, momentumSector Γ d H E₀ χ ≠ ⊥ → ∀ g, χ g ^ q = 1)
    (G : SimpleGraph V) {n : ℕ} [NeZero n] (π : V → ZMod n)
    (hπ : ∀ u v, G.Adj u v → (π v - π u).valMinAbs.natAbs ≤ 1)
    (e : Γ) (he : ∀ v, π (e • v) = π v + 1)
    (l : ℕ) (hl : l + q ≤ n / 2) (x y : V) :
    ∃ g ∈ supercell Γ d H E₀, (l : ℕ∞) < G.edist x (g • y) := by
  obtain ⟨g, hg, hdist⟩ : ∃ g ∈ supercell Γ d H E₀,
      ((n / 2 : ℕ) : ℕ∞) < G.edist x (g • y) + q := by
    simpa only [Nat.cast_one, one_mul] using
      exists_mem_supercell_lt_edist_add hq hden G (R := 1) Nat.zero_lt_one π hπ e he x y
  refine ⟨g, hg, ?_⟩
  by_contra hfar
  have hle := le_of_not_gt hfar
  have hlt : ((n / 2 : ℕ) : ℕ∞) < ((l + q : ℕ) : ℕ∞) := by
    calc
      ((n / 2 : ℕ) : ℕ∞) < G.edist x (g • y) + q := hdist
      _ ≤ (l : ℕ∞) + q := add_le_add hle le_rfl
      _ = ((l + q : ℕ) : ℕ∞) := by rw [Nat.cast_add]
  exact (not_lt_of_ge hl) (ENat.natCast_lt_natCast.mp hlt)

/-- **A supercell rotation of a ring carries a site far away.** The case of
`exists_mem_supercell_lt_edist_add` for the rotations of a ring of `n` sites, with the
coordinate of a site as a residue modulo `n`. -/
theorem exists_mem_supercell_lt_edist_add_ring {n : ℕ} [NeZero n]
    {H : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ} {E₀ : ℝ} {q : ℕ} (hq : 0 < q)
    (hden : ∀ χ : Multiplicative (Fin n) →* ℂ,
      momentumSector (Multiplicative (Fin n)) d H E₀ χ ≠ ⊥ → ∀ g, χ g ^ q = 1)
    (x y : Fin n) :
    ∃ g ∈ supercell (Multiplicative (Fin n)) d H E₀,
      ((n / 2 : ℕ) : ℕ∞) < (SimpleGraph.cycleGraph n).edist x (g • y) + q := by
  simpa only [Nat.cast_one, one_mul] using
    exists_mem_supercell_lt_edist_add hq hden (SimpleGraph.cycleGraph n) (R := 1)
      Nat.zero_lt_one
      (fun x : Fin n ↦ ((x : ℕ) : ZMod n)) natAbs_valMinAbs_sub_le_one_of_adj_cycleGraph
      (Multiplicative.ofAdd 1) (fun v ↦ by
        change (((1 + v : Fin n) : ℕ) : ZMod n) = _
        rw [Fin.val_add, ZMod.natCast_mod, Nat.cast_add, Fin.val_one', ZMod.natCast_mod,
          Nat.cast_one, add_comm]) x y

end TNLean.Lattice
