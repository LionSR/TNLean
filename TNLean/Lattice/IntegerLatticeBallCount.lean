/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Interval
import Mathlib.Topology.Instances.Int
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Ball counts in finite integer lattices

A ball of radius `r` in the coordinate maximum metric on the integer lattice is
contained in a box with side length `2 ⌈r⌉₊ + 1`. This gives the polynomial volume
growth used in Hastings' local index count (arXiv:cond-mat/0508554v3, lines 1273–1275).
-/

namespace TNLean.Lattice

/-- Distinct interaction centres in the integer lattice have polynomial ball growth.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1273–1275. -/
theorem card_centres_integerLattice_ball_le {κ : Type*} [Fintype κ]
    {D : ℕ} (c : κ → (Fin D → ℤ)) (hc : Function.Injective c)
    (x : Fin D → ℤ) (r : ℝ) :
    (Finset.univ.filter (fun k ↦ dist x (c k) ≤ r)).card ≤ (2 * ⌈r⌉₊ + 1) ^ D := by
  classical
  let m := ⌈r⌉₊
  let B := Fintype.piFinset fun j : Fin D ↦ Finset.Icc (x j - (m : ℤ)) (x j + m)
  have hsub : (Finset.univ.filter (fun k ↦ dist x (c k) ≤ r)).image c ⊆ B := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
    have hk' := (Finset.mem_filter.mp hk).2
    apply Fintype.mem_piFinset.mpr
    intro j
    have hjr : |(x j : ℝ) - c k j| ≤ r := by
      simpa only [Int.dist_eq] using (dist_le_pi_dist x (c k) j).trans hk'
    have hj : |(x j : ℝ) - c k j| ≤ (m : ℝ) := hjr.trans (Nat.le_ceil r)
    have hj' : |x j - c k j| ≤ (m : ℤ) := by exact_mod_cast hj
    obtain ⟨hlo, hhi⟩ := abs_le.mp hj'
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hB : B.card = (2 * m + 1) ^ D := by
    dsimp only [B]
    rw [Fintype.card_piFinset]
    have hcoord : ∀ j : Fin D,
        (Finset.Icc (x j - (m : ℤ)) (x j + m)).card = 2 * m + 1 := by
      intro j
      rw [Int.card_Icc]
      omega
    simp only [hcoord, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc
    _ = ((Finset.univ.filter (fun k ↦ dist x (c k) ≤ r)).image c).card :=
      (Finset.card_image_of_injective _ hc).symm
    _ ≤ B.card := Finset.card_le_card hsub
    _ = _ := hB

/-- Integer-lattice balls satisfy the form of polynomial growth used in the thermal
index bounds. Hastings, arXiv:cond-mat/0508554v3, lines 1273–1275. -/
theorem card_centres_integerLattice_ball_le_polynomial {κ : Type*}
    [Fintype κ] {D : ℕ}
    (c : κ → (Fin D → ℤ)) (hc : Function.Injective c) (x : Fin D → ℤ) (r : ℝ) :
    (Finset.univ.filter (fun k ↦ dist x (c k) ≤ r)).card ≤
      2 ^ D * (⌈r⌉₊ + 1) ^ D := by
  refine (card_centres_integerLattice_ball_le c hc x r).trans ?_
  rw [← Nat.mul_pow]
  exact Nat.pow_le_pow_left (by omega) D


/-- An injective coordinate map that does not increase distances transfers the integer
box count to the physical metric. In particular, coordinate maximum distance is bounded
by the intrinsic walk distance on an induced integer-lattice domain.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1273–1275. -/
theorem card_centres_ball_le_polynomial_of_dist_le {σ κ : Type*}
    [PseudoMetricSpace σ] [Fintype κ] {D : ℕ}
    (e : σ → (Fin D → ℤ)) (he : Function.Injective e)
    (hdist : ∀ a b, dist (e a) (e b) ≤ dist a b)
    (c : κ → σ) (hc : Function.Injective c) (i : σ) (r : ℝ) :
    (Finset.univ.filter (fun k ↦ dist i (c k) ≤ r)).card ≤
      2 ^ D * (⌈r⌉₊ + 1) ^ D := by
  classical
  refine (Finset.card_le_card ?_).trans
    (card_centres_integerLattice_ball_le_polynomial (e ∘ c) (he.comp hc) (e i) r)
  intro k hk
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ k,
    (hdist i (c k)).trans (Finset.mem_filter.mp hk).2⟩

/-- The polynomial ball bound transfers to a finite metric lattice embedded isometrically
in the coordinate maximum metric on the integer lattice, with distinct interaction centres.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1273–1275. -/
theorem card_centres_ball_le_polynomial_of_isometry {σ κ : Type*}
    [MetricSpace σ] [Fintype κ] {D : ℕ}
    (e : σ → (Fin D → ℤ)) (he : Isometry e) (c : κ → σ) (hc : Function.Injective c)
    (i : σ) (r : ℝ) :
    (Finset.univ.filter (fun k ↦ dist i (c k) ≤ r)).card ≤
      2 ^ D * (⌈r⌉₊ + 1) ^ D :=
  card_centres_ball_le_polynomial_of_dist_le e he.injective
    (fun a b ↦ (he.dist_eq a b).le) c hc i r

end TNLean.Lattice
