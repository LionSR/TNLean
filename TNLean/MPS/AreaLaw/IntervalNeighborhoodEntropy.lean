/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.EntropyInequalities
import TNLean.MPS.AreaLaw.ChainNeighborhood
import QICLean.Entropy.FiniteProductInformation
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Dist

/-!
# Entropy of neighborhoods of finite interval unions

A closed neighborhood of an interval of a finite chain is again an interval.
An empty interval has an empty neighborhood. A uniform interval entropy bound
therefore bounds the entropy of the neighborhood of a finite interval union
by the number of intervals times that same constant. Overlapping intervals
and empty families are permitted.

**Scope restriction (contiguous chains):** The sites are `Fin L`; the broader
finite-domain reading is recorded in
`docs/paper-gaps/tnlean_one_dimensional_connected_domain_scope.tex`.

Source: TNLean one-dimensional note, Lemma `lem:logsep`,
`part2a_mps_information.tex`, lines 458–461 and 482–487.
-/

open ManyBody (interval interval_eq_empty mem_interval)

open TNLean.Lattice

namespace TNLean.MPS.AreaLaw

/-- The exact closed real-radius neighborhood of a clipped interval.
Source: TNLean note, Lemma `lem:logsep`, `part2a_mps_information.tex:482–483`. -/
theorem chainNeighborhood_interval_eq {L : ℕ} (a z : ℕ)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    chainNeighborhood (interval L a z) ρ =
      if (interval L a z).Nonempty then
        interval L (a - Nat.floor ρ) (z + Nat.floor ρ)
      else ∅ := by
  classical
  split_ifs with hI
  · ext y
    simp only [mem_chainNeighborhood, mem_interval,
      ← Nat.le_floor_iff hρ]
    constructor
    · rintro ⟨x, hx, hdist⟩
      simp only [Nat.dist] at hdist
      omega
    · rintro ⟨hylo, hyhi⟩
      obtain ⟨x₀, hx₀⟩ := hI
      rw [mem_interval] at hx₀
      by_cases hay : y.val < a
      · refine ⟨⟨a, by omega⟩, ?_⟩
        simp only [Nat.dist]
        omega
      · by_cases hyz : y.val < z
        · exact ⟨y, ⟨Nat.le_of_not_gt hay, hyz⟩, by simp⟩
        · refine ⟨⟨z - 1, by omega⟩, ?_⟩
          simp only [Nat.dist]
          omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hI]

/-- On the sites `Fin L`, let every interval have a neighborhood `⋃_{x ∈ I} g x` that is
again an interval, and let every interval have entropy at most `c`. Then the neighborhood of
a union of `|s|` intervals has entropy at most `|s| c`, by subadditivity of the entropy over
the neighborhoods of the intervals. TNLean note, `part2a_mps_information.tex`,
lines 482–487. -/
theorem regionEntropy_biUnion_neighborhood_intervals_le
    {L q : ℕ} {κ : Type*}
    {Ω : EuclideanSpace ℂ (Fin L → Fin q)} (hΩ : ‖Ω‖ = 1) {c : ℝ}
    (hI : ∀ a z : ℕ,
      Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (interval L a z) Ω ≤ c)
    (g : Fin L → Finset (Fin L))
    (hg : ∀ a z : ℕ, ∃ u v : ℕ, (interval L a z).biUnion g = interval L u v)
    (s : Finset κ) (a z : κ → ℕ) :
    Entropy.regionEntropy (n := fun _ : Fin L ↦ q)
      ((s.biUnion (fun i ↦ interval L (a i) (z i))).biUnion g) Ω ≤ (s.card : ℝ) * c := by
  classical
  have hn (X : Finset (Fin L)) :
      0 ≤ Entropy.regionEntropy (n := fun _ : Fin L ↦ q) X Ω :=
    vonNeumannEntropy_nonneg_of_posSemidef_trace_one
      (Entropy.regionState_posSemidef X Ω) (Entropy.trace_regionState_eq_one hΩ)
  have hsub (X Y : Finset (Fin L)) :
      Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (X ∪ Y) Ω ≤
        Entropy.regionEntropy X Ω + Entropy.regionEntropy Y Ω := by
    linarith [TNLean.Lattice.regionEntropy_union_add_inter_le (Ω := Ω) X Y, hn (X ∩ Y)]
  have hsum : Entropy.regionEntropy (n := fun _ : Fin L ↦ q)
      (s.biUnion (fun i ↦ (interval L (a i) (z i)).biUnion g)) Ω ≤
      ∑ i ∈ s, Entropy.regionEntropy (n := fun _ : Fin L ↦ q)
        ((interval L (a i) (z i)).biUnion g) Ω := by
    simpa only [Finset.sup_eq_biUnion] using
      (Finset.apply_sup_le_sum
        (f := fun X : Finset (Fin L) ↦
          Entropy.regionEntropy (n := fun _ : Fin L ↦ q) X Ω)
        (TNLean.Lattice.regionEntropy_empty hΩ) (fun {X Y} ↦ hsub X Y)
        (s := fun i ↦ (interval L (a i) (z i)).biUnion g) s)
  have hNi (i : κ) : Entropy.regionEntropy (n := fun _ : Fin L ↦ q)
      ((interval L (a i) (z i)).biUnion g) Ω ≤ c := by
    obtain ⟨u, v, hgeo⟩ := hg (a i) (z i)
    simpa only [hgeo] using hI u v
  simpa only [Finset.biUnion_biUnion, Finset.sum_const, nsmul_eq_mul] using
    hsum.trans (Finset.sum_le_sum (fun i _ ↦ hNi i))

/-- A uniform interval entropy bound controls the neighborhood of a finite
interval union, including overlapping and empty components.
Source: TNLean note, Lemma `lem:logsep`, `part2a_mps_information.tex:458–461, 482–487`. -/
theorem regionEntropy_chainNeighborhood_biUnion_intervals_le
    {L q : ℕ} {κ : Type*}
    {Ω : EuclideanSpace ℂ (Fin L → Fin q)} (hΩ : ‖Ω‖ = 1)
    {c : ℝ}
    (hI : ∀ a z : ℕ,
      Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (interval L a z) Ω ≤ c)
    (s : Finset κ) (a z : κ → ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    let T := s.biUnion (fun i ↦ interval L (a i) (z i))
    Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (chainNeighborhood T ρ) Ω ≤
      (s.card : ℝ) * c := by
  classical
  have hN (S : Finset (Fin L)) :
      chainNeighborhood S ρ = S.biUnion fun x ↦ chainNeighborhood {x} ρ := by
    ext y
    simp only [mem_chainNeighborhood, Finset.mem_biUnion, Finset.mem_singleton,
      exists_prop, exists_eq_left]
  intro T
  rw [hN]
  refine regionEntropy_biUnion_neighborhood_intervals_le hΩ hI _ (fun a z ↦ ?_) s a z
  rw [← hN, chainNeighborhood_interval_eq a z ρ hρ]
  split_ifs
  · exact ⟨_, _, rfl⟩
  · exact ⟨0, 0, (interval_eq_empty le_rfl).symm⟩

end TNLean.MPS.AreaLaw
