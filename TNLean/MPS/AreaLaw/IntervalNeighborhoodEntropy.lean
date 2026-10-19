/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.EntropyInequalities
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

namespace TNLean.MPS.AreaLaw

/-- The exact closed real-radius neighborhood of a clipped interval.
Source: TNLean note, Lemma `lem:logsep`, `part2a_mps_information.tex:482–483`. -/
theorem chainNeighborhood_interval_eq {L : ℕ} (a z : ℕ)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    let N := fun S : Finset (Fin L) ↦
      Finset.univ.filter (fun y : Fin L ↦
        ∃ x ∈ S, (Nat.dist x.val y.val : ℝ) ≤ ρ)
    N (interval L a z) =
      if (interval L a z).Nonempty then
        interval L (a - Nat.floor ρ) (z + Nat.floor ρ)
      else ∅ := by
  classical
  dsimp only
  split_ifs with hI
  · ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_interval,
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
    let N := fun S : Finset (Fin L) ↦
      Finset.univ.filter (fun y : Fin L ↦
        ∃ x ∈ S, (Nat.dist x.val y.val : ℝ) ≤ ρ)
    Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (N T) Ω ≤
      (s.card : ℝ) * c := by
  classical
  let N := fun S : Finset (Fin L) ↦ Finset.univ.filter (fun y : Fin L ↦
    ∃ x ∈ S, (Nat.dist x.val y.val : ℝ) ≤ ρ)
  change Entropy.regionEntropy (N (s.biUnion (fun i ↦ interval L (a i) (z i)))) Ω ≤
    (s.card : ℝ) * c
  have hc : 0 ≤ c := by
    simpa only [interval_eq_empty (L := L) (Nat.le_refl 0), TNLean.Lattice.regionEntropy_empty hΩ]
      using hI 0 0
  have hn (X : Finset (Fin L)) :
      0 ≤ FiniteProduct.entropy (fun _ : Fin L ↦ Fin q) Ω X :=
    vonNeumannEntropy_nonneg_of_posSemidef_trace_one
      (FiniteProduct.reducedPure_posSemidef _ Ω X) (FiniteProduct.trace_reducedPure _ Ω hΩ X)
  have hsub (X Y : Finset (Fin L)) : Entropy.regionEntropy (X ∪ Y) Ω ≤
      Entropy.regionEntropy X Ω + Entropy.regionEntropy Y Ω := by
    simp only [Entropy.regionEntropy_eq_entropy]
    linarith [FiniteProduct.entropy_submodular (fun _ : Fin L ↦ Fin q) Ω X Y, hn (X ∩ Y)]
  have hNi (i : κ) : Entropy.regionEntropy (N (interval L (a i) (z i))) Ω ≤ c := by
    change Entropy.regionEntropy
      (Finset.univ.filter (fun y : Fin L ↦
        ∃ x ∈ interval L (a i) (z i), (Nat.dist x.val y.val : ℝ) ≤ ρ)) Ω ≤ c
    have hgeo := chainNeighborhood_interval_eq (L := L) (a i) (z i) ρ hρ
    dsimp only at hgeo
    rw [hgeo]
    split_ifs
    · exact hI _ _
    · simpa only [TNLean.Lattice.regionEntropy_empty hΩ] using hc
  have hNu (X Y : Finset (Fin L)) : N (X ∪ Y) = N X ∪ N Y := by
    ext y
    simp only [N, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      or_and_right, exists_or]
  induction s using Finset.induction_on with
  | empty => simp [N, TNLean.Lattice.regionEntropy_empty hΩ]
  | @insert i s hi ih =>
    rw [Finset.biUnion_insert, hNu, Finset.card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one]
    nlinarith [hsub (N (interval L (a i) (z i)))
      (N (s.biUnion (fun j ↦ interval L (a j) (z j)))), hNi i]

end TNLean.MPS.AreaLaw
