/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Chain.EntropyInequalities
import TNLean.MPS.AreaLaw.Chain.ChainNeighborhood
import QICLean.ManyBody.Entropy.RegionStrongSubadditivity
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Dist
import TNLean.MPS.AreaLaw.Chain.DomainIntervalNeighborhood
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import QICLean.ManyBody.Hamiltonian.GroundSpace

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

## Entropy on intrinsic neighborhoods of interval unions

The intrinsic graph neighborhood of a relative interval is a relative interval.
Subadditivity therefore extends a uniform interval entropy bound to neighborhoods
of finite unions of intervals, including overlapping and empty intervals. Applying
the interval area law gives the bound for the original gapped domain ground state.

Source: TNLean one-dimensional note, `part2a_mps_information.tex`, lines 482–487,
and the interval area-law estimate in Part I.
-/

section

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
      ManyBody.regionEntropy (X := fun _ ↦ Fin q) Ω (interval L a z) ≤ c)
    (g : Fin L → Finset (Fin L))
    (hg : ∀ a z : ℕ, ∃ u v : ℕ, (interval L a z).biUnion g = interval L u v)
    (s : Finset κ) (a z : κ → ℕ) :
    ManyBody.regionEntropy (X := fun _ ↦ Fin q)
      Ω ((s.biUnion (fun i ↦ interval L (a i) (z i))).biUnion g) ≤ (s.card : ℝ) * c := by
  classical
  have hn (X : Finset (Fin L)) :
      0 ≤ ManyBody.regionEntropy (X := fun _ ↦ Fin q) Ω X :=
    vonNeumannEntropy_nonneg_of_posSemidef_trace_one
      (ManyBody.regionState_posSemidef X Ω) (ManyBody.trace_regionState_eq_one hΩ)
  have hsub (X Y : Finset (Fin L)) :
      ManyBody.regionEntropy (X := fun _ ↦ Fin q) Ω (X ∪ Y) ≤
        ManyBody.regionEntropy Ω X + ManyBody.regionEntropy Ω Y := by
    linarith [ManyBody.regionEntropy_submodular _ Ω X Y, hn (X ∩ Y)]
  have hsum : ManyBody.regionEntropy (X := fun _ ↦ Fin q)
      Ω (s.biUnion (fun i ↦ (interval L (a i) (z i)).biUnion g)) ≤
      ∑ i ∈ s, ManyBody.regionEntropy (X := fun _ ↦ Fin q)
        Ω ((interval L (a i) (z i)).biUnion g) := by
    simpa only [Finset.sup_eq_biUnion] using
      (Finset.apply_sup_le_sum
        (f := fun X : Finset (Fin L) ↦
          ManyBody.regionEntropy (X := fun _ ↦ Fin q) Ω X)
        (ManyBody.regionEntropy_empty _ Ω hΩ) (fun {X Y} ↦ hsub X Y)
        (s := fun i ↦ (interval L (a i) (z i)).biUnion g) s)
  have hNi (i : κ) : ManyBody.regionEntropy (X := fun _ ↦ Fin q)
      Ω ((interval L (a i) (z i)).biUnion g) ≤ c := by
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
      ManyBody.regionEntropy (X := fun _ ↦ Fin q) Ω (interval L a z) ≤ c)
    (s : Finset κ) (a z : κ → ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    let T := s.biUnion (fun i ↦ interval L (a i) (z i))
    ManyBody.regionEntropy (X := fun _ ↦ Fin q) Ω (chainNeighborhood T ρ) ≤
      (s.card : ℝ) * c := by
  classical
  have hN (S : Finset (Fin L)) :
      chainNeighborhood S ρ = S.biUnion fun x ↦ chainNeighborhood {x} ρ := by
    ext y
    simp only [mem_chainNeighborhood, Finset.mem_biUnion, Finset.mem_singleton,
      exists_eq_left]
  intro T
  rw [hN]
  refine regionEntropy_biUnion_neighborhood_intervals_le hΩ hI _ (fun a z ↦ ?_) s a z
  rw [← hN, chainNeighborhood_interval_eq a z ρ hρ]
  split_ifs
  · exact ⟨_, _, rfl⟩
  · exact ⟨0, 0, (interval_eq_empty le_rfl).symm⟩

end TNLean.MPS.AreaLaw

end

section

open scoped Matrix.Norms.L2Operator

open ManyBody (interval lineDomainGraph DomainInteraction)

open SimpleGraph QuantumCircuit

open ManyBody (IsGapped groundSpace)

namespace TNLean.MPS.AreaLaw

/-- Auxiliary entropy bound for intrinsic neighborhoods of finite unions of relative
intervals. Overlaps and empty intervals are permitted.
Source: TNLean note, `part2a_mps_information.tex`, lines 482–487. -/
theorem regionEntropy_domainNeighborhood_biUnion_intervals_le
    {Λ : Finset ℤ} {q : ℕ} {κ : Type*}
    {Ω : EuclideanSpace ℂ (Fin Λ.card → Fin q)} (hΩ : ‖Ω‖ = 1) {c : ℝ}
    (hI : ∀ a b : ℕ,
      ManyBody.regionEntropy (X := fun _ ↦ Fin q) Ω (interval Λ.card a b) ≤ c)
    (s : Finset κ) (a b : κ → ℕ) (m : ℕ) :
    ManyBody.regionEntropy (X := fun _ ↦ Fin q)
      Ω ((s.biUnion (fun i ↦ interval Λ.card (a i) (b i))).biUnion
        (fun x ↦ ManyBody.graphBall (lineDomainGraph Λ) x m)) ≤ (s.card : ℝ) * c := by
  exact regionEntropy_biUnion_neighborhood_intervals_le hΩ hI _
    (domainNeighborhood_interval_eq Λ · · m) s a b

/-- The original gapped domain Hamiltonian bounds entropy on an intrinsic neighborhood
of a finite interval union.
Source: TNLean note, `part2a_mps_information.tex`, lines 482–487, together with the
interval area-law bound from Part I. -/
theorem _root_.ManyBody.DomainInteraction.regionEntropy_neighborhood_biUnion_intervals_le
    {Λ : Finset ℤ} {q R : ℕ} {J Δ : ℝ} {κ : Type*}
    (h : DomainInteraction Λ q R) (hh : ∀ X, (h.term X).IsHermitian) (hhJ : ∀ X, ‖h.term X‖ ≤ J)
        (hq : 1 ≤ q) (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    {E₀ : ℝ} {Ω : EuclideanSpace ℂ (Fin Λ.card → Fin q)}
    (hΩ : ‖Ω‖ = 1) (hgap : IsGapped h.hamiltonian E₀ Δ)
    (hspan : groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω})
    (s : Finset κ) (a b : κ → ℕ) (m : ℕ) :
    ManyBody.regionEntropy (X := fun _ ↦ Fin q)
      Ω ((s.biUnion (fun i ↦ interval Λ.card (a i) (b i))).biUnion
        (fun x ↦ ManyBody.graphBall (lineDomainGraph Λ) x m)) ≤
          (s.card : ℝ) * chainIntervalEntropyBound q R J Δ := by
  let hc : ManyBody.ChainInteraction Λ.card q R :=
    h.extend ManyBody.DomainSupport.toChainSupport
      ManyBody.DomainSupport.toChainSupport_injective (fun Y ↦ Y.1) fun _ ↦ subset_rfl
  have hext : hc.hamiltonian = h.hamiltonian := ManyBody.Interaction.hamiltonian_extend
  exact regionEntropy_domainNeighborhood_biUnion_intervals_le hΩ
    (fun u v ↦ regionEntropy_interval_le hq hJ hΔ hc
        (ManyBody.Interaction.isHermitian_extend_term hh)
        (ManyBody.Interaction.norm_extend_term_le hJ hhJ)
      hΩ (by simpa only [hext] using hgap) (by simpa only [hext] using hspan) u v) s a b m

end TNLean.MPS.AreaLaw

end
