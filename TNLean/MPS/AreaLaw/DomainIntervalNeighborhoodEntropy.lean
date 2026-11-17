/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.DomainIntervalNeighborhood
import TNLean.MPS.AreaLaw.IntervalNeighborhoodEntropy
import QICLean.Entropy.FiniteProductInformation
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Entropy on intrinsic neighborhoods of interval unions

The intrinsic graph neighborhood of a relative interval is a relative interval.
Subadditivity therefore extends a uniform interval entropy bound to neighborhoods
of finite unions of intervals, including overlapping and empty intervals. Applying
the interval area law gives the bound for the original gapped domain ground state.

Source: TNLean one-dimensional note, `part2a_mps_information.tex`, lines 482–487,
and the interval area-law estimate in Part I.
-/

open ManyBody (interval lineDomainGraph)

open SimpleGraph QuantumCircuit

namespace TNLean.MPS.AreaLaw

/-- Auxiliary entropy bound for intrinsic neighborhoods of finite unions of relative
intervals. Overlaps and empty intervals are permitted.
Source: TNLean note, `part2a_mps_information.tex`, lines 482–487. -/
theorem regionEntropy_domainNeighborhood_biUnion_intervals_le
    {Λ : Finset ℤ} {q : ℕ} {κ : Type*}
    {Ω : EuclideanSpace ℂ (Fin Λ.card → Fin q)} (hΩ : ‖Ω‖ = 1) {c : ℝ}
    (hI : ∀ a b : ℕ,
      Entropy.regionEntropy (n := fun _ : Fin Λ.card ↦ q) (interval Λ.card a b) Ω ≤ c)
    (s : Finset κ) (a b : κ → ℕ) (m : ℕ) :
    Entropy.regionEntropy (n := fun _ : Fin Λ.card ↦ q)
      ((s.biUnion (fun i ↦ interval Λ.card (a i) (b i))).biUnion
        (fun x ↦ ManyBody.graphBall (lineDomainGraph Λ) x m)) Ω ≤ (s.card : ℝ) * c := by
  exact regionEntropy_biUnion_neighborhood_intervals_le hΩ hI _
    (domainNeighborhood_interval_eq Λ · · m) s a b

/-- The original gapped domain Hamiltonian bounds entropy on an intrinsic neighborhood
of a finite interval union.
Source: TNLean note, `part2a_mps_information.tex`, lines 482–487, together with the
interval area-law bound from Part I. -/
theorem DomainHamiltonian.regionEntropy_neighborhood_biUnion_intervals_le
    {Λ : Finset ℤ} {q R : ℕ} {J Δ : ℝ} {κ : Type*}
    (h : DomainHamiltonian Λ q R J) (hq : 1 ≤ q) (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    {E₀ : ℝ} {Ω : EuclideanSpace ℂ (Fin Λ.card → Fin q)}
    (hgs : Matrix.IsGappedGroundState h.operator E₀ Ω Δ)
    (s : Finset κ) (a b : κ → ℕ) (m : ℕ) :
    Entropy.regionEntropy (n := fun _ : Fin Λ.card ↦ q)
      ((s.biUnion (fun i ↦ interval Λ.card (a i) (b i))).biUnion
        (fun x ↦ ManyBody.graphBall (lineDomainGraph Λ) x m)) Ω ≤
          (s.card : ℝ) * chainIntervalEntropyBound q R J Δ := by
  exact regionEntropy_domainNeighborhood_biUnion_intervals_le hgs.1
    (fun u v ↦ regionEntropy_interval_le hq hJ hΔ (h.toChain hJ)
      (by simpa only [h.toChain_operator hJ] using hgs) u v) s a b m

end TNLean.MPS.AreaLaw
