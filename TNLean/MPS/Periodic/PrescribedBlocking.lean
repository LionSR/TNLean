/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.StateVectorDecomposition
import TNLean.MPS.Periodic.BlockingEigenvalues
import TNLean.MPS.Periodic.BlockingFixedSpace
import TNLean.MPS.Periodic.StepOrbitSectors

/-!
# Prescribed blocking of a periodic tensor

The algebraic decomposition in arXiv:1708.00029, Lemma `lem:blocking-arbitrary`,
has gcd(m,p) nonzero blocks. This file obtains the projectors from periodicity,
rather than assuming a supplied cyclic decomposition. For positive blocking,
each compressed block is periodic of period m/gcd(m,p).

**Local fix (powered roots):** The root set uses order m/gcd(m,p); see
`docs/paper-gaps/dccsp17_blocking_peripheral_roots.tex` for the paper's omitted exponent.

## Main results

* `IsPeriodic.exists_stepOrbit_blockDecomposition`: nonzero left-canonical
  compressed blocks, their support isometries, equality of all MPVs, and their
  periodicity at positive blocking lengths.

## References

* De las Cuevas, Cirac, Schuch, Pérez-García, *Irreducible forms of Matrix Product
  States: Theory and Applications*, arXiv:1708.00029, Lemma `lem:blocking-arbitrary`.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-- Prescribed blocking of a periodic tensor into periodic blocks.
Source: arXiv:1708.00029, Lemma `lem:blocking-arbitrary`. -/
theorem IsPeriodic.exists_stepOrbit_blockDecomposition {d D m : ℕ}
    {A : MPSTensor d D} (hA : IsPeriodic m A) (p : ℕ) :
    let _ : NeZero m := ⟨Nat.ne_of_gt hA.period_pos⟩
    ∃ (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
      (dim : Fin (m.gcd p) → ℕ)
      (blocks : (a : Fin (m.gcd p)) → MPSTensor (blockPhysDim d p) (dim a))
      (V : (a : Fin (m.gcd p)) → Matrix (Fin D) (Fin (dim a)) ℂ),
      (∀ u, IsOrthogonalProjection (P u)) ∧ (∑ u, P u) = 1 ∧
      (∀ u, P u ≠ 0) ∧ (∀ u i, P u * A i = A i * P (u + 1)) ∧
      (∀ a, 0 < dim a) ∧ (∑ a, dim a) = D ∧
      (∀ a, IsLeftCanonical (blocks a)) ∧
      SameMPV₂ (blockTensor A p) (toTensorFromBlocks (μ := fun _ => 1) blocks) ∧
      (∀ a, (V a)ᴴ * V a = 1) ∧
      (∀ a, V a * (V a)ᴴ = stepOrbitProjection P p a) ∧
      (∀ a i, blocks a i = (V a)ᴴ * blockTensor A p i * V a) ∧
      (0 < p → ∀ a, IsPeriodic (m / m.gcd p) (blocks a)) := by
  let : NeZero m := ⟨Nat.ne_of_gt hA.period_pos⟩
  obtain ⟨P, hproj, hsum, hne, hshift⟩ := exists_paper_cyclic_projectors_of_isPeriodic A hA
  obtain ⟨dim, blocks, V, hdim, htotal, hcan, hmpv, hiso, hV, hC⟩ :=
    MPSTensor.exists_stepOrbit_blockDecomposition P hproj hsum hne A hA.leftCanonical hshift p
  refine ⟨P, dim, blocks, V, hproj, hsum, hne, hshift, hdim, htotal, hcan,
    hmpv, hiso, hV, hC, ?_⟩
  intro hp a
  exact ⟨hA.isIrreducibleFamily_compressed_stepOrbit P hproj hsum hshift hp a
      (blocks a) (V a) (hiso a) (hV a) (hC a), hcan a,
    Nat.div_gcd_pos_of_pos_left p hA.period_pos,
    hA.peripheral_compressed_stepOrbit_eq P hproj hsum hne hshift hp a
      (blocks a) (V a) (hiso a) (hV a) (hC a)⟩

end MPSTensor
