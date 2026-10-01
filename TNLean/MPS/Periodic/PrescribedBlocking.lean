/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.StateVectorDecomposition
import TNLean.MPS.Periodic.StepOrbitSectors

/-!
# Prescribed blocking of a periodic tensor

The algebraic decomposition in arXiv:1708.00029, Lemma `lem:blocking-arbitrary`,
has gcd(m,p) nonzero blocks. This file obtains the projectors from periodicity,
rather than assuming a supplied cyclic decomposition. Irreducibility and the
period of the compressed blocks remain separate conclusions.

## Main results

* `IsPeriodic.exists_stepOrbit_blockDecomposition`: nonzero left-canonical
  compressed blocks, their support isometries, and equality of all MPVs.

## References

* De las Cuevas, Cirac, Schuch, Pérez-García, *Irreducible forms of Matrix Product
  States: Theory and Applications*, arXiv:1708.00029, Lemma `lem:blocking-arbitrary`.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-- The algebraic part of prescribed blocking for a periodic tensor.
Source: arXiv:1708.00029, Lemma `lem:blocking-arbitrary`, construction of the blocks
before the peripheral-spectrum argument. No irreducibility or period assertion for the
compressed blocks is made here. -/
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
      (∀ a i, blocks a i = (V a)ᴴ * blockTensor A p i * V a) := by
  let : NeZero m := ⟨Nat.ne_of_gt hA.period_pos⟩
  obtain ⟨P, hproj, hsum, hne, hshift⟩ := exists_paper_cyclic_projectors_of_isPeriodic A hA
  obtain ⟨dim, blocks, V, hblocks⟩ :=
    MPSTensor.exists_stepOrbit_blockDecomposition P hproj hsum hne A hA.leftCanonical hshift p
  exact ⟨P, dim, blocks, V, hproj, hsum, hne, hshift, hblocks⟩

end MPSTensor
