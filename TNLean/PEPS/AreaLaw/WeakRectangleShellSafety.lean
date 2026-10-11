/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.SafeRectangleDilation
import TNLean.PEPS.AreaLaw.Geometry.LatticeDyadicRect

/-!
# Safety of selected squares in a weak-rectangle shell

A safe rectangle controls the selected squares in its dilated shell
whenever the square and dilation radii fit in its original clearance.
This uses the safe-box condition and does not require template separation.

Source: OpenAI, A two-dimensional area law from a global spectral gap,
September 24, 2026, proof of Proposition 9.5, 08-scanner.tex, lines 717–729,
at openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
The scalar clearance condition is stated explicitly for this auxiliary lemma.
Original formalization from the manuscript; no upstream Lean proof text reused.
-/

namespace TNLean.PEPS.AreaLaw

/-- Every selected square is safe when the cap and dilation radii fit in the
parent clearance. Source: proof of Proposition 9.5, 08-scanner.tex,
lines 723–729. -/
theorem IsSafe.isSafe_cappedDyadicPartition_shell
    {Λ : Finset (ℤ × ℤ)} {A : Finset (Site Λ)} {D₀ : ℕ} {Q : IntRect}
    (hsafe : IsSafe Λ A D₀ Q) (j L K k : ℕ) (z : ℤ × ℤ)
    (hj : j ≤ L) (hcap : 2 ^ K ≤ L)
    (hbudget : D₀ * L + L ≤ D₀ * Q.size)
    (hcell : (k, z) ∈ Geometry.cappedDyadicPartition
      ((Q.dilate j).toFinset \ Q.toFinset) K) :
    IsSafe Λ A D₀ (Geometry.latticeDyadicRect k z) := by
  obtain ⟨hk, hsub, _⟩ := (Geometry.mem_cappedDyadicPartition _ _ _ _).mp hcell
  have hsize : (Geometry.latticeDyadicRect k z).size ≤ L := by
    rw [Geometry.size_latticeDyadicRect]
    exact (Nat.pow_le_pow_right (n := 2) (by decide) hk).trans hcap
  have hcellBudget : D₀ * (Geometry.latticeDyadicRect k z).size + j ≤ D₀ * Q.size :=
    (Nat.add_le_add (Nat.mul_le_mul_left D₀ hsize) hj).trans hbudget
  apply hsafe.of_subset_dilate (j := j) ?_ hcellBudget
  simpa only [Geometry.toFinset_latticeDyadicRect] using
    hsub.trans Finset.sdiff_subset

end TNLean.PEPS.AreaLaw
