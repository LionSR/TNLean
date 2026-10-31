/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.ShortMomentum.LetterRelations
import TNLean.MPS.Examples.ShortMomentum.WeylSpans
import TNLean.MPS.ParentHamiltonian.IntersectionProperty

/-!
# Long-window intersections for the fifth-root Weyl tensor

When the shared interior has at least eight sites, its word span
is full. Existing trace-pairing reconstruction therefore gives the
one-step intersection, using the inverse of the first physical
letter. No intersection property is supplied as a hypothesis.

The exceptional overlaps producing eight and nine sites are not covered
here. Source context: SPWC10, arXiv:0909.5347, Theorem 5, main.tex lines
850--880; see `docs/audits/2026-10-29_weyl_short_volume_candidate.md`.
-/

open scoped BigOperators

namespace MPSTensor.ShortMomentum

/-- The one-step intersection once the common interior has at
least eight sites. -/
theorem groundSpace_intersection_threeLetterTensor_of_eight_le {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ 5) {K : ℕ} (hK : 8 ≤ K)
    {ψ : NSiteSpace 3 (K + 2)}
    (hLeft : InLeftGround (threeLetterTensor ζ) (K + 1) ψ)
    (hRight : InRightGround (threeLetterTensor ζ) (K + 1) ψ) :
    ψ ∈ groundSpace (threeLetterTensor ζ) (K + 2) := by
  classical
  choose Y hY using fun i ↦ LinearMap.mem_range.mp (hRight i)
  choose Z hZ using fun j ↦ LinearMap.mem_range.mp (hLeft j)
  refine mem_groundSpace_succ_of_intertwine (Z := Z)
    (fun j : Fin 3 ↦ if j = 0 then threeLetterTensor ζ 0 ^ 4 else 0) ?_
    (fun i ↦ (hY i).symm) ?_
  · simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [← pow_succ]
    exact threeLetterTensor_pow_five hζ.pow_eq_one 0
  · intro i j
    apply groundSpaceMap_injective_of_wordSpan_eq_top
      (isNBlkInjective_threeLetterTensor_of_eight_le hζ K hK)
    exact groundSpaceMap_mul_eq_of_restrict (fun i ↦ (hY i).symm)
      (fun j ↦ (hZ j).symm) i j

end MPSTensor.ShortMomentum
