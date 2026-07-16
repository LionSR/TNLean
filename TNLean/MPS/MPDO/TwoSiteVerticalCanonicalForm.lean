/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.HorizontalBlocking
import TNLean.MPS.MPDO.VerticalCanonicalForm

/-!
# Vertical canonical form before and after two-site blocking

For a horizontally canonical matrix product density operator, Proposition 4.13
applies both to the original tensor and to its two-site physical blocking.
This is the first step of the two-site comparison in Appendix C.4 of
arXiv:1606.00608.
-/

namespace MPOTensor

variable {d D : ℕ}

/-- A horizontally canonical matrix product density operator and its two-site
blocking are both in vertical canonical form.

Source: arXiv:1606.00608, Appendix C.4, lines 1951--1956. -/
theorem verticalCF_and_blockTwo_of_horizontalCF (M : MPOTensor d D)
    (hHorizontal : IsHorizontalCF M) (hM : IsMPDO M) :
    IsVerticalCF M ∧ IsVerticalCF (blockTwo M) := by
  exact ⟨verticalCF_of_horizontalCF M hHorizontal hM,
    verticalCF_of_horizontalCF (blockTwo M) hHorizontal.blockTwo hM.blockTwo⟩

end MPOTensor
