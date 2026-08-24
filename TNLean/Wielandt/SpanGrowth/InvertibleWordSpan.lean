/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.Wielandt.SpanGrowth.InvertibleWordSpan
import TNLean.Wielandt.Primitivity.Definitions
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Invertible-element word span growth for MPS tensors

This file preserves the established `MPSTensor` interface to finite-family
word-span growth. The underlying algebra is stated in `namespace Kraus` and
uses `Kraus.HasEventuallyFullWordSpan` directly. The MPS-specific rank,
normality, and index consequences remain here.
-/

open scoped Matrix ComplexOrder BigOperators
open Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- Normality is unchanged after adding a redundant one-step generator. -/
theorem isNormal_oneStepAugment_of_mem_wordSpan_one (A : MPSTensor d D)
    {X : Matrix (Fin D) (Fin D) ℂ} (hX : X ∈ Kraus.wordSpan A 1)
    (hN : Kraus.IsNormal A) :
    Kraus.IsNormal (Kraus.oneStepAugment A X) := by
  obtain ⟨N, hNpos, hNtop⟩ := (hasEventuallyFullKrausRank_iff_isNormal A).2 hN
  exact (hasEventuallyFullKrausRank_iff_isNormal (Kraus.oneStepAugment A X)).1
    ⟨N, hNpos, by simpa [Kraus.wordSpan_oneStepAugment_eq A hX N] using hNtop⟩

/-- The Kraus rank is unchanged after adding a redundant one-step generator. -/
theorem krausRank_oneStepAugment (A : MPSTensor d D)
    {X : Matrix (Fin D) (Fin D) ℂ} (hX : X ∈ Kraus.wordSpan A 1) :
    krausRank (Kraus.oneStepAugment A X) = krausRank A := by
  unfold krausRank
  rw [Kraus.wordSpan_oneStepAugment_eq A hX 1]

private theorem hasEventuallyFullWordSpan_of_isNormal_of_isUnit
    (A : MPSTensor d D) (i₀ : Fin d) (hU : IsUnit (A i₀))
    (hN : Kraus.IsNormal A) : Kraus.HasEventuallyFullWordSpan A := by
  obtain ⟨N, _hNpos, hNtop⟩ := (hasEventuallyFullKrausRank_iff_isNormal A).2 hN
  exact Filter.eventually_atTop.mpr
    ⟨N, fun m hm => Kraus.wordSpan_eq_top_of_ge_of_isUnit A i₀ hU hNtop hm⟩

/-- If an MPS tensor is normal and has an invertible entry, then the exact
word span at level `D² - krausRank A + 1` is full.

Paper: arXiv:0909.5347, Theorem 1 case (2); Wolf, Theorem 6.9. -/
theorem wordSpan_eq_top_of_isNormal_of_isUnit (A : MPSTensor d D)
    (i₀ : Fin d) (hU : IsUnit (A i₀)) (hN : Kraus.IsNormal A) :
    Kraus.wordSpan A (D ^ 2 - krausRank A + 1) = ⊤ := by
  unfold krausRank Kraus.wordSpan
  exact Kraus.wordSpan_eq_top_of_hasEventuallyFullWordSpan_of_isUnit A i₀ hU
    (hasEventuallyFullWordSpan_of_isNormal_of_isUnit A i₀ hU hN)

/-- The invertible-case numerical bound on the full-Kraus-rank index.

Paper: arXiv:0909.5347, Theorem 1 case (2); Wolf, Theorem 6.9. -/
theorem iIndex_le_of_isNormal_of_isUnit (A : MPSTensor d D)
    (i₀ : Fin d) (hU : IsUnit (A i₀)) (hN : Kraus.IsNormal A) :
    iIndex A ≤ D ^ 2 - krausRank A + 1 := by
  rw [iIndex]
  exact Nat.sInf_le ⟨by omega,
    wordSpan_eq_top_of_isNormal_of_isUnit A i₀ hU hN⟩

end MPSTensor
