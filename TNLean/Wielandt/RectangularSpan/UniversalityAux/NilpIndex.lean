/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Kraus.Wielandt.RectangularSpan.UniversalityAux.NilpIndex
import TNLean.Wielandt.RectangularSpan.UniversalityAux.Basic

/-!
# Nilpotent-index rectangular-span growth compatibility names

The nilpotent-index growth statements hold for arbitrary finite matrix families.
This module retains their established names for matrix product tensors.
-/

open scoped Matrix

namespace MPSTensor

open Matrix Module Wielandt

variable {d D : ℕ}

/-- Left multiplication raises the nilpotent-index rectangular word level by one. -/
theorem mulLeft_mem_rectSpan_nilpIndex_succ
    (A : MPSTensor d D) (i₀ : Fin d) (n : ℕ)
    {X : Matrix (Fin D) (Fin D) ℂ}
    (hX : X ∈ rectSpan ((A i₀) ^ nilpIndex (toLin' (A i₀))) A n) :
    (A i₀) * X ∈ rectSpan ((A i₀) ^ nilpIndex (toLin' (A i₀))) A (n + 1) :=
  Kraus.mulLeft_mem_rectSpan_nilpIndex_succ A i₀ n hX

/-- Left multiplication between consecutive nilpotent-index rectangular spans. -/
noncomputable def rectSpanNilpIndexLeftStep
    (A : MPSTensor d D) (i₀ : Fin d) (n : ℕ) :
    (rectSpan ((A i₀) ^ nilpIndex (toLin' (A i₀))) A n) →ₗ[ℂ]
      (rectSpan ((A i₀) ^ nilpIndex (toLin' (A i₀))) A (n + 1)) :=
  Kraus.rectSpanNilpIndexLeftStep A i₀ n

/-- Finrank is non-decreasing along the nilpotent-index rectangular spans. -/
theorem rectSpan_nilpIndex_finrank_mono
    (A : MPSTensor d D) (i₀ : Fin d) (n : ℕ) :
    finrank ℂ (rectSpan ((A i₀) ^ nilpIndex (toLin' (A i₀))) A n) ≤
      finrank ℂ (rectSpan ((A i₀) ^ nilpIndex (toLin' (A i₀))) A (n + 1)) :=
  Kraus.rectSpan_nilpIndex_finrank_mono A i₀ n

/-- Equal consecutive finranks make the nilpotent-index left step surjective. -/
theorem rectSpanNilpIndexLeftStep_surjective_of_finrank_eq
    (A : MPSTensor d D) (i₀ : Fin d) (n : ℕ)
    (hfin : finrank ℂ (rectSpan ((A i₀) ^ nilpIndex (toLin' (A i₀))) A n) =
            finrank ℂ (rectSpan ((A i₀) ^ nilpIndex (toLin' (A i₀))) A (n + 1))) :
    Function.Surjective (rectSpanNilpIndexLeftStep A i₀ n) :=
  Kraus.rectSpanNilpIndexLeftStep_surjective_of_finrank_eq A i₀ n hfin

end MPSTensor
