/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.Irreducible.FromSpectral
import TNLean.Wielandt.Primitivity.Equivalence

/-!
# The literal peripheral criterion in the quantum Wielandt equivalence

For a trace-preserving Kraus family, a positive-definite fixed matrix spanning
the fixed eigenspace, together with the absence of other peripheral eigenvalues,
implies irreducibility. Thus the source's third clause needs no separately supplied
irreducibility hypothesis. The channel-generic implication is supplied by QICLean.

## Main results

* `MPSTensor.primitivePaper_iff_exists_simple_peripheral_fixedPoint`:
  the literal equivalence of Proposition 3(a) and (c).
* `MPSTensor.hasEventuallyFullKrausRank_iff_exists_simple_peripheral_fixedPoint`:
  the literal equivalence of Proposition 3(b) and (c).

## References

* Sanz, Pérez-García, Wolf and Cirac, arXiv:0909.5347, strong irreducibility
  at lines 420–430 and Proposition 3 (`prop:equiv`), lines 504–555.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- The source's literal peripheral criterion supplies irreducibility rather than
assuming it. Source: arXiv:0909.5347, Proposition 3(c), lines 420–430 and 504–509. -/
theorem isStronglyIrreduciblePaper_of_simple_peripheral_fixedPoint [NeZero D]
    (A : MPSTensor d D) (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hfix : Kraus.transferMap A ρ = ρ) (hprim : IsPeripherallyPrimitive A)
    (hunique : ∀ σ : Matrix (Fin D) (Fin D) ℂ,
      Kraus.transferMap A σ = σ → ∃ c : ℂ, σ = c • ρ) :
    IsStronglyIrreduciblePaper A := by
  refine ⟨ρ, hρ, hfix, hprim, ?_⟩
  exact isIrreducibleMap_of_channel_posDef_fixedPoint_unique
    (Kraus.transferMap A) (Kraus.isChannel_mapLM A hNorm) ρ hρ hfix
    (fun σ _ hσ ↦ hunique σ hσ)

/-- Paper primitivity is equivalent to the literal positive-definite, simple fixed
eigenspace criterion, with no extra irreducibility premise.
Source: arXiv:0909.5347, Proposition 3(a)↔(c), lines 504–555. -/
theorem primitivePaper_iff_exists_simple_peripheral_fixedPoint [NeZero D]
    (A : MPSTensor d D) (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1) :
    IsPrimitivePaper A ↔
      ∃ ρ : Matrix (Fin D) (Fin D) ℂ, ρ.PosDef ∧ Kraus.transferMap A ρ = ρ ∧
        IsPeripherallyPrimitive A ∧
          ∀ σ : Matrix (Fin D) (Fin D) ℂ,
            Kraus.transferMap A σ = σ → ∃ c : ℂ, σ = c • ρ := by
  constructor
  · intro hA
    obtain ⟨ρ, hP, hρ⟩ := isPrimitiveMPS_of_isStronglyIrreduciblePaper A hNorm
      (isStronglyIrreduciblePaper_of_isPrimitivePaper A hNorm hA)
    refine ⟨ρ, hρ, hP.fixedPoint_is_fixed, hP.isPrimitive, ?_⟩
    intro σ hσ
    exact ⟨Matrix.trace σ / Matrix.trace ρ, hP.fixedPoint_unique σ hσ⟩
  · rintro ⟨ρ, hρ, hfix, hprim, hunique⟩
    exact (primitivePaper_iff_stronglyIrreducible A hNorm).mpr
      (isStronglyIrreduciblePaper_of_simple_peripheral_fixedPoint
        A hNorm ρ hρ hfix hprim hunique)

/-- Eventually full Kraus rank is equivalent to the source's literal peripheral
criterion. Source: arXiv:0909.5347, Proposition 3(b)↔(c), lines 504–555. -/
theorem hasEventuallyFullKrausRank_iff_exists_simple_peripheral_fixedPoint [NeZero D]
    (A : MPSTensor d D) (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1) :
    HasEventuallyFullKrausRank A ↔
      ∃ ρ : Matrix (Fin D) (Fin D) ℂ, ρ.PosDef ∧ Kraus.transferMap A ρ = ρ ∧
        IsPeripherallyPrimitive A ∧
          ∀ σ : Matrix (Fin D) (Fin D) ℂ,
            Kraus.transferMap A σ = σ → ∃ c : ℂ, σ = c • ρ :=
  (primitivePaper_iff_hasEventuallyFullKrausRank A hNorm).symm.trans
    (primitivePaper_iff_exists_simple_peripheral_fixedPoint A hNorm)

end MPSTensor
