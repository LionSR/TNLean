/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairDescendants

/-!
# Counting actual repair occurrences

Each child occurrence retains its parent and one of the nine centered
offsets. These data determine the occurrence, independently of geometric
separation of the mark locations.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, child marks, lines 404–409 and 506–514;
and `geometry:descendant-count`, lines 670–681.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

variable (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
  (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (Sstar : ℝ)

local notation "𝔇" => repairStage o Λ A C k₀ hC h₀ Sstar

/-- The recorded pair of centered-offset indices of an actual child.
Source: area-law Section 11, lines 404–409 and 506–514. -/
def repairMarkOffset (j : ℕ) (q : (𝔇 (j + 1)).markIndex) : Fin 3 × Fin 3 :=
  (show RepairNextMarkIndex j (𝔇 j).scale Sstar from q).2.2

/-- An actual child occurrence is determined by its parent occurrence and
its recorded offset. No assertion about distinct spatial locations is used.
Source: area-law Section 11, lines 404–409 and 506–514. -/
theorem repairMarkParent_repairMarkOffset_injective (j : ℕ) :
    Function.Injective (fun q : (𝔇 (j + 1)).markIndex ↦
      (repairMarkParent o Λ A C k₀ hC h₀ Sstar j q,
        repairMarkOffset o Λ A C k₀ hC h₀ Sstar j q)) := by
  exact fun q r h ↦
    Prod.ext (Subtype.ext (q.1.property.trans r.1.property.symm))
      (Prod.ext (Subtype.ext (congrArg Prod.fst h))
        (congrArg (fun z : (𝔇 j).markIndex × (Fin 3 × Fin 3) ↦ z.2) h))

end TNLean.PEPS.AreaLaw.Geometry
