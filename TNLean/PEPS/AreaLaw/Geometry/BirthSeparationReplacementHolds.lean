/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.BirthSeparationRepair
import TNLean.PEPS.AreaLaw.Geometry.RepairInduction

/-!
# Birth separation of replacements

The uniform repair induction of the area-law companion (Section 11,
`geometry:repair-induction`) holds, so the conditional birth separation of
replacement tiles holds outright.

**Scope restriction (replacement births):** this covers the replacement births
of the source lemma `geometry:birth-separation`, not the births of initial belt
tiles; documented in `docs/paper-gaps/arealaw2d_birth_separation_scope.tex`.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- Birth separation of replacements. There are one fixed `c₁ > 0` and a
threshold `T` such that, for every stopping scale `S_* ≥ T` and every layer
width, every sufficiently large lower layer index gives repair stages in which
every replacement born at a parent of scale `S` has distance at least
`c₁ d(S)^ρ₀` from the final actual region of every earlier or peer identifier
of its label. Source: area-law Section 11, `geometry:birth-separation`,
lines 573–659. -/
theorem exists_isRepairBirthSeparated :
    ∃ c₁ > 0, ∃ T : ℝ, ∀ Sstar, T ≤ Sstar → ∀ C : ℕ, ∃ K : ℕ,
      ∀ (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (k₀ : ℕ)
        (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀), K ≤ k₀ →
          IsRepairBirthSeparated o Λ A C k₀ hC h₀ Sstar c₁ :=
  exists_isRepairBirthSeparated_of_uniformRepairInductionStatement
    uniformRepairInductionStatement_holds

end TNLean.PEPS.AreaLaw.Geometry
