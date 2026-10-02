/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.RepresentationTheta
import TNLean.Algebra.ComplexSqrt

/-!
# Square-root weights on irreducible bond sectors

The square of the fourth-root operator acts by the square root of the
dimension-to-multiplicity ratio. On a multiplicity-one sector its weight is
the square root of the irreducible dimension. These are the bond weights
obtained by moving the two endpoint fourth-root factors onto one bond.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Section 7,
`Papers/1001.3807/paper_v3.tex`, lines 2977–3007.
-/

namespace Representation

variable {G V : Type*} [Group G] [Fintype G]
variable [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- Two endpoint fourth-root weights give the square-root weight on an
irreducible bond sector. Source: SCP10, Section 7, lines 2977–3007,
extended to arbitrary occurring multiplicities. -/
theorem thetaOperator_sq_apply_of_mem (ρ : Representation ℂ G V)
    (S : Subrepresentation ρ) [S.toRepresentation.IsIrreducible]
    {v : V} (hv : v ∈ S) :
    (thetaOperator ρ ^ 2) v =
      (Real.sqrt ((S.toRepresentation.character 1).re /
        (characterMultiplicity ρ S.toRepresentation.character).re) : ℂ) • v := by
  rw [pow_two, Module.End.mul_apply, thetaOperator_apply_of_mem ρ S hv,
    map_smul, thetaOperator_apply_of_mem ρ S hv, smul_smul, ← pow_two,
    Complex.ofReal_sqrt_sq _ (Real.sqrt_nonneg _)]

/-- On a multiplicity-one irreducible sector, the bond weight is the square
root of its dimension. Source: SCP10, Section 7, lines 2992–3007. -/
theorem thetaOperator_sq_apply_of_multiplicity_one (ρ : Representation ℂ G V)
    (S : Subrepresentation ρ) [S.toRepresentation.IsIrreducible]
    (hm : characterMultiplicity ρ S.toRepresentation.character = 1)
    {v : V} (hv : v ∈ S) :
    (thetaOperator ρ ^ 2) v =
      (Real.sqrt (Module.finrank ℂ S.toSubmodule : ℝ) : ℂ) • v := by
  rw [thetaOperator_sq_apply_of_mem ρ S hv, hm, char_one]
  simp only [Complex.natCast_re, Complex.one_re, div_one]

end Representation
