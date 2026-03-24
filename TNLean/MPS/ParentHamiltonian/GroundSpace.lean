import TNLean.MPS.Defs
import TNLean.MPS.Overlap.Basic


/-!
# Ground space placeholders

Scaffolding for parent-Hamiltonian ground-space development.
-/

namespace MPSTensor

open scoped BigOperators

/-- `N`-site physical configurations, reusing the project-wide `Cfg` abbreviation. -/
abbrev NSiteCfg (d N : ℕ) := Cfg d N

/-- `N`-site coefficient-function space. -/
abbrev NSiteSpace (d N : ℕ) := NSiteCfg d N → ℂ

variable {d D : ℕ}

/-- Placeholder map whose eventual image will define the ground space. -/
noncomputable def groundSpaceMap (A : MPSTensor d D) (L : ℕ) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] NSiteSpace d L := 0

/-- Placeholder definition of the local ground space. -/
noncomputable def groundSpace (A : MPSTensor d D) (L : ℕ) :
    Submodule ℂ (NSiteSpace d L) :=
  LinearMap.range (groundSpaceMap (d := d) (D := D) A L)

end MPSTensor
