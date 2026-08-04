/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.PerronFrobenius.Existence
import TNLean.Channel.Schwarz.PositiveMapProperties

/-!
# Extremal quantities r(X) and rTilde(X) for positive maps

Wolf Chapter 6, Eqs. (6.29)--(6.30).

## TODO
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix

variable {D : ℕ}

namespace PerronFrobeniusExtremal

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- The set of real λ such that (T - λ)(X) ≥ 0. -/
def rSet (T : Mat →ₗ[ℂ] Mat) (X : Mat) : Set ℝ :=
  {t : ℝ | (T X - (t : ℂ) • X).PosSemidef}

/-- r(X) = sup { t ∈ ℝ | (T - t)(X) ≥ 0 }.  Wolf Eq. (6.29). -/
noncomputable def r (T : Mat →ₗ[ℂ] Mat) (X : Mat) : ℝ :=
  sSup (rSet T X)

/-- rTilde(X) = inf { t ∈ ℝ | (T - t)(X) ≤ 0 }.  Wolf Eq. (6.30). -/
noncomputable def rTilde (T : Mat →ₗ[ℂ] Mat) (X : Mat) : ℝ :=
  sInf {t : ℝ | (T X - (t : ℂ) • X) ≤ 0}

/-- r_max = sup_{X ≥ 0, X ≠ 0} r(X). -/
noncomputable def rMax (T : Mat →ₗ[ℂ] Mat) : ℝ :=
  sSup (r T '' {X | X.PosSemidef ∧ X ≠ 0})

/-- rTildeMax = sup_{X ≥ 0, X ≠ 0} rTilde(X). -/
noncomputable def rTildeMax (T : Mat →ₗ[ℂ] Mat) : ℝ :=
  sSup (rTilde T '' {X | X.PosSemidef ∧ X ≠ 0})

end PerronFrobeniusExtremal
