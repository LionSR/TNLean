/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.SnakeGridApproximation
import TNLean.PEPS.AreaLaw.AreaLawTheorem

/-!
# Exponential snake MPS approximation of a gapped square ground state

The already proved uniform two-dimensional area law supplies the area-law
premise of the snake construction. The Hamiltonian has arbitrary finite-range
interactions on the open square, with no translation-invariance assumption.

Source: the square-grid comparison in the polynomial-PEPS manuscript,
Section 1; the threshold and normalization argument is
`part2a_mps_information.tex`, `sec:shortcut`, `thm:Bshort`, lines 73–92.
-/

open TNLean.Lattice

namespace TNLean.MPS.AreaLaw

/-- Every gapped finite-range ground vector on an open `L × L` square,
`L ≥ 2`, has a normalized open snake MPS within vector norm `1/L`, with
bond dimension at most `exp (C L)`. The constant depends only on the fixed
local dimension, interaction range, term-norm bound and gap.
Source: the square-grid comparison in the polynomial-PEPS manuscript,
Section 1, and the two-line route of `part2a_mps_information.tex`,
`thm:Bshort`, lines 73–92. -/
theorem exists_snakeGridMPS (q : ℕ) (hq : 1 ≤ q) (R : ℕ)
    (J Δ : ℝ) (hJ : 0 < J) (hΔ : 0 < Δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℕ, 2 ≤ L →
      ∀ H : LocalHamiltonian (PEPS.AreaLaw.rectangularDomain L L) q R J,
      ∀ E₀ : ℝ, ∀ Ω : StateSpace (PEPS.AreaLaw.rectangularDomain L L) q,
        IsGappedGroundState _ q H.operator E₀ Ω Δ →
        ∃ (D : ℕ) (Φ : StateSpace (PEPS.AreaLaw.rectangularDomain L L) q),
          ‖Φ‖ = 1 ∧ IsOpenMPS (L * L) q D (fun x ↦ snakeGridStateEquiv L q Φ x) ∧
          ‖Φ - Ω‖ ≤ 1 / (L : ℝ) ∧ (D : ℝ) ≤ Real.exp (C * L) :=
  exists_snakeGridMPS_of_uniformAreaLaw PEPS.AreaLaw.uniformAreaLaw q hq R J Δ hJ hΔ

end TNLean.MPS.AreaLaw
