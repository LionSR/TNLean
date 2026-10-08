/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.DependentSpectatorGapEquivalence
import TNLean.MPS.Overlap.Basic

/-!
# Dependent spectators for the joint mixed endpoint boundary coordinates

For every ordered pair \((x,y)\) of block labels, the active coordinates are
\(\mathrm{Fin}(D_x^0)\times\operatorname{Cfg}(d_0,N)\times\mathrm{Fin}(D_y^0)\).
Replacing the exterior multiplicities \(D_x^0D_y^0\) by
\((D_x^0+D_x^1)(D_y^0+D_y^1)\) preserves each common nonnegative norm gap.
The first endpoint dimensions are positive; the second endpoint dimensions
are arbitrary. All ordered pairs, including distinct labels, are retained,
and the label type may be empty.

This is an operator-theoretic specialization for the boundary coordinates
used in GLM23, arXiv:2203.12563, Section 5, lines 1695–1777. Identifying the
actual endpoint Hamiltonians with extensions of one common active family is
a separate step, and is not asserted here.
-/

namespace MPSTensor.MPOSymmetry

variable {r d₀ N : ℕ}

/-- For a fixed family of operators on the full ordered-pair active spaces,
enlarging both nonempty exterior spectator coordinates preserves exactly the
same common nonnegative norm gap. Neither positivity of the operators nor
equality of the two block labels is assumed. The label type may be empty.

Source context: GLM23, arXiv:2203.12563, Section 5, lines 1695–1777.
The identification with actual endpoint Hamiltonians remains separate. -/
theorem jointMixedEndpoint_spectatorGap_iff
    (D₀ D₁ : Fin r → ℕ) (hD₀ : ∀ x, 0 < D₀ x)
    (G : ∀ q : Fin r × Fin r,
      EuclideanSpace ℂ (Fin (D₀ q.1) × Cfg d₀ N × Fin (D₀ q.2)) →L[ℂ]
        EuclideanSpace ℂ (Fin (D₀ q.1) × Cfg d₀ N × Fin (D₀ q.2)))
    {δ : ℝ} (hδ : 0 ≤ δ) :
    (∀ v ∈ (LinearMap.ker (ContinuousLinearMap.dependentRightFiberwiseMap
        (S := fun q : Fin r × Fin r ↦ Fin (D₀ q.1) × Fin (D₀ q.2)) G).toLinearMap)ᗮ,
      δ * ‖v‖ ≤ ‖ContinuousLinearMap.dependentRightFiberwiseMap
        (S := fun q : Fin r × Fin r ↦ Fin (D₀ q.1) × Fin (D₀ q.2)) G v‖) ↔
      ∀ v ∈ (LinearMap.ker (ContinuousLinearMap.dependentRightFiberwiseMap
          (S := fun q : Fin r × Fin r ↦
            Fin (D₀ q.1 + D₁ q.1) × Fin (D₀ q.2 + D₁ q.2)) G).toLinearMap)ᗮ,
        δ * ‖v‖ ≤ ‖ContinuousLinearMap.dependentRightFiberwiseMap
          (S := fun q : Fin r × Fin r ↦
            Fin (D₀ q.1 + D₁ q.1) × Fin (D₀ q.2 + D₁ q.2)) G v‖ := by
  let : ∀ q : Fin r × Fin r, Nonempty (Fin (D₀ q.1) × Fin (D₀ q.2)) :=
    fun q ↦ ⟨⟨⟨0, hD₀ q.1⟩, ⟨0, hD₀ q.2⟩⟩⟩
  let : ∀ q : Fin r × Fin r,
      Nonempty (Fin (D₀ q.1 + D₁ q.1) × Fin (D₀ q.2 + D₁ q.2)) :=
    fun q ↦ ⟨⟨⟨0, by have h := hD₀ q.1; omega⟩,
      ⟨0, by have h := hD₀ q.2; omega⟩⟩⟩
  exact ContinuousLinearMap.norm_gap_dependentRightFiberwiseMap_iff_dependentRightFiberwiseMap
    G hδ

end MPSTensor.MPOSymmetry
