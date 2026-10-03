/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.PhysicalInteractionGap
import TNLean.MPS.Symmetry.PhysicalSpectatorCoordinates
import TNLean.MPS.Symmetry.TwoSiteBondInteraction

/-!
# Independent virtual bonds with additional physical sectors

The active virtual-pair sector carries the original independent-bond
interaction. Every neighboring pair that meets either additional physical
sector carries the identity penalty. This realizes the unused-state
penalty in the common physical space of arXiv:1010.3732, Section II.F.2,
equation eq:1d-sym:jointsym, in coordinates where neighboring terms commute.
-/

open scoped Matrix Kronecker

namespace Matrix

/-- The active pair carries the prescribed virtual bond; every pair
meeting an additional physical sector carries the identity. Source context:
arXiv:1010.3732, Section II.F.2, equation eq:1d-sym:jointsym. -/
noncomputable def physicalSpectatorEdgeInteraction (K d₀ d₁ : ℕ)
    (B : Matrix (Fin K × Fin K) (Fin K × Fin K) ℂ) (q h : Fin 3) :
    Matrix (EtaEdgeIndex ![K, d₀, d₁] ![K, 1, 1] q h)
      (EtaEdgeIndex ![K, d₀, d₁] ![K, 1, 1] q h) ℂ :=
  if hq : q = 0 then
    if hh : h = 0 then by
      subst q
      subst h
      exact B
    else 1
  else 1

/-- Projection-valued active bonds give projection-valued interactions
on every pair of sectors. Source context: arXiv:1010.3732,
Section II.F.2, equation eq:1d-sym:jointsym. -/
theorem physicalSpectatorEdgeInteraction_isStarProjection (K d₀ d₁ : ℕ)
    (B : Matrix (Fin K × Fin K) (Fin K × Fin K) ℂ)
    (hB : IsStarProjection B) (q h : Fin 3) :
    IsStarProjection (physicalSpectatorEdgeInteraction K d₀ d₁ B q h) := by
  unfold physicalSpectatorEdgeInteraction
  split_ifs with hq hh
  · subst q
    subst h
    exact hB
  all_goals exact IsStarProjection.one _

end Matrix

namespace MPSTensor

/-- Place a virtual bond in the active sector and penalize all other
pairs of sectors by the identity. Source context: arXiv:1010.3732,
Section II.F.2, equation eq:1d-sym:jointsym. -/
noncomputable def physicalSpectatorBondInteraction (K d₀ d₁ : ℕ)
    (B : Matrix (Fin K × Fin K) (Fin K × Fin K) ℂ) :
    MPOTensor.ChainOperator ((K * K + d₀) + d₁) 2 :=
  sectorBondInteraction ![K, d₀, d₁] ![K, 1, 1]
    (Matrix.physicalSpectatorEquiv K d₀ d₁)
    (Matrix.physicalSpectatorEdgeInteraction K d₀ d₁ B)

/-- An orthogonal-projection virtual bond gives an orthogonal-projection
interaction on the common physical space. Source context: arXiv:1010.3732,
Section II.F.2, equation eq:1d-sym:jointsym. -/
theorem physicalSpectatorBondInteraction_isStarProjection (K d₀ d₁ : ℕ)
    (B : Matrix (Fin K × Fin K) (Fin K × Fin K) ℂ)
    (hB : IsStarProjection B) :
    IsStarProjection (physicalSpectatorBondInteraction K d₀ d₁ B) := by
  exact sectorBondInteraction_isStarProjection _ _ _ _
    (Matrix.physicalSpectatorEdgeInteraction_isStarProjection K d₀ d₁ B hB)

/-- All periodic translates of the extended independent-bond interaction
commute. Source context: arXiv:1010.3732, Sections II.D.2 and II.F.2,
equation eq:1d-sym:jointsym. -/
theorem physicalSpectatorBondInteraction_translate_commute {N : ℕ} [NeZero N]
    (K d₀ d₁ : ℕ) (B : Matrix (Fin K × Fin K) (Fin K × Fin K) ℂ)
    (hN : 2 ≤ N) (i j : Fin N) :
    Commute (MPOTensor.embedLocalOperator 2 N hN i
      (physicalSpectatorBondInteraction K d₀ d₁ B))
      (MPOTensor.embedLocalOperator 2 N hN j
        (physicalSpectatorBondInteraction K d₀ d₁ B)) := by
  exact sectorBondInteraction_translate_commute _ _ _ _ hN i j

/-- The enlarged independent-bond Hamiltonian has no spectral values
between zero and one, uniformly in the chain length and in the dimensions
of the additional physical sectors. Source context: arXiv:1010.3732,
Sections II.D.2 and II.F.2, equation eq:1d-sym:jointsym. -/
theorem physicalSpectatorBondInteraction_spectrum_gap_one {N : ℕ}
    (K d₀ d₁ : ℕ) (B : Matrix (Fin K × Fin K) (Fin K × Fin K) ℂ)
    (hB : IsStarProjection B) (hN : 2 ≤ N) :
    ∀ z ∈ spectrum ℂ
      (interactionHamiltonian (physicalSpectatorBondInteraction K d₀ d₁ B) hN),
      0 ≤ z.re ∧ (z.re = 0 ∨ 1 ≤ z.re) := by
  exact sectorBondInteraction_spectrum_gap_one _ _ _ _
    (Matrix.physicalSpectatorEdgeInteraction_isStarProjection K d₀ d₁ B hB) hN

end MPSTensor
