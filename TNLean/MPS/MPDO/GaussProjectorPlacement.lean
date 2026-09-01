/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.GaussProjector
import TNLean.MPS.MPDO.PhysicalGibbsEmbedding

/-!
# Finite-chain placement of the local Gauss projector

The local Gauss projector is reindexed from a two-site matter configuration
and two gauge-leg labels into two chain-site coordinates. It is then embedded
on the periodic window beginning at `j`. This is the position-dependent
projector of FBC25, Equation `eq:gauge_projs` (arXiv:2502.20257,
lines 3494--3499).

Gauged-MPS invariance, commutativity, a spectral gap, and ground-space
completeness are not treated here.
-/

noncomputable section

namespace TNLean.Algebra

variable (d : ℕ) (G : Type*) [Group G] [Fintype G]

/-- The coordinate equivalence from a two-site matter configuration and its
ordered pair of gauge labels to two chain sites, each carrying one matter and
one gauge label.

This is the coordinate identification used to place the local kernel from
FBC25, Equation `eq:gauge_projs` (arXiv:2502.20257, lines 3494--3499). -/
def gaussLocalCoordinateEquiv :
    ((Fin 2 → Fin d) × (G × G)) ≃
      (Fin 2 → Fin (Fintype.card (Fin d × G))) :=
  ((Equiv.refl (Fin 2 → Fin d)).prodCongr
      (finTwoArrowEquiv G).symm).trans
    ((Equiv.arrowProdEquivProdArrow (Fin 2) (fun _ ↦ Fin d)
      (fun _ ↦ G)).symm.trans
        (Equiv.arrowCongr (Equiv.refl (Fin 2))
          (Fintype.equivFin (Fin d × G))))

@[simp]
theorem gaussLocalCoordinateEquiv_apply_zero
    (x : (Fin 2 → Fin d) × (G × G)) :
    gaussLocalCoordinateEquiv d G x 0 =
      Fintype.equivFin (Fin d × G) (x.1 0, x.2.1) :=
  rfl

@[simp]
theorem gaussLocalCoordinateEquiv_apply_one
    (x : (Fin 2 → Fin d) × (G × G)) :
    gaussLocalCoordinateEquiv d G x 1 =
      Fintype.equivFin (Fin d × G) (x.1 1, x.2.2) :=
  rfl

variable [DecidableEq G]

/-- The local Gauss projector reindexed into two-site chain-window
coordinates. -/
def gaussWindowProjector
    (R : G → G → Matrix.unitaryGroup (Fin 2 → Fin d) ℂ) :
    Matrix (Fin 2 → Fin (Fintype.card (Fin d × G)))
      (Fin 2 → Fin (Fintype.card (Fin d × G))) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ (gaussLocalCoordinateEquiv d G)
    (gaussProjector R)

/-- Reindexing the local Gauss projector into chain-window coordinates
preserves its star-projection property. -/
theorem isStarProjection_gaussWindowProjector
    (R : G → G → Matrix.unitaryGroup (Fin 2 → Fin d) ℂ) :
    IsStarProjection (gaussWindowProjector d G R) := by
  rw [isStarProjection_iff'] at *
  obtain ⟨hidempotent, hselfAdjoint⟩ := isStarProjection_gaussProjector R
  constructor
  · rw [gaussWindowProjector, ← map_mul, hidempotent]
  · rw [gaussWindowProjector, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_reindex]
    simpa [Matrix.star_eq_conjTranspose] using congrArg
      (Matrix.reindex (gaussLocalCoordinateEquiv d G)
        (gaussLocalCoordinateEquiv d G)) hselfAdjoint

/-- The local Gauss projector placed on the periodic two-site window beginning
at `j`, as in FBC25, Equation `eq:gauge_projs` (arXiv:2502.20257,
lines 3494--3499). -/
def placedGaussProjector
    (N : ℕ) (hN : 2 ≤ N) (j : Fin N)
    (R : G → G → Matrix.unitaryGroup (Fin 2 → Fin d) ℂ) :
    MPOTensor.ChainOperator (Fintype.card (Fin d × G)) N :=
  MPOTensor.embedLocalOperator 2 N hN j (gaussWindowProjector d G R)

/-- The Gauss projector placed on any periodic two-site window is a star
projection. -/
theorem isStarProjection_placedGaussProjector
    (N : ℕ) (hN : 2 ≤ N) (j : Fin N)
    (R : G → G → Matrix.unitaryGroup (Fin 2 → Fin d) ℂ) :
    IsStarProjection (placedGaussProjector d G N hN j R) :=
  MPOTensor.embedLocalOperator_isStarProjection 2 N hN j
    (isStarProjection_gaussWindowProjector d G R)

end TNLean.Algebra
