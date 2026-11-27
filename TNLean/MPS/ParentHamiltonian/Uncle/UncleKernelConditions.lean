/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Spectral.Gap.WeightedPositiveKernel
import TNLean.MPS.ParentHamiltonian.Uncle.UncleGroundSpaceInclusion

/-!
# Local conditions for the actual uncle Hamiltonian kernel

The uncle interaction is the matrix of an orthogonal-complement projection in the coordinates of
the two original sites, hence positive semidefinite, and so is the Hamiltonian of its translates
on a ring. Thus the actual finite Hamiltonian vanishes on a vector exactly when every cyclic
restriction of the vector lies in the explicit uncle boundary space.

Source: arXiv:1210.6613, proof of Theorem thm:gs-subspace-uncle,
lines 1050–1065. This identifies the analytic kernel conditions; their
intersection and periodic closure still require separate algebraic proofs.
-/

noncomputable section

open scoped Matrix BigOperators InnerProductSpace ComplexOrder MatrixOrder

namespace MPSTensor

open ManyBody.Interaction (translationInvariant)

variable {d a b : ℕ}

/-- The actual uncle interaction is positive semidefinite, with no injectivity premise.
Source: arXiv:1210.6613, the projector defining the uncle interaction and
proof of thm:gs-subspace-uncle, lines 1050–1065. -/
theorem posSemidef_uncleInteraction
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) :
    (uncleInteraction A B R L).PosSemidef :=
  (posSemidef_toMatrix'_parentInteraction (uncleTensor A B R L) 1).submatrix _

/-- The Hamiltonian of the translates of the uncle interaction on a ring is positive
semidefinite. This is the positivity used in the spectral conclusion of arXiv:1210.6613, proof
of thm:gapless. -/
theorem posSemidef_hamiltonian_uncleInteraction
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) (N : ℕ) [NeZero N] :
    (translationInvariant N (uncleInteraction A B R L)).hamiltonian.PosSemidef :=
  ManyBody.Interaction.posSemidef_hamiltonian fun i ↦ Matrix.nonneg_iff_posSemidef.mp
    (ManyBody.Interaction.translationInvariant_term_nonneg
      (posSemidef_uncleInteraction A B R L).nonneg i)

/-- Vanishing of the explicit uncle projector is exactly membership in its
blocked boundary space, transported to the original two physical sites.
Source: arXiv:1210.6613, eq:uncletensor-2site and the local kernel in
thm:gs-subspace-uncle, lines 1050–1065. -/
theorem uncleInteraction_apply_eq_zero_iff
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (v : EuclideanSpace ℂ (Cfg d 2)) :
    Matrix.toEuclideanLin (uncleInteraction A B R L) v = 0 ↔
      (blockedConfigLinearIsometryEquiv d 1 2).symm v ∈
        groundSpaceES (uncleTensor A B R L) 1 := by
  rw [toEuclideanLin_uncleInteraction_apply, LinearIsometryEquiv.map_eq_zero_iff]
  rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal]

/-- The actual periodic uncle Hamiltonian vanishes exactly when every
cyclic two-site restriction lies in the explicit uncle local kernel.
This is the common-kernel step of arXiv:1210.6613,
thm:gs-subspace-uncle, lines 1050–1065. No perturbation injectivity is
assumed; classifying this intersection is a separate argument. -/
theorem hamiltonian_uncleInteraction_apply_eq_zero_iff
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    {N : ℕ} (hN : 2 ≤ N) (v : EuclideanSpace ℂ (Cfg d N)) :
    haveI : NeZero N := ⟨by omega⟩;
    Matrix.toEuclideanLin
        (translationInvariant N (uncleInteraction A B R L)).hamiltonian v = 0 ↔
      ∀ (i : Fin N) (τ : Cfg d N),
        Matrix.toEuclideanLin (uncleInteraction A B R L)
          (LinearMap.withLpMap 2 (cyclicRestrictₗ (Fin.pos i) 2 i τ) v) = 0 :=
  haveI : NeZero N := ⟨by omega⟩
  toEuclideanLin_hamiltonian_translationInvariant_eq_zero_iff_sections hN _
    (posSemidef_uncleInteraction A B R L) v

end MPSTensor
