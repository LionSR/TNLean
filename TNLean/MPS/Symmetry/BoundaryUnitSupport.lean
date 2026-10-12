/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BoundaryClosedness
import TNLean.MPS.ParentHamiltonian.Defs
import TNLean.MPS.ParentHamiltonian.IntersectionProperty

/-!
# A boundary unit fixes the MPS support

Suppose arbitrary-boundary compatibility chooses one output state boundary at
all positive lengths. If a fixed operator boundary represents the physical
identity at one positive length where the MPS boundary map is injective, that
boundary fixes every boundary MPS at every positive length. Indeed, the identity
at the injectivity length forces the output state boundary to equal the input.

Consequently, writing \(Q_n\) for this boundary operator and \(P_n\) for the
canonical orthogonal projection onto the MPS ground space gives \(Q_nP_n=P_n\).
There is no nonzero-dimension assumption, and no assertion about length zero.

This supplies a sufficient condition for the unit-support normalization used in
GLM23 Appendix B. A physical unital weak-Hopf realization would still have to
produce and identify the boundary in these hypotheses. No weak Hopf algebra,
integral, adjoint closure, or general block-injective classification is
constructed here. In particular, \(Q_n\) is not asserted to be the ambient
identity, a projection, or an adjoint-preserving representation at every length.

## References

* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, `eq:compatible`,
  lines 431--469; Section 5, lines 1236--1320; Appendix B, lines 2463--2466.
* `docs/paper-gaps/glm23_wha_parent_completion.tex` records the remaining
  weak-Hopf realization and averaging obligations.
-/

open scoped Matrix

namespace MPOTensor

variable {d D₁ D₂ L n : ℕ} {T : MPOTensor d D₁} {A : MPSTensor d D₂}

/-- One physical identity at a positive injectivity length fixes every
boundary MPS at every positive length. The output boundary is identified using
the length-independent quantifier order of GLM23 `eq:compatible`.

This is a sufficient unit-support criterion for Appendix B, lines 2463--2466,
not a construction of the weak-Hopf unit. The same boundary `U` is used at the
calibration length and at the target length, which need not be larger. -/
theorem IsBoundaryCompatible.mpoWithBoundary_mulVec_eq_of_one_length_eq_one
    (h : IsBoundaryCompatible T A) (hInj : Kraus.IsNBlkInjective A L)
    (hL : 0 < L) {U : Matrix (Fin D₁) (Fin D₁) ℂ}
    (hU : mpoWithBoundary T U L = 1)
    (X : Matrix (Fin D₂) (Fin D₂) ℂ) (hn : 0 < n) :
    mpoWithBoundary T U n *ᵥ MPSTensor.mpvWithBoundary A X =
      (MPSTensor.mpvWithBoundary A X : (Fin n → Fin d) → ℂ) := by
  obtain ⟨Z, hZ⟩ := h U X
  have hZX : Z = X := by
    apply MPSTensor.groundSpaceMap_injective_of_isNBlkInjective hInj
    simpa only [hU, Matrix.one_mulVec, MPSTensor.mpvWithBoundary_eq_groundSpaceMap]
      using (hZ L hL).symm
  subst Z
  exact hZ n hn

/-- For a one-site-injective MPS, a physical identity at one site supplies the
positive-length unit-support condition of GLM23 Appendix B, lines 2463--2466.
No identity on the empty chain is required or concluded. -/
theorem IsBoundaryCompatible.mpoWithBoundary_mulVec_eq_of_one_site_eq_one
    (h : IsBoundaryCompatible T A) (hInj : Kraus.IsInjective A)
    {U : Matrix (Fin D₁) (Fin D₁) ℂ} (hU : mpoWithBoundary T U 1 = 1)
    (X : Matrix (Fin D₂) (Fin D₂) ℂ) (hn : 0 < n) :
    mpoWithBoundary T U n *ᵥ MPSTensor.mpvWithBoundary A X =
      (MPSTensor.mpvWithBoundary A X : (Fin n → Fin d) → ℂ) :=
  h.mpoWithBoundary_mulVec_eq_of_one_length_eq_one
    (Kraus.isNBlkInjective_one_of_isInjective hInj) Nat.one_pos hU X hn

/-- The same operator boundary fixes the entire local MPS ground space.
This is the subspace form of the unit-support step in GLM23 Appendix B,
lines 2463--2466, under the stated identity and injectivity hypotheses. -/
theorem IsBoundaryCompatible.mulVec_eq_of_mem_groundSpace_of_one_length_eq_one
    (h : IsBoundaryCompatible T A) (hInj : Kraus.IsNBlkInjective A L)
    (hL : 0 < L) {U : Matrix (Fin D₁) (Fin D₁) ℂ}
    (hU : mpoWithBoundary T U L = 1) (hn : 0 < n)
    {ψ : MPSTensor.NSiteSpace d n} (hψ : ψ ∈ MPSTensor.groundSpace A n) :
    mpoWithBoundary T U n *ᵥ ψ = ψ := by
  obtain ⟨X, rfl⟩ := hψ
  simpa only [MPSTensor.mpvWithBoundary_eq_groundSpaceMap] using
    h.mpoWithBoundary_mulVec_eq_of_one_length_eq_one hInj hL hU X hn

attribute [local instance] MPSTensor.groundSpaceES_hasOrthogonalProjection

/-- The actual canonical ground-space projection satisfies \(Q_nP_n=P_n\).
This is the unit-support normalization needed in GLM23 Appendix B,
lines 2463--2466. Adjoint closure, positivity, and idempotence of \(Q_n\)
are not needed for this one-sided composition identity. -/
theorem IsBoundaryCompatible.toEuclideanLin_comp_groundSpaceES_starProjection
    (h : IsBoundaryCompatible T A) (hInj : Kraus.IsNBlkInjective A L)
    (hL : 0 < L) {U : Matrix (Fin D₁) (Fin D₁) ℂ}
    (hU : mpoWithBoundary T U L = 1) (hn : 0 < n) :
    Matrix.toEuclideanLin (mpoWithBoundary T U n) ∘ₗ
        (MPSTensor.groundSpaceES A n).starProjection.toLinearMap =
      (MPSTensor.groundSpaceES A n).starProjection.toLinearMap := by
  apply LinearMap.ext
  intro ψ
  apply (WithLp.linearEquiv 2 ℂ (MPSTensor.NSiteSpace d n)).injective
  change mpoWithBoundary T U n *ᵥ
      ((WithLp.linearEquiv 2 ℂ (MPSTensor.NSiteSpace d n))
        ((MPSTensor.groundSpaceES A n).starProjection ψ)) = _
  exact h.mulVec_eq_of_mem_groundSpace_of_one_length_eq_one hInj hL hU hn
    ((MPSTensor.mem_groundSpaceES_iff A n _).mp
      (Submodule.starProjection_apply_mem _ _))

/-- One-site injectivity and a one-site physical unit imply the canonical
projection normalization at every positive length. This specializes the
unit-support criterion for GLM23 Appendix B, lines 2463--2466. -/
theorem IsBoundaryCompatible.toEuclideanLin_comp_groundSpaceES_starProjection_of_one_site
    (h : IsBoundaryCompatible T A) (hInj : Kraus.IsInjective A)
    {U : Matrix (Fin D₁) (Fin D₁) ℂ} (hU : mpoWithBoundary T U 1 = 1)
    (hn : 0 < n) :
    Matrix.toEuclideanLin (mpoWithBoundary T U n) ∘ₗ
        (MPSTensor.groundSpaceES A n).starProjection.toLinearMap =
      (MPSTensor.groundSpaceES A n).starProjection.toLinearMap :=
  h.toEuclideanLin_comp_groundSpaceES_starProjection
    (Kraus.isNBlkInjective_one_of_isInjective hInj) Nat.one_pos hU hn

end MPOTensor
