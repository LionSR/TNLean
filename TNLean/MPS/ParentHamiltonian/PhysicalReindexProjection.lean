/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.GroundSpaceGram
import TNLean.MPS.ParentHamiltonian.Martingale.Transport

/-!
# Physical alphabet reindexing of local parent projections

A bijection of physical letters induces an isometry of configuration spaces.
It carries the local boundary space to the boundary space of the reindexed
tensor, and conjugates the corresponding orthogonal parent projections.

These identities apply at every window length, including the two-site
supports used in Garre-Rubio–Lootens–Molnár, arXiv:2203.12563, Section 5.
-/

open scoped Matrix.Norms.Frobenius

namespace MPSTensor

variable {d₁ d₂ D : ℕ}

/-- Pull back physical configurations along an alphabet bijection, preserving
the standard \(\ell^2\) norm. -/
noncomputable def physicalReindexLinearIsometryEquiv
    (e : Fin d₁ ≃ Fin d₂) (N : ℕ) :
    EuclideanSpace ℂ (Cfg d₂ N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Cfg d₁ N) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (Equiv.arrowCongr (Equiv.refl (Fin N)) e).symm

/-- Configuration coefficients are pulled back letter by letter. -/
@[simp] theorem physicalReindexLinearIsometryEquiv_apply_apply
    (e : Fin d₁ ≃ Fin d₂) (N : ℕ)
    (v : EuclideanSpace ℂ (Cfg d₂ N)) (σ : Cfg d₁ N) :
    physicalReindexLinearIsometryEquiv e N v σ = v (fun i => e (σ i)) := rfl

/-- Conjugation by a physical alphabet bijection pulls back the entries of
a diagonal configuration operator. -/
theorem physicalReindexLinearIsometryEquiv_conj_diagonal
    (e : Fin d₁ ≃ Fin d₂) (N : ℕ) (f : Cfg d₂ N → ℂ) :
    (physicalReindexLinearIsometryEquiv e N).toLinearEquiv.conj
        (Matrix.toEuclideanLin (Matrix.diagonal f)) =
      Matrix.toEuclideanLin (Matrix.diagonal fun σ => f (fun i => e (σ i))) := by
  apply LinearMap.ext
  intro v
  apply PiLp.ext
  intro σ
  have hsymm : (physicalReindexLinearIsometryEquiv e N).symm v
      (fun i => e (σ i)) = v σ := by
    change physicalReindexLinearIsometryEquiv e N
      ((physicalReindexLinearIsometryEquiv e N).symm v) σ = v σ
    rw [LinearIsometryEquiv.apply_symm_apply]
  simpa [LinearEquiv.conj_apply_apply, physicalReindexLinearIsometryEquiv_apply_apply,
    Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_diagonal] using
    congrArg (fun z : ℂ => f (fun i => e (σ i)) * z) hsymm

/-- The Euclidean boundary map commutes with a bijective relabeling of the
physical alphabet. -/
theorem physicalReindexLinearIsometryEquiv_groundSpaceMapES
    (e : Fin d₁ ≃ Fin d₂) (A : MPSTensor d₂ D) (N : ℕ)
    (x : EuclideanSpace ℂ (Fin D × Fin D)) :
    physicalReindexLinearIsometryEquiv e N (groundSpaceMapES A N x) =
      groundSpaceMapES (Kraus.reindexPhysical e A) N x := by
  obtain ⟨X, rfl⟩ :=
    (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).toLinearEquiv.surjective x
  change physicalReindexLinearIsometryEquiv e N
      (groundSpaceMapES A N (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D) X)) =
    groundSpaceMapES (Kraus.reindexPhysical e A) N
      (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D) X)
  rw [groundSpaceMapES_frobeniusEquivEuclidean_apply,
    groundSpaceMapES_frobeniusEquivEuclidean_apply]
  apply PiLp.ext
  intro σ
  change groundSpaceMap A N X (fun i => e (σ i)) =
    groundSpaceMap (Kraus.reindexPhysical e A) N X σ
  simp only [groundSpaceMap_apply, Kraus.evalWord_reindexPhysical,
    List.map_ofFn, Function.comp_def]

/-- Relabeling the physical alphabet sends the local boundary space to its
isometric image. -/
theorem groundSpaceES_reindexPhysical_equiv
    (e : Fin d₁ ≃ Fin d₂) (A : MPSTensor d₂ D) (N : ℕ) :
    groundSpaceES (Kraus.reindexPhysical e A) N =
      (groundSpaceES A N).map
        (physicalReindexLinearIsometryEquiv e N).toLinearEquiv.toLinearMap := by
  rw [← range_groundSpaceMapES, ← range_groundSpaceMapES]
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨groundSpaceMapES A N x, ⟨x, rfl⟩,
      physicalReindexLinearIsometryEquiv_groundSpaceMapES e A N x⟩
  · rintro ⟨w, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, (physicalReindexLinearIsometryEquiv_groundSpaceMapES e A N x).symm⟩

/-- The canonical local parent projection is conjugated by the physical
configuration isometry under an alphabet bijection. -/
theorem parentInteractionES_reindexPhysical_equiv
    (e : Fin d₁ ≃ Fin d₂) (A : MPSTensor d₂ D) (N : ℕ) :
    parentInteractionES (Kraus.reindexPhysical e A) N =
      (physicalReindexLinearIsometryEquiv e N).toLinearEquiv.conj
        (parentInteractionES A N) := by
  have hOrth : (groundSpaceES (Kraus.reindexPhysical e A) N)ᗮ =
      ((groundSpaceES A N)ᗮ).map
        (physicalReindexLinearIsometryEquiv e N).toLinearEquiv.toLinearMap := by
    rw [groundSpaceES_reindexPhysical_equiv, Submodule.map_orthogonal_equiv]
  have hProj := congrArg
    (fun S : Submodule ℂ (EuclideanSpace ℂ (Cfg d₁ N)) =>
      S.starProjection.toLinearMap) hOrth
  refine hProj.trans ?_
  apply LinearMap.ext
  intro v
  exact Submodule.starProjection_map_apply
    (physicalReindexLinearIsometryEquiv e N) (groundSpaceES A N)ᗮ v

end MPSTensor
