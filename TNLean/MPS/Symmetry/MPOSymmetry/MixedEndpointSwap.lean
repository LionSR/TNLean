/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointProjectorComparison
import TNLean.MPS.ParentHamiltonian.PhysicalReindexProjection
import TNLean.MPS.Core.PhysicalReindexTransport

/-!
# Exchanging the two mixed endpoint sectors

Exchanging the two bond summands and both physical registers identifies the
second endpoint with the first endpoint of the reversed pair. The comparison
of local parent interactions therefore transports by an explicit physical
isometry, without a second independent projector argument.

Source: arXiv:2203.12563, Section 5, lines 1586–1601 and 1690–1692.
-/

open scoped Matrix InnerProductSpace ComplexOrder

namespace MPSTensor
namespace MPOSymmetry

variable {D₀ D₁ : ℕ}

/-- Exchange the two virtual direct summands. Source: arXiv:2203.12563,
Section 5, `defAgamma`, lines 1586–1601. -/
def mixedEndpointBondSwap (D₀ D₁ : ℕ) : Fin (D₀ + D₁) ≃ Fin (D₁ + D₀) :=
  finSumFinEquiv.symm.trans ((Equiv.sumComm _ _).trans finSumFinEquiv)

/-- Exchange the two sectors in both physical registers.
Source: arXiv:2203.12563, Section 5, `defAgamma`, lines 1586–1601. -/
def mixedEndpointPhysicalSwap (D₀ D₁ : ℕ) :
    Fin ((D₀ + D₁) * (D₀ + D₁)) ≃ Fin ((D₁ + D₀) * (D₁ + D₀)) :=
  finProdFinEquiv.symm.trans
    (((mixedEndpointBondSwap D₀ D₁).prodCongr (mixedEndpointBondSwap D₀ D₁)).trans
      finProdFinEquiv)

/-- The second endpoint in the original common physical space.
Source: arXiv:2203.12563, Section 5, `defAgamma`, lines 1586–1601. -/
noncomputable def mixedEndpointRightTensor (A₁ : MPSTensor (D₁ * D₁) D₁) (D₀ : ℕ) :
    MPSTensor ((D₀ + D₁) * (D₀ + D₁)) D₁ :=
  Kraus.reindexPhysical (mixedEndpointPhysicalSwap D₀ D₁)
    (mixedEndpointLeftTensor A₁ D₀)

/-- The exchanged first endpoint is exactly the second diagonal physical
sector, with all other letters zero. Source: arXiv:2203.12563,
Section 5, `defAgamma`, lines 1586–1601. -/
theorem mixedEndpointRightTensor_apply
    (A₁ : MPSTensor (D₁ * D₁) D₁) (p : Fin ((D₀ + D₁) * (D₀ + D₁))) :
    mixedEndpointRightTensor A₁ D₀ p =
      match finSumFinEquiv.symm (finProdFinEquiv.symm p).1,
          finSumFinEquiv.symm (finProdFinEquiv.symm p).2 with
      | .inr a, .inr b => A₁ (finProdFinEquiv (a, b))
      | _, _ => 0 := by
  obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective p
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective a
  obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective b
  cases a <;> cases b <;>
    simp [mixedEndpointRightTensor, Kraus.reindexPhysical, mixedEndpointLeftTensor,
      mixedEndpointPhysicalSwap, mixedEndpointBondSwap]

/-- The right physical embedding preserves arbitrary endpoint injectivity.
Source: arXiv:2203.12563, Section 5, lines 1580–1601. -/
theorem isInjective_mixedEndpointRightTensor
    (A₁ : MPSTensor (D₁ * D₁) D₁) (hA₁ : Kraus.IsInjective A₁) (D₀ : ℕ) :
    Kraus.IsInjective (mixedEndpointRightTensor A₁ D₀) :=
  (isInjective_reindexPhysical_equiv _ _).mpr
    (isInjective_mixedEndpointLeftTensor A₁ hA₁ D₀)

/-- Exchanging endpoint labels preserves each mixed letter after virtual
basis transport. Source: arXiv:2203.12563, `defAgamma`, lines 1586–1601. -/
theorem mixedEndpointBase_swap
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (p : Fin ((D₀ + D₁) * (D₀ + D₁))) :
    mixedEndpointBase A₁ A₀ (mixedEndpointPhysicalSwap D₀ D₁ p) =
      Matrix.reindexAlgEquiv ℂ ℂ (mixedEndpointBondSwap D₀ D₁)
        (mixedEndpointBase A₀ A₁ p) := by
  have hdisjoint (a : Fin D₀) (b : Fin D₁) : Fin.castAdd D₁ a ≠ Fin.natAdd D₀ b := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
    omega
  have hdisjoint' (b : Fin D₁) (a : Fin D₀) : Fin.natAdd D₀ b ≠ Fin.castAdd D₁ a :=
    (hdisjoint a b).symm
  ext i j
  obtain ⟨i, rfl⟩ := (mixedEndpointBondSwap D₀ D₁).surjective i
  obtain ⟨j, rfl⟩ := (mixedEndpointBondSwap D₀ D₁).surjective j
  obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective p
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective a
  obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective b
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  cases a <;> cases b <;> cases i <;> cases j <;>
    simp [mixedEndpointBase, mixedEndpointLetter, mixedEndpointPhysicalSwap,
      mixedEndpointBondSwap, Matrix.fromBlocks, Matrix.single_apply, hdisjoint, hdisjoint']

/-- Under sector exchange, the original second-endpoint insertion becomes
the first-endpoint insertion. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem bondInterpolationMatrix_one_swap :
    bondInterpolationMatrix D₁ D₀ 0 =
      Matrix.reindexAlgEquiv ℂ ℂ (mixedEndpointBondSwap D₀ D₁)
        (bondInterpolationMatrix D₀ D₁ 1) := by
  ext i j
  obtain ⟨i, rfl⟩ := (mixedEndpointBondSwap D₀ D₁).surjective i
  obtain ⟨j, rfl⟩ := (mixedEndpointBondSwap D₀ D₁).surjective j
  simp only [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, bondInterpolationMatrix, Matrix.diagonal_apply,
    Equiv.apply_eq_iff_eq]
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  cases i <;> simp [mixedEndpointBondSwap, bondInterpolationWeight]

private theorem trace_reindexAlgEquiv
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (X : Matrix ι ι ℂ) :
    Matrix.trace (Matrix.reindexAlgEquiv ℂ ℂ e X) = Matrix.trace X := by
  unfold Matrix.trace
  exact Fintype.sum_equiv e.symm _ _ fun _ => rfl

/-- The extended boundary maps at opposite endpoints intertwine under the
explicit physical and virtual sector exchanges. Source: arXiv:2203.12563,
Section 5, lines 1690–1692. -/
theorem insertedTwoSiteMap_swap_zero
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (X : Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ) :
    physicalReindexLinearIsometryEquiv (mixedEndpointPhysicalSwap D₀ D₁) 2
      (insertedTwoSiteMap (mixedEndpointBase A₁ A₀) (bondInterpolationMatrix D₁ D₀ 0)
        (WithLp.toLp 2 (fun p =>
          Matrix.reindexAlgEquiv ℂ ℂ (mixedEndpointBondSwap D₀ D₁) X p.1 p.2))) =
      insertedTwoSiteMap (mixedEndpointBase A₀ A₁) (bondInterpolationMatrix D₀ D₁ 1)
        (WithLp.toLp 2 (fun p => X p.1 p.2)) := by
  apply PiLp.ext
  intro σ
  simp only [physicalReindexLinearIsometryEquiv_apply_apply, insertedTwoSiteMap_apply]
  change Matrix.trace (mixedEndpointBase A₁ A₀ (mixedEndpointPhysicalSwap D₀ D₁ (σ 0)) *
    bondInterpolationMatrix D₁ D₀ 0 *
    mixedEndpointBase A₁ A₀ (mixedEndpointPhysicalSwap D₀ D₁ (σ 1)) *
    Matrix.reindexAlgEquiv ℂ ℂ (mixedEndpointBondSwap D₀ D₁) X) =
      Matrix.trace (mixedEndpointBase A₀ A₁ (σ 0) * bondInterpolationMatrix D₀ D₁ 1 *
        mixedEndpointBase A₀ A₁ (σ 1) * X)
  rw [mixedEndpointBase_swap, mixedEndpointBase_swap, bondInterpolationMatrix_one_swap,
    ← map_mul, ← map_mul, ← map_mul, trace_reindexAlgEquiv]

/-- The actual second-endpoint support is the isometric image of the first
support for the reversed pair. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpoint_extendedSupport_one_eq_map_swap
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) :
    (insertedTwoSiteMap (mixedEndpointBase A₀ A₁) (bondInterpolationMatrix D₀ D₁ 1)).range =
      (insertedTwoSiteMap (mixedEndpointBase A₁ A₀) (bondInterpolationMatrix D₁ D₀ 0)).range.map
        (physicalReindexLinearIsometryEquiv (mixedEndpointPhysicalSwap D₀ D₁) 2).toLinearMap := by
  let Φ := Matrix.reindexAlgEquiv ℂ ℂ (mixedEndpointBondSwap D₀ D₁)
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    let X : Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ := fun a b => v (a, b)
    refine ⟨insertedTwoSiteMap (mixedEndpointBase A₁ A₀) (bondInterpolationMatrix D₁ D₀ 0)
      (WithLp.toLp 2 (fun p => Φ X p.1 p.2)), ⟨_, rfl⟩, ?_⟩
    exact insertedTwoSiteMap_swap_zero A₀ A₁ X
  · rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    let Y : Matrix (Fin (D₁ + D₀)) (Fin (D₁ + D₀)) ℂ := fun a b => v (a, b)
    refine ⟨WithLp.toLp 2 (fun p => Φ.symm Y p.1 p.2), ?_⟩
    have hv : WithLp.toLp 2 (fun p : Fin (D₁ + D₀) × Fin (D₁ + D₀) => Y p.1 p.2) = v := by
      apply PiLp.ext
      rintro ⟨a, b⟩
      rfl
    have h := insertedTwoSiteMap_swap_zero A₀ A₁ (Φ.symm Y)
    simpa only [Φ, AlgEquiv.apply_symm_apply, hv, ContinuousLinearMap.coe_coe,
      LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv] using h.symm

/-- The second endpoint interaction is the conjugate of the first endpoint
interaction for the reversed pair. Source: arXiv:2203.12563, Section 5,
lines 1690–1692. -/
theorem mixedEndpointParentInteraction_one_eq_conj_swap
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) :
    (mixedEndpointParentInteraction A₀ A₁ 1).toLinearMap =
      (physicalReindexLinearIsometryEquiv (mixedEndpointPhysicalSwap D₀ D₁) 2).toLinearEquiv.conj
        (mixedEndpointParentInteraction A₁ A₀ 0).toLinearMap := by
  let U := physicalReindexLinearIsometryEquiv (mixedEndpointPhysicalSwap D₀ D₁) 2
  let S := (insertedTwoSiteMap (mixedEndpointBase A₁ A₀)
    (bondInterpolationMatrix D₁ D₀ 0)).range
  have hproj := congrArg
    (fun T : Submodule ℂ (EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) 2)) =>
      T.starProjection)
    (mixedEndpoint_extendedSupport_one_eq_map_swap A₀ A₁)
  apply LinearMap.ext
  intro v
  have hmap := Submodule.starProjection_map_apply U S v
  change v - (insertedTwoSiteMap (mixedEndpointBase A₀ A₁)
    (bondInterpolationMatrix D₀ D₁ 1)).range.starProjection v =
      U (U.symm v - S.starProjection (U.symm v))
  rw [hproj]
  change v - (S.map U.toLinearEquiv.toLinearMap).starProjection v =
    U (U.symm v - S.starProjection (U.symm v))
  rw [hmap, map_sub, U.apply_symm_apply]

end MPOSymmetry
end MPSTensor
