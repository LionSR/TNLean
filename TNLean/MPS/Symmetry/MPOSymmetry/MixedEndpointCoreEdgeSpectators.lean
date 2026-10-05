/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointEdgeProjectors
import TNLean.MPS.ParentHamiltonian.Martingale.SpectatorTransport

/-!
# Exterior spectator factors in the normalized endpoint edges

The normalized first and last edge constraints act independently of the
free exterior register. We prove this for the actual one-sided matrix
ranges, then identify the canonical projections with fiberwise extensions
of the corresponding one-dimensional-spectator constraints. These local
identities are used when assembling the common normalized core Hamiltonian.

Source: arXiv:2203.12563, Section 5, lines 1690–1692.
-/

namespace MPSTensor
namespace MPOSymmetry

open ContinuousLinearMap

noncomputable section

variable {D : ℕ} {ι : Type*} [Fintype ι]

/-- Move the first exterior index to a separate spectator coordinate. -/
def endpointFirstEdgeSpectatorEquiv (ι : Type*) (D : ℕ) :
    endpointFirstEdgeCfg ι D ≃ endpointFirstEdgeCfg PUnit D × ι where
  toFun := fun ((a, b), q) => (((PUnit.unit, b), q), a)
  invFun := fun (((_, b), q), a) => ((a, b), q)
  left_inv := fun _ => rfl
  right_inv := by rintro ⟨⟨⟨⟨⟩, b⟩, q⟩, a⟩; rfl

/-- Move the last exterior index to a separate spectator coordinate. -/
def endpointLastEdgeSpectatorEquiv (ι : Type*) (D : ℕ) :
    endpointLastEdgeCfg ι D ≃ endpointLastEdgeCfg PUnit D × ι where
  toFun := fun (q, (c, e)) => ((q, (c, PUnit.unit)), e)
  invFun := fun ((q, (c, _)), e) => (q, (c, e))
  left_inv := fun _ => rfl
  right_inv := by rintro ⟨⟨q, c, ⟨⟩⟩, e⟩; rfl

/-- The first-edge spectator regrouping is unitary in Euclidean coordinates. -/
def endpointFirstEdgeSpectatorIsometry (ι : Type*) [Fintype ι] (D : ℕ) :
    EuclideanSpace ℂ (endpointFirstEdgeCfg ι D) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (endpointFirstEdgeCfg PUnit D × ι) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (endpointFirstEdgeSpectatorEquiv ι D)

/-- The last-edge spectator regrouping is unitary in Euclidean coordinates. -/
def endpointLastEdgeSpectatorIsometry (ι : Type*) [Fintype ι] (D : ℕ) :
    EuclideanSpace ℂ (endpointLastEdgeCfg ι D) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (endpointLastEdgeCfg PUnit D × ι) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (endpointLastEdgeSpectatorEquiv ι D)

private theorem mem_firstEdgeCoreSupport_iff
    (A : MPSTensor (D * D) D) (v : EuclideanSpace ℂ (endpointFirstEdgeCfg ι D)) :
    v ∈ endpointFirstEdgeCoreSupportES A ι ↔
      ∃ Y : Matrix (Fin D) ι ℂ, ∀ a b q, v ((a, b), q) = (A q * Y) b a := by
  constructor
  · rintro ⟨_, ⟨Y, rfl⟩, rfl⟩
    exact ⟨Y, fun _ _ _ => rfl⟩
  · rintro ⟨Y, hY⟩
    refine ⟨endpointFirstEdgeCoreMap A ι Y, ⟨Y, rfl⟩, ?_⟩
    apply PiLp.ext
    rintro ⟨⟨a, b⟩, q⟩
    exact (hY a b q).symm

private theorem mem_lastEdgeCoreSupport_iff
    (A : MPSTensor (D * D) D) (v : EuclideanSpace ℂ (endpointLastEdgeCfg ι D)) :
    v ∈ endpointLastEdgeCoreSupportES A ι ↔
      ∃ Y : Matrix ι (Fin D) ℂ, ∀ q c e, v (q, (c, e)) = (Y * A q) e c := by
  constructor
  · rintro ⟨_, ⟨Y, rfl⟩, rfl⟩
    exact ⟨Y, fun _ _ _ => rfl⟩
  · rintro ⟨Y, hY⟩
    refine ⟨endpointLastEdgeCoreMap A ι Y, ⟨Y, rfl⟩, ?_⟩
    apply PiLp.ext
    rintro ⟨q, c, e⟩
    exact (hY q c e).symm

/-- The actual normalized first-edge range is a separate copy of the
one-spectator range at each value of its free exterior register. -/
theorem mem_endpointFirstEdgeCoreSupportES_iff_fibers
    (A : MPSTensor (D * D) D) (v : EuclideanSpace ℂ (endpointFirstEdgeCfg ι D)) :
    v ∈ endpointFirstEdgeCoreSupportES A ι ↔
      ∀ a, rightFiber (endpointFirstEdgeSpectatorIsometry ι D v) a ∈
        endpointFirstEdgeCoreSupportES A PUnit := by
  classical
  rw [mem_firstEdgeCoreSupport_iff]
  simp only [mem_firstEdgeCoreSupport_iff]
  constructor
  · rintro ⟨Y, hY⟩ a
    refine ⟨fun b _ => Y b a, ?_⟩
    rintro ⟨⟩ b q
    exact hY a b q
  · intro h
    choose Y hY using h
    refine ⟨fun b a => Y a b PUnit.unit, ?_⟩
    intro a b q
    exact hY a PUnit.unit b q

/-- The actual normalized last-edge range likewise splits over its free
exterior register. No injectivity or nonempty spectator hypothesis is needed. -/
theorem mem_endpointLastEdgeCoreSupportES_iff_fibers
    (A : MPSTensor (D * D) D) (v : EuclideanSpace ℂ (endpointLastEdgeCfg ι D)) :
    v ∈ endpointLastEdgeCoreSupportES A ι ↔
      ∀ e, rightFiber (endpointLastEdgeSpectatorIsometry ι D v) e ∈
        endpointLastEdgeCoreSupportES A PUnit := by
  classical
  rw [mem_lastEdgeCoreSupport_iff]
  simp only [mem_lastEdgeCoreSupport_iff]
  constructor
  · rintro ⟨Y, hY⟩ e
    refine ⟨fun _ c => Y e c, ?_⟩
    rintro q c ⟨⟩
    exact hY q c e
  · intro h
    choose Y hY using h
    refine ⟨fun e c => Y e PUnit.unit c, ?_⟩
    intro q c e
    exact hY e q c PUnit.unit

private theorem conj_projection_eq_fiberwise_of_ker_iff
    {E I S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [Fintype I] [Fintype S]
    (U : E ≃ₗᵢ[ℂ] EuclideanSpace ℂ (I × S))
    (P : E →ₗ[ℂ] E) (Q : EuclideanSpace ℂ I →ₗ[ℂ] EuclideanSpace ℂ I)
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection)
    (hker : ∀ v, v ∈ LinearMap.ker P ↔
      ∀ s, rightFiber (U v) s ∈ LinearMap.ker Q) :
    U.toLinearEquiv.conj P = (rightFiberwiseMap (S := S) Q.toContinuousLinearMap).toLinearMap := by
  let L := U.toLinearEquiv.conj P
  let R := (rightFiberwiseMap (S := S) Q.toContinuousLinearMap).toLinearMap
  have hL : L.IsSymmetricProjection :=
    ⟨hP.isIdempotentElem.map U.toLinearEquiv.conjRingEquiv,
      (LinearMap.isSymmetric_linearIsometryEquiv_conj_iff P U).mpr hP.isSymmetric⟩
  have hR : R.IsSymmetricProjection := isSymmetricProjection_rightFiberwiseMap _ hQ
  have hk : LinearMap.ker L = LinearMap.ker R := by
    ext y
    have hconj : y ∈ LinearMap.ker L ↔ U.symm y ∈ LinearMap.ker P := by
      change U (P (U.symm y)) = 0 ↔ P (U.symm y) = 0
      exact U.map_eq_zero_iff
    rw [hconj, mem_ker_rightFiberwiseMap_iff, hker]
    simp only [U.apply_symm_apply]
  apply LinearMap.IsSymmetricProjection.ext hL hR
  have hrL : LinearMap.range L = (LinearMap.ker L)ᗮ := by
    rw [← hL.isSymmetric.orthogonal_range, Submodule.orthogonal_orthogonal]
  have hrR : LinearMap.range R = (LinearMap.ker R)ᗮ := by
    rw [← hR.isSymmetric.orthogonal_range, Submodule.orthogonal_orthogonal]
  rw [hrL, hrR, hk]

/-- The canonical normalized first-edge constraint is the same fixed
one-spectator constraint at every exterior index. This is an operator
identity derived from the explicit matrix ranges. -/
theorem endpointFirstEdgeCoreConstraintES_conj_spectator
    (A : MPSTensor (D * D) D) (ι : Type*) [Fintype ι] :
    (endpointFirstEdgeSpectatorIsometry ι D).toLinearEquiv.conj
        (endpointFirstEdgeCoreConstraintES A ι) =
      (rightFiberwiseMap (S := ι)
        (endpointFirstEdgeCoreConstraintES A PUnit).toContinuousLinearMap).toLinearMap := by
  apply conj_projection_eq_fiberwise_of_ker_iff _ _ _
    (endpointFirstEdgeCoreConstraintES_isSymmetricProjection A ι)
    (endpointFirstEdgeCoreConstraintES_isSymmetricProjection A PUnit)
  intro v
  simpa only [endpointFirstEdgeCoreConstraintES, Submodule.ker_starProjection,
    Submodule.orthogonal_orthogonal] using mem_endpointFirstEdgeCoreSupportES_iff_fibers A v

/-- The canonical normalized last-edge constraint is the analogous
spectator extension of a fixed one-spectator constraint. -/
theorem endpointLastEdgeCoreConstraintES_conj_spectator
    (A : MPSTensor (D * D) D) (ι : Type*) [Fintype ι] :
    (endpointLastEdgeSpectatorIsometry ι D).toLinearEquiv.conj
        (endpointLastEdgeCoreConstraintES A ι) =
      (rightFiberwiseMap (S := ι)
        (endpointLastEdgeCoreConstraintES A PUnit).toContinuousLinearMap).toLinearMap := by
  apply conj_projection_eq_fiberwise_of_ker_iff _ _ _
    (endpointLastEdgeCoreConstraintES_isSymmetricProjection A ι)
    (endpointLastEdgeCoreConstraintES_isSymmetricProjection A PUnit)
  intro v
  simpa only [endpointLastEdgeCoreConstraintES, Submodule.ker_starProjection,
    Submodule.orthogonal_orthogonal] using mem_endpointLastEdgeCoreSupportES_iff_fibers A v

end
end MPOSymmetry
end MPSTensor
