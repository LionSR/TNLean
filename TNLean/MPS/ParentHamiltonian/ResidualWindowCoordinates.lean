/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.PeriodicResidualGroundSpace
import TNLean.MPS.ParentHamiltonian.SpectatorBoundaryGram
import Mathlib.LinearAlgebra.Matrix.Bilinear

/-!
# Three-window coordinates for correlated residual boundaries

The physical configuration is split into a blocked prefix `u`, a blocked
common interval `v`, and an original tail `τ`. The right window has rectangular
boundaries indexed by `u`; the left window has square boundaries indexed by
`τ`. The full residual boundary map factors through both. The right
factorization uses `Y * B^u`, while the left uses `Vᴴ * A^τ * Y`.

Their exact mixed Gram is a sum of ordinary prefix Gram pairings on the common
interval. The original tail remains in the virtual boundary. These identities
include zero lengths and require neither injectivity nor normalization.
They supply coordinates for a supported inverse-Gram cancellation; no
projector decay or all-residue gap is asserted.

Source: DCCSP17, arXiv:1708.00029, Lemma `lem:blocking-arbitrary`,
lines 434--451; Nachtergaele, arXiv:cond-mat/9410110,
Lemma `commutation` (ii), lines 2442--2531.
-/

open scoped Matrix InnerProductSpace Matrix.Norms.Frobenius
namespace MPSTensor
variable {d D E L : ℕ}

/-- Extract one rectangular matrix from a flattened Euclidean boundary family.
The flattened coordinates are ordered as family index, column, then row.
These are the Frobenius coordinates used in the residual version of
Nachtergaele, arXiv:cond-mat/9410110, Lemma `commutation` (ii). -/
noncomputable def rectangularBoundaryFamilyFiberₗ {S : Type*} [Fintype S] (u : S) :
    EuclideanSpace ℂ (S × (Fin E × Fin D)) →ₗ[ℂ] Matrix (Fin D) (Fin E) ℂ :=
  (LinearMap.pi fun i => LinearMap.pi fun j => LinearMap.proj (u, (j, i))).comp
    (WithLp.linearEquiv 2 ℂ (S × (Fin E × Fin D) → ℂ)).toLinearMap

/-- Right multiplication by the blocked prefix word in each rectangular
boundary fiber. Source: the boundary-word factorization underlying
Nachtergaele, arXiv:cond-mat/9410110, Lemma `commutation` (ii), lines 2442--2531. -/
noncomputable def residualWindowRightVirtualMapES
    (B : MPSTensor (blockPhysDim d L) E) (K : ℕ) :
    EuclideanSpace ℂ (Fin E × Fin D) →L[ℂ]
      EuclideanSpace ℂ (Cfg (blockPhysDim d L) K × (Fin E × Fin D)) :=
  LinearMap.toContinuousLinearMap <|
    (WithLp.linearEquiv 2 ℂ
      (Cfg (blockPhysDim d L) K × (Fin E × Fin D) → ℂ)).symm.toLinearMap.comp
    (LinearMap.pi fun p => ((LinearMap.proj p.2.1).comp (LinearMap.proj p.2.2)).comp
      ((mulRightLinearMap (l := Fin D) ℂ (Kraus.evalWord B (List.ofFn p.1))).comp
        (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E)).symm.toLinearEquiv.toLinearMap))

/-- The right residual window with a blocked prefix spectator.
Its coefficient at `(u,v,τ)` is `tr(B^v * Vᴴ * A^τ * X_u)`.
Source: DCCSP17, arXiv:1708.00029, Lemma `lem:blocking-arbitrary`,
lines 434--451; Nachtergaele, Lemma `commutation` (ii). -/
noncomputable def residualWindowRightMapES
    (A : MPSTensor d D) (B : MPSTensor (blockPhysDim d L) E)
    (V : Matrix (Fin D) (Fin E) ℂ) (K M r : ℕ) :
    EuclideanSpace ℂ (Cfg (blockPhysDim d L) K × (Fin E × Fin D)) →L[ℂ]
      EuclideanSpace ℂ (Cfg (blockPhysDim d L) K ×
        (Cfg (blockPhysDim d L) M × Cfg d r)) :=
  LinearMap.toContinuousLinearMap <|
    (WithLp.linearEquiv 2 ℂ (Cfg (blockPhysDim d L) K ×
      (Cfg (blockPhysDim d L) M × Cfg d r) → ℂ)).symm.toLinearMap.comp
    (LinearMap.pi fun p => (Matrix.traceLinearMap (Fin E) ℂ ℂ).comp
      ((mulLeftLinearMap (n := Fin E) ℂ
        (Kraus.evalWord B (List.ofFn p.2.1) * Vᴴ *
          Kraus.evalWord A (List.ofFn p.2.2))).comp (rectangularBoundaryFamilyFiberₗ p.1)))

/-- The blocked left window with an original-tail spectator.
Its coefficient at `(u,v,τ)` is `tr(B^u * B^v * Y_τ)`.
Source: Nachtergaele, arXiv:cond-mat/9410110,
Lemma `commutation` (ii), lines 2442--2531. -/
noncomputable def residualWindowLeftMapES
    (B : MPSTensor (blockPhysDim d L) E) (K M r : ℕ) :
    BoundaryFamilySpace (D := E) (Cfg d r) →L[ℂ]
      EuclideanSpace ℂ (Cfg (blockPhysDim d L) K ×
        (Cfg (blockPhysDim d L) M × Cfg d r)) :=
  LinearMap.toContinuousLinearMap <|
    (WithLp.linearEquiv 2 ℂ (Cfg (blockPhysDim d L) K ×
      (Cfg (blockPhysDim d L) M × Cfg d r) → ℂ)).symm.toLinearMap.comp
    (LinearMap.pi fun p => (Matrix.traceLinearMap (Fin E) ℂ ℂ).comp
      ((mulLeftLinearMap (n := Fin E) ℂ
        (Kraus.evalWord B (List.ofFn p.1) * Kraus.evalWord B (List.ofFn p.2.1))).comp
        ((LinearMap.proj p.2.2).comp
          (boundaryFamilyEquiv (D := E) (Cfg d r)).toLinearMap)))

/-- The full residual contraction in three consecutive configuration blocks.
Its coefficient is `tr(B^u * B^v * Vᴴ * A^τ * Y)`.
Source: DCCSP17, arXiv:1708.00029, Lemma `lem:blocking-arbitrary`,
lines 434--451; Nachtergaele, Lemma `commutation` (ii). -/
noncomputable def residualWindowMapES
    (A : MPSTensor d D) (B : MPSTensor (blockPhysDim d L) E)
    (V : Matrix (Fin D) (Fin E) ℂ) (K M r : ℕ) :
    EuclideanSpace ℂ (Fin E × Fin D) →L[ℂ]
      EuclideanSpace ℂ (Cfg (blockPhysDim d L) K ×
        (Cfg (blockPhysDim d L) M × Cfg d r)) :=
  LinearMap.toContinuousLinearMap <|
    (WithLp.linearEquiv 2 ℂ (Cfg (blockPhysDim d L) K ×
      (Cfg (blockPhysDim d L) M × Cfg d r) → ℂ)).symm.toLinearMap.comp
    (LinearMap.pi fun p => (Matrix.traceLinearMap (Fin E) ℂ ℂ).comp
      ((mulLeftLinearMap (n := Fin E) ℂ
        (Kraus.evalWord B (List.ofFn p.1) * Kraus.evalWord B (List.ofFn p.2.1) *
          Vᴴ * Kraus.evalWord A (List.ofFn p.2.2))).comp
          (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E)).symm.toLinearEquiv.toLinearMap))

/-- The full residual map factors through the right window by moving the
blocked prefix word to the right of the rectangular boundary.
This is exact trace cyclicity, with no injectivity assumption.
Source: Nachtergaele, arXiv:cond-mat/9410110, Lemma `commutation` (ii). -/
theorem residualWindowRightMapES_comp_rightVirtualMapES
    (A : MPSTensor d D) (B : MPSTensor (blockPhysDim d L) E)
    (V : Matrix (Fin D) (Fin E) ℂ) (K M r : ℕ) :
    (residualWindowRightMapES A B V K M r).comp
      (residualWindowRightVirtualMapES (D := D) B K) = residualWindowMapES A B V K M r := by
  ext x ⟨u, v, τ⟩
  change Matrix.trace ((Kraus.evalWord B (List.ofFn v) * Vᴴ *
    Kraus.evalWord A (List.ofFn τ)) *
      ((Matrix.frobeniusEquivEuclidean (Fin D) (Fin E)).symm x *
        Kraus.evalWord B (List.ofFn u))) =
    Matrix.trace ((Kraus.evalWord B (List.ofFn u) * Kraus.evalWord B (List.ofFn v) *
      Vᴴ * Kraus.evalWord A (List.ofFn τ)) *
        (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E)).symm x)
  simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm
    (Kraus.evalWord B (List.ofFn v) * Vᴴ * Kraus.evalWord A (List.ofFn τ) *
      (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E)).symm x)
    (Kraus.evalWord B (List.ofFn u))

/-- The full residual map factors through the left window with the correlated
boundary family `Vᴴ * A^τ * Y`. The physical tail is retained in that family.
Source: DCCSP17, arXiv:1708.00029, Lemma `lem:blocking-arbitrary`,
lines 434--451; Nachtergaele, Lemma `commutation` (ii). -/
theorem residualWindowLeftMapES_correlatedTailFamily
    (A : MPSTensor d D) (B : MPSTensor (blockPhysDim d L) E)
    (V : Matrix (Fin D) (Fin E) ℂ) (K M r : ℕ)
    (Y : Matrix (Fin D) (Fin E) ℂ) :
    residualWindowLeftMapES B K M r
      ((boundaryFamilyEquiv (D := E) (Cfg d r)).symm
        (fun τ => Vᴴ * Kraus.evalWord A (List.ofFn τ) * Y)) =
      residualWindowMapES A B V K M r
        (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E) Y) := by
  ext ⟨u, v, τ⟩
  change Matrix.trace ((Kraus.evalWord B (List.ofFn u) * Kraus.evalWord B (List.ofFn v)) *
    (Vᴴ * Kraus.evalWord A (List.ofFn τ) * Y)) =
    Matrix.trace ((Kraus.evalWord B (List.ofFn u) * Kraus.evalWord B (List.ofFn v) *
      Vᴴ * Kraus.evalWord A (List.ofFn τ)) * Y)
  simp only [Matrix.mul_assoc]

/-- Exact mixed Gram on the common blocked interval. The two middle
boundaries are `Vᴴ * A^τ * X_u` and `Y_τ * B^u`, in this order.
No limiting metric or quantitative contraction is asserted.
Reconstructed for Nachtergaele, arXiv:cond-mat/9410110,
Lemma `commutation` (ii), lines 2442--2531. -/
theorem inner_residualWindowRightMapES_leftMapES
    (A : MPSTensor d D) (B : MPSTensor (blockPhysDim d L) E)
    (V : Matrix (Fin D) (Fin E) ℂ) (K M r : ℕ)
    (x : EuclideanSpace ℂ (Cfg (blockPhysDim d L) K × (Fin E × Fin D)))
    (y : BoundaryFamilySpace (D := E) (Cfg d r)) :
    ⟪residualWindowRightMapES A B V K M r x, residualWindowLeftMapES B K M r y⟫_ℂ =
      ∑ u : Cfg (blockPhysDim d L) K, ∑ τ : Cfg d r,
        ⟪Matrix.frobeniusEquivEuclidean (Fin E) (Fin E)
            (Vᴴ * Kraus.evalWord A (List.ofFn τ) * rectangularBoundaryFamilyFiberₗ u x),
          groundSpaceGram B M (Matrix.frobeniusEquivEuclidean (Fin E) (Fin E)
            (boundaryFamilyEquiv (D := E) (Cfg d r) y τ *
              Kraus.evalWord B (List.ofFn u)))⟫_ℂ := by
  simp_rw [groundSpaceGram, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]
  simp_rw [PiLp.inner_apply]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro τ _
  apply Finset.sum_congr rfl
  intro v _
  change ⟪Matrix.trace ((Kraus.evalWord B (List.ofFn v) * Vᴴ *
    Kraus.evalWord A (List.ofFn τ)) * rectangularBoundaryFamilyFiberₗ u x),
    Matrix.trace ((Kraus.evalWord B (List.ofFn u) * Kraus.evalWord B (List.ofFn v)) *
      boundaryFamilyEquiv (D := E) (Cfg d r) y τ)⟫_ℂ =
    ⟪Matrix.trace (Kraus.evalWord B (List.ofFn v) *
      (Vᴴ * Kraus.evalWord A (List.ofFn τ) * rectangularBoundaryFamilyFiberₗ u x)),
      Matrix.trace (Kraus.evalWord B (List.ofFn v) *
        (boundaryFamilyEquiv (D := E) (Cfg d r) y τ * Kraus.evalWord B (List.ofFn u)))⟫_ℂ
  simpa only [Matrix.mul_assoc] using congrArg (fun z : ℂ =>
    inner ℂ (Matrix.trace (Kraus.evalWord B (List.ofFn v) * Vᴴ *
      Kraus.evalWord A (List.ofFn τ) * rectangularBoundaryFamilyFiberₗ u x)) z)
      (Matrix.trace_mul_comm (Kraus.evalWord B (List.ofFn u))
        (Kraus.evalWord B (List.ofFn v) * boundaryFamilyEquiv (D := E) (Cfg d r) y τ))

/-- Concatenate two blocked configurations, decode their physical sites,
and append the original tail. This bijection includes all zero lengths.
Source: the blocking coordinates of DCCSP17, arXiv:1708.00029,
Lemma `lem:blocking-arbitrary`, lines 434--451. -/
noncomputable def residualWindowConfigEquiv (d L K M r : ℕ) :
    Cfg (blockPhysDim d L) K × (Cfg (blockPhysDim d L) M × Cfg d r) ≃
      Cfg d ((K + M) * L + r) :=
  (Equiv.prodAssoc _ _ _).symm.trans
    ((Equiv.prodCongr ((Fin.appendEquiv K M).trans (blockedConfigEquiv d (K + M) L))
      (Equiv.refl (Cfg d r))).trans (Fin.appendEquiv ((K + M) * L) r))

/-- The three-window full map is precisely the residual boundary map
transported by the configuration bijection. Thus the product coordinates
preserve the physical inner product.
Source: DCCSP17, arXiv:1708.00029, Lemma `lem:blocking-arbitrary`,
lines 434--451; Nachtergaele, Lemma `commutation` (ii). -/
theorem residualWindowMapES_eq_reindex_blockedResidualBoundaryMapES
    (A : MPSTensor d D) (B : MPSTensor (blockPhysDim d L) E)
    (V : Matrix (Fin D) (Fin E) ℂ) (K M r : ℕ) :
    residualWindowMapES A B V K M r =
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (residualWindowConfigEquiv d L K M r).symm).toContinuousLinearMap.comp
          (blockedResidualBoundaryMapES A L B V (K + M) r) := by
  ext x ⟨u, v, τ⟩
  change Matrix.trace ((Kraus.evalWord B (List.ofFn u) *
    Kraus.evalWord B (List.ofFn v) * Vᴴ * Kraus.evalWord A (List.ofFn τ)) *
      (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E)).symm x) =
    blockedResidualBoundaryMap A L B V (K + M) r
      ((Matrix.frobeniusEquivEuclidean (Fin D) (Fin E)).symm x)
        (Fin.append (blockedConfigEquiv d (K + M) L (Fin.append u v)) τ)
  simp [blockedResidualBoundaryMap, Function.comp_def, List.ofFn_fin_append,
    Kraus.evalWord_append]
end MPSTensor
