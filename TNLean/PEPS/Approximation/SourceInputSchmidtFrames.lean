/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.CorrectedSourceFrames

/-!
# Isometric inputs from corrected and crossing sources

The original endpoint Schmidt columns and the exact joint crossing vector give
isometric maps into the input memories of the two local factors. All register
orders and identifications are fixed by the corrected and crossing source
positions. The crossing Schmidt weights and frames are constructed from the
actual normalized vector; no spanning or separation premise is supplied.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-exterior-input; Theorem 5.2, lines 409–480.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-source-resource-sourceinputschmidtframes-01
TNLean.PEPS.PairEffect.HasSchmidtInputFrames
Provenance-ID: 8769-source-resource-sourceinputschmidtframes-02
TNLean.PEPS.PairEffect.SourceCircuit.exists_correctedInputFrames
-/


noncomputable section
open scoped TensorProduct Matrix
namespace TNLean.PEPS.PairEffect

/-- A simultaneous Schmidt expansion of a corrected coordinate and a fixed
crossing vector, in the two memories determined by the actual register
partition. The witnesses are probability weights and two proper isometries. -/
def HasSchmidtInputFrames {I : Type} [Fintype I]
    (C T : Layout Bool) (f : EuclideanSpace ℂ I →ₗᵢ[ℂ] Mem C)
    (β : Mem (Layout.restrict (fun p : Bool ↦ p) T) ⊗[ℂ]
      Mem (Layout.restrict (fun p : Bool ↦ !p) T)) : Prop :=
  ∃ r : ℕ, ∃ lam : Fin r → ℝ,
    ∃ A : EuclideanSpace ℂ (I × Fin r) →ₗᵢ[ℂ]
      Mem (Layout.restrict (fun p : Bool ↦ p) (C ++ T)),
    ∃ B : EuclideanSpace ℂ (Fin r) →ₗᵢ[ℂ]
      Mem (Layout.restrict (fun p : Bool ↦ !p) (C ++ T)),
    (∀ j, 0 ≤ lam j) ∧ (∑ j, lam j) = 1 ∧ ∀ i : I,
      Layout.partitionIso (fun p : Bool ↦ p) (C ++ T)
        ((appendIso C T).symm (f (EuclideanSpace.basisFun _ ℂ i) ⊗ₜ[ℂ]
          (Layout.partitionIso (fun p : Bool ↦ p) T).symm β)) =
        ∑ j, (Real.sqrt (lam j) : ℂ) •
          (A (EuclideanSpace.basisFun _ ℂ (i, j)) ⊗ₜ[ℂ]
            B (EuclideanSpace.basisFun _ ℂ j))

end TNLean.PEPS.PairEffect

namespace TNLean.PEPS.PairEffect.SourceCircuit
open SourceInventory TNLean.PEPS.Approximation
variable {P : Type} {a b : Layout P}
/-- The affected input list consists of the corrected prefix and affected crossing registers. -/
private theorem affectedInputLayout (C T : Layout Bool)
    (hC : ∀ r ∈ C, r.owner = true) :
    Layout.restrict (fun p : Bool ↦ p) (C ++ T) =
      C ++ Layout.restrict (fun p : Bool ↦ p) T := by
  rw [Layout.restrict_append, Layout.restrict_eq_self_of_owner _ hC rfl]

/-- The corrected prefix contributes no exterior registers. -/
private theorem exteriorInputLayout (C T : Layout Bool)
    (hC : ∀ r ∈ C, r.owner = true) :
    Layout.restrict (fun p : Bool ↦ !p) (C ++ T) =
      Layout.restrict (fun p : Bool ↦ !p) T := by
  rw [Layout.restrict_append, Layout.restrict_eq_nil_of_owner _ hC rfl, List.nil_append]

/-- Tensor two proper coordinate frames and identify the resulting affected memory. -/
private def affectedInputFrame {I J : Type} [Fintype I] [Fintype J]
    (C T : Layout Bool) (hC : ∀ r ∈ C, r.owner = true)
    (f : EuclideanSpace ℂ I →ₗᵢ[ℂ] Mem C)
    (g : EuclideanSpace ℂ J →ₗᵢ[ℂ] Mem (Layout.restrict (fun p : Bool ↦ p) T)) :
    EuclideanSpace ℂ (I × J) →ₗᵢ[ℂ] Mem (Layout.restrict (fun p : Bool ↦ p) (C ++ T)) :=
  (Layout.memCongr (affectedInputLayout C T hC).symm).toLinearIsometry.comp
    ((appendIso C (Layout.restrict (fun p : Bool ↦ p) T)).symm.toLinearIsometry.comp
      ((TensorProduct.mapIsometry f g).comp
        (((EuclideanSpace.basisFun I ℂ).tensorProduct
          (EuclideanSpace.basisFun J ℂ)).repr.symm.toLinearIsometry)))

/-- Identify the exterior crossing frame with the exterior input memory. -/
private def exteriorInputFrame {J : Type} [Fintype J]
    (C T : Layout Bool) (hC : ∀ r ∈ C, r.owner = true)
    (h : EuclideanSpace ℂ J →ₗᵢ[ℂ] Mem (Layout.restrict (fun p : Bool ↦ !p) T)) :
    EuclideanSpace ℂ J →ₗᵢ[ℂ] Mem (Layout.restrict (fun p : Bool ↦ !p) (C ++ T)) :=
  (Layout.memCongr (exteriorInputLayout C T hC).symm).toLinearIsometry.comp h

/-- Tensoring register-list identifications preserves the underlying pure tensor. -/
private theorem memCongr_tmul_heq {Q : Type} {a a' b b' : Layout Q}
    (ha : a = a') (hb : b = b') (x : Mem a) (y : Mem b) :
    HEq (Layout.memCongr ha x ⊗ₜ[ℂ] Layout.memCongr hb y) (x ⊗ₜ[ℂ] y) := by
  cases ha
  cases hb
  rfl

/-- The two frame columns give the actual register partition of their three factors. -/
private theorem inputFrames_basis_tensor {I J : Type} [Fintype I] [Fintype J]
    (C T : Layout Bool) (hC : ∀ r ∈ C, r.owner = true)
    (f : EuclideanSpace ℂ I →ₗᵢ[ℂ] Mem C)
    (g : EuclideanSpace ℂ J →ₗᵢ[ℂ] Mem (Layout.restrict (fun p : Bool ↦ p) T))
    (h : EuclideanSpace ℂ J →ₗᵢ[ℂ] Mem (Layout.restrict (fun p : Bool ↦ !p) T))
    (i : I) (j : J) :
    affectedInputFrame C T hC f g (EuclideanSpace.basisFun _ ℂ (i, j)) ⊗ₜ[ℂ]
      exteriorInputFrame C T hC h (EuclideanSpace.basisFun _ ℂ j) =
      Layout.partitionIso (fun p : Bool ↦ p) (C ++ T)
        ((appendIso C T).symm (f (EuclideanSpace.basisFun _ ℂ i) ⊗ₜ[ℂ]
          (Layout.partitionIso (fun p : Bool ↦ p) T).symm
            (g (EuclideanSpace.basisFun _ ℂ j) ⊗ₜ[ℂ] h (EuclideanSpace.basisFun _ ℂ j)))) := by
  classical
  let cb := (EuclideanSpace.basisFun I ℂ).tensorProduct (EuclideanSpace.basisFun J ℂ)
  change Layout.memCongr (affectedInputLayout C T hC).symm
    ((appendIso C (Layout.restrict (fun p : Bool ↦ p) T)).symm
      ((TensorProduct.mapIsometry f g) (cb.repr.symm (EuclideanSpace.basisFun _ ℂ (i, j))))) ⊗ₜ[ℂ]
    Layout.memCongr (exteriorInputLayout C T hC).symm (h (EuclideanSpace.basisFun _ ℂ j)) = _
  have hc : cb.repr.symm (EuclideanSpace.basisFun _ ℂ (i, j)) =
      EuclideanSpace.basisFun _ ℂ i ⊗ₜ[ℂ] EuclideanSpace.basisFun _ ℂ j := by
    rw [EuclideanSpace.basisFun_apply, cb.repr_symm_single]
    exact OrthonormalBasis.tensorProduct_apply' _ _ _
  rw [hc]
  simp only [TensorProduct.mapIsometry_apply, TensorProduct.map_tmul,
    LinearIsometry.coe_toLinearMap]
  apply eq_of_heq
  exact (memCongr_tmul_heq _ _ _ _).trans
    (Layout.partitionIso_append_true_tmul (fun p : Bool ↦ p) C T hC rfl _ _ _).symm

/-- A normalized crossing vector gives probability weights and the two proper frames. -/
private theorem exists_inputFrames {I : Type} [Fintype I]
    (C T : Layout Bool) (hC : ∀ r ∈ C, r.owner = true)
    (f : EuclideanSpace ℂ I →ₗᵢ[ℂ] Mem C)
    (β : Mem (Layout.restrict (fun p : Bool ↦ p) T) ⊗[ℂ]
      Mem (Layout.restrict (fun p : Bool ↦ !p) T)) (hβ : ‖β‖ = 1) :
    HasSchmidtInputFrames C T f β := by
  obtain ⟨r, lam, g, h, hlam, hsum, hsource⟩ :=
    PairSource.exists_probability_schmidt_isometries _ _ β hβ
  refine ⟨r, lam, affectedInputFrame C T hC f g,
    exteriorInputFrame C T hC h, hlam, hsum, ?_⟩
  intro i
  rw [hsource]
  simp only [map_sum, map_smul, TensorProduct.tmul_sum, TensorProduct.tmul_smul]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg ((Real.sqrt (lam j) : ℂ) • ·)
    (inputFrames_basis_tensor C T hC f g h i j).symm

variable (w : SourceCircuit a b) (S : Finset (sourceLocations w))
    (E : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).1) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (F : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).2) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (hE : ∀ e ξ, (E e ξ)ᴴ * E e ξ = 1) (hF : ∀ e ξ, (F e ξ)ᴴ * F e ξ = 1)

open Classical in
/-- The actual crossing sources determine probability weights and isometric
local input maps. Their Schmidt expansion holds for every corrected endpoint
coordinate in the two prescribed local input memories. In particular, the
expansion and its isometries are constructed from the original source vectors. -/
theorem exists_correctedInputFrames (ξ : Choices (correctedMask w S) w) :
    HasSchmidtInputFrames (correctedSourceLayout w S) (crossingSourceLayout w S)
      (correctedSourceFrame w S E F hE hF ξ) (sourceCrossingVector w S ξ) := by
  exact exists_inputFrames _ _ (correctedSourceLayout_owners w S)
    (correctedSourceFrame w S E F hE hF ξ) (sourceCrossingVector w S ξ)
    (norm_sourceCrossingVector w S ξ)

end TNLean.PEPS.PairEffect.SourceCircuit
