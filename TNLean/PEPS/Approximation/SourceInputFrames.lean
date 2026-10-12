/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceInputPartition
import TNLean.PEPS.Approximation.SourceSlotBasis
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Data.List.NodupEquivFin

/-!
# Proper input frames from the original source endpoints

Tensoring the endpoint Schmidt isometries in the inherited order gives an
isometry into the actual corrected-source memory. No spanning assumption on
these endpoint frames is needed.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 383–434.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-exterior-input; Theorem 5.2, lines 409–480.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
-/


noncomputable section
open scoped TensorProduct Matrix ComplexConjugate
namespace TNLean.PEPS.PairEffect.SourceInventory

/-- A rectangular matrix with orthonormal columns gives its actual Euclidean isometry. -/
def matrixFrame {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (E : Matrix m n ℂ) (hE : Eᴴ * E = 1) :
    EuclideanSpace ℂ n →ₗᵢ[ℂ] EuclideanSpace ℂ m := by
  refine (Matrix.toEuclideanLin E).isometryOfOrthonormal
    (v := (EuclideanSpace.basisFun n ℂ).toBasis)
    (EuclideanSpace.basisFun n ℂ).orthonormal ?_
  have hmat : Matrix.of (fun i j ↦
      (Matrix.toEuclideanLin E) (EuclideanSpace.basisFun n ℂ j) i) = E := by
    ext i j
    change (E *ᵥ (EuclideanSpace.basisFun n ℂ j).ofLp) i = E i j
    simp [EuclideanSpace.basisFun_apply, Matrix.mulVec_single]
  apply Matrix.gram_eq_one_iff_orthonormal.mp
  rw [Matrix.gram_eq_conjTranspose_mul (EuclideanSpace.basisFun m ℂ)]
  simpa only [Function.comp_apply, OrthonormalBasis.coe_toBasis,
    EuclideanSpace.basisFun_repr, hmat] using hE

/-- Tensor the original endpoint frames in the prescribed list of source positions.
Repeated endpoint owners never identify distinct tensor positions. -/
def sourcePositionsFrame {P I : Type} (r : I → PairSource P)
    (A B : I → Type) [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (f : ∀ i, EuclideanSpace ℂ (A i) →ₗᵢ[ℂ] (r i).leftSpace)
    (g : ∀ i, EuclideanSpace ℂ (B i) →ₗᵢ[ℂ] (r i).rightSpace) :
    (indices : List I) →
      EuclideanSpace ℂ (∀ j : Fin indices.length, A (indices.get j) × B (indices.get j))
        →ₗᵢ[ℂ] Mem (sourcePositionsLayout r indices)
  | [] => ((OrthonormalBasis.singleton Unit ℂ).reindex
      (Equiv.ofUnique Unit (∀ j : Fin 0, A ([].get j) × B ([].get j)))).repr.symm.toLinearIsometry
  | i :: indices =>
      let tail := sourcePositionsFrame r A B f g indices
      let pair := (TensorProduct.mapIsometry (f i) (g i)).comp
        (((EuclideanSpace.basisFun (A i) ℂ).tensorProduct
          (EuclideanSpace.basisFun (B i) ℂ)).repr.symm.toLinearIsometry)
      let coord := (((EuclideanSpace.basisFun (A i × B i) ℂ).tensorProduct
        (EuclideanSpace.basisFun
          (∀ j : Fin indices.length, A (indices.get j) × B (indices.get j)) ℂ)).reindex
          (Fin.consEquiv (fun j : Fin (i :: indices).length ↦
            A ((i :: indices).get j) × B ((i :: indices).get j)))).repr.symm.toLinearIsometry
      (TensorProduct.assocIsometry ℂ (r i).leftSpace (r i).rightSpace
        (Mem (sourcePositionsLayout r indices))).toLinearIsometry.comp
          ((TensorProduct.mapIsometry pair tail).comp coord)

/-- The tensor frame columns are the actual endpoint preparations, with every
spectator input unchanged. -/
theorem sourcePositionsFrame_basis_prepare {P I : Type} (r : I → PairSource P)
    (A B : I → Type) [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (f : ∀ i, EuclideanSpace ℂ (A i) →ₗᵢ[ℂ] (r i).leftSpace)
    (g : ∀ i, EuclideanSpace ℂ (B i) →ₗᵢ[ℂ] (r i).rightSpace)
    (indices : List I) (a : ∀ i, A i × B i) (ℓ : Layout P) (x : Mem ℓ) :
    (appendIso (sourcePositionsLayout r indices) ℓ).symm
      (sourcePositionsFrame r A B f g indices
        (EuclideanSpace.basisFun _ ℂ (fun j ↦ a (indices.get j))) ⊗ₜ[ℂ] x) =
      (prepareSourcePositions r (fun i ↦
        f i (EuclideanSpace.basisFun (A i) ℂ (a i).1) ⊗ₜ[ℂ]
          g i (EuclideanSpace.basisFun (B i) ℂ (a i).2)) indices ℓ).eval x := by
  classical
  induction indices with
  | nil =>
    change (appendIso [] ℓ).symm
      (((OrthonormalBasis.singleton Unit ℂ).reindex
        (Equiv.ofUnique Unit (∀ j : Fin 0, A ([].get j) × B ([].get j)))).repr.symm
          (EuclideanSpace.basisFun _ ℂ (fun j ↦ a ([].get j))) ⊗ₜ[ℂ] x) = x
    simp [EuclideanSpace.basisFun_apply, OrthonormalBasis.reindex_apply,
      OrthonormalBasis.singleton_apply, appendIso]
  | cons i indices ih =>
    let pair := (TensorProduct.mapIsometry (f i) (g i)).comp
      (((EuclideanSpace.basisFun (A i) ℂ).tensorProduct
        (EuclideanSpace.basisFun (B i) ℂ)).repr.symm.toLinearIsometry)
    let cb := ((EuclideanSpace.basisFun (A i × B i) ℂ).tensorProduct
      (EuclideanSpace.basisFun
        (∀ j : Fin indices.length, A (indices.get j) × B (indices.get j)) ℂ)).reindex
        (Fin.consEquiv (fun j : Fin (i :: indices).length ↦
          A ((i :: indices).get j) × B ((i :: indices).get j)))
    change (appendIso (sourcePositionsLayout r (i :: indices)) ℓ).symm
      ((TensorProduct.assocIsometry ℂ (r i).leftSpace (r i).rightSpace
        (Mem (sourcePositionsLayout r indices)))
        ((TensorProduct.mapIsometry pair (sourcePositionsFrame r A B f g indices))
          (cb.repr.symm (EuclideanSpace.basisFun _ ℂ
            (fun j ↦ a ((i :: indices).get j))))) ⊗ₜ[ℂ] x) = _
    have hc : cb.repr.symm (EuclideanSpace.basisFun _ ℂ
        (fun j ↦ a ((i :: indices).get j))) =
        EuclideanSpace.basisFun (A i × B i) ℂ (a i) ⊗ₜ[ℂ]
          EuclideanSpace.basisFun _ ℂ (fun j ↦ a (indices.get j)) := by
      rw [EuclideanSpace.basisFun_apply, cb.repr_symm_single]
      have hh := OrthonormalBasis.reindex_apply
        ((EuclideanSpace.basisFun (A i × B i) ℂ).tensorProduct
          (EuclideanSpace.basisFun
            (∀ j : Fin indices.length, A (indices.get j) × B (indices.get j)) ℂ))
        (Fin.consEquiv (fun j : Fin (i :: indices).length ↦
          A ((i :: indices).get j) × B ((i :: indices).get j)))
        (fun j ↦ a ((i :: indices).get j))
      exact hh.trans (OrthonormalBasis.tensorProduct_apply'
        (EuclideanSpace.basisFun (A i × B i) ℂ)
        (EuclideanSpace.basisFun
          (∀ j : Fin indices.length, A (indices.get j) × B (indices.get j)) ℂ) _)
    rw [hc]
    simp only [TensorProduct.mapIsometry_apply, TensorProduct.map_tmul,
      LinearIsometry.coe_toLinearMap]
    have hp : pair (EuclideanSpace.basisFun (A i × B i) ℂ (a i)) =
        f i (EuclideanSpace.basisFun (A i) ℂ (a i).1) ⊗ₜ[ℂ]
          g i (EuclideanSpace.basisFun (B i) ℂ (a i).2) := by
      change (TensorProduct.mapIsometry (f i) (g i))
        (((EuclideanSpace.basisFun (A i) ℂ).tensorProduct
          (EuclideanSpace.basisFun (B i) ℂ)).repr.symm
            (EuclideanSpace.basisFun (A i × B i) ℂ (a i))) = _
      rw [EuclideanSpace.basisFun_apply, OrthonormalBasis.repr_symm_single]
      rw [OrthonormalBasis.tensorProduct_apply']
      simp only [TensorProduct.mapIsometry_apply, TensorProduct.map_tmul,
        LinearIsometry.coe_toLinearMap]
    rw [hp]
    change (appendIso (⟨(r i).left, (r i).leftSpace⟩ ::
        ⟨(r i).right, (r i).rightSpace⟩ :: sourcePositionsLayout r indices) ℓ).symm
        ((f i (EuclideanSpace.basisFun (A i) ℂ (a i).1) ⊗ₜ[ℂ]
          (g i (EuclideanSpace.basisFun (B i) ℂ (a i).2) ⊗ₜ[ℂ]
            sourcePositionsFrame r A B f g indices
              (EuclideanSpace.basisFun _ ℂ (fun j ↦ a (indices.get j))))) ⊗ₜ[ℂ] x) = _
    rw [appendIso_symm_cons_tmul, appendIso_symm_cons_tmul, ih]
    rfl

/-- The matrix isometry sends each coordinate vector to the recorded matrix column. -/
theorem matrixFrame_basis {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (E : Matrix m n ℂ) (hE : Eᴴ * E = 1) (j : n) :
    matrixFrame E hE (EuclideanSpace.basisFun n ℂ j) =
      WithLp.toLp 2 (fun i ↦ E i j) := by
  ext i
  change (E *ᵥ (EuclideanSpace.basisFun n ℂ j).ofLp) i = E i j
  simp [EuclideanSpace.basisFun_apply, Matrix.mulVec_single]

/-- The inherited list order enumerates each selected position exactly once. -/
private def selectedPositionEquiv {P : Type} (R : SourceInventory P)
    (selected : Fin R.length → Bool) :
    Fin (((List.finRange R.length).filter selected).length) ≃
      {i : Fin R.length // selected i = true} :=
  (List.Nodup.getEquiv ((List.finRange R.length).filter selected)
    ((List.nodup_finRange R.length).filter selected)).trans
      (Equiv.subtypeEquivRight (fun i ↦ by simp))

/-- The tensor frame on exactly the selected original positions, in their
inherited source-register order. Only selected positions occur in the target memory. -/
def selectedSourceFrame {P : Type} (R : SourceInventory P)
    (U V : Fin R.length → HSpace) (selected : Fin R.length → Bool)
    (A B : Fin R.length → Type) [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (f : ∀ i, EuclideanSpace ℂ (A i) →ₗᵢ[ℂ] U i)
    (g : ∀ i, EuclideanSpace ℂ (B i) →ₗᵢ[ℂ] V i) :
    EuclideanSpace ℂ (∀ i : {i : Fin R.length // selected i = true}, A i.1 × B i.1)
      →ₗᵢ[ℂ] Mem (freeSlotLayout R U V selected) :=
  let e := Equiv.piCongrLeft
    (fun i : {i : Fin R.length // selected i = true} ↦ A i.1 × B i.1)
    (selectedPositionEquiv R selected)
  (Layout.memCongr (sourcePositionsLayout_filter R U V selected)).toLinearIsometry.comp
    ((sourcePositionsFrame (slotReference R U V) A B f g
      ((List.finRange R.length).filter selected)).comp
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e.symm).toLinearIsometry)

/-- A selected tensor-frame column is the ordered endpoint tensor with the
canonical identification of its register layout. -/
theorem selectedSourceFrame_basis {P : Type} (R : SourceInventory P)
    (U V : Fin R.length → HSpace) (selected : Fin R.length → Bool)
    (A B : Fin R.length → Type) [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (f : ∀ i, EuclideanSpace ℂ (A i) →ₗᵢ[ℂ] U i)
    (g : ∀ i, EuclideanSpace ℂ (B i) →ₗᵢ[ℂ] V i) (a : ∀ i, A i × B i) :
    selectedSourceFrame R U V selected A B f g
        (EuclideanSpace.basisFun _ ℂ (fun i ↦ a i.1)) =
      Layout.memCongr (sourcePositionsLayout_filter R U V selected)
        (sourcePositionsFrame (slotReference R U V) A B f g
          ((List.finRange R.length).filter selected)
          (EuclideanSpace.basisFun _ ℂ
            (fun j ↦ a (((List.finRange R.length).filter selected).get j)))) := by
  classical
  let e := Equiv.piCongrLeft
    (fun i : {i : Fin R.length // selected i = true} ↦ A i.1 × B i.1)
    (selectedPositionEquiv R selected)
  change Layout.memCongr _ ((sourcePositionsFrame (slotReference R U V) A B f g _)
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e.symm)
      (EuclideanSpace.basisFun _ ℂ (fun i ↦ a i.1)))) = _
  congr 2
  rw [EuclideanSpace.basisFun_apply, EuclideanSpace.piLpCongrLeft_single,
    ← EuclideanSpace.basisFun_apply]
  rfl

/-- The selected proper tensor frame gives the actual free-source preparation
on every basis assignment and every spectator input. -/
theorem selectedSourceFrame_basis_prepare {P : Type} (R : SourceInventory P)
    (U V : Fin R.length → HSpace) (selected : Fin R.length → Bool)
    (A B : Fin R.length → Type) [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (f : ∀ i, EuclideanSpace ℂ (A i) →ₗᵢ[ℂ] U i)
    (g : ∀ i, EuclideanSpace ℂ (B i) →ₗᵢ[ℂ] V i) (a : ∀ i, A i × B i)
    (ℓ : Layout P) (x : Mem ℓ) :
    (appendIso (freeSlotLayout R U V selected) ℓ).symm
      (selectedSourceFrame R U V selected A B f g
        (EuclideanSpace.basisFun _ ℂ (fun i ↦ a i.1)) ⊗ₜ[ℂ] x) =
      (prepareFreeSlots R U V selected (fun i ↦
        f i (EuclideanSpace.basisFun (A i) ℂ (a i).1) ⊗ₜ[ℂ]
          g i (EuclideanSpace.basisFun (B i) ℂ (a i).2)) ℓ).eval x := by
  rw [selectedSourceFrame_basis, ← Layout.memCongr_append_tmul]
  have hp := sourcePositionsFrame_basis_prepare (slotReference R U V) A B f g
    ((List.finRange R.length).filter selected) a ℓ x
  apply eq_of_heq
  exact (Layout.memCongr_apply_heq _ _).trans
    ((heq_of_eq hp).trans (eval_prepareSourcePositions_filter R U V selected _ ℓ x))

end TNLean.PEPS.PairEffect.SourceInventory
