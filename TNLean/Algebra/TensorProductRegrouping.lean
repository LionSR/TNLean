/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CyclicInsertion
import TNLean.Algebra.TensorProductContraction

/-!
# Regrouping tensor products of inner product spaces

Bookkeeping for continuous linear maps between tensor products of complex inner product spaces,
and identifications of Euclidean tensor powers used to read registers of a stack.

* `ContinuousLinearMap.isoL` : the continuous linear map of a linear isometric equivalence,
  with its interaction with `lTensor`, `rTensor` and the reassociation isometries.
* `ContinuousLinearMap.clm_ext_tmul`, `ContinuousLinearMap.clm_ext_tmul₃`,
  `ContinuousLinearMap.tmul₃_induction` : extensionality and induction on pure tensors.
* `LinearIsometryEquiv.lTensor_tmul`, `LinearIsometryEquiv.rTensor_tmul` : isometric
  equivalences on one factor, on pure tensors.
* `EuclideanSpace.pairIso` : `ℂ^α ⊗ ℂ^β ≅ ℂ^{α × β}`, with
  `EuclideanSpace.pairIso_single_tmul_single` on basis vectors.
* `EuclideanSpace.consIso` : `ℂ^ι ⊗ ℂ^{Fin n → ι} ≅ ℂ^{Fin (n + 1) → ι}`, with
  `EuclideanSpace.piTensor_cons`, `EuclideanSpace.tensorPower_succ`,
  `CyclicInsertion.insertAt_zero_eq_consIso` and `CyclicInsertion.insertAt_succ_eq_consIso`.
* `EuclideanSpace.emptyIso` : `ℂ ≅ ℂ^{Fin 0 → ι}`.

These generic statements are candidates for QICLean.
-/

noncomputable section

open scoped InnerProductSpace TensorProduct

namespace ContinuousLinearMap

variable {E F G H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The continuous linear map of a linear isometric equivalence. -/
abbrev isoL (e : E ≃ₗᵢ[ℂ] F) : E →L[ℂ] F := e.toLinearIsometry.toContinuousLinearMap

@[simp]
theorem isoL_apply (e : E ≃ₗᵢ[ℂ] F) (x : E) : isoL e x = e x := rfl

theorem clm_ext_tmul {f g : E ⊗[ℂ] F →L[ℂ] G} (h : ∀ x y, f (x ⊗ₜ y) = g (x ⊗ₜ y)) : f = g := by
  ext1 z
  induction z using TensorProduct.inductionOn with
  | tmul x y => exact h x y
  | add a b ha hb => rw [map_add, map_add, ha, hb]

theorem clm_ext_tmul₃ {f g : E ⊗[ℂ] (F ⊗[ℂ] G) →L[ℂ] H}
    (h : ∀ x y z, f (x ⊗ₜ (y ⊗ₜ z)) = g (x ⊗ₜ (y ⊗ₜ z))) : f = g := by
  refine clm_ext_tmul fun x w => ?_
  induction w using TensorProduct.inductionOn with
  | tmul y z => exact h x y z
  | add a b ha hb => rw [TensorProduct.tmul_add, map_add, map_add, ha, hb]

/-- Induction over a triple tensor product `E ⊗ (F ⊗ G)` through its pure tensors. -/
theorem tmul₃_induction {motive : E ⊗[ℂ] (F ⊗[ℂ] G) → Prop} (u : E ⊗[ℂ] (F ⊗[ℂ] G))
    (tmul : ∀ x y z, motive (x ⊗ₜ (y ⊗ₜ z)))
    (add : ∀ a b, motive a → motive b → motive (a + b)) : motive u := by
  induction u using TensorProduct.inductionOn with
  | tmul x w =>
      induction w using TensorProduct.inductionOn with
      | tmul y z => exact tmul x y z
      | add a b ha hb => rw [TensorProduct.tmul_add]; exact add _ _ ha hb
  | add a b ha hb => exact add a b ha hb

@[simp]
theorem isoL_trans (e : E ≃ₗᵢ[ℂ] F) (e' : F ≃ₗᵢ[ℂ] G) : isoL (e.trans e') = isoL e' ∘L isoL e :=
  rfl

theorem isoL_lTensor (e : F ≃ₗᵢ[ℂ] G) : isoL (e.lTensor E) = (isoL e).lTensor E :=
  clm_ext_tmul fun x y => by simp [LinearIsometryEquiv.lTensor_def]

theorem isoL_rTensor (e : E ≃ₗᵢ[ℂ] F) : isoL (e.rTensor G) = (isoL e).rTensor G :=
  clm_ext_tmul fun x y => by simp [LinearIsometryEquiv.rTensor_def]

theorem iso_lTensor_apply (e : F ≃ₗᵢ[ℂ] G) (z : E ⊗[ℂ] F) :
    e.lTensor E z = (isoL e).lTensor E z :=
  DFunLike.congr_fun (isoL_lTensor e) z

theorem iso_rTensor_apply (e : E ≃ₗᵢ[ℂ] F) (z : E ⊗[ℂ] G) :
    e.rTensor G z = (isoL e).rTensor G z :=
  DFunLike.congr_fun (isoL_rTensor e) z

theorem lTensor_lTensor_assoc_symm (f : G →L[ℂ] H) (z : E ⊗[ℂ] (F ⊗[ℂ] G)) :
    (TensorProduct.assocIsometry ℂ E F H).symm ((f.lTensor F).lTensor E z) =
      f.lTensor (E ⊗[ℂ] F) ((TensorProduct.assocIsometry ℂ E F G).symm z) := by
  refine DFunLike.congr_fun (f := isoL (TensorProduct.assocIsometry ℂ E F H).symm ∘L
    (f.lTensor F).lTensor E) (g := f.lTensor (E ⊗[ℂ] F) ∘L
      isoL (TensorProduct.assocIsometry ℂ E F G).symm) (clm_ext_tmul₃ fun x y w => ?_) z
  simp only [comp_apply, isoL_apply, lTensor_tmul, TensorProduct.assocIsometry_symm_apply,
    TensorProduct.assoc_symm_tmul]

theorem rTensor_lTensor_comm (f : E →L[ℂ] F) (g : G →L[ℂ] H) (z : E ⊗[ℂ] G) :
    f.rTensor H (g.lTensor E z) = g.lTensor F (f.rTensor G z) := by
  refine DFunLike.congr_fun (f := f.rTensor H ∘L g.lTensor E) (g := g.lTensor F ∘L f.rTensor G)
    (clm_ext_tmul fun x y => ?_) z
  simp only [comp_apply, lTensor_tmul, rTensor_tmul]

theorem leftCommL_lTensor_rTensor (f : F →L[ℂ] G) (z : E ⊗[ℂ] (F ⊗[ℂ] H)) :
    leftCommL E G H ((f.rTensor H).lTensor E z) = f.rTensor (E ⊗[ℂ] H) (leftCommL E F H z) := by
  refine DFunLike.congr_fun (f := leftCommL E G H ∘L (f.rTensor H).lTensor E)
    (g := f.rTensor (E ⊗[ℂ] H) ∘L leftCommL E F H) (clm_ext_tmul₃ fun x y w => ?_) z
  simp only [comp_apply, lTensor_tmul, rTensor_tmul, leftCommL_tmul]

theorem lTensor_comp_apply (f : F →L[ℂ] G) (g : H →L[ℂ] F) (z : E ⊗[ℂ] H) :
    f.lTensor E (g.lTensor E z) = (f ∘L g).lTensor E z := by
  rw [lTensor_comp]
  rfl

theorem rTensor_comp_apply (f : F →L[ℂ] G) (g : H →L[ℂ] F) (z : H ⊗[ℂ] E) :
    f.rTensor E (g.rTensor E z) = (f ∘L g).rTensor E z := by
  rw [rTensor_comp]
  rfl

end ContinuousLinearMap

namespace LinearIsometryEquiv

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [NormedAddCommGroup G] [InnerProductSpace ℂ G]

/-- A linear isometric equivalence on the second factor, on a pure tensor. -/
theorem lTensor_tmul (e : F ≃ₗᵢ[ℂ] G) (x : E) (y : F) : e.lTensor E (x ⊗ₜ y) = x ⊗ₜ e y := by
  simp [LinearIsometryEquiv.lTensor_def]

/-- A linear isometric equivalence on the first factor, on a pure tensor. -/
theorem rTensor_tmul (e : E ≃ₗᵢ[ℂ] F) (x : E) (y : G) : e.rTensor G (x ⊗ₜ y) = e x ⊗ₜ y := by
  simp [LinearIsometryEquiv.rTensor_def]

end LinearIsometryEquiv

namespace EuclideanSpace

variable {α β ι : Type} [Fintype α] [Fintype β] [Fintype ι]

/-- The identification `ℂ^α ⊗ ℂ^β ≅ ℂ^{α × β}` with `(x ⊗ y) (a, b) = x a * y b`. -/
def pairIso (α β : Type) [Fintype α] [Fintype β] :
    EuclideanSpace ℂ α ⊗[ℂ] EuclideanSpace ℂ β ≃ₗᵢ[ℂ] EuclideanSpace ℂ (α × β) :=
  ((EuclideanSpace.basisFun α ℂ).tensorProduct (EuclideanSpace.basisFun β ℂ)).repr

@[simp]
theorem pairIso_tmul_apply (x : EuclideanSpace ℂ α) (y : EuclideanSpace ℂ β) (i : α × β) :
    pairIso α β (x ⊗ₜ y) i = x i.1 * y i.2 := by
  simp [pairIso, OrthonormalBasis.tensorProduct_repr_tmul_apply', mul_comm]

/-- `pairIso` sends `|a⟩ ⊗ |b⟩` to `|a, b⟩`. -/
theorem pairIso_single_tmul_single [DecidableEq α] [DecidableEq β] (a : α) (b : β) :
    pairIso α β ((EuclideanSpace.single a (1 : ℂ) : EuclideanSpace ℂ α) ⊗ₜ
      (EuclideanSpace.single b (1 : ℂ) : EuclideanSpace ℂ β)) =
      EuclideanSpace.single (a, b) (1 : ℂ) := by
  ext i
  rw [pairIso_tmul_apply]
  simp only [PiLp.single_apply, ite_zero_mul_ite_zero, one_mul, Prod.ext_iff]

/-- The identification `ℂ^ι ⊗ ℂ^{Fin n → ι} ≅ ℂ^{Fin (n + 1) → ι}` placing the first factor in
register `0`. -/
def consIso (ι : Type) [Fintype ι] (n : ℕ) :
    EuclideanSpace ℂ ι ⊗[ℂ] EuclideanSpace ℂ (Fin n → ι) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Fin (n + 1) → ι) :=
  (pairIso ι (Fin n → ι)).trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Fin.consEquiv fun _ => ι))

@[simp]
theorem consIso_tmul_apply {n : ℕ} (x : EuclideanSpace ℂ ι) (y : EuclideanSpace ℂ (Fin n → ι))
    (f : Fin (n + 1) → ι) : consIso ι n (x ⊗ₜ y) f = x (f 0) * y (Fin.tail f) := by
  simp [consIso, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft',
    Fin.consEquiv]

theorem piTensor_cons {n : ℕ} (v : EuclideanSpace ℂ ι) (u : Fin n → EuclideanSpace ℂ ι) :
    piTensor (Fin.cons v u : Fin (n + 1) → EuclideanSpace ℂ ι) =
      consIso ι n (v ⊗ₜ piTensor u) := by
  ext f
  simp [piTensor_apply, Fin.prod_univ_succ, Fin.tail]

theorem tensorPower_succ {n : ℕ} (η : EuclideanSpace ℂ ι) :
    tensorPower (Fin (n + 1)) η = consIso ι n (η ⊗ₜ tensorPower (Fin n) η) := by
  rw [tensorPower, tensorPower, ← piTensor_cons]
  congr 1
  funext i
  refine Fin.cases rfl (fun _ => rfl) i

/-- The one-dimensional space `ℂ^{Fin 0 → ι}` identified with `ℂ`. -/
def emptyIso (ι : Type) [Fintype ι] : ℂ ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 0 → ι) :=
  (OrthonormalBasis.singleton Unit ℂ).repr.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.ofUnique Unit (Fin 0 → ι)))

theorem emptyIso_one (η : EuclideanSpace ℂ ι) : emptyIso ι 1 = tensorPower (Fin 0) η := by
  ext f
  simp [emptyIso, tensorPower, piTensor_apply, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft', OrthonormalBasis.singleton_repr]

end EuclideanSpace

namespace CyclicInsertion

open EuclideanSpace

variable {ι : Type} [Fintype ι]

theorem insertAt_zero_eq_consIso {n : ℕ} (η v : EuclideanSpace ℂ ι) :
    insertAt η (0 : Fin (n + 1)) v = consIso ι n (v ⊗ₜ tensorPower (Fin n) η) := by
  rw [insertAt_zero, piTensor_cons]
  rfl

theorem insertAt_succ_eq_consIso {n : ℕ} (η v : EuclideanSpace ℂ ι) (k : Fin n) :
    insertAt η k.succ v = consIso ι n (η ⊗ₜ insertAt η k v) := by
  rw [insertAt_apply, insertAt_apply, ← piTensor_cons, Fin.cons_update]
  congr 2
  funext i
  refine Fin.cases rfl (fun _ => rfl) i

end CyclicInsertion
