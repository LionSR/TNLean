/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Ring

/-!
# Product ranges with site-dependent alphabets

A coefficient vector is in the range of a site-dependent product of physical
maps if and only if each one-coordinate slice belongs to the range of the map
at that site. The input and output alphabets may be empty, as may the set of
sites. No injectivity, surjectivity, or common rank is assumed.

Both the input and output alphabet may vary at each site. The local
retractions are chosen independently, so this includes unequal virtual bond
dimensions without embeddings into a common ambient alphabet.

Source: the product-support argument underlying SCP10, arXiv:1001.3807,
Section 7, lines 2992–3019.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {Site : Type*} [Fintype Site] [DecidableEq Site]
variable {In Out : Site → Type*}

/-- The product matrix of a family of physical maps, one at each site. -/
def dependentPhysicalProductFamilyMatrix (F : (v : Site) → Matrix (Out v) (In v) ℂ) :
    Matrix ((v : Site) → Out v) ((v : Site) → In v) ℂ :=
  fun τ σ => ∏ v, F v (τ v) (σ v)

/-- Apply a possibly different physical map at every site. -/
def dependentPhysicalProductFamilyMap [∀ v, Fintype (In v)]
    (F : (v : Site) → Matrix (Out v) (In v) ℂ) :
    (((v : Site) → In v) → ℂ) →ₗ[ℂ] (((v : Site) → Out v) → ℂ) :=
  Matrix.mulVecLin (dependentPhysicalProductFamilyMatrix F)

/-- The coefficient formula for a site-dependent physical product. -/
theorem dependentPhysicalProductFamilyMap_apply [∀ v, Fintype (In v)]
    (F : (v : Site) → Matrix (Out v) (In v) ℂ)
    (ψ : ((v : Site) → In v) → ℂ) (τ : (v : Site) → Out v) :
    dependentPhysicalProductFamilyMap F ψ τ =
      ∑ σ : (v : Site) → In v, (∏ v, F v (τ v) (σ v)) * ψ σ := rfl

/-- Products of physical matrices compose separately at each site. -/
theorem dependentPhysicalProductFamilyMatrix_mul {Mid : Site → Type*} [∀ v, Fintype (Mid v)]
    (F : (v : Site) → Matrix (Out v) (Mid v) ℂ) (L : (v : Site) → Matrix (Mid v) (In v) ℂ) :
    dependentPhysicalProductFamilyMatrix F * dependentPhysicalProductFamilyMatrix L =
      dependentPhysicalProductFamilyMatrix (fun v => F v * L v) := by
  ext τ σ
  simp only [dependentPhysicalProductFamilyMatrix, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (v : Site) (j : Mid v) => F v (τ v) j * L v j (σ v))).symm

/-- Products of physical maps compose separately at each site. -/
theorem dependentPhysicalProductFamilyMap_comp {Mid : Site → Type*}
    [∀ v, Fintype (In v)] [∀ v, Fintype (Mid v)]
    (F : (v : Site) → Matrix (Out v) (Mid v) ℂ) (L : (v : Site) → Matrix (Mid v) (In v) ℂ) :
    dependentPhysicalProductFamilyMap F ∘ₗ dependentPhysicalProductFamilyMap L =
      dependentPhysicalProductFamilyMap (fun v => F v * L v) := by
  simp only [dependentPhysicalProductFamilyMap, ← Matrix.mulVecLin_mul,
    dependentPhysicalProductFamilyMatrix_mul]

omit [DecidableEq Site] in
/-- Identity matrices at every site give the identity product matrix. -/
@[simp] theorem dependentPhysicalProductFamilyMatrix_one [∀ v, DecidableEq (Out v)] :
    dependentPhysicalProductFamilyMatrix (fun v : Site => (1 : Matrix (Out v) (Out v) ℂ)) = 1 := by
  ext τ σ
  simp only [dependentPhysicalProductFamilyMatrix, Matrix.one_apply, Fintype.prod_boole,
    ← funext_iff]

/-- Identity maps at every site give the identity product map. -/
@[simp] theorem dependentPhysicalProductFamilyMap_one
    [∀ v, Fintype (Out v)] [∀ v, DecidableEq (Out v)] :
    dependentPhysicalProductFamilyMap (fun v : Site => (1 : Matrix (Out v) (Out v) ℂ)) =
      LinearMap.id := by
  simp only [dependentPhysicalProductFamilyMap, dependentPhysicalProductFamilyMatrix_one,
    Matrix.mulVecLin_one]

/-- A product with only one nonidentity coordinate acts on that coordinate's slice. -/
theorem dependentPhysicalProductFamilyMap_oneCoordinate_apply
    [∀ v, Fintype (Out v)] [∀ v, DecidableEq (Out v)]
    (v : Site) (P : Matrix (Out v) (Out v) ℂ)
    (ψ : ((v : Site) → Out v) → ℂ) (τ : (v : Site) → Out v) :
    dependentPhysicalProductFamilyMap
        (Function.update (fun w => (1 : Matrix (Out w) (Out w) ℂ)) v P) ψ τ =
      ∑ s : Out v, P (τ v) s * ψ (Function.update τ v s) := by
  classical
  let e := Equiv.piSplitAt v Out
  have hcoeff (s : Out v) (β : (w : {w : Site // w ≠ v}) → Out w.1) :
      (∏ w, (Function.update (fun w => (1 : Matrix (Out w) (Out w) ℂ)) v P w)
        (τ w) (e.symm (s, β) w)) =
        P (τ v) s * if (fun w : {w : Site // w ≠ v} => τ w.1) = β then 1 else 0 := by
    rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ v)]
    have hfirst : (Function.update (fun w => (1 : Matrix (Out w) (Out w) ℂ)) v P v)
        (τ v) (e.symm (s, β) v) = P (τ v) s := by
      simp [e, Equiv.piSplitAt]
    rw [hfirst]
    congr 1
    rw [Finset.prod_subtype (Finset.univ \ {v}) (p := fun w => w ≠ v) (F := inferInstance)
      (fun w => by simp)]
    have hout (w : {w : Site // w ≠ v}) :
        (Function.update (fun w => (1 : Matrix (Out w) (Out w) ℂ)) v P w.1)
          (τ w.1) (e.symm (s, β) w.1) =
          if τ w.1 = β w then 1 else 0 := by
      simp [e, Equiv.piSplitAt, w.2, Matrix.one_apply]
    simp only [hout, Fintype.prod_boole, ← funext_iff]
  change (∑ σ : (v : Site) → Out v,
    (∏ w, (Function.update (fun w => (1 : Matrix (Out w) (Out w) ℂ)) v P w) (τ w) (σ w)) *
      ψ σ) = _
  rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  simp only [hcoeff]
  rw [Finset.sum_eq_single (fun w : {w : Site // w ≠ v} => τ w.1)]
  · have hcfg : e.symm (s, fun w : {w : Site // w ≠ v} => τ w.1) =
        Function.update τ v s := by
      funext w
      by_cases h : w = v
      · subst w
        simp [e, Equiv.piSplitAt]
      · simp [e, Equiv.piSplitAt, h]
    simp only [hcfg, eq_self, ite_true, mul_one]
  · intro β _ hβ
    rw [ite_eq_right (Ne.symm hβ), mul_zero, zero_mul]
  · simp

/-- If each local matrix fixes every slice at its own site, the full product
fixes the coefficient vector. The local matrices need not be projections. -/
theorem dependentPhysicalProductFamilyMap_fixed_of_slices_fixed [∀ v, Fintype (Out v)]
    (P : (v : Site) → Matrix (Out v) (Out v) ℂ) (ψ : ((v : Site) → Out v) → ℂ)
    (hψ : ∀ v τ, P v *ᵥ (fun s => ψ (Function.update τ v s)) =
      fun s => ψ (Function.update τ v s)) :
    dependentPhysicalProductFamilyMap P ψ = ψ := by
  classical
  let F (S : Finset Site) (v : Site) : Matrix (Out v) (Out v) ℂ := if v ∈ S then P v else 1
  have hone (v : Site) : dependentPhysicalProductFamilyMap
      (Function.update (fun w => (1 : Matrix (Out w) (Out w) ℂ)) v (P v)) ψ = ψ := by
    funext τ
    rw [dependentPhysicalProductFamilyMap_oneCoordinate_apply]
    simpa only [Matrix.mulVec, dotProduct, Function.update_eq_self] using
      congr_fun (hψ v τ) (τ v)
  have hS (S : Finset Site) : dependentPhysicalProductFamilyMap (F S) ψ = ψ := by
    induction S using Finset.induction with
    | empty =>
      simp only [F, Finset.notMem_empty, ite_false, dependentPhysicalProductFamilyMap_one,
        LinearMap.id_apply]
    | @insert v S hv ih =>
      have hprod : (fun w =>
          Function.update (fun w => (1 : Matrix (Out w) (Out w) ℂ)) v (P v) w * F S w) =
          F (insert v S) := by
        funext w
        by_cases hw : w = v
        · subst w
          simp [F, hv]
        · simp [F, hw]
      calc dependentPhysicalProductFamilyMap (F (insert v S)) ψ =
          dependentPhysicalProductFamilyMap
            (Function.update (fun w => (1 : Matrix (Out w) (Out w) ℂ)) v (P v))
            (dependentPhysicalProductFamilyMap (F S) ψ) := by
            rw [← LinearMap.comp_apply, dependentPhysicalProductFamilyMap_comp, hprod]
        _ = ψ := by rw [ih, hone]
  simpa only [F, Finset.mem_univ, ite_true] using hS Finset.univ

/-- Every one-coordinate slice of a physical product image lies in the local
physical range, with all other output coordinates left arbitrary. -/
theorem dependentPhysicalProductFamilyMap_slice_mem_range [∀ v, Fintype (In v)]
    (F : (v : Site) → Matrix (Out v) (In v) ℂ) (ψ : ((v : Site) → In v) → ℂ)
    (v : Site) (τ : (v : Site) → Out v) :
    (fun s => dependentPhysicalProductFamilyMap F ψ (Function.update τ v s)) ∈
      LinearMap.range (Matrix.mulVecLin (F v)) := by
  classical
  have hsum : (fun s => dependentPhysicalProductFamilyMap F ψ (Function.update τ v s)) =
      ∑ σ : (v : Site) → In v, ((∏ w ∈ Finset.univ.erase v, F w (τ w) (σ w)) * ψ σ) •
        (fun s => F v s (σ v)) := by
    funext s
    simp only [dependentPhysicalProductFamilyMap_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
    apply Finset.sum_congr rfl
    intro σ _
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ v)]
    simp only [Function.update_self]
    have hout : (∏ w ∈ Finset.univ.erase v, F w (Function.update τ v s w) (σ w)) =
        ∏ w ∈ Finset.univ.erase v, F w (τ w) (σ w) := by
      apply Finset.prod_congr rfl
      intro w hw
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)]
    rw [hout]
    ring
  rw [hsum]
  apply Submodule.sum_mem
  intro σ _
  apply Submodule.smul_mem
  refine ⟨Pi.single (σ v) 1, ?_⟩
  ext s
  simp [Matrix.mulVec_single, Matrix.col]

/-- A vector lies in the product range exactly when every one-coordinate
slice is in the range of the map at that site. This allows site-dependent
input and output alphabets of different sizes, as well as different ranks,
zero matrices, and empty alphabets.
Source: the product support underlying SCP10, Section 7, lines 2992–3019. -/
theorem mem_range_dependentPhysicalProductFamilyMap_iff [∀ v, Fintype (In v)] [∀ v, Finite (Out v)]
    (F : (v : Site) → Matrix (Out v) (In v) ℂ) (ψ : ((v : Site) → Out v) → ℂ) :
    ψ ∈ LinearMap.range (dependentPhysicalProductFamilyMap F) ↔
      ∀ v τ, (fun s => ψ (Function.update τ v s)) ∈
        LinearMap.range (Matrix.mulVecLin (F v)) := by
  classical
  let := fun v => Fintype.ofFinite (Out v)
  constructor
  · rintro ⟨χ, rfl⟩ v τ
    exact dependentPhysicalProductFamilyMap_slice_mem_range F χ v τ
  · intro hψ
    have hlocal (v : Site) : ∃ L : Matrix (In v) (Out v) ℂ,
        ∀ q ∈ LinearMap.range (Matrix.mulVecLin (F v)), (F v * L) *ᵥ q = q := by
      let f := Matrix.mulVecLin (F v)
      obtain ⟨r, hr⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
      obtain ⟨l, hl⟩ := r.exists_extend
      refine ⟨LinearMap.toMatrix' l, ?_⟩
      intro q hq
      rw [← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec]
      change f (l q) = q
      have hlq := LinearMap.congr_fun hl ⟨q, hq⟩
      have hrq := congr_arg Subtype.val (LinearMap.congr_fun hr ⟨q, hq⟩)
      exact hlq ▸ hrq
    choose L hL using hlocal
    have hproduct := dependentPhysicalProductFamilyMap_fixed_of_slices_fixed (fun v => F v * L v) ψ
      (fun v τ => hL v _ (hψ v τ))
    refine ⟨dependentPhysicalProductFamilyMap L ψ, ?_⟩
    simpa only [← LinearMap.comp_apply, dependentPhysicalProductFamilyMap_comp] using hproduct

end TNLean.PEPS
