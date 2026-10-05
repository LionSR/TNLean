/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.SemiRegularBondProductIsometry
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Product ranges from one-coordinate support

A coefficient vector lies in the range of a product of physical maps exactly
when each one-coordinate slice lies in the range of the corresponding local
map. Neither injectivity nor surjectivity is required. In particular, the
statement includes empty site sets and empty input and output alphabets.

The reverse implication uses a linear section on the local range, extended to
the full output space, and applies its associated retraction at every site.
This supplies the product-support step for the supported bond transformations
in SCP10, arXiv:1001.3807, Section 7, lines 2992–3019.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {Site In Out : Type*} [Fintype Site] [DecidableEq Site]

private def productFamilyMatrix (F : Site → Matrix Out In ℂ) :
    Matrix (Site → Out) (Site → In) ℂ :=
  fun τ σ => ∏ v, F v (τ v) (σ v)

private def productFamilyMap [Fintype In] (F : Site → Matrix Out In ℂ) :
    ((Site → In) → ℂ) →ₗ[ℂ] ((Site → Out) → ℂ) :=
  Matrix.mulVecLin (productFamilyMatrix F)

private theorem productFamilyMap_comp {Mid : Type*} [Fintype In] [Fintype Mid]
    (F : Site → Matrix Out Mid ℂ) (L : Site → Matrix Mid In ℂ) :
    productFamilyMap F ∘ₗ productFamilyMap L = productFamilyMap (fun v => F v * L v) := by
  classical
  unfold productFamilyMap
  rw [← Matrix.mulVecLin_mul]
  congr 1
  ext τ σ
  simp only [productFamilyMatrix, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (v : Site) (j : Mid) => F v (τ v) j * L v j (σ v))).symm

private theorem productFamilyMap_oneCoordinate_apply [Fintype Out] [DecidableEq Out]
    (v : Site) (P : Matrix Out Out ℂ) (ψ : (Site → Out) → ℂ) (τ : Site → Out) :
    productFamilyMap (fun w => if w = v then P else 1) ψ τ =
      ∑ s : Out, P (τ v) s * ψ (Function.update τ v s) := by
  classical
  let e := Equiv.funSplitAt v Out
  have hcoeff (s : Out) (β : {w : Site // w ≠ v} → Out) :
      (∏ w, (if w = v then P else 1) (τ w) (e.symm (s, β) w)) =
        P (τ v) s * if (fun w : {w : Site // w ≠ v} => τ w.1) = β then 1 else 0 := by
    rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ v)]
    have hfirst : (if v = v then P else 1) (τ v) (e.symm (s, β) v) = P (τ v) s := by
      simp [e, Equiv.funSplitAt, Equiv.piSplitAt]
    rw [hfirst]
    congr 1
    rw [Finset.prod_subtype (Finset.univ \ {v}) (p := fun w => w ≠ v) (F := inferInstance)
      (fun w => by simp)]
    have hout (w : {w : Site // w ≠ v}) :
        (if w.1 = v then P else 1) (τ w.1) (e.symm (s, β) w.1) =
          if τ w.1 = β w then 1 else 0 := by
      simp [e, Equiv.funSplitAt, Equiv.piSplitAt, w.2, Matrix.one_apply]
    simp only [hout, Fintype.prod_boole, ← funext_iff]
  change (∑ σ : Site → Out, (∏ w, (if w = v then P else 1) (τ w) (σ w)) * ψ σ) = _
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
        simp [e, Equiv.funSplitAt, Equiv.piSplitAt]
      · simp [e, Equiv.funSplitAt, Equiv.piSplitAt, h]
    simp only [hcfg, eq_self, ite_true, mul_one]
  · intro β _ hβ
    rw [ite_eq_right (Ne.symm hβ), mul_zero, zero_mul]
  · simp

/-- If a local matrix fixes every one-coordinate slice, its full product fixes
the coefficient vector. The matrix need not be a projection. -/
theorem physicalProductMap_fixed_of_slices_fixed [Fintype Out]
    (P : Matrix Out Out ℂ) (ψ : (Site → Out) → ℂ)
    (hψ : ∀ v τ, P *ᵥ (fun s => ψ (Function.update τ v s)) =
      fun s => ψ (Function.update τ v s)) :
    physicalProductMap Site P ψ = ψ := by
  classical
  let F (S : Finset Site) (v : Site) : Matrix Out Out ℂ := if v ∈ S then P else 1
  have hone (v : Site) : productFamilyMap (fun w => if w = v then P else 1) ψ = ψ := by
    funext τ
    rw [productFamilyMap_oneCoordinate_apply]
    simpa only [Matrix.mulVec, dotProduct, Function.update_eq_self] using
      congr_fun (hψ v τ) (τ v)
  have hS (S : Finset Site) : productFamilyMap (F S) ψ = ψ := by
    induction S using Finset.induction with
    | empty =>
      have hid : productFamilyMap (F ∅) = LinearMap.id := by
        simp only [productFamilyMap, F, Finset.notMem_empty, ite_false]
        unfold productFamilyMatrix
        have hm : (fun τ σ : Site → Out => ∏ v, (1 : Matrix Out Out ℂ) (τ v) (σ v)) =
            (1 : Matrix (Site → Out) (Site → Out) ℂ) := by
          ext τ σ
          simp only [Matrix.one_apply, Fintype.prod_boole, ← funext_iff]
        rw [hm, Matrix.mulVecLin_one]
      rw [hid, LinearMap.id_apply]
    | @insert v S hv ih =>
      have hprod : (fun w => (if w = v then P else 1) * F S w) = F (insert v S) := by
        funext w
        by_cases hw : w = v
        · subst w
          simp [F, hv]
        · simp [F, hw]
      calc productFamilyMap (F (insert v S)) ψ =
          productFamilyMap (fun w => if w = v then P else 1) (productFamilyMap (F S) ψ) := by
            rw [← LinearMap.comp_apply, productFamilyMap_comp, hprod]
        _ = ψ := by rw [ih, hone]
  change productFamilyMap (fun _ : Site => P) ψ = ψ
  simpa only [F, Finset.mem_univ, ite_true] using hS Finset.univ

/-- Every one-coordinate slice of a physical product image lies in the local
physical range, with all other output coordinates left arbitrary. -/
theorem physicalProductMap_slice_mem_range [Fintype In]
    (F : Matrix Out In ℂ) (ψ : (Site → In) → ℂ) (v : Site) (τ : Site → Out) :
    (fun s => physicalProductMap Site F ψ (Function.update τ v s)) ∈
      LinearMap.range (Matrix.mulVecLin F) := by
  classical
  have hsum : (fun s => physicalProductMap Site F ψ (Function.update τ v s)) =
      ∑ σ : Site → In, ((∏ w ∈ Finset.univ.erase v, F (τ w) (σ w)) * ψ σ) •
        (fun s => F s (σ v)) := by
    funext s
    simp only [physicalProductMap_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro σ _
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ v)]
    simp only [Function.update_self]
    have hout : (∏ w ∈ Finset.univ.erase v, F (Function.update τ v s w) (σ w)) =
        ∏ w ∈ Finset.univ.erase v, F (τ w) (σ w) := by
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

/-- A vector is in the full product range precisely when every one-coordinate
slice is in the local range. No rank or nonemptiness assumption is needed.
Source: the product support underlying SCP10, Section 7, lines 2992–3019. -/
theorem mem_range_physicalProductMap_iff [Fintype In] [Finite Out]
    (F : Matrix Out In ℂ) (ψ : (Site → Out) → ℂ) :
    ψ ∈ LinearMap.range (physicalProductMap Site F) ↔
      ∀ v τ, (fun s => ψ (Function.update τ v s)) ∈
        LinearMap.range (Matrix.mulVecLin F) := by
  classical
  let := Fintype.ofFinite Out
  constructor
  · rintro ⟨χ, rfl⟩ v τ
    exact physicalProductMap_slice_mem_range F χ v τ
  · intro hψ
    let f := Matrix.mulVecLin F
    obtain ⟨r, hr⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
    obtain ⟨l, hl⟩ := r.exists_extend
    let L := LinearMap.toMatrix' l
    have hfixed (q : Out → ℂ) (hq : q ∈ f.range) : (F * L) *ᵥ q = q := by
      rw [← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec]
      change f (l q) = q
      have hlq := LinearMap.congr_fun hl ⟨q, hq⟩
      have hrq := congr_arg Subtype.val (LinearMap.congr_fun hr ⟨q, hq⟩)
      exact hlq ▸ hrq
    have hproduct := physicalProductMap_fixed_of_slices_fixed (F * L) ψ
      (fun v τ => hfixed _ (hψ v τ))
    refine ⟨physicalProductMap Site L ψ, ?_⟩
    simpa only [physicalProductMap, ← LinearMap.comp_apply, ← Matrix.mulVecLin_mul,
      physicalProductMatrix_mul] using hproduct

end TNLean.PEPS
