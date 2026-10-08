/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.DependentLiftedCut

/-!
# Recovering closed tensors from lifted regional contractions

When every endpoint outside a region is exposed by the cut, restricting a
lifted regional range to the product of the actual local physical ranges
recovers the full cut contraction range. Outside endpoint labels are summed
independently before the local tensors are restored.

Source: the product-support reconstruction in SCP10, arXiv:1001.3807,
Theorem 5.4 and Section 7.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS.DependentBondNetwork

variable {Vertex Edge : Type*} [Fintype Vertex] [Fintype Edge]
variable [DecidableEq Vertex] [DecidableEq Edge]
variable (tail head : Edge → Vertex) (D : Edge → Type*)
variable [∀ e, Fintype (D e)] [∀ e, DecidableEq (D e)]
variable {Phys : Vertex → Type*}

/-- Replace the outside labels of a boundary while retaining every inside label. -/
def cutReplaceOutside (R : Finset Vertex) (C : Finset Edge)
    (κ : CutConfig C D) (ξ : (v : {v // v ∉ R}) → LocalConfig tail head D v.1) :
    CutConfig C D := fun p ↦
  if h : endpointVertex tail head (p.1.1, p.2) ∈ R then κ p
  else ξ ⟨endpointVertex tail head (p.1.1, p.2), h⟩ ⟨(p.1.1, p.2), rfl⟩

private def replaceOutsideEndpoints (R : Finset Vertex) (β : EndpointConfig D)
    (ξ : (v : {v // v ∉ R}) → LocalConfig tail head D v.1) : EndpointConfig D := fun p ↦
  if h : endpointVertex tail head p ∈ R then β p
  else ξ ⟨endpointVertex tail head p, h⟩ ⟨p, rfl⟩

omit [Fintype Vertex] [Fintype Edge] [DecidableEq Edge]
    [∀ e, Fintype (D e)] [∀ e, DecidableEq (D e)] in
private theorem replaceOutsideEndpoints_inside (R : Finset Vertex) (β : EndpointConfig D)
    (ξ : (v : {v // v ∉ R}) → LocalConfig tail head D v.1)
    {v : Vertex} (hv : v ∈ R) :
    endpointSiteEquiv tail head D (replaceOutsideEndpoints tail head D R β ξ) v =
      endpointSiteEquiv tail head D β v := by
  funext p
  simp only [endpointSiteEquiv_apply, replaceOutsideEndpoints, p.2, hv, ↓reduceDIte]

omit [Fintype Vertex] [Fintype Edge] [DecidableEq Edge]
    [∀ e, Fintype (D e)] [∀ e, DecidableEq (D e)] in
private theorem replaceOutsideEndpoints_outside (R : Finset Vertex) (β : EndpointConfig D)
    (ξ : (v : {v // v ∉ R}) → LocalConfig tail head D v.1) (v : {v // v ∉ R}) :
    endpointSiteEquiv tail head D (replaceOutsideEndpoints tail head D R β ξ) v.1 = ξ v := by
  rcases v with ⟨v, hv⟩
  funext ⟨p, hp⟩
  dsimp only at hp
  subst v
  simp [endpointSiteEquiv_apply, replaceOutsideEndpoints, hv]

omit [Fintype Vertex] [∀ e, Fintype (D e)] in
private theorem cutInteriorWeight_replaceOutsideEndpoints (R : Finset Vertex) (C : Finset Edge)
    (hcut : ∀ p : Endpoint Edge, endpointVertex tail head p ∉ R → p.1 ∈ C)
    (β : EndpointConfig D) (ξ : (v : {v // v ∉ R}) → LocalConfig tail head D v.1) :
    cutInteriorWeight D C (replaceOutsideEndpoints tail head D R β ξ) =
      cutInteriorWeight D C β := by
  unfold cutInteriorWeight
  apply Finset.prod_congr rfl
  intro e _
  by_cases he : e ∈ C
  · simp only [he, ↓reduceIte]
  · have ht : endpointVertex tail head (e, true) ∈ R := by
      by_contra h
      exact he (hcut (e, true) h)
    have hf : endpointVertex tail head (e, false) ∈ R := by
      by_contra h
      exact he (hcut (e, false) h)
    have hβt : replaceOutsideEndpoints tail head D R β ξ (e, true) = β (e, true) := by
      simp only [replaceOutsideEndpoints, ht, ↓reduceDIte]
    have hβf : replaceOutsideEndpoints tail head D R β ξ (e, false) = β (e, false) := by
      simp only [replaceOutsideEndpoints, hf, ↓reduceDIte]
    rw [hβt, hβf]

private def outsideEndpointSwapEquiv (R : Finset Vertex) :
    (EndpointConfig D × ((v : {v // v ∉ R}) → LocalConfig tail head D v.1)) ≃
      (EndpointConfig D × ((v : {v // v ∉ R}) → LocalConfig tail head D v.1)) :=
  Function.Involutive.toPerm (fun z ↦ (replaceOutsideEndpoints tail head D R z.1 z.2,
    fun v ↦ endpointSiteEquiv tail head D z.1 v.1)) (by
      rintro ⟨β, ξ⟩
      apply Prod.ext
      · funext p
        simp only [replaceOutsideEndpoints]
        split_ifs <;> rfl
      · funext v
        exact replaceOutsideEndpoints_outside tail head D R β ξ v)

/-- Changing only the physical indices outside a region. -/
def replaceOutsidePhysical (R : Finset Vertex) (σ : (v : Vertex) → Phys v)
    (τ : OutsidePhysicalConfig R Phys) : (v : Vertex) → Phys v := fun v ↦
  if h : v ∈ R then σ v else τ ⟨v, h⟩

omit [Fintype Vertex] in
/-- Restricting after replacing the outside physical configuration returns
the replacement configuration. -/
@[simp] theorem outsidePhysicalRestriction_replaceOutsidePhysical (R : Finset Vertex)
    (σ : (v : Vertex) → Phys v) (τ : OutsidePhysicalConfig R Phys) :
    outsidePhysicalRestriction R (replaceOutsidePhysical R σ τ) = τ := by
  funext v
  simp [outsidePhysicalRestriction, replaceOutsidePhysical, v.2]

omit [Fintype Vertex] in
/-- Replacing outside physical coordinates by their original values changes nothing. -/
@[simp] theorem replaceOutsidePhysical_restriction (R : Finset Vertex)
    (σ : (v : Vertex) → Phys v) :
    replaceOutsidePhysical R σ (outsidePhysicalRestriction R σ) = σ := by
  funext v
  simp only [replaceOutsidePhysical, outsidePhysicalRestriction]
  split_ifs <;> rfl

omit [Fintype Vertex] in
private theorem replaceOutsidePhysical_update (R : Finset Vertex)
    (σ : (v : Vertex) → Phys v) (τ : OutsidePhysicalConfig R Phys)
    (v : {v // v ∉ R}) (s : Phys v.1) :
    replaceOutsidePhysical R σ (Function.update τ v s) =
      Function.update (replaceOutsidePhysical R σ τ) v.1 s := by
  funext w
  by_cases h : w = v.1
  · subst w
    simp [replaceOutsidePhysical, v.2]
  · by_cases hw : w ∈ R
    · simp [replaceOutsidePhysical, hw, h]
    · simp [replaceOutsidePhysical, hw, h, show (⟨w, hw⟩ : {v // v ∉ R}) ≠ v from
        fun hh ↦ h (congrArg Subtype.val hh)]


omit [Fintype Vertex] [Fintype Edge] [DecidableEq Edge]
    [∀ e, Fintype (D e)] [∀ e, DecidableEq (D e)] in
private theorem cutReplaceOutside_swap (R : Finset Vertex) (C : Finset Edge)
    (β : EndpointConfig D) (ξ : (v : {v // v ∉ R}) → LocalConfig tail head D v.1) :
    cutReplaceOutside tail head D R C
        (cutRestriction D C (replaceOutsideEndpoints tail head D R β ξ))
        (fun v ↦ endpointSiteEquiv tail head D β v.1) = cutRestriction D C β := by
  funext p
  simp only [cutReplaceOutside, cutRestriction, replaceOutsideEndpoints,
    endpointSiteEquiv_apply]
  split_ifs <;> rfl

omit [∀ e, DecidableEq (D e)] in
private theorem sum_outsideEndpointSwap (R : Finset Vertex)
    (f : EndpointConfig D → ((v : {v // v ∉ R}) → LocalConfig tail head D v.1) → ℂ) :
    (∑ β, ∑ ξ, f (replaceOutsideEndpoints tail head D R β ξ)
      (fun v ↦ endpointSiteEquiv tail head D β v.1)) = ∑ β, ∑ ξ, f β ξ := by
  simpa only [Fintype.sum_prod_type, outsideEndpointSwapEquiv,
    Function.Involutive.toPerm, Equiv.coe_fn_mk] using
    (outsideEndpointSwapEquiv tail head D R).sum_comp (fun z ↦ f z.1 z.2)

/-- The boundary obtained by summing the old outside virtual labels and
pulling the outside physical boundary back through chosen local maps. -/
def reconstructedCutBoundary [∀ v, Fintype (Phys v)]
    (R : Finset Vertex) (C : Finset Edge)
    (hcut : ∀ p : Endpoint Edge, endpointVertex tail head p ∉ R → p.1 ∈ C)
    (L : (v : {v // v ∉ R}) → Matrix (LocalConfig tail head D v.1) (Phys v.1) ℂ)
    (M : CutConfig C D × OutsidePhysicalConfig R Phys → ℂ) (κ : CutConfig C D) : ℂ :=
  ∑ ξ : (v : {v // v ∉ R}) → LocalConfig tail head D v.1,
    ∑ τ : OutsidePhysicalConfig R Phys,
      M (cutReplaceOutside tail head D R C κ ξ, τ) *
        ∏ v : {v // v ∉ R}, L v (outsideCutLocalConfig tail head D R C hcut κ v) (τ v)

/-- Outside physical maps are absorbed into a joint cut boundary by summing
the old outside endpoint labels independently from the newly inserted ones. -/
theorem cutMap_reconstructedCutBoundary [∀ v, Fintype (Phys v)]
    (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ)
    (R : Finset Vertex) (C : Finset Edge)
    (hcut : ∀ p : Endpoint Edge, endpointVertex tail head p ∉ R → p.1 ∈ C)
    (L : (v : {v // v ∉ R}) → Matrix (LocalConfig tail head D v.1) (Phys v.1) ℂ)
    (M : CutConfig C D × OutsidePhysicalConfig R Phys → ℂ)
    (σ : (v : Vertex) → Phys v) :
    cutMap tail head D A C (reconstructedCutBoundary tail head D R C hcut L M) σ =
      dependentPhysicalProductFamilyMap
        (fun v : {v // v ∉ R} ↦
          LinearMap.toMatrix' (localSiteMap tail head D A v.1) * L v)
        (fun τ ↦ liftedCutMap tail head D A R C M (replaceOutsidePhysical R σ τ))
        (outsidePhysicalRestriction R σ) := by
  classical
  let f (β : EndpointConfig D)
      (ξ : (v : {v // v ∉ R}) → LocalConfig tail head D v.1) : ℂ :=
    ∑ τ : OutsidePhysicalConfig R Phys,
      ((M (cutReplaceOutside tail head D R C (cutRestriction D C β) ξ, τ) *
        ∏ v : {v // v ∉ R}, L v (endpointSiteEquiv tail head D β v.1) (τ v)) *
        cutInteriorWeight D C β) * ∏ v, A v (endpointSiteEquiv tail head D β v) (σ v)
  have hexpand : cutMap tail head D A C
      (reconstructedCutBoundary tail head D R C hcut L M) σ = ∑ β, ∑ ξ, f β ξ := by
    simp only [cutMap_apply, cutCoeff, reconstructedCutBoundary,
      outsideCutLocalConfig_restriction, Finset.sum_mul, f]
  rw [hexpand, ← sum_outsideEndpointSwap tail head D R f]
  simp only [f, cutReplaceOutside_swap, replaceOutsideEndpoints_outside,
    cutInteriorWeight_replaceOutsideEndpoints tail head D R C hcut]
  have hprod (β : EndpointConfig D)
      (ξ : (v : {v // v ∉ R}) → LocalConfig tail head D v.1) :
      (∏ v, A v (endpointSiteEquiv tail head D
        (replaceOutsideEndpoints tail head D R β ξ) v) (σ v)) =
      (∏ v ∈ R, A v (endpointSiteEquiv tail head D β v) (σ v)) *
        ∏ v : {v // v ∉ R}, A v (ξ v) (σ v.1) := by
    rw [← Finset.prod_filter_mul_prod_filter_not (s := Finset.univ) (p := fun v ↦ v ∈ R)]
    congr 1
    · simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
      apply Finset.prod_congr rfl
      intro v hv
      rw [replaceOutsideEndpoints_inside tail head D R β ξ hv]
    · rw [Finset.prod_subtype _ (p := fun v ↦ v ∉ R) (F := inferInstance)
        (fun _ ↦ by simp)]
      apply Finset.prod_congr rfl
      intro v _
      rw [replaceOutsideEndpoints_outside]
  simp_rw [hprod]
  have hentry (v : Vertex) (η : LocalConfig tail head D v) (s : Phys v) :
      LinearMap.toMatrix' (localSiteMap tail head D A v) s η = A v η s := by
    simp [LinearMap.toMatrix'_apply, localSiteMap_apply, Pi.single_apply]
  simp only [dependentPhysicalProductFamilyMap_apply, Matrix.mul_apply, hentry]
  simp_rw [Fintype.prod_sum]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ξ _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro τ _
  simp only [liftedCutMap_apply, liftedCutCoeff,
    outsidePhysicalRestriction_replaceOutsidePhysical, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro β _
  have hins : (∏ v ∈ R, A v (endpointSiteEquiv tail head D β v)
      (replaceOutsidePhysical R σ τ v)) =
      ∏ v ∈ R, A v (endpointSiteEquiv tail head D β v) (σ v) := by
    apply Finset.prod_congr rfl
    intro v hv
    simp only [replaceOutsidePhysical, hv, ↓reduceDIte]
  rw [hins]
  simp only [Finset.prod_mul_distrib, outsidePhysicalRestriction]
  ring


/-- A lifted regional contraction whose physical coefficients lie in the
product of all local tensor ranges is a genuine cut contraction. -/
theorem liftedCutSpace_inf_range_product_le_cutSpace [∀ v, Finite (Phys v)]
    (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ)
    (R : Finset Vertex) (C : Finset Edge)
    (hcut : ∀ p : Endpoint Edge, endpointVertex tail head p ∉ R → p.1 ∈ C) :
    liftedCutSpace tail head D A R C ⊓
        LinearMap.range (dependentPhysicalProductFamilyMap
          (fun v ↦ LinearMap.toMatrix' (localSiteMap tail head D A v))) ≤
      cutSpace tail head D A C := by
  classical
  let (v : Vertex) := Fintype.ofFinite (Phys v)
  have hlocal (v : {v // v ∉ R}) :
      ∃ L : Matrix (LocalConfig tail head D v.1) (Phys v.1) ℂ,
        ∀ q ∈ LinearMap.range (localSiteMap tail head D A v.1),
          (LinearMap.toMatrix' (localSiteMap tail head D A v.1) * L) *ᵥ q = q := by
    let f := localSiteMap tail head D A v.1
    obtain ⟨r, hr⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
    obtain ⟨l, hl⟩ := r.exists_extend
    refine ⟨LinearMap.toMatrix' l, ?_⟩
    intro q hq
    rw [← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
    have hlq := LinearMap.congr_fun hl ⟨q, hq⟩
    have hrq := congr_arg Subtype.val (LinearMap.congr_fun hr ⟨q, hq⟩)
    exact hlq ▸ hrq
  choose L hL using hlocal
  rintro ψ ⟨⟨M, hM⟩, hψ⟩
  refine ⟨reconstructedCutBoundary tail head D R C hcut L M, ?_⟩
  funext σ
  rw [cutMap_reconstructedCutBoundary]
  have hfixed : dependentPhysicalProductFamilyMap
      (fun v : {v // v ∉ R} ↦ LinearMap.toMatrix' (localSiteMap tail head D A v.1) * L v)
      (fun τ ↦ ψ (replaceOutsidePhysical R σ τ)) =
        (fun τ ↦ ψ (replaceOutsidePhysical R σ τ)) := by
    apply dependentPhysicalProductFamilyMap_fixed_of_slices_fixed
    intro v τ
    apply hL v
    simp_rw [replaceOutsidePhysical_update]
    have hs := (mem_range_dependentPhysicalProductFamilyMap_iff _ ψ).mp hψ v.1
      (replaceOutsidePhysical R σ τ)
    change (fun s ↦ ψ (Function.update (replaceOutsidePhysical R σ τ) v.1 s)) ∈
      LinearMap.range (Matrix.toLin' (LinearMap.toMatrix' (localSiteMap tail head D A v.1))) at hs
    simpa only [Matrix.toLin'_toMatrix'] using hs
  change dependentPhysicalProductFamilyMap _
    (fun τ ↦ (liftedCutMap tail head D A R C M) (replaceOutsidePhysical R σ τ)) _ = _
  rw [hM, hfixed]
  simp only [replaceOutsidePhysical_restriction]

/-- A cut exposing every outside endpoint is the lifted regional range
intersected with the product of the original local tensor ranges. No
injectivity, group action, or nonempty-alphabet hypothesis is needed. -/
theorem cutSpace_eq_liftedCutSpace_inf_range_product [∀ v, Finite (Phys v)]
    (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ)
    (R : Finset Vertex) (C : Finset Edge)
    (hcut : ∀ p : Endpoint Edge, endpointVertex tail head p ∉ R → p.1 ∈ C) :
    cutSpace tail head D A C = liftedCutSpace tail head D A R C ⊓
      LinearMap.range (dependentPhysicalProductFamilyMap
        (fun v ↦ LinearMap.toMatrix' (localSiteMap tail head D A v))) := by
  exact le_antisymm
    (le_inf (cutSpace_le_liftedCutSpace tail head D A R C hcut)
      (cutSpace_le_range_product tail head D A C))
    (liftedCutSpace_inf_range_product_le_cutSpace tail head D A R C hcut)

end TNLean.PEPS.DependentBondNetwork
