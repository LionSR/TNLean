/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.InjectiveVertexCoordinates
import TNLean.PEPS.ParentHamiltonian.RegionPhysicalGroundSpaceTransport

/-!
# Common one-site image conditions and the product vertex image

The intersection of the site-image conditions, with all spectator physical
indices free, is the image of the product of the vertex tensor maps.
Chosen local left inverses give local retractions onto these images; the
product retraction fixes every vector satisfying the local conditions.

Source: the independent site inverses and virtual-pair construction of
CPGSV21, arXiv:2011.12127, Section IV.C.1, lines 2017–2044.
This identifies the product site image, before imposing virtual bond
constraints, and is not a ground-state uniqueness assertion.

## References

- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- J. I. Cirac, D. Pérez-García,
  N. Schuch, F. Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V] {d : ℕ}

/-- A physical map applied at one vertex and the identity elsewhere. -/
noncomputable def oneVertexPhysicalFamily (v : V) (P : Matrix (Fin d) (Fin d) ℂ) :
    V → Matrix (Fin d) (Fin d) ℂ := fun w => if w = v then P else 1

/-- The product physical map of identity matrices is the identity. -/
theorem globalPhysicalMap_one :
    globalPhysicalMap (fun _ : V => (1 : Matrix (Fin d) (Fin d) ℂ)) = LinearMap.id := by
  apply LinearMap.ext
  intro ψ
  change (fullRegionPhysicalEquiv d).symm
    (regionPhysicalMap Finset.univ (fun _ : V => (1 : Matrix (Fin d) (Fin d) ℂ))
      (fullRegionPhysicalEquiv d ψ)) = ψ
  simp only [regionPhysicalMap, regionPhysicalProductMatrix_one, Matrix.mulVecLin_one,
    LinearMap.id_apply, LinearEquiv.symm_apply_apply]

/-- Composition of global physical maps is pointwise composition of their matrices. -/
theorem globalPhysicalMap_comp {e f : ℕ}
    (F : V → Matrix (Fin f) (Fin e) ℂ) (L : V → Matrix (Fin e) (Fin d) ℂ) :
    globalPhysicalMap F ∘ₗ globalPhysicalMap L = globalPhysicalMap (fun v => F v * L v) := by
  apply LinearMap.ext
  intro ψ
  change (fullRegionPhysicalEquiv f).symm
    (regionPhysicalMap Finset.univ F ((fullRegionPhysicalEquiv e)
      ((fullRegionPhysicalEquiv e).symm
        (regionPhysicalMap Finset.univ L (fullRegionPhysicalEquiv d ψ))))) = _
  rw [LinearEquiv.apply_symm_apply, ← LinearMap.comp_apply, regionPhysicalMap_comp]
  rfl

/-- The one-vertex product map acts on the corresponding one-site slice. -/
theorem globalPhysicalMap_oneVertex_apply (v : V) (P : Matrix (Fin d) (Fin d) ℂ)
    (ψ : (V → Fin d) → ℂ) (τ : V → Fin d) :
    globalPhysicalMap (oneVertexPhysicalFamily v P) ψ τ =
      ∑ s : Fin d, P (τ v) s * ψ (Function.update τ v s) := by
  classical
  let e := Equiv.funSplitAt v (Fin d)
  have hcoeff (s : Fin d) (β : {w : V // w ≠ v} → Fin d) :
      (∏ w, oneVertexPhysicalFamily v P w (τ w) (e.symm (s, β) w)) =
        P (τ v) s * if (fun w : {w : V // w ≠ v} => τ w.1) = β then 1 else 0 := by
    rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ v)]
    have hfirst : oneVertexPhysicalFamily v P v (τ v) (e.symm (s, β) v) = P (τ v) s := by
      simp [oneVertexPhysicalFamily, e, Equiv.funSplitAt, Equiv.piSplitAt]
    rw [hfirst]
    congr 1
    rw [Finset.prod_subtype (Finset.univ \ {v}) (p := fun w => w ≠ v) (F := inferInstance)
      (fun w => by simp)]
    have hout (w : {w : V // w ≠ v}) :
        oneVertexPhysicalFamily v P w.1 (τ w.1) (e.symm (s, β) w.1) =
          if τ w.1 = β w then 1 else 0 := by
      simp [oneVertexPhysicalFamily, e, Equiv.funSplitAt, Equiv.piSplitAt, w.2,
        Matrix.one_apply]
    simp only [hout, Fintype.prod_boole, ← funext_iff]
  rw [globalPhysicalMap_apply]
  rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  simp only [hcoeff]
  rw [Finset.sum_eq_single (fun w : {w : V // w ≠ v} => τ w.1)]
  · have hcfg : e.symm (s, fun w : {w : V // w ≠ v} => τ w.1) =
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

/-- Simultaneous one-vertex fixed-point conditions imply the product fixed-point
condition. The matrices need not be orthogonal projections or positive. -/
theorem globalPhysicalMap_fixed_of_oneVertex_fixed
    (P : V → Matrix (Fin d) (Fin d) ℂ) (ψ : (V → Fin d) → ℂ)
    (hψ : ∀ v, globalPhysicalMap (oneVertexPhysicalFamily v (P v)) ψ = ψ) :
    globalPhysicalMap P ψ = ψ := by
  classical
  let F (S : Finset V) (v : V) : Matrix (Fin d) (Fin d) ℂ := if v ∈ S then P v else 1
  have hS (S : Finset V) : globalPhysicalMap (F S) ψ = ψ := by
    induction S using Finset.induction with
    | empty => simpa only [F, Finset.notMem_empty, ite_false, LinearMap.id_apply] using
        LinearMap.congr_fun (globalPhysicalMap_one (V := V) (d := d)) ψ
    | @insert v S hv ih =>
      have hprod : (fun w => oneVertexPhysicalFamily v (P v) w * F S w) =
          F (insert v S) := by
        funext w
        by_cases hw : w = v
        · subst w
          simp [oneVertexPhysicalFamily, F, hv]
        · simp [oneVertexPhysicalFamily, F, hw]
      calc globalPhysicalMap (F (insert v S)) ψ =
          globalPhysicalMap (oneVertexPhysicalFamily v (P v)) (globalPhysicalMap (F S) ψ) := by
            rw [← LinearMap.comp_apply, globalPhysicalMap_comp, hprod]
        _ = ψ := by rw [ih, hψ]
  simpa only [F, Finset.mem_univ, ite_true] using hS Finset.univ

/-- Extract a one-site physical slice, with every other physical index fixed. -/
def vertexPhysicalSlice (v : V) (τ : V → Fin d) :
    ((V → Fin d) → ℂ) →ₗ[ℂ] (Fin d → ℂ) where
  toFun ψ s := ψ (Function.update τ v s)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The one-vertex product map is the local matrix on each one-site slice. -/
theorem vertexPhysicalSlice_globalPhysicalMap_oneVertex (v : V)
    (P : Matrix (Fin d) (Fin d) ℂ) (ψ : (V → Fin d) → ℂ) (τ : V → Fin d) :
    vertexPhysicalSlice v τ (globalPhysicalMap (oneVertexPhysicalFamily v P) ψ) =
      P *ᵥ vertexPhysicalSlice v τ ψ := by
  funext s
  change globalPhysicalMap (oneVertexPhysicalFamily v P) ψ (Function.update τ v s) =
    (P *ᵥ (fun t => ψ (Function.update τ v t))) s
  rw [globalPhysicalMap_oneVertex_apply]
  simp only [Function.update_self, Function.update_idem, Matrix.mulVec, dotProduct]

variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Common singleton site-image conditions, with every spectator index free.
Source: the physical site-image conditions before virtual bond constraints in
CPGSV21, Section IV.C.1, lines 2017–2044. -/
noncomputable def vertexImageGroundSpace (A : Tensor Γ d) : Submodule ℂ ((V → Fin d) → ℂ) :=
  ⨅ v : V, ⨅ τ : V → Fin d, (localTensorMap A v).range.comap (vertexPhysicalSlice v τ)

/-- Membership is exactly the collection of true one-site image conditions. -/
theorem mem_vertexImageGroundSpace_iff (A : Tensor Γ d) (ψ : (V → Fin d) → ℂ) :
    ψ ∈ vertexImageGroundSpace A ↔ ∀ v τ,
      vertexPhysicalSlice v τ ψ ∈ (localTensorMap A v).range := by
  simp only [vertexImageGroundSpace, Submodule.mem_iInf, Submodule.mem_comap]

/-- The site tensor followed by its chosen inverse is a retraction onto its image.
It need not be orthogonal. Source: the site inverses in CPGSV21,
Section IV.C.1, lines 2017–2044. -/
noncomputable def vertexImageProjection (A : Tensor Γ d) (hA : IsVertexInjective A)
    (v : V) : Matrix (Fin d) (Fin d) ℂ :=
  LinearMap.toMatrix' (localTensorMap A v ∘ₗ localLeftInverse A hA v)

/-- A local physical vector is fixed by the site retraction exactly when it is
in the actual site tensor image. Source: CPGSV21, Section IV.C.1,
lines 2017–2044. -/
theorem vertexImageProjection_mulVec_eq_self_iff (A : Tensor Γ d) (hA : IsVertexInjective A)
    (v : V) (q : Fin d → ℂ) :
    vertexImageProjection A hA v *ᵥ q = q ↔ q ∈ (localTensorMap A v).range := by
  rw [vertexImageProjection, LinearMap.toMatrix'_mulVec]
  change localTensorMap A v (localLeftInverse A hA v q) = q ↔ _
  constructor
  · intro h
    exact ⟨localLeftInverse A hA v q, h⟩
  · rintro ⟨x, rfl⟩
    rw [localLeftInverse_apply_localTensorMap]

/-- Express the product vertex tensor map in globally indexed physical coordinates.
Source: the independent site maps in CPGSV21, Section IV.C.1, lines 2017–2044. -/
noncomputable def globalVertexTensorMap (A : Tensor Γ d) :
    (RegionVertexVirtualConfig A Finset.univ → ℂ) →ₗ[ℂ] ((V → Fin d) → ℂ) :=
  (fullRegionPhysicalEquiv d).symm.toLinearMap ∘ₗ regionVertexTensorMap A Finset.univ

/-- The product site inverse in globally indexed physical coordinates. -/
noncomputable def globalVertexLeftInverse (A : Tensor Γ d) (hA : IsVertexInjective A) :
    ((V → Fin d) → ℂ) →ₗ[ℂ] (RegionVertexVirtualConfig A Finset.univ → ℂ) :=
  regionVertexLeftInverse A hA Finset.univ ∘ₗ (fullRegionPhysicalEquiv d).toLinearMap

/-- The product of the local retractions is the vertex map times its product inverse.
Source: the independent inverse construction in CPGSV21,
Section IV.C.1, lines 2017–2044. -/
theorem globalPhysicalMap_vertexImageProjection (A : Tensor Γ d) (hA : IsVertexInjective A) :
    globalPhysicalMap (vertexImageProjection A hA) =
      globalVertexTensorMap A ∘ₗ globalVertexLeftInverse A hA := by
  apply LinearMap.ext
  intro ψ
  change (fullRegionPhysicalEquiv d).symm
    (regionPhysicalMap Finset.univ (vertexImageProjection A hA) (fullRegionPhysicalEquiv d ψ)) =
      (fullRegionPhysicalEquiv d).symm
        (regionVertexTensorMap A Finset.univ
          (regionVertexLeftInverse A hA Finset.univ (fullRegionPhysicalEquiv d ψ)))
  have hP : vertexImageProjection A hA = fun v =>
      LinearMap.toMatrix' (localTensorMap A v) *
        LinearMap.toMatrix' (localLeftInverse A hA v) := by
    funext v
    exact LinearMap.toMatrix'_comp _ _
  rw [hP, ← regionPhysicalMap_comp]
  rfl

/-- Each one-site image condition makes its one-vertex retraction fix the full vector.
Source: the independent image conditions in CPGSV21,
Section IV.C.1, lines 2017–2044. -/
theorem oneVertexPhysicalMap_vertexImageProjection_eq_self_of_mem
    (A : Tensor Γ d) (hA : IsVertexInjective A) {ψ : (V → Fin d) → ℂ}
    (hψ : ψ ∈ vertexImageGroundSpace A) (v : V) :
    globalPhysicalMap (oneVertexPhysicalFamily v (vertexImageProjection A hA v)) ψ = ψ := by
  rw [mem_vertexImageGroundSpace_iff] at hψ
  funext τ
  rw [globalPhysicalMap_oneVertex_apply]
  have hq := (vertexImageProjection_mulVec_eq_self_iff A hA v _).mpr (hψ v τ)
  have h := congr_fun hq (τ v)
  simpa only [Matrix.mulVec, dotProduct, vertexPhysicalSlice, LinearMap.coe_mk,
    AddHom.coe_mk, Function.update_eq_self] using h

/-- The common one-site image conditions imply explicit reconstruction through
the product site map. No global reconstruction condition is assumed.
Source: independent site inverses in CPGSV21, Section IV.C.1, lines 2017–2044. -/
theorem globalVertexTensorMap_leftInverse_eq_self_of_mem
    (A : Tensor Γ d) (hA : IsVertexInjective A) {ψ : (V → Fin d) → ℂ}
    (hψ : ψ ∈ vertexImageGroundSpace A) :
    globalVertexTensorMap A (globalVertexLeftInverse A hA ψ) = ψ := by
  have h := globalPhysicalMap_fixed_of_oneVertex_fixed (vertexImageProjection A hA) ψ
    (oneVertexPhysicalMap_vertexImageProjection_eq_self_of_mem A hA hψ)
  rw [globalPhysicalMap_vertexImageProjection] at h
  exact h

/-- Each one-site retraction fixes the product site embedding.
Source: tensoring the site inverses in CPGSV21, Section IV.C.1, lines 2017–2044. -/
theorem oneVertexPhysicalMap_comp_globalVertexTensorMap
    (A : Tensor Γ d) (hA : IsVertexInjective A) (v : V) :
    globalPhysicalMap (oneVertexPhysicalFamily v (vertexImageProjection A hA v)) ∘ₗ
      globalVertexTensorMap A = globalVertexTensorMap A := by
  classical
  have hprod : (fun w => oneVertexPhysicalFamily v (vertexImageProjection A hA v) w *
      LinearMap.toMatrix' (localTensorMap A w)) =
        fun w => LinearMap.toMatrix' (localTensorMap A w) := by
    funext w
    by_cases hw : w = v
    · subst w
      simp only [oneVertexPhysicalFamily, ite_true, vertexImageProjection]
      have hL : localLeftInverse A hA v ∘ₗ localTensorMap A v = LinearMap.id :=
        localLeftInverseAt_comp_localTensorMap A (hA v)
      rw [← LinearMap.toMatrix'_comp, LinearMap.comp_assoc, hL, LinearMap.comp_id]
    · simp only [oneVertexPhysicalFamily, hw, ite_false, Matrix.one_mul]
  apply LinearMap.ext
  intro x
  change (fullRegionPhysicalEquiv d).symm
    (regionPhysicalMap Finset.univ
      (oneVertexPhysicalFamily v (vertexImageProjection A hA v))
      ((fullRegionPhysicalEquiv d) ((fullRegionPhysicalEquiv d).symm
        (regionVertexTensorMap A Finset.univ x)))) = _
  rw [LinearEquiv.apply_symm_apply]
  change (fullRegionPhysicalEquiv d).symm
    ((regionPhysicalMap Finset.univ
      (oneVertexPhysicalFamily v (vertexImageProjection A hA v)) ∘ₗ
      regionPhysicalMap Finset.univ (fun w => LinearMap.toMatrix' (localTensorMap A w))) x) = _
  rw [regionPhysicalMap_comp, hprod]
  rfl

/-- Every vector in the product vertex image satisfies the actual singleton-image
conditions. Source: CPGSV21, Section IV.C.1, lines 2017–2044. -/
theorem globalVertexTensorMap_mem_vertexImageGroundSpace
    (A : Tensor Γ d) (hA : IsVertexInjective A)
    (x : RegionVertexVirtualConfig A Finset.univ → ℂ) :
    globalVertexTensorMap A x ∈ vertexImageGroundSpace A := by
  rw [mem_vertexImageGroundSpace_iff]
  intro v τ
  apply (vertexImageProjection_mulVec_eq_self_iff A hA v _).mp
  rw [← vertexPhysicalSlice_globalPhysicalMap_oneVertex]
  have h := LinearMap.congr_fun (oneVertexPhysicalMap_comp_globalVertexTensorMap A hA v) x
  rw [LinearMap.comp_apply] at h
  rw [h]

/-- The intersection of all spectator-lifted one-site tensor images is exactly
the image of the product site tensor map. No virtual bond condition or positivity
assumption is needed. Source: the independent site inverses in CPGSV21,
Section IV.C.1, lines 2017–2044. -/
theorem vertexImageGroundSpace_eq_range_globalVertexTensorMap
    (A : Tensor Γ d) (hA : IsVertexInjective A) :
    vertexImageGroundSpace A = (globalVertexTensorMap A).range := by
  apply le_antisymm
  · intro ψ hψ
    exact ⟨globalVertexLeftInverse A hA ψ,
      globalVertexTensorMap_leftInverse_eq_self_of_mem A hA hψ⟩
  · rintro ψ ⟨x, rfl⟩
    exact globalVertexTensorMap_mem_vertexImageGroundSpace A hA x

/-- In regional coordinates the common singleton-image space is the range of
 the original full-region vertex tensor map. -/
theorem vertexImageGroundSpace_map_fullRegionPhysicalEquiv
    (A : Tensor Γ d) (hA : IsVertexInjective A) :
    (vertexImageGroundSpace A).map (fullRegionPhysicalEquiv d).toLinearMap =
      (regionVertexTensorMap A Finset.univ).range := by
  rw [vertexImageGroundSpace_eq_range_globalVertexTensorMap A hA]
  apply le_antisymm
  · rintro y ⟨ψ, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, by simp [globalVertexTensorMap]⟩
  · rintro y ⟨x, rfl⟩
    exact ⟨globalVertexTensorMap A x, ⟨x, rfl⟩, by simp [globalVertexTensorMap]⟩

end TNLean.PEPS
