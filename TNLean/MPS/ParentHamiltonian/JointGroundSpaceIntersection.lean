/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.IntersectionProperty
import TNLean.MPS.ParentHamiltonian.Defs
import Mathlib.LinearAlgebra.DFinsupp

/-!
# Joint intersection from independent middle support spaces

Suppose each sector satisfies a one-step intersection property and that the
sector support spaces on the common middle interval are independent. The sum
of the sector spaces then satisfies the same intersection property. The proof
is geometric: after adjoining the exterior physical indices, each pair of
left and right sector spaces lies in one member of an independent family.
Uniqueness of the sector decomposition separates the two restrictions.

No normalization, cyclic decomposition, or virtual-boundary injectivity is
assumed in the family theorem. Individual intersection identities and middle
independence are explicit hypotheses. In particular, the result is an
intermediate criterion, not the unrestricted intersection theorem for a
finite family of periodic tensors.

Source: Nachtergaele, arXiv:cond-mat/9410110, Section 4, Proposition
forintersection and Lemma intersectionequivalence, equations (4.4).
-/

open scoped BigOperators

namespace Submodule

variable {𝕜 E ι : Type*} [Ring 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- Two finite sums contained sectorwise in an independent family intersect
as the sum of the corresponding intersections. This is the decomposition
argument underlying Nachtergaele, arXiv:cond-mat/9410110, Section 4,
Lemma intersectionequivalence. -/
theorem iSup_inf_iSup_eq_of_le_independent [Finite ι]
    (U V W : ι → Submodule 𝕜 E) (hW : iSupIndep W)
    (hU : ∀ i, U i ≤ W i) (hV : ∀ i, V i ≤ W i) :
    (⨆ i, U i) ⊓ (⨆ i, V i) = ⨆ i, U i ⊓ V i := by
  classical
  let := Fintype.ofFinite ι
  apply le_antisymm
  · intro x hx
    obtain ⟨u, hu, hux⟩ := (mem_iSup_iff_exists_finsupp U x).mp hx.1
    obtain ⟨v, hv, hvx⟩ := (mem_iSup_iff_exists_finsupp V x).mp hx.2
    have huv : ∀ i, u i = v i := by
      intro i
      exact (iSupIndep_iff_finsetSum_eq_imp_eq W).mp hW Finset.univ u v
        (fun j _ => ⟨hU j (hu j), hV j (hv j)⟩)
        (by simpa [Finsupp.sum_fintype] using hux.trans hvx.symm) i (Finset.mem_univ i)
    rw [← hux]
    exact Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i
      ⟨hu i, (huv i).symm ▸ hv i⟩
  · exact iSup_le fun i => le_inf
      ((inf_le_left.trans (le_iSup U i))) ((inf_le_right.trans (le_iSup V i)))

variable {F τ : Type*} [AddCommGroup F] [Module 𝕜 F]

/-- Independence is preserved when all vectors are determined by a family
of linear restrictions, and each restriction lies in the same sector.
Source: the middle-interval restriction argument of Nachtergaele,
arXiv:cond-mat/9410110, Section 4, Proposition forintersection. -/
theorem iSupIndep_iInf_comap_of_separating
    (W : ι → Submodule 𝕜 F) (hW : iSupIndep W) (f : τ → E →ₗ[𝕜] F)
    (hSep : ∀ x, (∀ t, f t x = 0) → x = 0) :
    iSupIndep (fun i => ⨅ t, (W i).comap (f t)) := by
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s v hv hsum i hi
  apply hSep
  intro t
  exact (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero W).mp hW s
    (fun j => f t (v j)) (fun j hj => (Submodule.mem_iInf _).mp (hv j hj) t)
    (by rw [← map_sum, hsum, map_zero]) i hi

private theorem iInf_comap_iSup_of_linearEquiv [Finite ι]
    (U : ι → Submodule 𝕜 F) (e : E ≃ₗ[𝕜] (τ → F)) :
    (⨅ t, (⨆ i, U i).comap ((LinearMap.proj t).comp e.toLinearMap)) =
      ⨆ i, ⨅ t, (U i).comap ((LinearMap.proj t).comp e.toLinearMap) := by
  classical
  let := Fintype.ofFinite ι
  apply le_antisymm
  · intro x hx
    have hx' : ∀ t, e x t ∈ ⨆ i, U i := (Submodule.mem_iInf _).mp hx
    choose v hv hsum using fun t =>
      (mem_iSup_iff_exists_finsupp U (e x t)).mp (hx' t)
    let y : ι → E := fun i => e.symm (fun t => v t i)
    have hy : ∀ i, y i ∈ ⨅ t, (U i).comap ((LinearMap.proj t).comp e.toLinearMap) := by
      intro i
      simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.comp_apply,
        LinearEquiv.coe_coe, LinearMap.proj_apply, y, LinearEquiv.apply_symm_apply]
      exact fun t => hv t i
    have heq : ∑ i, y i = x := by
      apply e.injective
      ext t
      simpa [map_sum, y, Finsupp.sum_fintype] using hsum t
    rw [← heq]
    exact Submodule.sum_mem _ fun i _ => mem_iSup_of_mem i (hy i)
  · refine iSup_le fun i => iInf_mono fun t => ?_
    exact Submodule.comap_mono (le_iSup U i)

end Submodule
namespace MPSTensor

private noncomputable def firstRestrictionEquiv (d n : ℕ) :
    NSiteSpace d (n + 1) ≃ₗ[ℂ] (Fin d → NSiteSpace d n) where
  toFun ψ := fun a => restrictFirst ψ a
  invFun φ := fun σ => φ (σ 0) (Fin.tail σ)
  left_inv ψ := by
    ext σ
    simp only [restrictFirst_apply, Fin.cons_self_tail]
  right_inv φ := by
    ext a σ
    simp [restrictFirst_apply]
  map_add' ψ φ := rfl
  map_smul' c ψ := rfl

private noncomputable def lastRestrictionEquiv (d n : ℕ) :
    NSiteSpace d (n + 1) ≃ₗ[ℂ] (Fin d → NSiteSpace d n) where
  toFun ψ := fun b => restrictLast ψ b
  invFun φ := fun σ => φ (σ (Fin.last n)) (Fin.init σ)
  left_inv ψ := by
    ext σ
    simp only [restrictLast_apply, Fin.snoc_init_self]
  right_inv φ := by
    ext b σ
    simp [restrictLast_apply]
  map_add' ψ φ := rfl
  map_smul' c ψ := rfl

variable {d n : ℕ} {ι : Type*}

/-- Adjoining the first and last physical indices preserves independence
of the middle support spaces. No tensor representation is needed.
Source: Nachtergaele, arXiv:cond-mat/9410110, equation (4.2) and
Lemma intersectionequivalence. -/
theorem iSupIndep_middleRestriction_comap
    (G : ι → Submodule ℂ (NSiteSpace d n)) (hG : iSupIndep G) :
    iSupIndep (fun i => ⨅ a : Fin d, ⨅ b : Fin d,
      (G i).comap ((restrictLastₗ b).comp (restrictFirstₗ a))) := by
  have h := Submodule.iSupIndep_iInf_comap_of_separating G hG
    (fun ab : Fin d × Fin d => (restrictLastₗ ab.2).comp (restrictFirstₗ ab.1))
  have hSep : ∀ ψ : NSiteSpace d (n + 2),
      (∀ ab : Fin d × Fin d, ((restrictLastₗ ab.2).comp (restrictFirstₗ ab.1)) ψ = 0) →
      ψ = 0 := by
    intro ψ hψ
    apply eq_of_forall_restrictFirst_eq
    intro a
    ext σ
    have hσ := congrFun (hψ (a, σ (Fin.last n))) (Fin.init σ)
    simpa only [LinearMap.comp_apply, restrictFirstₗ, restrictLastₗ,
      LinearMap.coe_mk, AddHom.coe_mk, Fin.snoc_init_self, Pi.zero_apply,
      restrictFirst_apply] using hσ
  simpa only [iInf_prod] using h hSep

/-- If the sector spaces restrict into independent middle spaces, the
intersection of their two enlarged sums is the sum of their individual
intersections. Source: Nachtergaele, arXiv:cond-mat/9410110, Section 4,
Proposition forintersection and Lemma intersectionequivalence. -/
theorem restriction_intersection_iSup_eq_of_middle_independent [Finite ι]
    (G : ι → Submodule ℂ (NSiteSpace d n))
    (H : ι → Submodule ℂ (NSiteSpace d (n + 1)))
    (hG : iSupIndep G)
    (hFirst : ∀ i ψ, ψ ∈ H i → ∀ a, restrictFirst ψ a ∈ G i)
    (hLast : ∀ i ψ, ψ ∈ H i → ∀ b, restrictLast ψ b ∈ G i) :
    ((⨅ b : Fin d, (⨆ i, H i).comap (restrictLastₗ b)) ⊓
      ⨅ a : Fin d, (⨆ i, H i).comap (restrictFirstₗ a)) =
      ⨆ i, (⨅ b : Fin d, (H i).comap (restrictLastₗ b)) ⊓
        ⨅ a : Fin d, (H i).comap (restrictFirstₗ a) := by
  let U := fun i => ⨅ b : Fin d, (H i).comap (restrictLastₗ b)
  let V := fun i => ⨅ a : Fin d, (H i).comap (restrictFirstₗ a)
  let W := fun i => ⨅ a : Fin d, ⨅ b : Fin d,
    (G i).comap ((restrictLastₗ b).comp (restrictFirstₗ a))
  have hU : ∀ i, U i ≤ W i := by
    intro i ψ hψ
    simp only [W, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.comp_apply]
    intro a b
    have h := hFirst i (restrictLast ψ b) ((Submodule.mem_iInf _).mp hψ b) a
    convert h using 1
    ext σ
    simp only [restrictFirst, restrictLast, restrictFirstₗ, restrictLastₗ,
      LinearMap.coe_mk, AddHom.coe_mk, Fin.cons_snoc_eq_snoc_cons]
  have hV : ∀ i, V i ≤ W i := by
    intro i ψ hψ
    simp only [W, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.comp_apply]
    intro a b
    exact hLast i (restrictFirst ψ a) ((Submodule.mem_iInf _).mp hψ a) b
  have hULift : (⨅ b : Fin d, (⨆ i, H i).comap (restrictLastₗ b)) = ⨆ i, U i := by
    exact Submodule.iInf_comap_iSup_of_linearEquiv H (lastRestrictionEquiv d (n + 1))
  have hVLift : (⨅ a : Fin d, (⨆ i, H i).comap (restrictFirstₗ a)) = ⨆ i, V i := by
    exact Submodule.iInf_comap_iSup_of_linearEquiv H (firstRestrictionEquiv d (n + 1))
  rw [hULift, hVLift]
  exact Submodule.iSup_inf_iSup_eq_of_le_independent U V W
    (iSupIndep_middleRestriction_comap G hG) hU hV

/-- A finite tensor family inherits the one-step intersection property
from its individual members whenever their middle ground spaces are
independent. No cyclic-boundary or normalization hypotheses are added.
Source: Nachtergaele, arXiv:cond-mat/9410110, equation (4.4), Proposition
forintersection, and Lemma intersectionequivalence. -/
theorem iSup_groundSpace_eq_restriction_intersection_of_middle_independent
    [Finite ι] {dim : ι → ℕ} (A : ∀ i, MPSTensor d (dim i))
    (hIndep : iSupIndep (fun i => groundSpace (A i) n))
    (hInter : ∀ i,
      ((⨅ b : Fin d, (groundSpace (A i) (n + 1)).comap (restrictLastₗ b)) ⊓
        ⨅ a : Fin d, (groundSpace (A i) (n + 1)).comap (restrictFirstₗ a)) =
        groundSpace (A i) (n + 2)) :
    ((⨅ b : Fin d, (⨆ i, groundSpace (A i) (n + 1)).comap (restrictLastₗ b)) ⊓
      ⨅ a : Fin d, (⨆ i, groundSpace (A i) (n + 1)).comap (restrictFirstₗ a)) =
      ⨆ i, groundSpace (A i) (n + 2) := by
  rw [restriction_intersection_iSup_eq_of_middle_independent
    (fun i => groundSpace (A i) n) (fun i => groundSpace (A i) (n + 1)) hIndep
    (fun i ψ hψ => groundSpace_inRightGround (A i) n hψ)
    (fun i ψ hψ => groundSpace_inLeftGround (A i) n hψ)]
  simp only [hInter]

/-- Independence of the open-boundary support spaces is unchanged by
passing to their Euclidean realization. This coordinate observation relates
the geometric spaces in Nachtergaele, arXiv:cond-mat/9410110, Section 4,
to their orthogonal projections. -/
theorem groundSpace_iSupIndep_iff_groundSpaceES_iSupIndep
    {dim : ι → ℕ} (A : ∀ i, MPSTensor d (dim i)) (N : ℕ) :
    iSupIndep (fun i => groundSpace (A i) N) ↔
      iSupIndep (fun i => groundSpaceES (A i) N) := by
  exact (iSupIndep_map_orderIso_iff
    (Submodule.orderIsoMapComap (WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm)).symm

end MPSTensor

