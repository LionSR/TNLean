/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinVecEta
import TNLean.MPS.Examples.PVBSGroundSpace
import TNLean.MPS.ParentHamiltonian.CoefficientPairing

/-!
# Explicit normalization of the PVBS parent interaction

For real hopping μ, the forbidden two-site vectors are `|11⟩` and
`|01⟩ - μ |10⟩`. The actual parent interaction is the sum of their
orthogonal projections, with the second divided by `1 + μ²`.

Source: Bachmann–Nachtergaele, arXiv:1112.4097, Section II, equations (4)–(7),
with one species, zero phase, and left-to-right matrix products.
-/

open scoped Matrix BigOperators InnerProductSpace

namespace MPSTensor

private theorem sum_cfg_two (f : Cfg 2 2 → ℂ) : ∑ σ, f σ = ∑ a, ∑ b, f ![a, b] := by
  rw [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (piFinTwoEquiv fun _ => Fin 2) _ _ fun σ => ?_
  simp only [piFinTwoEquiv_apply]
  congr 1
  exact Matrix.eq_vecCons_fin_two σ

/-- The canonical parent projector has the normalized PVBS occupation/hopping formula.
No independently defined Hamiltonian is used. -/
theorem parentInteraction_pvbs_two_apply (μ : ℝ) (v : NSiteSpace 2 2) (σ : Cfg 2 2) :
    parentInteraction (pvbsTensor (μ : ℂ)) 2 v σ =
      (((μ : ℂ) ^ 2 * (σ 0).val + (σ 1).val) * v σ -
        (μ : ℂ) * (if σ 0 = σ 1 then 0 else v (σ ∘ Equiv.swap 0 1))) /
          (1 + (μ : ℂ) ^ 2) := by
  classical
  have hdreal : 0 < 1 + μ ^ 2 := by positivity
  have hd : (1 + (μ : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hdreal.ne'
  let z := (v ![0, 1] - (μ : ℂ) * v ![1, 0]) / (1 + (μ : ℂ) ^ 2)
  let w : NSiteSpace 2 2 := fun τ =>
    if τ 0 = 0 then (if τ 1 = 0 then 0 else z)
    else if τ 1 = 0 then -(μ : ℂ) * z else v ![1, 1]
  let e := WithLp.linearEquiv 2 ℂ (NSiteSpace 2 2)
  let G := groundSpaceES (pvbsTensor (μ : ℂ)) 2
  have hwperp : e.symm w ∈ Gᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    have hu' : e u ∈ groundSpace (pvbsTensor (μ : ℂ)) 2 :=
      (mem_groundSpaceES_iff _ _ u).mp hu
    obtain ⟨a, b, hab⟩ := (mem_groundSpace_pvbsTensor_iff (μ : ℂ) 2 (e u)).mp hu'
    rw [← e.symm_apply_apply u, inner_withLpLinearEquiv_symm, hab]
    simp only [sum_cfg_two, Fin.sum_univ_two]
    simp [w, pvbsVacuum, pvbsEdge, Pi.single_apply, funext_iff, Fin.forall_fin_succ,
      Fin.tail, map_mul]
    ring
  have hwground : e.symm v - e.symm w ∈ G := by
    rw [mem_groundSpaceES_iff]
    change v - w ∈ groundSpace (pvbsTensor (μ : ℂ)) 2
    apply (mem_groundSpace_pvbs_two_iff (μ : ℂ) _).mpr
    constructor
    · simp [w]
    · simp [w, z]
      field_simp
      ring
  have hw : w = parentInteraction (pvbsTensor (μ : ℂ)) 2 v := by
    change w = e (Gᗮ.starProjection (e.symm v))
    rw [Submodule.eq_starProjection_of_mem_orthogonal hwperp
      (Submodule.le_orthogonal_orthogonal G hwground), e.apply_symm_apply]
  rw [← hw]
  have hswap (a b : Fin 2) : (![a, b] : Cfg 2 2) ∘ Equiv.swap 0 1 = ![b, a] := by
    ext k
    fin_cases k <;> simp
  obtain ⟨a, b, rfl⟩ : ∃ a b : Fin 2, σ = ![a, b] := by
    exact ⟨σ 0, σ 1, Matrix.eq_vecCons_fin_two σ⟩
  fin_cases a <;> fin_cases b <;> simp [w, z, hswap] <;> field_simp <;> ring

end MPSTensor
