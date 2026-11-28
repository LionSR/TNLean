/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.ParentInteraction.CyclicWindowPermutation
import TNLean.MPS.ParentHamiltonian.ParentInteraction.Transport
import QICLean.Algebra.Combinatorics.TupleEquiv
import TNLean.MPS.Examples.PVBS.PVBSGroundSpace
import TNLean.MPS.ParentHamiltonian.ParentInteraction.CoefficientPairing

/-!
# Periodic PVBS Hamiltonian and particle number

Periodic summation cancels the asymmetric boundary fields. The resulting
Hamiltonian is a nonnegative multiple of the critical PVBS parent Hamiltonian
plus `(μ - 1)² / (1 + μ²)` times particle number. This identity retains the
two oriented windows when the ring has exactly two sites.

It also contains the following results.

* `MPSTensor.parentInteraction_pvbs_two_apply`: explicit normalization of the PVBS parent
  interaction.

## References

Bachmann–Nachtergaele, arXiv:1112.4097, Section II, equations (4)–(8),
restricted here to one species with zero phase.

The formulas are stated for the terms and the Hamiltonian of the parent interaction on the
ring (`parentRingInteraction`), acting through `Matrix.toEuclideanLin`.
-/

open scoped Matrix BigOperators InnerProductSpace

namespace MPSTensor

section PVBSLocalInteraction

/-!
## Explicit normalization of the PVBS parent interaction

For real hopping μ, the forbidden two-site vectors are `|11⟩` and
`|01⟩ - μ |10⟩`. The actual parent interaction is the sum of their
orthogonal projections, with the second divided by `1 + μ²`.

### References

 Bachmann–Nachtergaele, arXiv:1112.4097, Section II, equations (4)–(7),
with one species, zero phase, and left-to-right matrix products.
-/

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
  let G := ((groundSpace (pvbsTensor (μ : ℂ)) 2).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)
  have hwperp : e.symm w ∈ Gᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    have hu' : e u ∈ groundSpace (pvbsTensor (μ : ℂ)) 2 :=
      (mem_map_groundSpace_iff _ _ u).mp hu
    obtain ⟨a, b, hab⟩ := (mem_groundSpace_pvbsTensor_iff (μ : ℂ) 2 (e u)).mp hu'
    rw [← e.symm_apply_apply u, inner_withLpLinearEquiv_symm, hab]
    simp only [sum_cfg_two, Fin.sum_univ_two]
    simp [w, pvbsVacuum, pvbsEdge, Pi.single_apply, funext_iff, Fin.forall_fin_succ,
      Fin.tail, map_mul]
    ring
  have hwground : e.symm v - e.symm w ∈ G := by
    rw [mem_map_groundSpace_iff]
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
  obtain ⟨a, b, rfl⟩ : ∃ a b : Fin 2, σ = ![a, b] := ⟨σ 0, σ 1, Matrix.eq_vecCons_fin_two σ⟩
  fin_cases a <;> fin_cases b <;> simp [w, z, hswap] <;> field_simp <;> ring

end PVBSLocalInteraction

section PVBSHamiltonian

/-- The actual translated PVBS interaction has the occupation/hopping formula
at every cyclic bond, including either orientation of a two-site ring. -/
theorem toEuclideanLin_parentRingInteraction_term_pvbs_two_apply (μ : ℝ) {N : ℕ}
    (hN : 2 ≤ N) (i : Fin N) (v : EuclideanSpace ℂ (Cfg 2 N)) (σ : Cfg 2 N) :
    haveI : NeZero N := ⟨by omega⟩;
    Matrix.toEuclideanLin ((parentRingInteraction (pvbsTensor (μ : ℂ)) 2 N).term i) v σ =
      (((μ : ℂ) ^ 2 * (σ i).val + (σ (cyclicForwardSite i 1)).val) * v σ -
        (μ : ℂ) * (if σ i = σ (cyclicForwardSite i 1) then 0
          else v (σ ∘ Equiv.swap i (cyclicForwardSite i 1)))) / (1 + (μ : ℂ) ^ 2) := by
  have : NeZero N := ⟨by omega⟩
  rw [toEuclideanLin_parentRingInteraction_term_apply _ hN,
    toEuclideanLin_toMatrix'_parentInteraction]
  change parentInteraction (pvbsTensor (μ : ℂ)) 2
    (fun τ => v (cyclicCfg (Fin.pos i) 2 i τ σ)) (extractWindow 2 i σ) = _
  rw [parentInteraction_pvbs_two_apply,
    cyclicCfg_extractWindow (Fin.pos i) hN,
    cyclicCfg_extractWindow_comp_swap_of_le (Fin.pos i) hN]
  simp [extractWindow, cyclicForwardSite, Nat.mod_eq_of_lt i.isLt, mul_ite]
  split_ifs <;> simp_all

/-- Relative to the critical interaction, the local change is a diagonal
occupation field with different weights at the two ends of the bond. -/
theorem toEuclideanLin_parentRingInteraction_term_pvbs_decomposition (μ : ℝ) {N : ℕ}
    (hN : 2 ≤ N) (i : Fin N) (v : EuclideanSpace ℂ (Cfg 2 N)) (σ : Cfg 2 N) :
    haveI : NeZero N := ⟨by omega⟩;
    Matrix.toEuclideanLin ((parentRingInteraction (pvbsTensor (μ : ℂ)) 2 N).term i) v σ =
      ((2 * μ / (1 + μ ^ 2) : ℝ) : ℂ) *
          Matrix.toEuclideanLin ((parentRingInteraction (pvbsTensor 1) 2 N).term i) v σ +
        ( (((μ ^ 2 - μ) / (1 + μ ^ 2) : ℝ) : ℂ) * (σ i).val +
          (((1 - μ) / (1 + μ ^ 2) : ℝ) : ℂ) * (σ (cyclicForwardSite i 1)).val ) *
            v σ := by
  have : NeZero N := ⟨by omega⟩
  have hdreal : 0 < 1 + μ ^ 2 := by positivity
  have hd : (1 + (μ : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hdreal.ne'
  rw [toEuclideanLin_parentRingInteraction_term_pvbs_two_apply μ hN]
  have h := toEuclideanLin_parentRingInteraction_term_pvbs_two_apply 1 hN i v σ
  norm_num only [Complex.ofReal_one, one_pow, one_mul] at h
  rw [h]
  push_cast
  field_simp
  ring

/-- On a periodic ring, the PVBS Hamiltonian is the sum of a positive multiple
of the critical parent and the squared hopping imbalance times particle number. -/
theorem toEuclideanLin_hamiltonian_parentRingInteraction_pvbs_decomposition (μ : ℝ) {N : ℕ}
    (hN : 2 ≤ N) (v : EuclideanSpace ℂ (Cfg 2 N)) (σ : Cfg 2 N) :
    haveI : NeZero N := ⟨by omega⟩;
    Matrix.toEuclideanLin (parentRingInteraction (pvbsTensor (μ : ℂ)) 2 N).hamiltonian v σ =
      ((2 * μ / (1 + μ ^ 2) : ℝ) : ℂ) *
        Matrix.toEuclideanLin (parentRingInteraction (pvbsTensor 1) 2 N).hamiltonian v σ +
      ((((μ - 1) ^ 2 / (1 + μ ^ 2) : ℝ) : ℂ) *
        (∑ i : Fin N, ((σ i).val : ℂ))) * v σ := by
  have : NeZero N := ⟨by omega⟩
  let : NeZero N := ⟨by omega⟩
  have hshift : ∑ i : Fin N, ((σ (cyclicForwardSite i 1)).val : ℂ) =
      ∑ i : Fin N, ((σ i).val : ℂ) := by
    simp_rw [← cyclicSuccessorEquiv_apply]
    exact Equiv.sum_comp (cyclicSuccessorEquiv N) (fun i => ((σ i).val : ℂ))
  rw [ManyBody.Interaction.hamiltonian, ManyBody.Interaction.hamiltonian, map_sum, map_sum]
  simp only [LinearMap.sum_apply, WithLp.ofLp_sum, Finset.sum_apply,
    toEuclideanLin_parentRingInteraction_term_pvbs_decomposition μ hN, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul, hshift]
  push_cast
  ring

end PVBSHamiltonian

end MPSTensor
