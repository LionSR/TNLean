/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.Cluster
import TNLean.MPS.Symmetry.SPTFixedPoint

/-!
# Cluster state as the `Z₂ × Z₂` SPT fixed point

**Source.** Cirac, Pérez-García, Schuch, Verstraete (arXiv:2011.12127), §III.A,
`Papers/2011.12127/TN-Review-main.tex` line 1157: "In the particular case of e.g. an
on-site `Z₂ × Z₂` symmetry, the simplest group exhibiting non-trivial 2-cocycles, this
construction precisely yields the 1D cluster state (Appendix A) when blocking pairs of
adjacent sites."
Review: arXiv:2011.12127, Appendix A, "The cluster state".

**Formalized here.** For the non-trivial class of `Z₂ × Z₂`, represented by the
cluster projective representation `clusterProjRep` (`σ_z`, `σ_x`), the fixed-point
tensor `sptFixedPointTensor 2` and the length-`2` blocked cluster tensor differ by a
unitary on the four-dimensional physical space and the trivial gauge.  Every virtual
representation of the fixed-point tensor has a non-trivial class.

The fixed-point tensor is the one of `TNLean.MPS.Symmetry.SPTFixedPoint`, not the
printed tensor; see the local fix recorded there and
`docs/paper-gaps/rmp_spt_fixed_point_tensor.tex`.

## Main definitions

* `MPSTensor.clusterSPTUnitary`

## Main results

* `MPSTensor.clusterSPTUnitary_mul_conjTranspose`
* `MPSTensor.clusterBlocked_eq_sum_sptFixedPointTensor`
* `MPSTensor.isNontrivialClass_of_clusterSPTFixedPoint`

## References

- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- Cirac, Pérez-García,
  Schuch, Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*
-/

open scoped Matrix BigOperators

noncomputable section

namespace MPSTensor

open TNLean.Algebra

/-- The physical unitary relating the blocked cluster tensor to the fixed-point
tensor: its row `i` lists the entries of `√2 · A_cluster^i`. -/
def clusterSPTUnitary : Matrix (Fin 4) (Fin (2 * 2)) ℂ := fun i j =>
  (Real.sqrt 2 : ℂ) * clusterBlocked i (sptPair j).1 (sptPair j).2

/-- **The blocked cluster tensor is the fixed-point tensor up to a physical
unitary.** Source: arXiv:2011.12127, §III.A (`Papers/2011.12127/TN-Review-main.tex`
line 1157). -/
theorem clusterBlocked_eq_sum_sptFixedPointTensor (i : Fin 4) :
    clusterBlocked i = ∑ j : Fin (2 * 2), clusterSPTUnitary i j • sptFixedPointTensor 2 j := by
  classical
  have h2 : (Real.sqrt 2 : ℂ) * ((Real.sqrt ((2 : ℕ) : ℝ) : ℂ))⁻¹ = 1 := by
    rw [Nat.cast_ofNat, mul_inv_cancel₀]
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  simp only [clusterSPTUnitary, sptFixedPointTensor, smul_smul, mul_assoc]
  conv_lhs => rw [Matrix.matrix_eq_sum_single (clusterBlocked i)]
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [sptPair, Equiv.symm_apply_apply, sptScale]
  rw [mul_comm (clusterBlocked i a b), ← mul_assoc, h2, one_mul, Matrix.smul_single,
    smul_eq_mul, mul_one]

/-- **The physical relation is unitary.** -/
theorem clusterSPTUnitary_mul_conjTranspose :
    clusterSPTUnitary * clusterSPTUnitaryᴴ = 1 := by
  classical
  have hs : (Real.sqrt 2 : ℂ) * star (Real.sqrt 2 : ℂ) = 2 := by
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num)]; norm_num
  ext i k
  have hik : (clusterSPTUnitary * clusterSPTUnitaryᴴ) i k =
      2 * ∑ a : Fin 2, ∑ b : Fin 2, clusterBlocked i a b * star (clusterBlocked k a b) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, clusterSPTUnitary, star_mul']
    rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [sptPair, Equiv.symm_apply_apply]
    rw [← hs]; ring
  rw [hik]
  fin_cases i <;> fin_cases k <;>
    simp [clusterBlocked_zero, clusterBlocked_one, clusterBlocked_two, clusterBlocked_three,
      Fin.sum_univ_two] <;> norm_num

/-- **The cluster fixed point is a non-trivial SPT phase.** Every virtual projective
representation of the fixed-point tensor built from `clusterProjRep` has a
non-trivial class. -/
theorem isNontrivialClass_of_clusterSPTFixedPoint
    {ω' : ScalarCocycle (Multiplicative (ZMod 2 × ZMod 2))}
    (ρ' : ProjectiveRepresentation (D := 2) ω')
    (hρ' : ∀ g i,
      twistedTensor (sptFixedPointTensor 2) (sptFixedPointAction clusterProjRep 1) g i =
      (ρ'.X (g⁻¹) : Matrix (Fin 2) (Fin 2) ℂ) * sptFixedPointTensor 2 i *
        (((ρ'.X (g⁻¹))⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) :
    ScalarCocycle.IsNontrivialClass ω' := by
  intro h
  exact cluster_isNontrivialSPT
    (((cohomologousTo_of_sptFixedPointTensor clusterProjRep ρ' hρ').symm).trans h)

end MPSTensor
