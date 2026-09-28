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
unitary on the four-dimensional physical space and the trivial gauge, and this unitary
intertwines the cluster `Z₂ × Z₂` action with the fixed-point action.  Every virtual
representation of the fixed-point tensor has a non-trivial class.

**Local fix (fixed-point tensor):** the source's claim concerns the fixed-point tensor it
prints, `A^{ab}_{xy} = e^{i(ω(a,x) + φ(b))} δ_{y,ax}`, whose letters commute with the printed
gauges, so it is not normal and cannot equal the injective blocked cluster tensor.  The
comparison here uses the dimer fixed point `D^{-1/2} |a⟩⟨b|` of
`TNLean.MPS.Symmetry.SPTFixedPoint`, which the printed claims describe; documented in
`docs/paper-gaps/rmp_spt_fixed_point_tensor.tex`.

## Main definitions

* `MPSTensor.clusterSPTUnitary`

## Main results

* `MPSTensor.clusterSPTUnitary_mul_conjTranspose`
* `MPSTensor.clusterBlocked_eq_sum_sptFixedPointTensor`
* `MPSTensor.clusterZ2Z2Action_mul_clusterSPTUnitary`
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

/-- Source: arXiv:2011.12127, §III.A (`Papers/2011.12127/TN-Review-main.tex` line 1157).
The physical unitary relating the blocked cluster tensor to the fixed-point tensor: its row
`i` lists the entries of `√2 · A_cluster^i`. -/
def clusterSPTUnitary : Matrix (Fin 4) (Fin (2 * 2)) ℂ := fun i j =>
  (Real.sqrt 2 : ℂ) * clusterBlocked i (sptPair j).1 (sptPair j).2

/-- **The blocked cluster tensor is the fixed-point tensor up to a physical
unitary.** Source: arXiv:2011.12127, §III.A (`Papers/2011.12127/TN-Review-main.tex`
line 1157). -/
theorem clusterBlocked_eq_sum_sptFixedPointTensor (i : Fin 4) :
    clusterBlocked i = ∑ j : Fin (2 * 2), clusterSPTUnitary i j • sptFixedPointTensor 2 j := by
  classical
  have h2 : (Real.sqrt 2 : ℂ) * ((Real.sqrt ((2 : ℕ) : ℝ) : ℂ))⁻¹ = 1 := by
    rw [Nat.cast_ofNat]; exact Complex.sqrtTwo_mul_invSqrtTwo
  simp only [clusterSPTUnitary, sptFixedPointTensor, smul_smul, mul_assoc]
  conv_lhs => rw [Matrix.matrix_eq_sum_single (clusterBlocked i)]
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [sptPair, Equiv.symm_apply_apply, sptScale]
  rw [mul_comm (clusterBlocked i a b), ← mul_assoc, h2, one_mul, Matrix.smul_single,
    smul_eq_mul, mul_one]

/-- **The physical relation is unitary.** Source: arXiv:2011.12127, §III.A
(`Papers/2011.12127/TN-Review-main.tex` line 1157). -/
theorem clusterSPTUnitary_mul_conjTranspose :
    clusterSPTUnitary * clusterSPTUnitaryᴴ = 1 := by
  classical
  have hs : (Real.sqrt 2 : ℂ) * star (Real.sqrt 2 : ℂ) = 2 := by
    rw [Complex.star_def, Complex.conj_ofReal, ← sq, Complex.ofReal_sqrt_sq 2 (by norm_num)]
    norm_num
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

/-- **The unitary intertwines the two symmetries.** Source: arXiv:2011.12127, §III.A
(`Papers/2011.12127/TN-Review-main.tex` line 1157). `clusterSPTUnitary` carries the
fixed-point action of `clusterProjRep` to the `Z₂ × Z₂` action of the blocked cluster
state: `U_cluster(g) V = V U_fp(g)`.  Both tensors realize the symmetry `g` with the
same virtual gauge `σ`-matrix, and the fixed-point letters are linearly independent. -/
theorem clusterZ2Z2Action_mul_clusterSPTUnitary (g : Multiplicative (ZMod 2 × ZMod 2)) :
    clusterZ2Z2Action g * clusterSPTUnitary =
      clusterSPTUnitary * sptFixedPointAction clusterProjRep 1 g := by
  classical
  have hg : g⁻¹ = g := by revert g; decide
  have hA (i : Fin 4) : twistedTensor clusterBlocked clusterZ2Z2Action g i =
      (clusterProjRep.X g : Matrix (Fin 2) (Fin 2) ℂ) * clusterBlocked i *
        (((clusterProjRep.X g)⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [← clusterBlocked_twist_intertwine g i, Matrix.mul_assoc, Units.mul_inv,
      Matrix.mul_one]
  have expand {ι : Type} [Fintype ι] (P : Matrix (Fin 4) ι ℂ) (Q : Matrix ι (Fin (2 * 2)) ℂ)
      (i : Fin 4) : ∑ k, (P * Q) i k • sptFixedPointTensor 2 k =
        ∑ l, P i l • ∑ k, Q l k • sptFixedPointTensor 2 k := by
    simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
    exact Finset.sum_comm
  ext i k
  refine congrFun (eq_of_sum_smul_sptFixedPointTensor_eq (D := 2) ?_) k
  calc ∑ k, (clusterZ2Z2Action g * clusterSPTUnitary) i k • sptFixedPointTensor 2 k
      = twistedTensor clusterBlocked clusterZ2Z2Action g i := by
        rw [expand]
        simp only [← clusterBlocked_eq_sum_sptFixedPointTensor]
        rfl
    _ = (clusterProjRep.X g : Matrix (Fin 2) (Fin 2) ℂ) *
          (∑ l, clusterSPTUnitary i l • sptFixedPointTensor 2 l) *
          (((clusterProjRep.X g)⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) := by
        rw [hA, ← clusterBlocked_eq_sum_sptFixedPointTensor]
    _ = ∑ l, clusterSPTUnitary i l •
          twistedTensor (sptFixedPointTensor 2) (sptFixedPointAction clusterProjRep 1) g l := by
        simp only [twistedTensor_sptFixedPointTensor, sptGauge, MonoidHom.one_apply,
          one_smul, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
        erw [hg]
    _ = _ := by rw [expand]; rfl

/-- **The cluster fixed point is a non-trivial SPT phase.** Every virtual projective
representation of the fixed-point tensor built from `clusterProjRep` has a
non-trivial class.  Source: arXiv:2011.12127, §III.A
(`Papers/2011.12127/TN-Review-main.tex` line 1157), for the on-site `Z₂ × Z₂` symmetry,
with the local fix of the module docstring. -/
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
