/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Analysis.MarginalSupport
import TNLean.Analysis.CfcKronecker
import TNLean.Channel.MaximalOverlap

/-!
# Support projectors of bipartite marginals

This file begins the tensor-product formulation of the decorrelation-to-parent
implication in the parent-commuting-Hamiltonian equivalence.  Its first step is
the absorption property of the projector onto the support of a marginal.

## Main results

* `Matrix.PosSemidef.leftKroneckerEmbed_supportProj_mul_self`: the lifted support
  projector of the right partial trace fixes the original positive
  semidefinite operator on the left.
* `Matrix.PosSemidef.mul_leftKroneckerEmbed_supportProj_self`: the corresponding
  right absorption identity.

## References

* arXiv:1606.00608, Appendix D.2, lines 2225--2235: the bipartite state
  identity and the support-projector absorption identity.
-/

open scoped Matrix ComplexOrder Kronecker
open Matrix Finset

namespace Matrix

section Bipartite

variable {L R : Type*} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

/-- Partial trace and tensor-product lift are adjoint for the trace pairing:
\(\operatorname{tr}((M\otimes\mathbf 1)\rho)
=\operatorname{tr}(M\operatorname{tr}_R\rho)\). -/
theorem trace_leftKroneckerEmbed_mul
    (M : Matrix L L ℂ) (ρ : Matrix (L × R) (L × R) ℂ) :
    (leftKroneckerEmbed (n := R) M * ρ).trace = (M * partialTraceRight ρ).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fintype.sum_prod_type,
    leftKroneckerEmbed_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    partialTraceRight_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_eq_single r]
  · simp
  · intro s _ hrs
    simp [Ne.symm hrs]
  · simp

/-- The lifted support projector of the right partial trace fixes a positive
semidefinite bipartite operator on the left.

This is the operator form of the left support-projector absorption identity in
arXiv:1606.00608, Appendix D.2, lines 2225--2235.  The source takes \(\rho\) to
be the orthogonal projector \(P_{AXB}\); the same argument holds for every
positive semidefinite \(\rho\).  Taking the left factor to be \(A\otimes X\)
and the right factor to be \(B\) gives
\((P_{AX}\otimes\mathbf 1_B)P_{AXB}=P_{AXB}\). -/
theorem PosSemidef.leftKroneckerEmbed_supportProj_mul_self
    {ρ : Matrix (L × R) (L × R) ℂ} (hρ : ρ.PosSemidef) :
    leftKroneckerEmbed (n := R)
        (Matrix.PosSemidef.partialTraceRight hρ).isHermitian.supportProj * ρ = ρ := by
  classical
  set σ := Matrix.partialTraceRight ρ with hσ
  have hσpos : σ.PosSemidef := Matrix.PosSemidef.partialTraceRight hρ
  set P := hσpos.isHermitian.supportProj with hP
  set Q : Matrix L L ℂ := 1 - P with hQ
  have hQherm : Q.IsHermitian := by
    rw [hQ]
    exact hσpos.isHermitian.one_sub_supportProj_isHermitian
  have hQidem : Q * Q = Q := by
    rw [hQ, hP]
    exact hσpos.isHermitian.one_sub_supportProj_idem
  have hQσ : Q * σ = 0 := by
    rw [hQ, hP]
    exact hσpos.isHermitian.one_sub_supportProj_mul_self
  have hliftQherm : (leftKroneckerEmbed (n := R) Q).IsHermitian := by
    change (leftKroneckerEmbed (n := R) Q)ᴴ = leftKroneckerEmbed (n := R) Q
    rw [← star_eq_conjTranspose, ← map_star, star_eq_conjTranspose, hQherm.eq]
  have hliftQidem :
      leftKroneckerEmbed (n := R) Q * leftKroneckerEmbed (n := R) Q =
        leftKroneckerEmbed (n := R) Q := by
    rw [← map_mul, hQidem]
  have hliftQρ : leftKroneckerEmbed (n := R) Q * ρ = 0 := by
    refine hρ.proj_mul_eq_zero_of_trace_eq_zero hliftQherm hliftQidem ?_
    rw [trace_leftKroneckerEmbed_mul, ← hσ, hQσ, Matrix.trace_zero]
  have hsplit :
      (1 : Matrix (L × R) (L × R) ℂ) - leftKroneckerEmbed (n := R) Q =
        leftKroneckerEmbed (n := R) P := by
    rw [← map_one (leftKroneckerEmbed (m := L) (n := R)), ← map_sub, hQ]
    abel
  rw [← hsplit, Matrix.sub_mul, Matrix.one_mul, hliftQρ, sub_zero]

/-- The lifted support projector of the right partial trace also fixes a
positive semidefinite bipartite operator on the right.

Together with `PosSemidef.leftKroneckerEmbed_supportProj_mul_self`, this proves
both support-projector absorption identities of arXiv:1606.00608,
Appendix D.2, lines 2228--2235, for the \(AX|B\) bipartition. -/
theorem PosSemidef.mul_leftKroneckerEmbed_supportProj_self
    {ρ : Matrix (L × R) (L × R) ℂ} (hρ : ρ.PosSemidef) :
    ρ * leftKroneckerEmbed (n := R)
        (Matrix.PosSemidef.partialTraceRight hρ).isHermitian.supportProj = ρ := by
  have hleft := hρ.leftKroneckerEmbed_supportProj_mul_self
  have hliftHerm :
      (leftKroneckerEmbed (n := R)
        (Matrix.PosSemidef.partialTraceRight hρ).isHermitian.supportProj).IsHermitian := by
    change (leftKroneckerEmbed (n := R)
      (Matrix.PosSemidef.partialTraceRight hρ).isHermitian.supportProj)ᴴ = _
    rw [← star_eq_conjTranspose, ← map_star, star_eq_conjTranspose,
      (Matrix.PosSemidef.partialTraceRight hρ).isHermitian.supportProj_isHermitian.eq]
  have h := congrArg Matrix.conjTranspose hleft
  rwa [Matrix.conjTranspose_mul, hρ.isHermitian.eq, hliftHerm.eq] at h

end Bipartite

end Matrix
