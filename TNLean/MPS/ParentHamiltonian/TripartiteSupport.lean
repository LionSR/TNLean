/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Analysis.MarginalSupport
import TNLean.Channel.MaximalOverlap

/-!
# Support projectors of bipartite marginals

This file begins the tensor-product formulation of the decorrelation-to-parent
implication in the parent-commuting-Hamiltonian equivalence.  Its first step is
the absorption property of the projector onto the support of a marginal.

## Main definitions

* `Matrix.liftLeftFactor`: the lift \(M \otimes \mathbf 1\) of an operator on
  the left tensor factor.

## Main results

* `Matrix.PosSemidef.liftLeftFactor_supportProj_mul_self`: the lifted support
  projector of the right partial trace fixes the original positive
  semidefinite operator on the left.
* `Matrix.PosSemidef.mul_liftLeftFactor_supportProj_self`: the corresponding
  right absorption identity.

## References

* arXiv:1606.00608, Appendix D.2, lines 2225--2235, especially equations
  `varphiPAXB` and `Propproj`.
-/

open scoped Matrix ComplexOrder Kronecker
open Matrix Finset

namespace Matrix

section Bipartite

variable {L R : Type*} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

/-- The tensor-product lift \(M \otimes \mathbf 1_R\) of an operator on the
left factor. -/
noncomputable def liftLeftFactor (M : Matrix L L ℂ) : Matrix (L × R) (L × R) ℂ :=
  M ⊗ₖ (1 : Matrix R R ℂ)

omit [DecidableEq L] in
/-- Partial trace and tensor-product lift are adjoint for the trace pairing:
\(\operatorname{tr}((M\otimes\mathbf 1)\rho)
=\operatorname{tr}(M\operatorname{tr}_R\rho)\). -/
theorem trace_liftLeftFactor_mul (M : Matrix L L ℂ) (ρ : Matrix (L × R) (L × R) ℂ) :
    (liftLeftFactor (R := R) M * ρ).trace = (M * partialTraceRight ρ).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fintype.sum_prod_type,
    liftLeftFactor, Matrix.kroneckerMap_apply, Matrix.one_apply, partialTraceRight_apply,
    Finset.mul_sum]
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

This is the operator form of the first equality in equation `Propproj` of
arXiv:1606.00608, Appendix D.2, lines 2225--2235.  Taking the left factor to be
\(A\otimes X\) and the right factor to be \(B\) gives
\((P_{AX}\otimes\mathbf 1_B)P_{AXB}=P_{AXB}\). -/
theorem PosSemidef.liftLeftFactor_supportProj_mul_self
    {ρ : Matrix (L × R) (L × R) ℂ} (hρ : ρ.PosSemidef) :
    liftLeftFactor (R := R) (Matrix.PosSemidef.partialTraceRight hρ).isHermitian.supportProj * ρ
      = ρ := by
  classical
  set σ := Matrix.partialTraceRight ρ with hσ
  have hσpos : σ.PosSemidef := Matrix.PosSemidef.partialTraceRight hρ
  set P := hσpos.isHermitian.supportProj with hP
  set Q : Matrix L L ℂ := 1 - P with hQ
  have hQherm : Q.IsHermitian := by
    rw [hQ]
    exact Matrix.isHermitian_one.sub hσpos.isHermitian.supportProj_isHermitian
  have hPidem : P * P = P := by
    rw [hP]
    exact hσpos.isHermitian.supportProj_idem
  have hQidem : Q * Q = Q := by
    calc
      Q * Q = 1 - P - P + P * P := by rw [hQ]; noncomm_ring
      _ = Q := by rw [hPidem, hQ]; abel
  have hPσ : P * σ = σ := by
    rw [hP]
    exact hσpos.isHermitian.supportProj_mul_self
  have hQσ : Q * σ = 0 := by
    rw [hQ, Matrix.sub_mul, Matrix.one_mul, hPσ, sub_self]
  have hliftQherm : (liftLeftFactor (R := R) Q).IsHermitian := by
    rw [Matrix.IsHermitian, liftLeftFactor, Matrix.conjTranspose_kronecker,
      hQherm.eq, Matrix.conjTranspose_one]
  have hliftQidem :
      liftLeftFactor (R := R) Q * liftLeftFactor (R := R) Q = liftLeftFactor (R := R) Q := by
    rw [liftLeftFactor, ← Matrix.mul_kronecker_mul, hQidem, Matrix.one_mul]
  have hliftQρ : liftLeftFactor (R := R) Q * ρ = 0 := by
    refine hρ.proj_mul_eq_zero_of_trace_eq_zero hliftQherm hliftQidem ?_
    rw [trace_liftLeftFactor_mul, ← hσ, hQσ, Matrix.trace_zero]
  have hsplit :
      (1 : Matrix (L × R) (L × R) ℂ) - liftLeftFactor (R := R) Q
        = liftLeftFactor (R := R) P := by
    ext i j
    by_cases hL : i.1 = j.1 <;> by_cases hR : i.2 = j.2 <;>
      simp [liftLeftFactor, hQ, Matrix.one_apply, Prod.ext_iff, hL, hR]
  rw [← hsplit, Matrix.sub_mul, Matrix.one_mul, hliftQρ, sub_zero]

/-- The lifted support projector of the right partial trace also fixes a
positive semidefinite bipartite operator on the right.

Together with `PosSemidef.liftLeftFactor_supportProj_mul_self`, this proves both
equalities in equation `Propproj` of arXiv:1606.00608, Appendix D.2,
lines 2228--2235, for the \(AX|B\) bipartition. -/
theorem PosSemidef.mul_liftLeftFactor_supportProj_self
    {ρ : Matrix (L × R) (L × R) ℂ} (hρ : ρ.PosSemidef) :
    ρ * liftLeftFactor (R := R) (Matrix.PosSemidef.partialTraceRight hρ).isHermitian.supportProj
      = ρ := by
  have hleft := hρ.liftLeftFactor_supportProj_mul_self
  have hliftHerm :
      (liftLeftFactor (R := R)
        (Matrix.PosSemidef.partialTraceRight hρ).isHermitian.supportProj).IsHermitian := by
    rw [Matrix.IsHermitian, liftLeftFactor, Matrix.conjTranspose_kronecker,
      (Matrix.PosSemidef.partialTraceRight hρ).isHermitian.supportProj_isHermitian.eq,
      Matrix.conjTranspose_one]
  have h := congrArg Matrix.conjTranspose hleft
  rwa [Matrix.conjTranspose_mul, hρ.isHermitian.eq, hliftHerm.eq] at h

end Bipartite

end Matrix
