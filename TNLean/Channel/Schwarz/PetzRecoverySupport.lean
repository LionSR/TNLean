/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.PetzRecovery
import TNLean.Channel.Schwarz.RelativeEntropyDataProcessing

/-!
# Support-domain input for partial-trace Petz recovery

This file verifies that the marginal of a positive semidefinite matrix lies in
the support domain on which the completed partial-trace Petz channel agrees
with the support formula, provided the joint matrices satisfy the corresponding
kernel inclusion.

## Main result

* `Matrix.partialTraceRightPetzChannel_apply_partialTraceRight_of_support`:
  the completed channel and the support Petz map agree on the first marginal.

## References

* P. Hayden, R. Jozsa, D. Petz, and A. Winter, *Structure of States Which
  Satisfy Strong Subadditivity of Quantum Entropy with Equality*, Theorem 3,
  equation (8), arXiv:quant-ph/0304007v2.
-/

open scoped Matrix ComplexOrder MatrixOrder

namespace Matrix

namespace IsHermitian

variable {n : Type*} [Fintype n] [DecidableEq n]
  {A B : Matrix n n ℂ}

/-- If the kernel of a Hermitian matrix `A` is contained in the kernel of a
Hermitian matrix `B`, then the support projection of `A` absorbs `B` on both
sides.

This is the support-domain linear-algebra step in the singular Petz transpose
formula of Hayden--Jozsa--Petz--Winter, arXiv:quant-ph/0304007v2, Theorem 3,
equation (8). -/
theorem supportProj_mul_mul_supportProj_of_mulVec_kernel_le
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hker : ∀ v : n → ℂ, A.mulVec v = 0 → B.mulVec v = 0) :
    hA.supportProj * B * hA.supportProj = B := by
  classical
  have hAcomp : A * (1 - hA.supportProj) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hA.mul_supportProj_self, sub_self]
  have hBcomp : B * (1 - hA.supportProj) = 0 := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [Matrix.zero_mulVec, ← Matrix.mulVec_mulVec]
    apply hker
    rw [Matrix.mulVec_mulVec, hAcomp, Matrix.zero_mulVec]
  have hBright : B = B * hA.supportProj := by
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at hBcomp
    exact hBcomp
  have hBcompLeft : (1 - hA.supportProj) * B = 0 := by
    simpa [Matrix.conjTranspose_mul, hA.supportProj_isHermitian.eq, hB.eq] using
      congrArg Matrix.conjTranspose hBcomp
  have hBleft : B = hA.supportProj * B := by
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at hBcompLeft
    exact hBcompLeft
  calc
    hA.supportProj * B * hA.supportProj = B * hA.supportProj := by rw [← hBleft]
    _ = B := hBright.symm

end IsHermitian

variable {L R : Type*} [Fintype L] [DecidableEq L]
  [Fintype R] [DecidableEq R]

/-- If positive semidefinite matrices `ρ` and `σ` satisfy
$\ker σ \subseteq \ker ρ$, then the completed Petz channel associated with `σ` agrees
with its support formula when applied to `partialTraceRight ρ`.

The support inclusion transfers to the two marginals, so the first marginal is
absorbed on both sides by the support projection of the reference marginal.
Thus the complementary preparation term vanishes. This isolates the support
domain of the singular Petz transpose formula in Hayden--Jozsa--Petz--Winter,
arXiv:quant-ph/0304007v2, Theorem 3, equation (8). -/
theorem partialTraceRightPetzChannel_apply_partialTraceRight_of_support
    {ρ σ : Matrix (L × R) (L × R) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hsupp : ∀ v : L × R → ℂ, σ.mulVec v = 0 → ρ.mulVec v = 0) :
    partialTraceRightPetzChannel σ hσ (partialTraceRight ρ) =
      partialTraceRightPetzMap σ hσ (partialTraceRight ρ) := by
  apply partialTraceRightPetzChannel_apply_of_supported
  exact IsHermitian.supportProj_mul_mul_supportProj_of_mulVec_kernel_le
    (PosSemidef.partialTraceRight hσ).isHermitian
    (PosSemidef.partialTraceRight hρ).isHermitian
    (fun _ hw => partialTraceRight_support hσ hsupp hw)

end Matrix
