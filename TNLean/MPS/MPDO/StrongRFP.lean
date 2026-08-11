/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalClosure

/-!
# The unnormalized structural Strong-RFP relation

This file translates the diagram labelled `Strong-RFP` in CPSV16 Appendix D
(arXiv:1606.00608, lines 2109--2113, figure `APPE_Fig2.png`). The diagram places
one copy of the MPO tensor `M` on the left physical site, a positive matrix `P`
on the right physical site, and conjugates their physical tensor product by a
square two-site unitary `U`. Its literal orientation is

\[
  M_2 = U (M_1 \otimes P) U^\dagger.
\]

The source only assumes `P ≥ 0`; in particular it does not normalize `P` by
`tr P = 1`. Consequently this is an unnormalized local structural relation,
not the trace-preserving-CP-map predicate `MPOTensor.IsRFPViaTS` of Definition
4.1. No virtual gauge or scalar proportionality is included.

## Main definitions

* `MPOTensor.IsStrongRFP`: the literal local tensor relation in the source
  diagram.

## Main results

* `MPOTensor.strongRFP_tensor_relation_iff_physClose`: the fixed-witness tensor
  relation is equivalent to the physical-closure identity.
* `MPOTensor.isStrongRFP_iff_physClose`: the corresponding existential
  equivalence.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608, Appendix D,
  lines 2109--2116, figure `APPE_Fig2.png` (paper label `Strong-RFP`).
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

namespace MPOTensor

variable {d D : ℕ}

/-- The unnormalized structural **Strong-RFP** relation from CPSV16 Appendix D,
lines 2109--2113 and figure `APPE_Fig2.png` (paper label `Strong-RFP`).

There exist a positive semidefinite right-site physical matrix `P` and a square
unitary `U` on the two-site physical space such that, entrywise in the two open
physical legs,

\[
 M^{i_1j_1}M^{i_2j_2}
 = \sum_{a,b} U_{i,a} P_{a_2b_2}\overline{U_{j,b}}\,M^{a_1b_1}.
\]

This is exactly the orientation `M₂ = U (M₁ ⊗ P) U†` shown in the figure. The
matrix `P` is not required to have trace one. The equality is literal: it has
no virtual gauge and no proportionality scalar. This predicate is therefore
not identified with `IsRFPViaTS`. -/
def IsStrongRFP (M : MPOTensor d D) : Prop :=
  ∃ (P : Matrix (Fin d) (Fin d) ℂ)
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ),
    P.PosSemidef ∧ U ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ ∧
      ∀ i j : Fin d × Fin d,
        M i.1 j.1 * M i.2 j.2 =
          ∑ a, ∑ b,
            (U i a * P a.2 b.2 * star (U j b)) • M a.1 b.1

/-- The local tensor identity with fixed witnesses is equivalent to the
physical-closure identity
`M₂(X) = U (M₁(X) ⊗ P) U†` for every virtual matrix `X`.

The reverse implication uses nondegeneracy of the finite-dimensional trace
pairing; no injectivity or canonical-form hypothesis is needed.

Source: CPSV16, arXiv:1606.00608, Appendix D, lines 2109--2113 and figure
`APPE_Fig2.png` (paper label `Strong-RFP`). -/
theorem strongRFP_tensor_relation_iff_physClose
    (M : MPOTensor d D) (P : Matrix (Fin d) (Fin d) ℂ)
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    (∀ i j : Fin d × Fin d,
      M i.1 j.1 * M i.2 j.2 =
        ∑ a, ∑ b,
          (U i a * P a.2 b.2 * star (U j b)) • M a.1 b.1) ↔
      ∀ X : Matrix (Fin D) (Fin D) ℂ,
        physClose2 M X = U * (physClose1 M X ⊗ₖ P) * Uᴴ := by
  constructor
  · intro h X
    ext i j
    rw [physClose2_apply, h i j]
    simp only [Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul,
      Matrix.trace_smul, smul_eq_mul, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
      physClose1_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  · intro h i j
    apply sub_eq_zero.mp
    apply (Matrix.trace_mul_right_eq_zero_iff _).mp
    intro X
    rw [Matrix.sub_mul, Matrix.trace_sub]
    have hEntry := congrArg (fun A => A i j) (h X)
    rw [physClose2_apply] at hEntry
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.kroneckerMap_apply, physClose1_apply] at hEntry
    simp only [Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul,
      Matrix.trace_smul, smul_eq_mul]
    rw [Finset.sum_comm]
    apply sub_eq_zero.mpr
    rw [hEntry]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    ring

/-- The source's structural Strong-RFP predicate is equivalent to the existence
of a positive right-site matrix and square two-site unitary satisfying
`M₂(X) = U (M₁(X) ⊗ P) U†` for every virtual closure `X`.

Source: CPSV16, arXiv:1606.00608, Appendix D, lines 2109--2113 and figure
`APPE_Fig2.png` (paper label `Strong-RFP`). -/
theorem isStrongRFP_iff_physClose (M : MPOTensor d D) :
    IsStrongRFP M ↔
      ∃ (P : Matrix (Fin d) (Fin d) ℂ)
        (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ),
        P.PosSemidef ∧ U ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ ∧
          ∀ X : Matrix (Fin D) (Fin D) ℂ,
            physClose2 M X = U * (physClose1 M X ⊗ₖ P) * Uᴴ := by
  simp only [IsStrongRFP, strongRFP_tensor_relation_iff_physClose]

end MPOTensor
