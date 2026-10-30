/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.MargolusConstantGates
import TNLean.QCA.ConsecutivePairObservables
import TNLean.QCA.BipartiteQuasiLocalEmbedding
import TNLean.MPS.MPU.StandardFormFromGates
import TNLean.MPS.MPU.TwoSiteStandardFormOpenWord

/-!
# The standard-form output is the actual fixed Margolus local rule

The four physical output coordinates of a supplied standard form are
placed on the two neighbouring shifted pairs in increasing site order.
Its full matrix-unit expansion is exactly the fixed-gate rule derived
from the QCA, including the actual translation by minus two on the left.

Source: Schumacher--Werner, quant-ph/0405174, bruleU/bruleV and locMarg,
lines 980--1008; CPSV17, arXiv:1703.09188, StandardForm, lines 603--622,
and Appendix line 2308.
-/

open scoped Matrix Kronecker BigOperators

namespace SpinChain.PropagatesWithin

variable {d : ℕ} [NeZero d]
  {ω : QuasiLocalAlgebra d ≃⋆ₐ[ℂ] QuasiLocalAlgebra d}
  (hω : PropagatesWithin ω (Finset.Icc (-1) 1))

/-- The standard-form four-half-site matrix, in actual neighbouring
pair coordinates, is the literal constant Margolus output rule. This
identity holds for any gates with the indicated factor dimensions;
unitarity and an assumed circuit equality are unnecessary.
Source: Schumacher--Werner locMarg, lines 980--1008; CPSV17 StandardForm,
lines 603--622. -/
theorem twoLinkOutputObservable_eq_constantMargolusGateRule
    (u : Matrix (Fin (supportAlgebraMatrixSize hω 0) ×
      Fin (supportAlgebraMatrixSize hω 1)) (Fin d × Fin d) ℂ)
    (v : Matrix (Fin d × Fin d) (Fin (supportAlgebraMatrixSize hω 1) ×
      Fin (supportAlgebraMatrixSize hω 0)) ℂ)
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    bipartiteMatrixToQuasiLocalObservable (disjoint_leftPair_rightPair 0)
        (Matrix.reindex
          ((consecutivePairConfigEquiv d (-1)).prodCongr (consecutivePairConfigEquiv d 1))
          ((consecutivePairConfigEquiv d (-1)).prodCongr (consecutivePairConfigEquiv d 1))
          (MPOTensor.twoLinkOutputObservable u v A)) =
      constantMargolusGateRule hω v (u * A * uᴴ) := by
  classical
  let e := (consecutivePairConfigEquiv d (-1)).prodCongr (consecutivePairConfigEquiv d 1)
  let H := (bipartiteMatrixToQuasiLocalObservable (d := d)
    (disjoint_leftPair_rightPair 0)).comp (Matrix.matrixReindexStarAlgEquiv e).toStarAlgHom
  have hleft (B : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
      quasiLocalTranslation d (-2)
          (matrixToQuasiLocalObservable d (rightPair 0)
            (Matrix.reindex (consecutivePairConfigEquiv d 1)
              (consecutivePairConfigEquiv d 1) B)) =
        matrixToQuasiLocalObservable d (leftPair 0)
          (Matrix.reindex (consecutivePairConfigEquiv d (-1))
            (consecutivePairConfigEquiv d (-1)) B) := by
    exact quasiLocalTranslation_consecutivePair d (-2) 1 B
  have hproduct (B C : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
      H (B ⊗ₖ C) =
        matrixToQuasiLocalObservable d (leftPair 0)
            (Matrix.reindex (consecutivePairConfigEquiv d (-1))
              (consecutivePairConfigEquiv d (-1)) B) *
          matrixToQuasiLocalObservable d (rightPair 0)
            (Matrix.reindex (consecutivePairConfigEquiv d 1)
              (consecutivePairConfigEquiv d 1) C) := by
    have hreindex : Matrix.reindex e e (B ⊗ₖ C) =
        Matrix.reindex (consecutivePairConfigEquiv d (-1))
            (consecutivePairConfigEquiv d (-1)) B ⊗ₖ
          Matrix.reindex (consecutivePairConfigEquiv d 1)
            (consecutivePairConfigEquiv d 1) C := by
      ext x y
      rfl
    change bipartiteMatrixToQuasiLocalObservable _ (Matrix.reindex e e (B ⊗ₖ C)) = _
    exact (congrArg (bipartiteMatrixToQuasiLocalObservable (d := d)
      (disjoint_leftPair_rightPair 0)) hreindex).trans
        (bipartiteMatrixToQuasiLocalObservable_kronecker (disjoint_leftPair_rightPair 0) _ _)
  change H (MPOTensor.twoLinkOutputObservable u v A) = _
  rw [MPOTensor.twoLinkOutputObservable_eq_sum_kronecker]
  simp only [map_sum, map_smul, hproduct, ← hleft, constantMargolusGateRule]

/-- A nearest-neighbour translation-covariant QCA supplies an explicit
standard-form tensor whose four-half-site output is its actual local
rule at every translate. The tensor and its MPU property are constructed.
This local statement precedes identification with the completed action
on the twice-blocked physical alphabet.
Source: CPSV17, Appendix line 2308 and StandardForm, lines 603--622;
Schumacher--Werner bruleU/bruleV and translation compatibility,
lines 980--1001 and 1033--1041. -/
theorem exists_standardFormTensor_actual_margolus_rule (hcov : TranslationCovariant ω) :
    ∃ (u : Matrix (Fin (supportAlgebraMatrixSize hω 0) ×
          Fin (supportAlgebraMatrixSize hω 1)) (Fin d × Fin d) ℂ)
      (v : Matrix (Fin d × Fin d) (Fin (supportAlgebraMatrixSize hω 1) ×
          Fin (supportAlgebraMatrixSize hω 0)) ℂ)
      (_S : MPOTensor.TwoSiteStandardFormData (MPOTensor.standardFormTensorOfGates u v) u v),
      (MPOTensor.standardFormTensorOfGates u v).IsMPU ∧
      ∀ (t : ℤ) (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ),
        ω (quasiLocalTranslation d t (matrixToQuasiLocalObservable d (evenPair 0)
          (Matrix.reindex (consecutivePairConfigEquiv d 0)
            (consecutivePairConfigEquiv d 0) A))) =
          quasiLocalTranslation d t
            (bipartiteMatrixToQuasiLocalObservable (disjoint_leftPair_rightPair 0)
              (Matrix.reindex
                ((consecutivePairConfigEquiv d (-1)).prodCongr
                  (consecutivePairConfigEquiv d 1))
                ((consecutivePairConfigEquiv d (-1)).prodCongr
                  (consecutivePairConfigEquiv d 1))
                (MPOTensor.twoLinkOutputObservable u v A))) := by
  obtain ⟨u, v, hu, hv, _, _, hlocal⟩ := exists_fixed_margolus_unitary_gates hω hcov
  refine ⟨u, v, MPOTensor.standardFormTensorOfGatesData u v hu hv,
    MPOTensor.isMPU_standardFormTensorOfGates u v hu hv, ?_⟩
  intro t A
  rw [hlocal, twoLinkOutputObservable_eq_constantMargolusGateRule]

end SpinChain.PropagatesWithin
