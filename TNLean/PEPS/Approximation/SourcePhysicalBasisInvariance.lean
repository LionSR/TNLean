/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourcePhysicalDensity
import QICLean.Channel.PartialTraceBasisInvariance

/-!
# Basis independence of actual physical corrected terms

For a mixed pure input, the physical corrected term is a finite sum of the
actual substituted circuit output vectors. Its trace norm is consequently
independent of the orthonormal bases on the physical and discarded memories.
The corrected term and its original source occurrences remain fixed.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 338–549.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-exterior-contraction.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
-/


noncomputable section
open scoped TensorProduct Matrix ComplexConjugate
namespace TNLean.PEPS.PairEffect.SourceCircuit

variable {P m n : Type} [Fintype m] [Fintype n] {a b : Layout P}

/-- The original source-basis substitution acts on a mixed input as the outer
product of its two actual output vectors. -/
theorem sourceBasisMatrix_mul_vecMulVec (w : SourceCircuit a b)
    (S : Finset (sourceLocations w)) (u v : SourceBasisChoice w S)
    (bIn : OrthonormalBasis n ℂ (Mem a)) (bOut : OrthonormalBasis m ℂ (Mem b))
    (ψ φ : Mem a) :
    sourceBasisMatrix w S u bIn bOut *
        Matrix.vecMulVec (bIn.repr ψ).ofLp (fun j ↦ conj (bIn.repr φ j)) *
          (sourceBasisMatrix w S v bIn bOut)ᴴ =
      Matrix.vecMulVec
        (bOut.repr (evalWithSources w
          (selectedSourceVectors w S (labelBasisVectors w S u)) ψ)).ofLp
        (fun j ↦ conj (bOut.repr (evalWithSources w
          (selectedSourceVectors w S (labelBasisVectors w S v)) φ) j)) := by
  classical
  have h (q : SourceBasisChoice w S) (x : Mem a) :
      sourceBasisMatrix w S q bIn bOut *ᵥ (bIn.repr x).ofLp =
        (bOut.repr (evalWithSources w
          (selectedSourceVectors w S (labelBasisVectors w S q)) x)).ofLp :=
    LinearMap.toMatrix_mulVec_repr bIn.toBasis bOut.toBasis
      (evalWithSources w (selectedSourceVectors w S (labelBasisVectors w S q))).toLinearMap x
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, h]
  change Matrix.vecMulVec _ (star (bIn.repr φ).ofLp ᵥ*
    (sourceBasisMatrix w S v bIn bOut)ᴴ) = _
  rw [← Matrix.star_mulVec, h]
  rfl

open Classical in
/-- Changing physical or discarded orthonormal coordinates preserves the norm
of the same original corrected term, for arbitrary local correction matrices. -/
theorem rectangularTraceNorm_physicalCorrectedSourceTerm_basis_eq
    {x y d e : Type} [Fintype x] [Fintype y] [Fintype d] [Fintype e]
    (physical garbage : Layout P) (w : SourceCircuit a (physical ++ garbage))
    (S : Finset (sourceLocations w))
    (E : ∀ q : sourceLocations w, branchLabels w q.1 → branchLabels w q.1 →
      Matrix (Fin (sourceDims w q).1 × Fin (sourceDims w q).2)
        (Fin (sourceDims w q).1 × Fin (sourceDims w q).2) ℂ)
    (bIn : OrthonormalBasis n ℂ (Mem a))
    (bX : OrthonormalBasis x ℂ (Mem physical)) (bY : OrthonormalBasis y ℂ (Mem physical))
    (bd : OrthonormalBasis d ℂ (Mem garbage)) (be : OrthonormalBasis e ℂ (Mem garbage))
    (ψ φ : Mem a) :
    Matrix.rectangularTraceNorm (physicalCorrectedSourceTerm physical garbage w S E
      bIn bY be (Matrix.vecMulVec (bIn.repr ψ).ofLp (fun j ↦ conj (bIn.repr φ j)))) =
    Matrix.rectangularTraceNorm (physicalCorrectedSourceTerm physical garbage w S E
      bIn bX bd (Matrix.vecMulVec (bIn.repr ψ).ofLp (fun j ↦ conj (bIn.repr φ j)))) := by
  let c (q : SourceBasisChoice w S × SourceBasisChoice w S) :=
    ∏ i : S, E i.1 (q.1 i).1 (q.2 i).1 (q.1 i).2 (q.2 i).2
  let z (q : SourceBasisChoice w S × SourceBasisChoice w S) :=
    appendIso physical garbage (evalWithSources w
      (selectedSourceVectors w S (labelBasisVectors w S q.1)) ψ)
  let t (q : SourceBasisChoice w S × SourceBasisChoice w S) :=
    appendIso physical garbage (evalWithSources w
      (selectedSourceVectors w S (labelBasisVectors w S q.2)) φ)
  have h := OrthonormalBasis.rectangularTraceNorm_partialTrace_sum_rankOne_basis_eq
    bX bY bd be c z t
  change Matrix.rectangularTraceNorm (Matrix.partialTraceRight
    (correctedSourceTerm w S E bIn
      ((bY.tensorProduct be).map (appendIso physical garbage).symm) _)) =
    Matrix.rectangularTraceNorm (Matrix.partialTraceRight
      (correctedSourceTerm w S E bIn
        ((bX.tensorProduct bd).map (appendIso physical garbage).symm) _))
  unfold correctedSourceTerm
  simp_rw [sourceBasisMatrix_mul_vecMulVec]
  simpa only [Fintype.sum_prod_type, c, z, t, OrthonormalBasis.map,
    LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.trans_apply] using h

end TNLean.PEPS.PairEffect.SourceCircuit
