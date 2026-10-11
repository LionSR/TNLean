/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourcePhysicalDensity

/-!
# Physical density of a pure circuit input

For any input vector, multiplication of its rank-one density by the actual circuit
matrix gives the outer product of the output vector in the physical and discarded
coordinates. The physical density is its partial trace. No normalization is needed.

Source: polynomial-PEPS, `04-compression.tex`, lines 218–227 and 338–355.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-effect-circuit-error; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
-/


noncomputable section
open scoped Matrix ComplexConjugate
namespace TNLean.PEPS.PairEffect.SourceCircuit

/-- The physical density of an arbitrary pure input is the partial trace of
the literal output vector in the physical and garbage product coordinates.
No normalization premise is needed. Source: polynomial-PEPS,
`04-compression.tex:218–227` and `338–355`. -/
theorem physicalDensity_pure_input {P n x d : Type}
    [Fintype n] [Fintype x] [Fintype d] {a : Layout P}
    (physical garbage : Layout P) (w : SourceCircuit a (physical ++ garbage))
    (bIn : OrthonormalBasis n ℂ (Mem a))
    (bPhysical : OrthonormalBasis x ℂ (Mem physical))
    (bGarbage : OrthonormalBasis d ℂ (Mem garbage)) (ψ : Mem a) :
    physicalDensity physical garbage w bIn bPhysical bGarbage
      (Matrix.vecMulVec (bIn.repr ψ) (fun j ↦ conj (bIn.repr ψ j))) =
      Matrix.partialTraceRight
        (Matrix.vecMulVec
          (((appendIso physical garbage).trans (bPhysical.tensorProduct bGarbage).repr)
            (w.eval ψ))
          (fun j ↦ conj (((appendIso physical garbage).trans
            (bPhysical.tensorProduct bGarbage).repr) (w.eval ψ) j))) := by
  classical
  let B := (bPhysical.tensorProduct bGarbage).map (appendIso physical garbage).symm
  let M := LinearMap.toMatrix bIn.toBasis B.toBasis w.eval.toLinearMap
  change Matrix.partialTraceRight
    (M * Matrix.vecMulVec (bIn.repr ψ) (star (bIn.repr ψ).ofLp) * Mᴴ) = _
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec]
  have hin : (fun i ↦ bIn.toBasis.repr ψ i) = (bIn.repr ψ).ofLp :=
    funext (bIn.coe_toBasis_repr_apply ψ)
  have hout : (fun i ↦ B.toBasis.repr (w.eval ψ) i) = (B.repr (w.eval ψ)).ofLp :=
    funext (B.coe_toBasis_repr_apply (w.eval ψ))
  have hrepr : M *ᵥ (bIn.repr ψ).ofLp = (B.repr (w.eval ψ)).ofLp :=
    (congrArg (fun v : n → ℂ ↦ M *ᵥ v) hin.symm).trans
      ((LinearMap.toMatrix_mulVec_repr bIn.toBasis B.toBasis w.eval.toLinearMap ψ).trans hout)
  rw [hrepr]
  rfl

end TNLean.PEPS.PairEffect.SourceCircuit
