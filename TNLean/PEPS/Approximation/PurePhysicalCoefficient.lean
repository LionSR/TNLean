/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.PureSourceMatrix
import QICLean.Channel.PartialTrace

/-!
# Physical coefficients after tracing the prepared source output

The ket and bra columns are computed in the same physical and discarded
coordinate spaces. The final trace sums over a single common discarded index.
Neither the input vector nor the resulting mixed coefficient is normalized.
Source: polynomial-PEPS Theorem 5.2, eq:compression-source-gate and
rem:compression-retained-norm, manuscript revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section
open scoped BigOperators TensorProduct Matrix ComplexConjugate
namespace TNLean.Lattice.PartyCircuit.Word

/-- The physical entry of a mixed prepared coefficient is the sum of the ket
and conjugated bra output columns over their common discarded coordinate.
Source: polynomial-PEPS Theorem 5.2, eq:compression-source-gate and the final
partywise trace in its proof; Remark 5.3, rem:compression-retained-norm. -/
theorem preparedDensityCoefficient_pure_partialTrace_apply
    {P n X D : Type} [Fintype n] [Fintype X] [Fintype D]
    (R : SourceInventory P) (U V : Fin R.length → HSpace)
    {A B : Fin R.length → Type}
    [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (bU : ∀ i, OrthonormalBasis (A i) ℂ (U i))
    (bV : ∀ i, OrthonormalBasis (B i) ℂ (V i))
    (ℓ physical garbage : Layout P)
    (v v' : Word (SourceInventory.slotLayout R U V ++ ℓ) (physical ++ garbage))
    (bIn : OrthonormalBasis n ℂ (Mem ℓ))
    (bPhysical : OrthonormalBasis X ℂ (Mem physical))
    (bGarbage : OrthonormalBasis D ℂ (Mem garbage))
    (ψ : Mem ℓ) (x y : ∀ i, A i × B i) (a b : X) :
    let bOut := (bPhysical.tensorProduct bGarbage).map
      (appendIso physical garbage).symm
    Matrix.partialTraceRight
      (v.preparedDensityCoefficient R U V (fun i ↦ bU i) (fun i ↦ bV i)
        (fun i ↦ bU i) (fun i ↦ bV i) ℓ v' bIn bOut
        (Matrix.vecMulVec (bIn.repr ψ).ofLp (fun j ↦ conj (bIn.repr ψ j))) x y) a b =
      ∑ g : D, v.pureSourceMatrix R U V bU bV ℓ bOut ψ (a, g) x *
        conj (v'.pureSourceMatrix R U V bU bV ℓ bOut ψ (b, g) y) := by
  exact congrArg
    (fun M : Matrix (X × D) (X × D) ℂ ↦ Matrix.partialTraceRight M a b)
    (preparedDensityCoefficient_pure_eq_vecMulVec R U V bU bV ℓ v v' bIn
      ((bPhysical.tensorProduct bGarbage).map (appendIso physical garbage).symm)
      ψ x y)

end TNLean.Lattice.PartyCircuit.Word
