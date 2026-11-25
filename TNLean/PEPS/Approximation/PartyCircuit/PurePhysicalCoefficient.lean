/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Circuit.Party.Compression.SourceReplacement.Columns
import QICLean.Algebra.PartialTrace

/-!
# Physical coefficients after tracing the prepared source output

The ket and bra columns are read through the same readout into physical and
discarded coordinates. The final trace sums over a single common discarded index.
Neither the input vector nor the resulting mixed coefficient is normalized.
Source: polynomial-PEPS Theorem 5.2, eq:compression-source-gate and
rem:compression-retained-norm, manuscript revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section
open scoped BigOperators Matrix ComplexConjugate
open Matrix ManyBody

namespace QuantumCircuit.Party.Word

variable {P : Type} [Fintype P] [DecidableEq P] (R : SourceInventory P)
  (B : SourceInventory.SlotBases R.length) (X : P → Type) [∀ p, Fintype (X p)]
  [∀ p, DecidableEq (X p)] {Y : P → Type} [∀ p, Fintype (Y p)]

/-- The physical entry of a mixed prepared coefficient, read through a readout `K` into physical
and discarded coordinates, is the sum of the ket and conjugated bra output columns over their
common discarded coordinate.
Source: polynomial-PEPS Theorem 5.2, eq:compression-source-gate and the final
partywise trace in its proof; Remark 5.3, rem:compression-retained-norm. -/
theorem preparedDensityCoefficient_pure_partialTrace_apply {Phys Env : Type} [Fintype Env]
    (K : Matrix (Phys × Env) (Config Y) ℂ) (v v' : Word (SourceInventory.slotSystem R B X) Y)
    (ψ : EuclideanSpace ℂ (Config X)) (x y : ∀ i, B.left i × B.right i) (a b : Phys) :
    partialTraceRight
      (K * v.preparedDensityCoefficient R B X (fun _ a ↦ EuclideanSpace.single a 1)
        (fun _ a ↦ EuclideanSpace.single a 1) (fun _ a ↦ EuclideanSpace.single a 1)
        (fun _ a ↦ EuclideanSpace.single a 1) v' (euclideanOuterProduct ψ ψ) x y * Kᴴ) a b =
      ∑ g : Env, (K * v.pureSourceMatrix R B X ψ) (a, g) x *
        conj ((K * v'.pureSourceMatrix R B X ψ) (b, g) y) := by
  rw [preparedDensityCoefficient_pure_eq_vecMulVec, mul_vecMulVec, vecMulVec_mul,
    partialTraceRight_apply]
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  simp only [vecMulVec_apply, mulVec, vecMul, dotProduct, mul_apply, conjTranspose_apply,
    map_sum, map_mul, RCLike.star_def, mul_comm]

end QuantumCircuit.Party.Word
