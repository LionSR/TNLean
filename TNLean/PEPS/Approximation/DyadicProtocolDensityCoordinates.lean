/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.RectangularTraceNormAlgebra
import TNLean.PEPS.Approximation.ApproximateCircuitDensity
import TNLean.PEPS.Approximation.DyadicProtocolOriginalCircuit
import TNLean.PEPS.Approximation.OriginalCircuitGateMaps

/-!
# The physical density in the protocol's site coordinates

The physical density computed from the original chronological circuit is
indexed by the parties' physical configurations. Reindexing it by the
protocol's configuration equivalence gives the actual protocol density
indexed by configurations of the square. The original vector is retained
and the actual private registers are traced out, without normalization.
The same coordinate change preserves the trace norm of every density comparison.

Source: polynomial-PEPS manuscript, `07-assembly.tex`, lines 36–63;
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

namespace TNLean.PEPS.Approximation.DyadicProtocol

open TNLean.PEPS.PairEffect
attribute [local instance] Classical.propDecidable

variable {L q : ℕ} {P : Type} [Fintype P] (D : DyadicProtocol L q P)

/-- Reindexing the original circuit's unnormalized physical density gives the
actual protocol density; only the existing physical configuration equivalence
is used. Source: polynomial-PEPS manuscript, 07-assembly.tex, lines 36–49. -/
theorem reindex_original_physicalDensity :
    letI := Layout.finiteDimensional_mem_of_registers D.privateOutput D.finite_privateOutput
    Matrix.reindex D.physicalConfigEquiv D.physicalConfigEquiv
      (D.originalCircuit.produce.physicalDensityWithGateMaps
        D.originalCircuit.canonicalGateMaps
        (familyLabelledPhysicalReadout D.physicalDimension D.physicalOrder
          D.physicalOrder_nodup D.mem_physicalOrder D.privateOutput)
        D.input.vector) = D.physicalDensity := by
  simp only [EffectCircuit.physicalDensityWithGateMaps,
    OriginalCircuit.evalWithGateMaps_canonicalGateMaps, D.eval_originalCircuit]
  simp only [physicalDensity, readout, LinearIsometryEquiv.trans_apply]
  let := Layout.finiteDimensional_mem_of_registers D.privateOutput D.finite_privateOutput
  set u := familyLabelledPhysicalReadout D.physicalDimension D.physicalOrder
    D.physicalOrder_nodup D.mem_physicalOrder D.privateOutput
    (Layout.memCongr D.layout_changes (D.trajectory D.changes))
  rw [Matrix.reindex_apply, ← Matrix.partialTraceRight_submatrix_prod_equiv
    D.physicalConfigEquiv (Equiv.refl (Fin (Module.finrank ℂ (Mem D.privateOutput).carrier)))]
  rfl

/-- The physical configuration equivalence preserves the comparison trace norm.
Source: polynomial-PEPS manuscript, 07-assembly.tex, lines 36–63. -/
theorem rectangularTraceNorm_reindex_sub_physicalDensity
    (M : Matrix ((p : P) → Fin (D.physicalDimension p))
      ((p : P) → Fin (D.physicalDimension p)) ℂ) :
    letI := Layout.finiteDimensional_mem_of_registers D.privateOutput D.finite_privateOutput
    Matrix.rectangularTraceNorm
      (Matrix.reindex D.physicalConfigEquiv D.physicalConfigEquiv M - D.physicalDensity) =
    Matrix.rectangularTraceNorm
      (M - D.originalCircuit.produce.physicalDensityWithGateMaps
        D.originalCircuit.canonicalGateMaps
        (familyLabelledPhysicalReadout D.physicalDimension D.physicalOrder
          D.physicalOrder_nodup D.mem_physicalOrder D.privateOutput)
        D.input.vector) := by
  let := Layout.finiteDimensional_mem_of_registers D.privateOutput D.finite_privateOutput
  rw [← D.reindex_original_physicalDensity]
  simpa only [Matrix.reindex_apply, Matrix.submatrix_sub, Pi.sub_apply] using
    Matrix.rectangularTraceNorm_reindex D.physicalConfigEquiv D.physicalConfigEquiv
      (M - D.originalCircuit.produce.physicalDensityWithGateMaps
        D.originalCircuit.canonicalGateMaps
        (familyLabelledPhysicalReadout D.physicalDimension D.physicalOrder
          D.physicalOrder_nodup D.mem_physicalOrder D.privateOutput)
        D.input.vector)

end TNLean.PEPS.Approximation.DyadicProtocol
