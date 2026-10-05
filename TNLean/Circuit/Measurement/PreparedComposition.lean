/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Measurement.Rounds

/-!
# Applying coherent measurement implementations to prepared states

A prepared vector can be followed by a sequence implementing a linear map on that vector.
The total depth is additive, and every nonzero output of the composite is proportional to
the mapped vector. Zero intermediate branches stay zero without postselection.

## References

* arXiv:2307.01696, "Tree-RG circuit with measurements" and
  "Long-range MPS using measurements".
* arXiv:2103.13367, "State transformations with QC and LOCC".
-/

open Matrix

namespace QuantumCircuit

variable {d N : ℕ} [NeZero N]

/-- Append an implementation to a prepared state, adding their nearest-neighbor depths. -/
theorem IsPreparedWithMeasurementRoundsInDepth.apply_implementation
    {T S : ℕ} {ψ : (Fin N → Fin d) → ℂ}
    (hψ : IsPreparedWithMeasurementRoundsInDepth T ψ)
    {Rs : List (MeasurementRound d N)}
    {E : Set ((Fin N → Fin d) → ℂ)}
    {W : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ}
    (hRs : MeasurementRound.IsRoundsImplementationOn Rs E W)
    (hψE : ψ ∈ E) (hdepth : (Rs.map MeasurementRound.depth).sum ≤ S) :
    IsPreparedWithMeasurementRoundsInDepth (T + S) (W *ᵥ ψ) := by
  obtain ⟨v, Rs₀, h₀, hv, hprep⟩ := hψ
  refine ⟨v, Rs₀ ++ Rs, ?_, hv, fun w hw hw0 => ?_⟩
  · simpa only [List.map_append, List.sum_append] using Nat.add_le_add h₀ hdepth
  · obtain ⟨u, hu, hwu⟩ := MeasurementRound.mem_outputs_append.mp hw
    by_cases hu0 : u = 0
    · subst u
      have hzero : w ∈ MeasurementRound.outputs Rs ((0 : ℂ) • ψ) := by simpa using hwu
      obtain ⟨z, -, hz⟩ := MeasurementRound.mem_outputs_smul 0 hzero
      exact (hw0 (by simpa using hz)).elim
    · obtain ⟨c, rfl⟩ := hprep u hu hu0
      obtain ⟨z, hz, rfl⟩ := MeasurementRound.mem_outputs_smul c hwu
      obtain ⟨c', rfl⟩ := hRs ψ hψE z hz
      exact ⟨c * c', by rw [smul_smul]⟩

end QuantumCircuit
