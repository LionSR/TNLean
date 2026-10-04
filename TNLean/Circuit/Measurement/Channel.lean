/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Channel.Feedforward
import TNLean.Circuit.Measurement.Rounds

/-!
# Channels induced by measurement rounds

A measurement round acts on arbitrary input operators by averaging its unnormalized
outcome operations. The result is trace preserving and completely positive. On pure inputs
it is the sum of the output projectors; a deterministic preparation of a normalized pure
state therefore has that state's projector as its average output.

## Main results

* `QuantumCircuit.MeasurementRound.map_isKrausCPTP` — a measurement round is a channel.
* `QuantumCircuit.MeasurementRound.map_vecMulVec_of_isPreparationOf` — deterministic pure
  preparation agrees with the average channel output on normalized inputs and targets.

## References

* Piroli, Styliaris and Cirac, arXiv:2103.13367, paragraphs "Quantum circuits and LOCC"
  and "State transformations with QC and LOCC".
-/

open Matrix
open scoped BigOperators

noncomputable section

namespace QuantumCircuit

variable {d N : ℕ} [NeZero N]

namespace MeasurementRound

/-- The average channel of a measurement round, on arbitrary input operators. -/
def map (R : MeasurementRound d N) :
    Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ :=
  rectangularKrausMap R.kraus

/-- On a pure input, the channel is the sum of the unnormalized output projectors.
A zero-probability outcome contributes the zero matrix. -/
theorem map_vecMulVec (R : MeasurementRound d N) (v : (Fin N → Fin d) → ℂ) :
    R.map (vecMulVec v (star v)) =
      ∑ m, vecMulVec (R.kraus m *ᵥ v) (star (R.kraus m *ᵥ v)) := by
  change (∑ m, R.kraus m * vecMulVec v (star v) * (R.kraus m)ᴴ) = _
  simp only [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_conjTranspose,
    star_star]

/-- The corrected measurement operators of a round resolve the identity. -/
theorem sum_kraus (R : MeasurementRound d N) : ∑ m, (R.kraus m)ᴴ * R.kraus m = 1 := by
  classical
  have hP (m : R.measured → Fin d) :
      (outcomeProj R.measured m)ᴴ * outcomeProj R.measured m = outcomeProj R.measured m := by
    simp only [outcomeProj, diagonal_conjTranspose, diagonal_mul_diagonal]
    congr 1
    funext x
    simp only [Pi.star_apply]
    split_ifs <;> simp
  have hterm (m : R.measured → Fin d) :
      (R.kraus m)ᴴ * R.kraus m =
        (circuitOp R.circuit)ᴴ * outcomeProj R.measured m * circuitOp R.circuit := by
    have hV := Unitary.star_mul_self_of_mem (finKronecker_mem_unitary
      (R.correction_mem_unitary m))
    rw [star_eq_conjTranspose] at hV
    unfold kraus
    simp only [conjTranspose_mul]
    calc
      _ = (circuitOp R.circuit)ᴴ *
          ((outcomeProj R.measured m)ᴴ *
            ((finKronecker (R.correction m))ᴴ * finKronecker (R.correction m)) *
              outcomeProj R.measured m) * circuitOp R.circuit := by noncomm_ring
      _ = _ := by rw [hV, Matrix.mul_one, hP]
  simp_rw [hterm]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, sum_outcomeProj, Matrix.mul_one]
  exact Unitary.star_mul_self_of_mem (circuitOp_mem_unitary R.circuit)

/-- Forgetting the measurement outcomes gives a trace-preserving completely positive map. -/
theorem map_isKrausCPTP (R : MeasurementRound d N) : IsKrausCPTP R.map :=
  rectangularKrausMap_isKrausCPTP R.kraus R.sum_kraus

/-- A deterministic preparation by a round gives the target pure density matrix when
both the product input and target are normalized to trace one. -/
theorem map_vecMulVec_of_isPreparationOf (R : MeasurementRound d N)
    (v : Fin N → Fin d → ℂ) (ψ : (Fin N → Fin d) → ℂ)
    (h : (R.toProtocol v).IsPreparationOf ψ)
    (hv : trace (vecMulVec (productVector v) (star (productVector v))) = 1)
    (hψ : trace (vecMulVec ψ (star ψ)) = 1) :
    R.map (vecMulVec (productVector v) (star (productVector v))) =
      vecMulVec ψ (star ψ) := by
  classical
  have hout (m : R.measured → Fin d) :
      ∃ c : ℂ, R.kraus m *ᵥ productVector v = c • ψ := by
    rw [← R.toProtocol_output v m]
    by_cases hm : (R.toProtocol v).postMeasurement m = 0
    · exact ⟨0, by simp [MeasurementProtocol.output, hm]⟩
    · exact h.2 m hm
  choose c hc using hout
  have hmap : R.map (vecMulVec (productVector v) (star (productVector v))) =
      (∑ m, c m * star (c m)) • vecMulVec ψ (star ψ) := by
    rw [R.map_vecMulVec]
    simp_rw [hc, star_smul, smul_vecMulVec, vecMulVec_smul, smul_smul]
    exact Finset.sum_smul.symm
  have htrace := R.map_isKrausCPTP.trace_map
    (vecMulVec (productVector v) (star (productVector v)))
  rw [hmap, trace_smul, hv, hψ, smul_eq_mul, mul_one] at htrace
  rw [hmap, htrace, one_smul]

end MeasurementRound

end QuantumCircuit
