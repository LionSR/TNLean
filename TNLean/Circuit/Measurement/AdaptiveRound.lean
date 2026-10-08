/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Measurement.AdaptiveConversion
import TNLean.Circuit.Measurement.Channel

/-!
# Measurement rounds as adaptive channels

A fixed-basis measurement round is an adaptive protocol with the same quantum-depth bound.
Its circuit is followed by the onsite instrument measuring the chosen sites. The complete
outcome tuple is communicated, and determines the product of correction unitaries. Averaging
these branches gives exactly the existing round's arbitrary-input channel.

## Main results

* `QuantumCircuit.MeasurementRound.adaptive` — the average map of a measurement round is
  a finite adaptive local protocol of depth equal to its circuit length.

## References

* Piroli, Styliaris and Cirac, arXiv:2103.13367, paragraph "State transformations with
  QC and LOCC", restricted to the fixed-basis rounds of `MeasurementRound`.
-/

open Matrix
open scoped BigOperators

noncomputable section
namespace QuantumCircuit
variable {d N : ℕ}

/-- Computational-basis measurement on the chosen sites, with one identity outcome elsewhere. -/
private def measuredInstrument (S : Finset (Fin N)) : OnsiteChannel d d (Fin N) where
  r i := if i ∈ S then d else 1
  kraus i j := if i ∈ S then
    diagonal (fun a : Fin d ↦ if a.val = j.val then 1 else 0) else 1
  sum_kraus i := by
    classical
    by_cases hi : i ∈ S
    · rw [ite_eq_left hi]
      simp only [ite_eq_left hi]
      ext a b
      simp [Matrix.sum_apply, Matrix.diagonal_apply, Fin.val_inj, Matrix.one_apply]
    · simp [hi]

/-- The onsite outcome tuples are exactly the configurations on the measured sites. -/
private def measuredOutcomeEquiv (S : Finset (Fin N)) :
    ((i : Fin N) → Fin ((measuredInstrument (d := d) S).r i)) ≃ (S → Fin d) where
  toFun J i := ⟨(J i).val, by simpa [measuredInstrument, i.property] using (J i).isLt⟩
  invFun m i := if hi : i ∈ S then
    ⟨(m ⟨i, hi⟩).val, by simpa only [measuredInstrument, ite_eq_left hi] using (m ⟨i, hi⟩).isLt⟩
    else ⟨0, by simp [measuredInstrument, hi]⟩
  left_inv J := by
    funext i
    apply Fin.ext
    by_cases hi : i ∈ S
    · simp [hi]
    · have hlt : (J i).val < 1 := by simpa [measuredInstrument, hi] using (J i).isLt
      simp [hi, show (J i).val = 0 by omega]
  right_inv m := by
    funext i
    apply Fin.ext
    simp [i.property]

/-- The product Kraus operator is the projector onto its measured configuration. -/
private theorem measuredInstrument_krausOp (S : Finset (Fin N))
    (J : (i : Fin N) → Fin ((measuredInstrument (d := d) S).r i)) :
    (measuredInstrument S).krausOp J = outcomeProj S (measuredOutcomeEquiv S J) := by
  classical
  ext x y
  simp only [OnsiteChannel.krausOp, rectKronecker_apply, outcomeProj, Matrix.diagonal_apply]
  by_cases hxy : x = y
  · subst y
    have hfac (i : Fin N) :
        (measuredInstrument S).kraus i (J i) (x i) (x i) =
          if ∀ hi : i ∈ S, x i = measuredOutcomeEquiv S J ⟨i, hi⟩ then 1 else 0 := by
      by_cases hi : i ∈ S
      · simp [measuredInstrument, hi, measuredOutcomeEquiv, Fin.ext_iff]
        rfl
      · simp [measuredInstrument, hi]
    simp_rw [hfac]
    rw [Finset.prod_boole]
    simp
  · have hi : ∃ i, x i ≠ y i := Function.ne_iff.mp hxy
    obtain ⟨i, hi⟩ := hi
    rw [ite_eq_right hxy]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    by_cases hS : i ∈ S
    · simp [measuredInstrument, hS, hi]
    · simp [measuredInstrument, hS, hi]

/-- The product of the local correction unitaries as an onsite channel. -/
private def correctionChannel (u : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hu : ∀ i, u i ∈ unitary (Matrix (Fin d) (Fin d) ℂ)) : OnsiteChannel d d (Fin N) where
  r _ := 1
  kraus i _ := u i
  sum_kraus i := by
    simpa only [Fin.sum_univ_one, star_eq_conjTranspose] using
      Unitary.star_mul_self_of_mem (hu i)

/-- The channel of the local corrections is conjugation by their tensor product. -/
private theorem correctionChannel_map (u : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hu : ∀ i, u i ∈ unitary (Matrix (Fin d) (Fin d) ℂ)) :
    (correctionChannel u hu).map = singleKrausMap (finKronecker u) := by
  apply LinearMap.ext
  intro X
  change (∑ _ : Fin N → Fin 1, finKronecker u * X * (finKronecker u)ᴴ) =
    finKronecker u * X * (finKronecker u)ᴴ
  simp

variable [NeZero N]

/-- A computational-basis measurement round is a finite adaptive protocol, with its circuit
length as the quantum-depth bound. Measuring all chosen sites simultaneously is an onsite
instrument, and the communicated outcome selects the onsite correction. -/
theorem MeasurementRound.adaptive (R : MeasurementRound d N) :
    IsAdaptiveChannelProtocol R.depth R.map := by
  classical
  let Φ := measuredInstrument (d := d) R.measured
  let E := measuredOutcomeEquiv (d := d) R.measured
  let Ψ := fun J : (i : Fin N) → Fin (Φ.r i) ↦
    singleKrausMap (finKronecker (R.correction (E J)))
  have hfeed : IsAdaptiveChannelProtocol 0 (Φ.feedforwardMap Ψ) := by
    apply IsAdaptiveChannelProtocol.instrument
    intro J
    change IsAdaptiveChannelProtocol 0
      (singleKrausMap (finKronecker (R.correction (E J))))
    rw [← correctionChannel_map (R.correction (E J)) (R.correction_mem_unitary (E J))]
    exact .onsite _
  have hCircuit :
      IsAdaptiveChannelProtocol R.depth (singleKrausMap (circuitOp R.circuit)) := by
    have h := (IsLocalChannelProtocol.onsite (OnsiteChannel.id d (Fin N))).channelCircuitMap_comp
      (R.circuit.map BondLayer.toChannelLayer)
    simpa only [List.length_map, zero_add, OnsiteChannel.id_map, LinearMap.comp_id,
      channelCircuitMap_map_toChannelLayer, MeasurementRound.depth] using h.adaptive
  have hmap : Φ.feedforwardMap Ψ ∘ₗ singleKrausMap (circuitOp R.circuit) = R.map := by
    apply LinearMap.ext
    intro X
    simp only [LinearMap.comp_apply, OnsiteChannel.feedforwardMap, LinearMap.sum_apply,
      Ψ, singleKrausMap_apply]
    change (∑ J, finKronecker (R.correction (E J)) *
      (Φ.krausOp J * (circuitOp R.circuit * X * (circuitOp R.circuit)ᴴ) * (Φ.krausOp J)ᴴ) *
        (finKronecker (R.correction (E J)))ᴴ) = ∑ m, R.kraus m * X * (R.kraus m)ᴴ
    simp only [Φ, measuredInstrument_krausOp]
    simpa only [MeasurementRound.kraus, Matrix.conjTranspose_mul, Matrix.mul_assoc, E] using
      E.sum_comp (fun m ↦ R.kraus m * X * (R.kraus m)ᴴ)
  simpa only [Nat.add_zero, hmap] using hCircuit.comp hfeed

end QuantumCircuit
