/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.PEPS.AreaLaw.Scan.ActualScanMeasures
import TNLean.PEPS.AreaLaw.Scan.GlobalReplicaEnergyCoordinates

/-!
# Global replica energy of the actual filtered scan vector

The mean energy of each actual fill or charge round equals the real part of the global
replica energy in the same filtered vector, expressed in the successive
physical, C and R coordinates. The physical matrix is the sum of the actual
truncated terms formed using the supplied reference state. Neither an
eigenvalue equation nor a normalization assumption is imposed.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 371–384 and 416–451, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open TensorPower TensorPower.ReplicaTransport
open scoped BigOperators Matrix

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

variable {Λ : Finset (ℤ × ℤ)} {q d R : ℕ} {J : ℝ} [NeZero q] [NeZero d]
  [LinearOrder (AdmissibleSupport Λ R)]
  (S : CollarScan (Site Λ) (AdmissibleSupport Λ R))
  (hm : 0 < S.m) (hM : 0 < S.M) (s : ℕ)
  (h : LocalHamiltonian Λ q R J) (Ω : StateSpace Λ q) (Δ : ℝ) (L : ℕ)
  (a : ℝ) (pre : (k : ℕ) → Config k
    (fun v => Fin (augmentedDimensions (V := Site Λ) q (fun _ => d) v)) → ℂ)

/-- The actual fill mean energy is the global replica expectation in the same
filtered vector after the coordinate bijection, including zero copies.
The reference state in the truncated terms is unchanged.
Source: OpenAI area-law manuscript, `08-scanner.tex`, lines 371–384 and
416–451, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem actualFillScanRound_meanEnergy_eq_globalReplicaMeanHamiltonian
    (k : ℕ) (p : ℝ) :
    (S.actualFillScanRound hm hM s (augmentedDimensions q (fun _ => d))
      (S.actualEnergyTerms h Ω Δ L (fun _ => d)) a pre).meanEnergy k p =
      let n := augmentedDimensions (V := Site Λ) q (fun _ => d)
      let D := S.actualFillData hm hM s
      let v := Matrix.Transport.filteredVector (D.rootPath n (a / 2) k p) (pre k)
      let vO := v ∘ augmentedReplicaConfigurationEquiv q d k
      (star vO ⬝ᵥ
        (Matrix.globalReplicaMeanHamiltonian (fun _ : Site Λ => Fin q) (Fin d) (Fin d)
          (∑ i, S.truncatedEnergyTerm h Ω Δ L i) k *ᵥ vO)).re := by
  simpa only [actualFillScanRound_meanEnergy] using
    congrArg Complex.re (star_dotProduct_copyMean_augmentOperator q d k
      (∑ i, S.truncatedEnergyTerm h Ω Δ L i)
      (Matrix.Transport.filteredVector
        ((S.actualFillData hm hM s).rootPath
          (augmentedDimensions q (fun _ => d)) (a / 2) k p) (pre k)))

/-- The actual charge mean energy is the global replica expectation in the same
filtered vector after the coordinate bijection, including zero copies.
The reference state in the truncated terms is unchanged.
Source: OpenAI area-law manuscript, `08-scanner.tex`, lines 371–384 and
416–451, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem actualChargeScanRound_meanEnergy_eq_globalReplicaMeanHamiltonian
    (k : ℕ) (p : ℝ) :
    (S.actualChargeScanRound hm hM s (augmentedDimensions q (fun _ => d))
      (S.actualEnergyTerms h Ω Δ L (fun _ => d)) a pre).meanEnergy k p =
      let n := augmentedDimensions (V := Site Λ) q (fun _ => d)
      let D := S.actualChargeData hm hM s
      let v := Matrix.Transport.filteredVector (D.rootPath n (a / 2) k p) (pre k)
      let vO := v ∘ augmentedReplicaConfigurationEquiv q d k
      (star vO ⬝ᵥ
        (Matrix.globalReplicaMeanHamiltonian (fun _ : Site Λ => Fin q) (Fin d) (Fin d)
          (∑ i, S.truncatedEnergyTerm h Ω Δ L i) k *ᵥ vO)).re := by
  simpa only [actualChargeScanRound_meanEnergy] using
    congrArg Complex.re (star_dotProduct_copyMean_augmentOperator q d k
      (∑ i, S.truncatedEnergyTerm h Ω Δ L i)
      (Matrix.Transport.filteredVector
        ((S.actualChargeData hm hM s).rootPath
          (augmentedDimensions q (fun _ => d)) (a / 2) k p) (pre k)))
end TNLean.PEPS.AreaLaw.Scan.CollarScan
