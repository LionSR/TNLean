/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.TransportRoundEnergy
import TNLean.PEPS.AreaLaw.Scan.ActualEntropySampling
import TNLean.PEPS.AreaLaw.Scan.FillTransport
import TNLean.PEPS.AreaLaw.Scan.ActualEnergyTerms

/-!
# Literal measures for actual fill and charge rounds

The actual recursive history trees, old/new partitions and conditional choices
specialize the canonical leaf measures. The same supplied family `pre` enters the
state, root norm and replica energy. Admissibility and cross-band commutation are
derived from the existing actual geometry. No integrability, mass or scalar
transport identity is supplied as a certificate.

This source-only candidate is uncompiled and depends on acceptance of the pending
upstream measure API. It advances the measure-valued round edge of scanner assembly,
without constructing `ScanData`, a physical prevector, comparator or ground state.
Fixed-parameter finiteness gives no continuity in the interpolation parameter.

Source: *A two-dimensional area law from a global spectral gap*,
`06-transport.tex`, lines 364–434, and `08-scanner.tex`, lines 416–451.
-/

open scoped BigOperators Matrix
open Matrix MeasureTheory Set
open TensorPower TensorPower.ReplicaTransport Entropy

noncomputable section

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
  (S : CollarScan V I) (hm : 0 < S.m) (hM : 0 < S.M) (s : ℕ)
  (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)] (E : EnergyTerms (V ⊕ Bool) n I)
  (a : ℝ) (pre : (k : ℕ) → Config k (fun v => Fin (n v)) → ℂ)

/-- The actual fill round, with interpolation scale `a/2` and the literal unit sphere.
The supplied family is shared by its old and new states. -/
def actualFillScanRound : ScanRound I (CoherentSphere (SiteConfig n)) :=
  transportScanRound (S.actualFillData hm hM s) n E S.IsGoodOldHistory (a / 2) pre

/-- The actual charge round, with interpolation scale `a/2` and the literal unit sphere.
The supplied family is shared by its old and new states. -/
def actualChargeScanRound : ScanRound I (CoherentSphere (SiteConfig n)) :=
  transportScanRound (S.actualChargeData hm hM s) n E S.IsGoodOldHistory (a / 2) pre

/-- The actual fill old sphere integral equals the existing literal state integral. -/
theorem integral_actualFillScanRound_old (ha : 0 ≤ a) (k : ℕ) (p : ℝ)
    (h : History S.K S.m S.M s)
    {f : (SiteConfig n → ℂ) → ℝ} (hf : Continuous f) :
    (∫ θ, f (fun x => θ.1 x) ∂(S.actualFillScanRound hm hM s n E a pre).μOld k p h) =
      (S.actualFillData hm hM s).oldFourierCoherentIntegral n (a / 2) k (pre k) p h f :=
  integral_transportScanRound_old (S.actualFillData hm hM s) n E S.IsGoodOldHistory (a / 2) pre
    (S.actualFillData_isAdmissible hm hM s) (div_nonneg ha (by norm_num)) k
    (S.fillTransportData_crossBandCommute _ n (div_nonneg ha (by norm_num)) k) p h hf

/-- The actual fill new sphere integral equals the existing literal state integral. -/
theorem integral_actualFillScanRound_new (ha : 0 ≤ a) (k : ℕ) (p : ℝ)
    (h : History S.K S.m S.M s) (c : Unit)
    {f : (SiteConfig n → ℂ) → ℝ} (hf : Continuous f) :
    (∫ θ, f (fun x => θ.1 x) ∂(S.actualFillScanRound hm hM s n E a pre).μNew k p h c) =
      ∫ u, Transport.fourierWeight u * realCoherentIntegral k (TransportData.base n)
        ((S.actualFillData hm hM s).state n (a / 2) k (pre k) p ⟨h, some c⟩ u) f :=
  integral_transportScanRound_new (S.actualFillData hm hM s) n E S.IsGoodOldHistory (a / 2) pre
    (S.actualFillData_isAdmissible hm hM s) (div_nonneg ha (by norm_num)) k
    (S.fillTransportData_crossBandCommute _ n (div_nonneg ha (by norm_num)) k) p h c hf

/-- The actual fill old and new measures have Fourier mass one half in the interior.
The replica count is unrestricted, and the hypotheses concern the supplied vector. -/
theorem actualFillScanRound_mass (ha : 0 ≤ a) (k : ℕ)
    (hsym : pre k ∈ symmetricSubspace k (fun v => Fin (n v))) (hpre : pre k ≠ 0)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (h : History S.K S.m S.M s) :
    ((S.actualFillScanRound hm hM s n E a pre).μOld k p h).real univ = 1 / 2 ∧
      ∀ c, ((S.actualFillScanRound hm hM s n E a pre).μNew k p h c).real univ = 1 / 2 :=
  transportScanRound_mass (S.actualFillData hm hM s) n E S.IsGoodOldHistory (a / 2) pre
    (S.actualFillData_isAdmissible hm hM s) (div_nonneg ha (by norm_num)) k
    (S.fillTransportData_crossBandCommute _ n (div_nonneg ha (by norm_num)) k) hsym hpre hp h

/-- Actual fill choice gain is the existing transport entropy gain, at every real p. -/
theorem actualFillScanRound_choiceGainSum (ha : 0 ≤ a) (k : ℕ) (p : ℝ) :
    (S.actualFillScanRound hm hM s n E a pre).choiceGainSum k p =
      (S.actualFillData hm hM s).entropyGain n (a / 2) k (pre k) p :=
  transportScanRound_choiceGainSum (S.actualFillData hm hM s) n E S.IsGoodOldHistory (a / 2) pre
    (S.actualFillData_isAdmissible hm hM s) (div_nonneg ha (by norm_num)) k
    (S.fillTransportData_crossBandCommute _ n (div_nonneg ha (by norm_num)) k) p

/-- Both split-probability factors in the actual fill energy sum agree with the
existing transport error on the closed interpolation interval. -/
theorem actualFillScanRound_energySum (ha : 0 ≤ a) (k : ℕ)
    {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    (S.actualFillScanRound hm hM s n E a pre).energySum k p =
      (S.actualFillData hm hM s).energyError E (a / 2) k (pre k) p :=
  transportScanRound_energySum (S.actualFillData hm hM s) n E S.IsGoodOldHistory (a / 2) pre
    (S.actualFillData_isAdmissible hm hM s) (div_nonneg ha (by norm_num)) k
    (S.fillTransportData_crossBandCommute _ n (div_nonneg ha (by norm_num)) k) hp

/-- The actual charge old sphere integral equals the existing literal state integral. -/
theorem integral_actualChargeScanRound_old (ha : 0 ≤ a) (k : ℕ) (p : ℝ)
    (h : History S.K S.m S.M s)
    {f : (SiteConfig n → ℂ) → ℝ} (hf : Continuous f) :
    (∫ θ, f (fun x => θ.1 x) ∂(S.actualChargeScanRound hm hM s n E a pre).μOld k p h) =
      (S.actualChargeData hm hM s).oldFourierCoherentIntegral n (a / 2) k (pre k) p h f :=
  integral_transportScanRound_old (S.actualChargeData hm hM s) n E S.IsGoodOldHistory (a / 2) pre
    (S.actualChargeData_isAdmissible hm hM s) (div_nonneg ha (by norm_num)) k
    (S.chargeTransportData_crossBandCommute _ _ n (div_nonneg ha (by norm_num)) k) p h hf

/-- The actual charge new sphere integral equals the existing literal state integral. -/
theorem integral_actualChargeScanRound_new (ha : 0 ≤ a) (k : ℕ) (p : ℝ)
    (h : History S.K S.m S.M s) (c : ChargeChoices S.K S.M)
    {f : (SiteConfig n → ℂ) → ℝ} (hf : Continuous f) :
    (∫ θ, f (fun x => θ.1 x) ∂(S.actualChargeScanRound hm hM s n E a pre).μNew k p h c) =
      ∫ u, Transport.fourierWeight u * realCoherentIntegral k (TransportData.base n)
        ((S.actualChargeData hm hM s).state n (a / 2) k (pre k) p ⟨h, some c⟩ u) f :=
  integral_transportScanRound_new (S.actualChargeData hm hM s) n E S.IsGoodOldHistory (a / 2) pre
    (S.actualChargeData_isAdmissible hm hM s) (div_nonneg ha (by norm_num)) k
    (S.chargeTransportData_crossBandCommute _ _ n (div_nonneg ha (by norm_num)) k) p h c hf

/-- The actual charge old and new measures have Fourier mass one half in the interior.
The replica count is unrestricted, and the hypotheses concern the supplied vector. -/
theorem actualChargeScanRound_mass (ha : 0 ≤ a) (k : ℕ)
    (hsym : pre k ∈ symmetricSubspace k (fun v => Fin (n v))) (hpre : pre k ≠ 0)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (h : History S.K S.m S.M s) :
    ((S.actualChargeScanRound hm hM s n E a pre).μOld k p h).real univ = 1 / 2 ∧
      ∀ c, ((S.actualChargeScanRound hm hM s n E a pre).μNew k p h c).real univ = 1 / 2 :=
  transportScanRound_mass (S.actualChargeData hm hM s) n E S.IsGoodOldHistory (a / 2) pre
    (S.actualChargeData_isAdmissible hm hM s) (div_nonneg ha (by norm_num)) k
    (S.chargeTransportData_crossBandCommute _ _ n (div_nonneg ha (by norm_num)) k) hsym hpre hp h

/-- Actual charge choice gain is the existing transport entropy gain, at every real p. -/
theorem actualChargeScanRound_choiceGainSum (ha : 0 ≤ a) (k : ℕ) (p : ℝ) :
    (S.actualChargeScanRound hm hM s n E a pre).choiceGainSum k p =
      (S.actualChargeData hm hM s).entropyGain n (a / 2) k (pre k) p :=
  transportScanRound_choiceGainSum (S.actualChargeData hm hM s) n E S.IsGoodOldHistory (a / 2) pre
    (S.actualChargeData_isAdmissible hm hM s) (div_nonneg ha (by norm_num)) k
    (S.chargeTransportData_crossBandCommute _ _ n (div_nonneg ha (by norm_num)) k) p

/-- Both split-probability factors in the actual charge energy sum agree with the
existing transport error on the closed interpolation interval. -/
theorem actualChargeScanRound_energySum (ha : 0 ≤ a) (k : ℕ)
    {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    (S.actualChargeScanRound hm hM s n E a pre).energySum k p =
      (S.actualChargeData hm hM s).energyError E (a / 2) k (pre k) p :=
  transportScanRound_energySum (S.actualChargeData hm hM s) n E S.IsGoodOldHistory (a / 2) pre
    (S.actualChargeData_isAdmissible hm hM s) (div_nonneg ha (by norm_num)) k
    (S.chargeTransportData_crossBandCommute _ _ n (div_nonneg ha (by norm_num)) k) hp

/-- The literal charge-round defect is the actual good-history entropy defect already
used by the physical sampling inequality, for every real interpolation parameter. -/
theorem actualChargeScanRound_chargeDefect (ha : 0 ≤ a) (k : ℕ) (p : ℝ) :
    (S.actualChargeScanRound hm hM s n E a pre).chargeDefect k p =
      S.actualChargeEntropyDefect hm hM s n E (a / 2) k (pre k) p := by
  rw [actualChargeScanRound, transportScanRound_chargeDefect _ _ _ _ _ _
    (S.actualChargeData_isAdmissible hm hM s) (div_nonneg ha (by norm_num)) k
    (S.chargeTransportData_crossBandCommute _ _ n (div_nonneg ha (by norm_num)) k)]
  unfold actualChargeEntropyDefect
  apply Finset.sum_congr rfl
  intro h _
  have hw : (S.actualChargeData hm hM s).histTree.weight h = historyWeight h :=
    historyMeanTree_weight _ _ _ hm hM s h
  simp only [hw]

end TNLean.PEPS.AreaLaw.Scan.CollarScan

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

variable {Λ : Finset (ℤ × ℤ)} {q R : ℕ} {J : ℝ} [NeZero q]
  [LinearOrder (AdmissibleSupport Λ R)]
  (S : CollarScan (Site Λ) (AdmissibleSupport Λ R))
  (hm : 0 < S.m) (hM : 0 < S.M) (s : ℕ)
  (h : LocalHamiltonian Λ q R J) (Ω : StateSpace Λ q) (Δ : ℝ) (L : ℕ)
  (aux : Bool → ℕ) [∀ b, NeZero (aux b)] (a : ℝ)
  (pre : (k : ℕ) → Config k
    (fun v => Fin (augmentedDimensions (V := Site Λ) q aux v)) → ℂ)

/-- With the actual augmented terms, the fill mean-energy field is the expectation
of the actual augmented truncated replica Hamiltonian in the same filtered vector.
No eigenvalue equation is asserted, including at zero copies. -/
theorem actualFillScanRound_meanEnergy (k : ℕ) (p : ℝ) :
    (S.actualFillScanRound hm hM s (augmentedDimensions q aux)
      (S.actualEnergyTerms h Ω Δ L aux) a pre).meanEnergy k p =
      let n := augmentedDimensions (V := Site Λ) q aux
      let D := S.actualFillData hm hM s
      let v := Transport.filteredVector (D.rootPath n (a / 2) k p) (pre k)
      (star v ⬝ᵥ (copyMean n k
        (augmentOperator q aux (∑ i, S.truncatedEnergyTerm h Ω Δ L i)) *ᵥ v)).re := by
  dsimp only [actualFillScanRound, transportScanRound]
  rw [S.replicaEnergy_actualEnergyTerms h Ω Δ L aux k]

/-- With the actual augmented terms, the charge mean-energy field is the expectation
of the actual augmented truncated replica Hamiltonian in the same filtered vector.
No eigenvalue equation is asserted, including at zero copies. -/
theorem actualChargeScanRound_meanEnergy (k : ℕ) (p : ℝ) :
    (S.actualChargeScanRound hm hM s (augmentedDimensions q aux)
      (S.actualEnergyTerms h Ω Δ L aux) a pre).meanEnergy k p =
      let n := augmentedDimensions (V := Site Λ) q aux
      let D := S.actualChargeData hm hM s
      let v := Transport.filteredVector (D.rootPath n (a / 2) k p) (pre k)
      (star v ⬝ᵥ (copyMean n k
        (augmentOperator q aux (∑ i, S.truncatedEnergyTerm h Ω Δ L i)) *ᵥ v)).re := by
  dsimp only [actualChargeScanRound, transportScanRound]
  rw [S.replicaEnergy_actualEnergyTerms h Ω Δ L aux k]

end TNLean.PEPS.AreaLaw.Scan.CollarScan
