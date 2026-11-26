/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scanner.Rounds.TransportRoundEnergy
import TNLean.PEPS.AreaLaw.Scanner.Rounds.ActualEntropySampling
import TNLean.PEPS.AreaLaw.Scanner.Rounds.FillTransport
import TNLean.PEPS.AreaLaw.Scanner.Statuses.ActualEnergyTerms
import TNLean.PEPS.AreaLaw.Scanner.Rounds.AugmentedEnergyCoordinates
import QICLean.ManyBody.Replica.LowDefect.RegionalLowDefectMass

/-!
# Literal measures for actual fill and charge rounds

The actual recursive history trees, old/new partitions and conditional choices
specialize the canonical leaf measures. The same supplied family `pre` enters the
state, root norm and replica energy. Admissibility and cross-band commutation are
derived from the existing actual geometry. No integrability, mass or scalar
transport identity is supplied as a certificate.

These constructions give the measures for individual fill and charge rounds,
without constructing `ScanData`, a physical prevector, comparator or ground state.
Fixed-parameter finiteness gives no continuity in the interpolation parameter.

Source: *A two-dimensional area law from a global spectral gap*,
`06-transport.tex`, lines 364–434, and `08-scanner.tex`, lines 416–451.

It also contains the following results.

*
  `TNLean.PEPS.AreaLaw.Scan.CollarScan.actualFillScanRound_meanEnergy_eq_globalReplicaMeanHamiltonian`,
  `TNLean.PEPS.AreaLaw.Scan.CollarScan.actualChargeScanRound_meanEnergy_eq_globalReplicaMeanHamiltonian`:
  global replica energy of the actual filtered scan vector.
* `TNLean.PEPS.AreaLaw.Scan.CollarScan.norm_filteredVector_actualChargeData`,
  `TNLean.PEPS.AreaLaw.Scan.CollarScan.actualChargeScanRound_globalLowDefectProjection_mass_ge`: the
  gap estimate for the actual charge filtered vector.
-/

section ActualScanMeasures

open scoped Matrix.Norms.L2Operator

open scoped BigOperators Matrix
open Matrix MeasureTheory Set
open TensorPower TensorPower.ReplicaTransport Entropy

noncomputable section

open ManyBody (AdmissibleSupport PlaneInteraction)

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
  (S : CollarScan V I) (hm : 0 < S.m) (hM : 0 < S.M) (s : ℕ)
  (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)] (E : EnergyTerms (V ⊕ Bool) n I)
  (a : ℝ) (pre : (k : ℕ) → Config k (fun v => Fin (n v)) → ℂ)

/-- The actual fill round, with interpolation scale `a/2` and the literal unit sphere.
The supplied family is shared by its old and new states. -/
def actualFillScanRound : ScanRound I (CoherentSphere (∀ v, Fin (n v))) :=
  transportScanRound (S.actualFillData hm hM s) n E S.IsGoodOldHistory (a / 2) pre

/-- The actual charge round, with interpolation scale `a/2` and the literal unit sphere.
The supplied family is shared by its old and new states. -/
def actualChargeScanRound : ScanRound I (CoherentSphere (∀ v, Fin (n v))) :=
  transportScanRound (S.actualChargeData hm hM s) n E S.IsGoodOldHistory (a / 2) pre

/-- The actual fill old sphere integral equals the existing literal state integral. -/
theorem integral_actualFillScanRound_old (ha : 0 ≤ a) (k : ℕ) (p : ℝ)
    (h : History S.K S.m S.M s)
    {f : ((∀ v, Fin (n v)) → ℂ) → ℝ} (hf : Continuous f) :
    (∫ θ, f (fun x => θ.1 x) ∂(S.actualFillScanRound hm hM s n E a pre).μOld k p h) =
      (S.actualFillData hm hM s).oldFourierCoherentIntegral n (a / 2) k (pre k) p h f :=
  integral_transportScanRound_old (S.actualFillData hm hM s) n E S.IsGoodOldHistory (a / 2) pre
    (S.actualFillData_isAdmissible hm hM s) (div_nonneg ha (by norm_num)) k
    (S.fillTransportData_crossBandCommute _ n (div_nonneg ha (by norm_num)) k) p h hf

/-- The actual fill new sphere integral equals the existing literal state integral. -/
theorem integral_actualFillScanRound_new (ha : 0 ≤ a) (k : ℕ) (p : ℝ)
    (h : History S.K S.m S.M s) (c : Unit)
    {f : ((∀ v, Fin (n v)) → ℂ) → ℝ} (hf : Continuous f) :
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
    {f : ((∀ v, Fin (n v)) → ℂ) → ℝ} (hf : Continuous f) :
    (∫ θ, f (fun x => θ.1 x) ∂(S.actualChargeScanRound hm hM s n E a pre).μOld k p h) =
      (S.actualChargeData hm hM s).oldFourierCoherentIntegral n (a / 2) k (pre k) p h f :=
  integral_transportScanRound_old (S.actualChargeData hm hM s) n E S.IsGoodOldHistory (a / 2) pre
    (S.actualChargeData_isAdmissible hm hM s) (div_nonneg ha (by norm_num)) k
    (S.chargeTransportData_crossBandCommute _ _ n (div_nonneg ha (by norm_num)) k) p h hf

/-- The actual charge new sphere integral equals the existing literal state integral. -/
theorem integral_actualChargeScanRound_new (ha : 0 ≤ a) (k : ℕ) (p : ℝ)
    (h : History S.K S.m S.M s) (c : ChargeChoices S.K S.M)
    {f : ((∀ v, Fin (n v)) → ℂ) → ℝ} (hf : Continuous f) :
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
  (S : CollarScan ↥Λ (AdmissibleSupport Λ R))
  (hm : 0 < S.m) (hM : 0 < S.M) (s : ℕ)
  (h : PlaneInteraction Λ q R) (hh : ∀ X, (h.term X).IsHermitian) (hhJ : ∀ X, ‖h.term X‖ ≤ J)
      (Ω : EuclideanSpace ℂ (↥Λ → Fin q)) (Δ : ℝ) (L : ℕ)
  (aux : Bool → ℕ) [∀ b, NeZero (aux b)] (a : ℝ)
  (pre : (k : ℕ) → Config k
    (fun v => Fin (augmentedDimensions (V := ↥Λ) q aux v)) → ℂ)

/-- With the actual augmented terms, the fill mean-energy field is the expectation
of the actual augmented truncated replica Hamiltonian in the same filtered vector.
No eigenvalue equation is asserted, including at zero copies. -/
theorem actualFillScanRound_meanEnergy (k : ℕ) (p : ℝ) :
    (S.actualFillScanRound hm hM s (augmentedDimensions q aux)
      (S.actualEnergyTerms h Ω J Δ L aux) a pre).meanEnergy k p =
      let n := augmentedDimensions (V := ↥Λ) q aux
      let D := S.actualFillData hm hM s
      let v := Transport.filteredVector (D.rootPath n (a / 2) k p) (pre k)
      (star v ⬝ᵥ (copyMean n k
        (augmentOperator q aux (∑ i, S.truncatedEnergyTerm h Ω J Δ L i)) *ᵥ v)).re := by
  dsimp only [actualFillScanRound, transportScanRound]
  rw [S.replicaEnergy_actualEnergyTerms h Ω Δ L aux k]

/-- With the actual augmented terms, the charge mean-energy field is the expectation
of the actual augmented truncated replica Hamiltonian in the same filtered vector.
No eigenvalue equation is asserted, including at zero copies. -/
theorem actualChargeScanRound_meanEnergy (k : ℕ) (p : ℝ) :
    (S.actualChargeScanRound hm hM s (augmentedDimensions q aux)
      (S.actualEnergyTerms h Ω J Δ L aux) a pre).meanEnergy k p =
      let n := augmentedDimensions (V := ↥Λ) q aux
      let D := S.actualChargeData hm hM s
      let v := Transport.filteredVector (D.rootPath n (a / 2) k p) (pre k)
      (star v ⬝ᵥ (copyMean n k
        (augmentOperator q aux (∑ i, S.truncatedEnergyTerm h Ω J Δ L i)) *ᵥ v)).re := by
  dsimp only [actualChargeScanRound, transportScanRound]
  rw [S.replicaEnergy_actualEnergyTerms h Ω Δ L aux k]

end TNLean.PEPS.AreaLaw.Scan.CollarScan

end

end ActualScanMeasures

section ActualGlobalReplicaEnergy

/-!
## Global replica energy of the actual filtered scan vector

The mean energy of each actual fill or charge round equals the real part of the global
replica energy in the same filtered vector, expressed in the successive
physical, C and R coordinates. The physical matrix is the sum of the actual
truncated terms formed using the supplied reference state. Neither an
eigenvalue equation nor a normalization assumption is imposed.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 371–384 and 416–451, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped Matrix.Norms.L2Operator

noncomputable section

open TensorPower TensorPower.ReplicaTransport
open scoped BigOperators Matrix

open ManyBody (AdmissibleSupport PlaneInteraction)

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

variable {Λ : Finset (ℤ × ℤ)} {q d R : ℕ} {J : ℝ} [NeZero q] [NeZero d]
  [LinearOrder (AdmissibleSupport Λ R)]
  (S : CollarScan ↥Λ (AdmissibleSupport Λ R))
  (hm : 0 < S.m) (hM : 0 < S.M) (s : ℕ)
  (h : PlaneInteraction Λ q R) (hh : ∀ X, (h.term X).IsHermitian) (hhJ : ∀ X, ‖h.term X‖ ≤ J)
      (Ω : EuclideanSpace ℂ (↥Λ → Fin q)) (Δ : ℝ) (L : ℕ)
  (a : ℝ) (pre : (k : ℕ) → Config k
    (fun v => Fin (augmentedDimensions (V := ↥Λ) q (fun _ => d) v)) → ℂ)

/-- The actual fill mean energy is the global replica expectation in the same
filtered vector after the coordinate bijection, including zero copies.
The reference state in the truncated terms is unchanged.
Source: OpenAI area-law manuscript, `08-scanner.tex`, lines 371–384 and
416–451, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem actualFillScanRound_meanEnergy_eq_globalReplicaMeanHamiltonian
    (k : ℕ) (p : ℝ) :
    (S.actualFillScanRound hm hM s (augmentedDimensions q (fun _ => d))
      (S.actualEnergyTerms h Ω J Δ L (fun _ => d)) a pre).meanEnergy k p =
      let n := augmentedDimensions (V := ↥Λ) q (fun _ => d)
      let D := S.actualFillData hm hM s
      let v := Matrix.Transport.filteredVector (D.rootPath n (a / 2) k p) (pre k)
      let vO := v ∘ augmentedReplicaConfigurationEquiv q d k
      (star vO ⬝ᵥ
        (Matrix.globalReplicaMeanHamiltonian (fun _ : ↥Λ => Fin q) (Fin d) (Fin d)
          (∑ i, S.truncatedEnergyTerm h Ω J Δ L i) k *ᵥ vO)).re := by
  simpa only [actualFillScanRound_meanEnergy] using
    congrArg Complex.re (star_dotProduct_copyMean_augmentOperator q d k
      (∑ i, S.truncatedEnergyTerm h Ω J Δ L i)
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
      (S.actualEnergyTerms h Ω J Δ L (fun _ => d)) a pre).meanEnergy k p =
      let n := augmentedDimensions (V := ↥Λ) q (fun _ => d)
      let D := S.actualChargeData hm hM s
      let v := Matrix.Transport.filteredVector (D.rootPath n (a / 2) k p) (pre k)
      let vO := v ∘ augmentedReplicaConfigurationEquiv q d k
      (star vO ⬝ᵥ
        (Matrix.globalReplicaMeanHamiltonian (fun _ : ↥Λ => Fin q) (Fin d) (Fin d)
          (∑ i, S.truncatedEnergyTerm h Ω J Δ L i) k *ᵥ vO)).re := by
  simpa only [actualChargeScanRound_meanEnergy] using
    congrArg Complex.re (star_dotProduct_copyMean_augmentOperator q d k
      (∑ i, S.truncatedEnergyTerm h Ω J Δ L i)
      (Matrix.Transport.filteredVector
        ((S.actualChargeData hm hM s).rootPath
          (augmentedDimensions q (fun _ => d)) (a / 2) k p) (pre k)))
end TNLean.PEPS.AreaLaw.Scan.CollarScan

end

end ActualGlobalReplicaEnergy

section ActualReplicaDefect

/-!
## The gap estimate for the actual charge filtered vector

This is an application of the gap-to-projection estimate to the same filtered
vector that defines the actual charge mean energy. The reference vector Ω in
the truncated terms is retained. The gap and defect projection use the same supplied unit vector Ωt.
In the application, Ωt is the chosen ground vector of the truncated Hamiltonian.

Normalization follows from the positive metric root and a nonzero initial
vector. Simultaneous symmetry and auxiliary labels remain explicit conditions
on that actual vector. Their construction is a separate step; this conditional
statement does not construct physical scanner data.

Source: OpenAI, A two-dimensional area law from a global spectral gap,
07-comparators.tex, comparator:defect-mass, lines 421--443;
08-scanner.tex, lines 371--384 and 416--451, revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section
open Matrix TensorPower TensorPower.ReplicaTransport PermutationRepresentation
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder

open ManyBody (AdmissibleSupport PlaneInteraction)

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open Classical in
/-- The literal actual charge filtered vector is normalized at every copy
count and every real interpolation parameter. Its root is positive definite
by the actual charge geometry; the parameter is clamped by the definition
of the root path. Nonvanishing concerns the same supplied initial vector.
Source: 06-transport.tex, transport:filtered-vector, lines 388--392;
08-scanner.tex, lines 371--384 and 416--451, adc7f124. -/
theorem norm_filteredVector_actualChargeData
    {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
    (S : CollarScan V I) (hm : 0 < S.m) (hM : 0 < S.M) (s : ℕ)
    (n : V ⊕ Bool → ℕ) [∀ x, NeZero (n x)]
    (a : ℝ) (ha : 0 ≤ a) (k : ℕ)
    (pre : Config k (fun x => Fin (n x)) → ℂ) (hpre : pre ≠ 0) (p : ℝ) :
    ‖WithLp.toLp 2
      (Matrix.Transport.filteredVector
        ((S.actualChargeData hm hM s).rootPath n (a / 2) k p) pre)‖ = 1 := by
  classical
  have hroot : ((S.actualChargeData hm hM s).rootPath n (a / 2) k p).PosDef :=
    Matrix.MeanTree.posDef_eval
      ((S.actualChargeData hm hM s).posDef_input
        (S.actualChargeData_isAdmissible hm hM s) (div_nonneg ha (by norm_num))
        (S.chargeTransportData_crossBandCommute _ _ n (div_nonneg ha (by norm_num)) k))
      ((S.actualChargeData hm hM s).tree (Set.projIcc (0 : ℝ) 1 zero_le_one p))
  have hsquare : ‖WithLp.toLp 2
      (Matrix.Transport.filteredVector
        ((S.actualChargeData hm hM s).rootPath n (a / 2) k p) pre)‖ ^ 2 = 1 :=
    (Matrix.re_star_dotProduct_self_eq_norm_sq _).symm.trans
      (congrArg Complex.re (Matrix.Transport.star_dotProduct_filteredVector hroot hpre))
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (hsquare.trans (one_pow 2).symm)

open Classical in
/-- The common low-defect projection of the supplied unit vector
has mass at least one minus the actual charge excess mean energy divided by
the full truncated gap and cutoff fraction. The physical Hamiltonian and
filtered vector are the ones in the actual charge energy identity.
The nonnegative metric parameter and nonzero initial vector are properties
of the physical construction; they are not additional hypotheses of the
area-law theorem. Their derivation from that construction is separate.
Source: 07-comparators.tex, comparator:defect-mass, lines 421--443;
08-scanner.tex, lines 371--384 and 416--451, adc7f124. -/
theorem actualChargeScanRound_globalLowDefectProjection_mass_ge
    {Λ : Finset (ℤ × ℤ)} {q d R : ℕ} {J : ℝ} [NeZero q] [NeZero d]
    [LinearOrder (AdmissibleSupport Λ R)]
    (S : CollarScan ↥Λ (AdmissibleSupport Λ R))
    (hm : 0 < S.m) (hM : 0 < S.M) (s : ℕ)
    (h : PlaneInteraction Λ q R)
    (Ω : EuclideanSpace ℂ (↥Λ → Fin q)) (Δ : ℝ) (L : ℕ)
    (Ωt : EuclideanSpace ℂ (↥Λ → Fin q)) (e₀ g : ℝ)
    (hΩt : ‖Ωt‖ = 1)
    (hgap : ((∑ i, S.truncatedEnergyTerm h Ω J Δ L i) - (e₀ : ℂ) • 1 -
      (g : ℂ) • (1 - Matrix.vecMulVec Ωt.ofLp (star Ωt.ofLp))).PosSemidef)
    (hg : 0 < g) (a : ℝ) (ha : 0 ≤ a)
    (pre : (k : ℕ) → Config k
      (fun v => Fin (augmentedDimensions (V := ↥Λ) q (fun _ => d) v)) → ℂ)
    {k : ℕ} (hk : 0 < k) (hpre : pre k ≠ 0) (p : ℝ)
    (ellC ellR : IrrepLabel (Equiv.Perm (Fin k))) {τ : ℝ} (hτ : 0 < τ) :
    let β := fun _ : ↥Λ => Fin q
    let ι₀ := addedSiteSpace (addedSiteSpace β (Fin d)) (Fin d)
    let n := augmentedDimensions (V := ↥Λ) q (fun _ => d)
    let D := S.actualChargeData hm hM s
    let v := Matrix.Transport.filteredVector (D.rootPath n (a / 2) k p) (pre k)
    let vO : EuclideanSpace ℂ (Config k ι₀) :=
      WithLp.toLp 2 (v ∘ augmentedReplicaConfigurationEquiv q d k)
    symProj (copyPerm ((x : Option (Option ↥Λ)) → ι₀ x) k) *ᵥ vO = vO.ofLp →
    labelProj (subsystemPerm k ι₀ {some none}) ellC *ᵥ vO = vO.ofLp →
    labelProj (subsystemPerm k ι₀ {none}) ellR *ᵥ vO = vO.ofLp →
    1 - ((S.actualChargeScanRound hm hM s n
        (S.actualEnergyTerms h Ω J Δ L (fun _ => d)) a pre).meanEnergy k p - e₀) / g / τ ≤
      (star vO ⬝ᵥ
        (Matrix.globalReplicaLowDefectProjection β (Fin d) (Fin d) Ωt.ofLp
          k ellC ellR τ *ᵥ vO)).re := by
  classical
  intro β ι₀ n D v vO hsym hC hR
  have hvO : ‖vO‖ = 1 :=
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (augmentedReplicaConfigurationEquiv q d k).symm).norm_map
        (WithLp.toLp 2 v)).trans
      (S.norm_filteredVector_actualChargeData hm hM s n a ha k (pre k) hpre p)
  simpa only [n, S.actualChargeScanRound_meanEnergy_eq_globalReplicaMeanHamiltonian
    hm hM s h Ω Δ L a pre k p] using
      Matrix.globalReplicaLowDefectProjection_gap_mass_ge β (Fin d) (Fin d)
        hgap hΩt hg hk ellC ellR hτ vO hvO hsym hC hR

end TNLean.PEPS.AreaLaw.Scan.CollarScan

end

end ActualReplicaDefect
