/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Representation.ReplicaTransport.LeafMeasure
import QICLean.Representation.ReplicaTransport.Energy
import TNLean.PEPS.AreaLaw.Scan.Defs
import TNLean.PEPS.AreaLaw.Scan.OldStateIntegral

/-!
# A scan round on the literal coherent sphere

The two measures are the canonical Fourier-weighted measures of the old and new
leaves of one transport datum. Both use the same supplied replica vector and root
path. History and conditional-choice weights remain outside these measures.
This is data for one round, not a construction of `ScanData` or a choice of prevector.

The pending upstream `LeafMeasure` import makes this a source-only, uncompiled
candidate until the upstream API is accepted and a dependency update is authorized.
No parameter-continuity or comparator assertion follows from fixed-parameter finiteness.

Source: *A two-dimensional area law from a global spectral gap*, Proposition 7.4,
`06-transport.tex`, lines 364–434, and `08-scanner.tex`, lines 416–451.
-/

open scoped BigOperators Matrix unitInterval
open Matrix MeasureTheory Set
open TensorPower TensorPower.ReplicaTransport Entropy

noncomputable section

namespace TensorPower.ReplicaTransport.TransportData

variable {V H ι : Type} [Fintype V] [DecidableEq V] {K : ℕ}
  [Fintype H] [DecidableEq H] {C : H → Type}
  [∀ h, Fintype (C h)] [∀ h, DecidableEq (C h)]
  {n : V → ℕ} (D : TransportData V K H C) (E : EnergyTerms V n ι)

omit [DecidableEq H] [∀ h, DecidableEq (C h)] in
/-- An unsplit leaf has identically zero split entropy, directly from the defining
sum over exceptional bands (`06-transport.tex`, lines 342–347). -/
theorem splitEta_eq_zero_of_not_mem_splitLeaves {i : ι} {j : Σ h, Option (C h)}
    (hj : j ∉ D.splitLeaves E i) (θ : EuclideanSpace ℂ (SiteConfig n)) :
    D.splitEta E i j θ = 0 := by
  classical
  simp [splitEta, D.forall_contains_of_not_mem_splitLeaves E hj]

end TensorPower.ReplicaTransport.TransportData

namespace TNLean.PEPS.AreaLaw.Scan

variable {V H ι : Type} [Fintype V] [DecidableEq V] {K : ℕ}
  [Fintype H] [DecidableEq H] {C : H → Type}
  [∀ h, Fintype (C h)] [∀ h, DecidableEq (C h)] [Fintype ι]
  (D : TransportData V K H C) (n : V → ℕ) [∀ v, NeZero (n v)]
  (E : EnergyTerms V n ι) (good : H → Prop) (t : ℝ)
  (pre : (k : ℕ) → Config k (fun v => Fin (n v)) → ℂ)

/-- The literal data of a round on the unit sphere. No analytic conclusion is a
field supplied to this constructor (`06-transport.tex`, lines 377–420). -/
def transportScanRound : ScanRound ι (CoherentSphere (SiteConfig n)) where
  H := H
  Ch := C
  w := D.histTree.weight
  q := fun h => (D.choiceTree h).weight
  good := good
  splitOld := fun i h => ⟨h, none⟩ ∈ D.splitLeaves E i
  splitNew := fun i h c => ⟨h, some c⟩ ∈ D.splitLeaves E i
  etaOld := fun i h θ => D.splitEta E i ⟨h, none⟩ θ.1
  etaNew := fun i h c θ => D.splitEta E i ⟨h, some c⟩ θ.1
  choiceGain := fun h θ => D.choiceEntropySymbol n h (fun x => θ.1 x)
  μOld := fun k p h => D.transportLeafMeasure n t k (pre k) p ⟨h, none⟩
  μNew := fun k p h c => D.transportLeafMeasure n t k (pre k) p ⟨h, some c⟩
  logNormSq := fun k p => Real.log (Transport.filteredNormSq (D.rootPath n t k p) (pre k))
  meanEnergy := fun k p =>
    let v := Transport.filteredVector (D.rootPath n t k p) (pre k)
    (star v ⬝ᵥ (E.replicaEnergy k *ᵥ v)).re

/-- Old measures are finite for every real parameter and every supplied vector. -/
instance isFiniteMeasure_transportScanRound_old (k : ℕ) (p : ℝ) (h : H) :
    IsFiniteMeasure ((transportScanRound D n E good t pre).μOld k p h) :=
  D.isFiniteMeasure_transportLeafMeasure n t k (pre k) p ⟨h, none⟩

/-- New measures are finite for every real parameter and every supplied vector. -/
instance isFiniteMeasure_transportScanRound_new (k : ℕ) (p : ℝ) (h : H) (c : C h) :
    IsFiniteMeasure ((transportScanRound D n E good t pre).μNew k p h c) :=
  D.isFiniteMeasure_transportLeafMeasure n t k (pre k) p ⟨h, some c⟩

/-- Integrating on the literal old sphere gives the existing same-old-state integral. -/
theorem integral_transportScanRound_old (hD : D.IsAdmissible) (ht : 0 ≤ t)
    (k : ℕ) (hcomm : D.CrossBandCommute n t k) (p : ℝ) (h : H)
    {f : (SiteConfig n → ℂ) → ℝ} (hf : Continuous f) :
    (∫ θ, f (fun x => θ.1 x) ∂(transportScanRound D n E good t pre).μOld k p h) =
      D.oldFourierCoherentIntegral n t k (pre k) p h f :=
  D.integral_transportLeafMeasure n t k (pre k) p ⟨h, none⟩ hD ht hcomm hf

/-- The new sphere integral retains the actual new terminal state. -/
theorem integral_transportScanRound_new (hD : D.IsAdmissible) (ht : 0 ≤ t)
    (k : ℕ) (hcomm : D.CrossBandCommute n t k) (p : ℝ) (h : H) (c : C h)
    {f : (SiteConfig n → ℂ) → ℝ} (hf : Continuous f) :
    (∫ θ, f (fun x => θ.1 x) ∂(transportScanRound D n E good t pre).μNew k p h c) =
      ∫ u, Transport.fourierWeight u *
        realCoherentIntegral k (TransportData.base n) (D.state n t k (pre k) p ⟨h, some c⟩ u) f :=
  D.integral_transportLeafMeasure n t k (pre k) p ⟨h, some c⟩ hD ht hcomm hf

/-- Both leaf kinds have Fourier mass one half at every interior parameter, including
zero copies when the supplied scalar vector is nonzero. -/
theorem transportScanRound_mass (hD : D.IsAdmissible) (ht : 0 ≤ t)
    (k : ℕ) (hcomm : D.CrossBandCommute n t k)
    (hsym : pre k ∈ symmetricSubspace k (fun v => Fin (n v))) (hpre : pre k ≠ 0)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (h : H) :
    ((transportScanRound D n E good t pre).μOld k p h).real univ = 1 / 2 ∧
      ∀ c, ((transportScanRound D n E good t pre).μNew k p h c).real univ = 1 / 2 :=
  ⟨D.transportLeafMeasure_real_univ n t k (pre k) p ⟨h, none⟩ hD ht hcomm hsym hpre hp,
    fun c => D.transportLeafMeasure_real_univ n t k (pre k) p ⟨h, some c⟩
      hD ht hcomm hsym hpre hp⟩

/-- The two inactive endpoint leaves remain zero measures. -/
theorem transportScanRound_inactive (k : ℕ) (h : H) :
    (transportScanRound D n E good t pre).μOld k 1 h = 0 ∧
      ∀ c, (transportScanRound D n E good t pre).μNew k 0 h c = 0 :=
  ⟨D.transportLeafMeasure_old_one n t k (pre k) h,
    fun c => D.transportLeafMeasure_new_zero n t k (pre k) h c⟩

/-- At the complementary active endpoints the same nonzero symmetric vector still
has Fourier mass one half; no replacement probability measure is chosen. -/
theorem transportScanRound_active (hD : D.IsAdmissible) (ht : 0 ≤ t)
    (k : ℕ) (hcomm : D.CrossBandCommute n t k)
    (hsym : pre k ∈ symmetricSubspace k (fun v => Fin (n v))) (hpre : pre k ≠ 0)
    (h : H) :
    ((transportScanRound D n E good t pre).μOld k 0 h).real univ = 1 / 2 ∧
      ∀ c, ((transportScanRound D n E good t pre).μNew k 1 h c).real univ = 1 / 2 := by
  constructor
  · apply D.transportLeafMeasure_real_univ_of_weight_ne_zero n t k (pre k) 0
      ⟨h, none⟩ hD ht hcomm hsym hpre
    simpa [TransportData.tree, MeanTree.weight_interpTree_old] using
      (hD.histWeight_pos h).ne'
  · intro c
    apply D.transportLeafMeasure_real_univ_of_weight_ne_zero n t k (pre k) 1
      ⟨h, some c⟩ hD ht hcomm hsym hpre
    rw [TransportData.tree, MeanTree.weight_interpTree_new]
    simpa using
      (mul_pos (hD.histWeight_pos h) (hD.choiceWeight_pos h c)).ne'

/-- Choice gain uses history weights without a terminal factor `1 - p` and the same
old state for all choices. The identity holds at every real parameter. -/
theorem transportScanRound_choiceGainSum (hD : D.IsAdmissible) (ht : 0 ≤ t)
    (k : ℕ) (hcomm : D.CrossBandCommute n t k) (p : ℝ) :
    (transportScanRound D n E good t pre).choiceGainSum k p =
      D.entropyGain n t k (pre k) p := by
  rw [D.entropyGain_eq_sum_oldFourierCoherentIntegral n t k (pre k) p]
  apply Finset.sum_congr rfl
  intro h _
  exact congrArg (fun x : ℝ => D.histTree.weight h * x)
    (integral_transportScanRound_old D n E good t pre hD ht k hcomm p h
      (D.continuous_choiceEntropySymbol n h))

open Classical in
/-- The charge defect is the good-history average of the literal old split entropy.
The split indicator disappears because an unsplit leaf has zero split entropy. -/
theorem transportScanRound_chargeDefect (hD : D.IsAdmissible) (ht : 0 ≤ t)
    (k : ℕ) (hcomm : D.CrossBandCommute n t k) (p : ℝ) :
    (transportScanRound D n E good t pre).chargeDefect k p =
      ∑ h, if good h then D.histTree.weight h *
        D.oldFourierCoherentIntegral n t k (pre k) p h
          (fun θ => ∑ i, D.splitEta E i ⟨h, none⟩ ((EuclideanSpace.equiv _ ℂ).symm θ))
      else 0 := by
  classical
  unfold ScanRound.chargeDefect
  dsimp only [transportScanRound]
  apply Finset.sum_congr rfl
  intro h _
  change (if good h then D.histTree.weight h * _ else 0) = _
  by_cases hg : good h
  · simp only [hg, ↓reduceIte]
    congr 1
    have hcont (i : ι) : Continuous fun θ : SiteConfig n → ℂ =>
        D.splitEta E i ⟨h, none⟩ ((EuclideanSpace.equiv _ ℂ).symm θ) := by
      unfold TransportData.splitEta
      exact continuous_finsetSum _ fun g _ => continuous_splitBandEta _ _
    rw [D.oldFourierCoherentIntegral_sum n t k (pre k) p h Finset.univ _
      (fun i _ => hcont i)]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : (⟨h, none⟩ : Σ h, Option (C h)) ∈ D.splitLeaves E i
    · simp only [hi, ↓reduceIte]
      exact integral_transportScanRound_old D n E good t pre hD ht k hcomm p h (hcont i)
    · simp only [hi, ↓reduceIte]
      simp [D.splitEta_eq_zero_of_not_mem_splitLeaves E hi,
        TransportData.oldFourierCoherentIntegral, realCoherentIntegral]
  · simp only [hg, ↓reduceIte]

end TNLean.PEPS.AreaLaw.Scan
