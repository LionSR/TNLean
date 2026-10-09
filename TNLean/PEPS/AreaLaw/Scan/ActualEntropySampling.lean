/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualChargeData
import TNLean.PEPS.AreaLaw.Scan.SplitEntropyCost
import TNLean.PEPS.AreaLaw.Scan.OldStateIntegral
import TNLean.PEPS.AreaLaw.Scan.SupportCompatibility
import QICLean.Representation.ReplicaTransport.Energy

/-!
# Actual split entropy sampled in the old transported state

Physical support compatibility is derived from the actual geometry, then the
pointwise classical sampling inequality is identified with the canonical
old-leaf split entropy. Fourier and coherent integration use the same actual
old state for every conditional choice. Good histories contribute the split
cost; all remaining histories contribute nonnegative move entropy.

This proves the entropy sampling portion only. It does not construct a
pre-vector, typical sector, comparator estimate, or complete scanner data.
The integral inequality uses positivity; its probability interpretation for
a nonzero symmetric pre-vector at an interior parameter is supplied by the
separate old-state mass theorem.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 424–451, and `06-transport.tex`, lines 390–412,
at `openai/math@adc7f124`.
-/

open scoped BigOperators
open TensorPower TensorPower.ReplicaTransport

noncomputable section

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]

/-- The actual good-old-history split entropy cost, using the actual old
transported state, Fourier weight and coherent integral. -/
def actualChargeEntropyDefect (S : CollarScan V I) (hm : 0 < S.m) (hM : 0 < S.M)
    (k : ℕ) (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)]
    (E : EnergyTerms (V ⊕ Bool) n I) (t : ℝ) (r : ℕ)
    (pre : Config r (fun v => Fin (n v)) → ℂ) (p : ℝ) : ℝ := by
  classical
  let D := S.actualChargeData hm hM k
  exact ∑ h, if S.IsGoodOldHistory h then
    historyWeight h * D.oldFourierCoherentIntegral n t r pre p h
      (fun θ => ∑ i, D.splitEta E i ⟨h, none⟩ ((EuclideanSpace.equiv _ ℂ).symm θ))
  else 0

/-- Actual physical geometry supplies compatibility; good-history sampling
then dominates the actual old-leaf split entropy, pointwise in one vector. -/
theorem good_sum_splitEta_le_choiceEntropySymbol_domainGraph
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x => ambientDepth T hT x.val) {k L μ : ℕ}
    (hm0 : 0 < S.m) (hM : 0 < S.M) (h : History S.K S.m S.M k)
    (n : Site Λ ⊕ Bool → ℕ) [∀ v, NeZero (n v)]
    (E : EnergyTerms (Site Λ ⊕ Bool) n I)
    (hsupport : ∀ i, E.support i =
      (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i)).map
        ⟨Sum.inl, Sum.inl_injective⟩)
    (hn : 2 ≤ S.n) (hm : 2 ≤ S.m) (hk : k + 1 ≤ S.n * S.m)
    (hr : 2 * S.r₀ ≤ S.D) (hD : 4 * S.D ≤ S.m) (hDpos : 1 ≤ S.D)
    (hL : 8 * S.K * S.m ≤ L) (hC : 3 * (μ : ℝ) ≤ S.C₁)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hmult : ∀ x, (Finset.univ.filter fun i => S.anchor i = x).card ≤ μ)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    (hgood : S.IsGoodOldHistory h) (θ : SiteConfig n → ℂ) :
    ((1 / (2 * (S.C₁ + 1))) / ((S.n : ℝ) * S.D)) *
        (∑ i, (S.actualChargeData hm0 hM k).splitEta E i ⟨h, none⟩
          ((EuclideanSpace.equiv _ ℂ).symm θ)) ≤
      (S.actualChargeData hm0 hM k).choiceEntropySymbol n h θ := by
  classical
  let histTree := historyMeanTree S.K S.m S.M hm0 hM k
  let choiceTree := fun _ : History S.K S.m S.M k => chargeChoiceTree S.K S.M hM
  have hcompat := chargeTransportData_supportCompatible_domainGraph hT S hgraph hdepth
    histTree choiceTree (by omega) hk (by omega) hDpos hD hL hrows hclear n E hsupport
  have heta := S.designatedSplitIncidenceCost_eq_sum_splitEta n histTree choiceTree E
    hsupport hcompat h ((EuclideanSpace.equiv _ ℂ).symm θ)
  have hbound := (good_designatedEntropyCost_le_expected_chargeEta_domainGraph hT S
    hgraph hdepth h n ((EuclideanSpace.equiv _ ℂ).symm θ)
    hn hm hk hr hD hDpos hL hC hrows hmult hclear hgood).2
  have hchoice : (S.actualChargeData hm0 hM k).choiceEntropySymbol n h θ =
      ∑ c : ChargeChoices S.K S.M, chargeWeight c *
        ∑ g, moveEta n (augmentedPartition (S.oldChargeState h g))
          (S.quantumChargeMove g (h.1 g) (k + 1) (c g) (S.oldChargeState h g))
          ((EuclideanSpace.equiv _ ℂ).symm θ) := by
    simp only [TransportData.choiceEntropySymbol, actualChargeData, chargeTransportData,
      chargeChoiceTree_weight, Finset.mul_sum]
    exact Finset.sum_comm
  rw [hchoice]
  rw [heta] at hbound
  exact hbound

/-- The actual entropy gain dominates the good-old-history split cost with
the physical sampling coefficient. The same old state is used on both sides
for each history and Fourier parameter; no sampling or compatibility field
is assumed. -/
theorem actualChargeEntropyDefect_le_entropyGain_domainGraph
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x => ambientDepth T hT x.val) {k L μ : ℕ}
    (hm0 : 0 < S.m) (hM : 0 < S.M)
    (n : Site Λ ⊕ Bool → ℕ) [∀ v, NeZero (n v)]
    (E : EnergyTerms (Site Λ ⊕ Bool) n I)
    (hsupport : ∀ i, E.support i =
      (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i)).map
        ⟨Sum.inl, Sum.inl_injective⟩)
    (hn : 2 ≤ S.n) (hm : 2 ≤ S.m) (hk : k + 1 ≤ S.n * S.m)
    (hr : 2 * S.r₀ ≤ S.D) (hD : 4 * S.D ≤ S.m) (hDpos : 1 ≤ S.D)
    (hL : 8 * S.K * S.m ≤ L) (hC : 3 * (μ : ℝ) ≤ S.C₁)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hmult : ∀ x, (Finset.univ.filter fun i => S.anchor i = x).card ≤ μ)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    {t : ℝ} (ht : 0 ≤ t) (r : ℕ)
    (pre : Config r (fun v => Fin (n v)) → ℂ) (p : ℝ) :
    ((1 / (2 * (S.C₁ + 1))) / ((S.n : ℝ) * S.D)) *
        S.actualChargeEntropyDefect hm0 hM k n E t r pre p ≤
      (S.actualChargeData hm0 hM k).entropyGain n t r pre p := by
  classical
  let D := S.actualChargeData hm0 hM k
  let F (h : History S.K S.m S.M k) (θ : SiteConfig n → ℂ) :=
    ∑ i, D.splitEta E i ⟨h, none⟩ ((EuclideanSpace.equiv _ ℂ).symm θ)
  let α : ℝ := (1 / (2 * (S.C₁ + 1))) / ((S.n : ℝ) * S.D)
  have hAdm : D.IsAdmissible := S.actualChargeData_isAdmissible hm0 hM k
  have hcomm : D.CrossBandCommute n t r :=
    S.chargeTransportData_crossBandCommute _ _ n ht r
  have hF (h : History S.K S.m S.M k) : Continuous (F h) := by
    unfold F TransportData.splitEta
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun g _ =>
      continuous_splitBandEta _ _
  change α * (∑ h, if S.IsGoodOldHistory h then
      historyWeight h * D.oldFourierCoherentIntegral n t r pre p h (F h) else 0) ≤
    D.entropyGain n t r pre p
  rw [D.entropyGain_eq_sum_oldFourierCoherentIntegral n t r pre p, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro h _
  have hw : D.histTree.weight h = historyWeight h := historyMeanTree_weight _ _ _ hm0 hM k h
  rw [hw]
  by_cases hg : S.IsGoodOldHistory h
  · simp only [hg, ↓reduceIte]
    rw [mul_left_comm]
    apply mul_le_mul_of_nonneg_left _ (historyWeight_nonneg h)
    rw [← D.oldFourierCoherentIntegral_const_mul n t r pre p h α (F h)]
    apply D.oldFourierCoherentIntegral_mono n hAdm ht hcomm pre p h
      (continuous_const.mul (hF h)) (D.continuous_choiceEntropySymbol n h)
    intro θ
    exact good_sum_splitEta_le_choiceEntropySymbol_domainGraph hT S hgraph hdepth hm0 hM h
      n E hsupport hn hm hk hr hD hDpos hL hC hrows hmult hclear hg θ
  · simp only [hg, ↓reduceIte, mul_zero]
    exact mul_nonneg (historyWeight_nonneg h)
      (D.oldFourierCoherentIntegral_nonneg n hAdm ht hcomm pre p h
        (D.continuous_choiceEntropySymbol n h) (D.choiceEntropySymbol_nonneg n hAdm h))

end TNLean.PEPS.AreaLaw.Scan.CollarScan
