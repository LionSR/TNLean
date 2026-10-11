/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualEntropySampling

/-!
# Actual old-state entropy integration regressions

The tests retain the actual recursive trees, distinguish terminal old-edge
weights from derivative entropy weights, and keep one old state through
conditional averaging. Zero-band and repeated-support tests cover degenerate
index families without imposing normalization on the coherent vector.
-/

set_option autoImplicit false

open TensorPower TensorPower.ReplicaTransport MeasureTheory
open Entropy (SiteConfig)
open scoped BigOperators ComplexOrder
open TNLean.PEPS.AreaLaw.Scan

namespace TNLeanTest.ActualTransportedEntropy

/-- A concrete scanner with an inhabited history family and no bands. -/
private def zeroBandScan : CollarScan (Fin 1) (Fin 2) where
  graph := ⊥
  A := Finset.univ
  depth := fun _ => 0
  anchor := fun _ => 0
  n := 2
  m := 4
  K := 0
  D := 1
  r₀ := 0
  C₁ := 6

private theorem zeroBandScan_m_pos : 0 < zeroBandScan.m := by decide

private theorem zeroBandScan_M_pos : 0 < zeroBandScan.M := by
  norm_num [CollarScan.M, chargeSlotCount, zeroBandScan]

/-- No-band histories have an explicit member for every history length. -/
private def zeroBandHistory (k : ℕ) :
    History zeroBandScan.K zeroBandScan.m zeroBandScan.M k :=
  ⟨Fin.elim0, fun _ => Fin.elim0⟩

example : (zeroBandScan.actualChargeData zeroBandScan_m_pos zeroBandScan_M_pos 2).IsAdmissible :=
  zeroBandScan.actualChargeData_isAdmissible zeroBandScan_m_pos zeroBandScan_M_pos 2

example : historyWeight (zeroBandHistory 2) = 1 := by
  simp [historyWeight, zeroBandScan]

-- This zero-band conclusion is inhabited; no premise asks for an impossible band.
example (n : Fin 1 ⊕ Bool → ℕ) [∀ v, NeZero (n v)] (t : ℝ) (r : ℕ)
    (pre : Config r (fun v => Fin (n v)) → ℂ) (p : ℝ) :
    (zeroBandScan.actualChargeData zeroBandScan_m_pos zeroBandScan_M_pos 2).entropyGain
      n t r pre p = 0 := by
  unfold TransportData.entropyGain
  apply Finset.sum_eq_zero
  intro h _
  apply Finset.sum_eq_zero
  intro g _
  exact Fin.elim0 g

/-- A support that actually meets the near side and middle, but not the far side. -/
private def splitPartition : PYF (Fin 3) := ⟨{0}, {1}, {2}⟩

example : splitPartition.IsPartition ∧ splitPartition.SplitsToP {0, 1} ∧
    ¬ splitPartition.Contains {0, 1} := by
  unfold PYF.IsPartition PYF.SplitsToP PYF.Contains splitPartition
  decide

example : splitPartition.SplitsToF {1, 2} ∧
    ¬ splitPartition.Contains {1, 2} := by
  unfold PYF.SplitsToF PYF.Contains splitPartition
  decide

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]

-- The combined measure uses the actual old leaf, including at p = 1.
example (S : CollarScan V I) (hm : 0 < S.m) (hM : 0 < S.M) (k : ℕ)
    (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)] (t : ℝ) (r : ℕ)
    (pre : Config r (fun v => Fin (n v)) → ℂ) (h : History S.K S.m S.M k)
    (f : (SiteConfig n → ℂ) → ℝ) :
    (S.actualChargeData hm hM k).oldFourierCoherentIntegral n t r pre 1 h f =
      ∫ u, Matrix.Transport.fourierWeight u * realCoherentIntegral r (TransportData.base n)
        ((S.actualChargeData hm hM k).state n t r pre 1 ⟨h, none⟩ u) f := rfl

-- Choice-dependent symbols are integrated against one common old state.
example (S : CollarScan V I) (hm : 0 < S.m) (hM : 0 < S.M) (k : ℕ)
    (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)] (t : ℝ) (r : ℕ)
    (pre : Config r (fun v => Fin (n v)) → ℂ) (p : ℝ)
    (h : History S.K S.m S.M k)
    (f : ChargeChoices S.K S.M → (SiteConfig n → ℂ) → ℝ)
    (hf : ∀ c, Continuous (f c)) :
    (S.actualChargeData hm hM k).oldFourierCoherentIntegral n t r pre p h
        (fun θ => ∑ c, chargeWeight c * f c θ) =
      ∑ c, chargeWeight c *
        (S.actualChargeData hm hM k).oldFourierCoherentIntegral n t r pre p h (f c) := by
  refine ((S.actualChargeData hm hM k).oldFourierCoherentIntegral_sum n t r pre p h
    Finset.univ (fun c θ => chargeWeight c * f c θ)
    (fun c _ => continuous_const.mul (hf c))).trans ?_
  apply Finset.sum_congr rfl
  intro c _
  exact (S.actualChargeData hm hM k).oldFourierCoherentIntegral_const_mul
    n t r pre p h (chargeWeight c) (f c)

-- A constant has mass c/2 on actual trees, with all source-state premises retained.
example (S : CollarScan V I) (hm : 0 < S.m) (hM : 0 < S.M) (k : ℕ)
    (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)] {t : ℝ} (ht : 0 ≤ t) (r : ℕ)
    {pre : Config r (fun v => Fin (n v)) → ℂ}
    (hsym : pre ∈ symmetricSubspace r (fun v => Fin (n v))) (hpre : pre ≠ 0)
    {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (h : History S.K S.m S.M k) (c : ℝ) :
    (S.actualChargeData hm hM k).oldFourierCoherentIntegral n t r pre p h
      (fun _ => c) = c / 2 := by
  have hmass := (S.actualChargeData hm hM k).oldFourierCoherentIntegral_one n
    (S.actualChargeData_isAdmissible hm hM k) ht
    (S.chargeTransportData_crossBandCommute _ _ n ht r) hsym hpre hp h
  have hscale := (S.actualChargeData hm hM k).oldFourierCoherentIntegral_const_mul
    n t r pre p h c (fun _ => 1)
  simpa only [mul_one, hmass, div_eq_mul_inv, one_mul] using hscale

-- Terminal old leaves do carry the old-edge factor.
example (S : CollarScan V I) (hm : 0 < S.m) (hM : 0 < S.M) (k : ℕ)
    (p : unitInterval) (h : History S.K S.m S.M k) :
    (Matrix.MeanTree.interpTree (S.actualChargeData hm hM k).histTree
      (S.actualChargeData hm hM k).choiceTree p).weight ⟨h, none⟩ =
        (1 - (p : ℝ)) * historyWeight h :=
  historyMeanTree_interp_weight_old S.K S.m S.M hm hM k p h

-- The derivative entropy gain does not carry that terminal old-edge factor.
example (S : CollarScan V I) (hm : 0 < S.m) (hM : 0 < S.M) (k : ℕ)
    (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)] (t : ℝ) (r : ℕ)
    (pre : Config r (fun v => Fin (n v)) → ℂ) (p : ℝ) :
    (S.actualChargeData hm hM k).entropyGain n t r pre p =
      ∑ h, historyWeight h *
        (S.actualChargeData hm hM k).oldFourierCoherentIntegral n t r pre p h
          ((S.actualChargeData hm hM k).choiceEntropySymbol n h) := by
  rw [TransportData.entropyGain_eq_sum_oldFourierCoherentIntegral]
  simp only [CollarScan.actualChargeData, CollarScan.chargeTransportData,
    historyMeanTree_weight]

-- Zero bands have no entropy integrand, for every coherent vector.
example (S : CollarScan V I) (hK : S.K = 0) (hm : 0 < S.m) (hM : 0 < S.M)
    (k : ℕ) (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)]
    (h : History S.K S.m S.M k) (θ : SiteConfig n → ℂ) :
    (S.actualChargeData hm hM k).choiceEntropySymbol n h θ = 0 := by
  apply Finset.sum_eq_zero
  intro g _
  have hg := g.isLt
  omega

-- Two interaction labels with the same support remain two split-entropy summands.
-- Their energy operators need not be equal.
example (S : CollarScan V (Fin 2)) (hm : 0 < S.m) (hM : 0 < S.M) (k : ℕ)
    (n : V ⊕ Bool → ℕ) (E : EnergyTerms (V ⊕ Bool) n (Fin 2))
    (hsupport : E.support 1 = E.support 0) (h : History S.K S.m S.M k)
    (θ : EuclideanSpace ℂ (SiteConfig n)) :
    (∑ i, (S.actualChargeData hm hM k).splitEta E i ⟨h, none⟩ θ) =
      2 * (S.actualChargeData hm hM k).splitEta E 0 ⟨h, none⟩ θ := by
  classical
  let D := S.actualChargeData hm hM k
  have hsplit : D.splitEta E 1 ⟨h, none⟩ θ = D.splitEta E 0 ⟨h, none⟩ θ := by
    delta TransportData.splitEta
    exact congrArg (fun B : Finset (V ⊕ Bool) =>
      ∑ g ∈ Finset.univ.filter (fun g => ¬ (D.leafPart ⟨h, none⟩ g).Contains B),
        splitBandEta n (D.leafPart ⟨h, none⟩ g) B θ) hsupport
  change (∑ i, D.splitEta E i ⟨h, none⟩ θ) = 2 * D.splitEta E 0 ⟨h, none⟩ θ
  rw [Fin.sum_univ_two, hsplit]
  ring

-- The actual old endpoint is the same retained history-tree evaluation.
example (S : CollarScan V I) (hm : 0 < S.m) (hM : 0 < S.M) (k : ℕ)
    {N : Type*} [Fintype N] [DecidableEq N]
    (A : History S.K S.m S.M k → Matrix N N ℂ)
    (B : History S.K S.m S.M (k + 1) → Matrix N N ℂ)
    (hA : ∀ h, (A h).PosDef) (hB : ∀ h, (B h).PosDef) :
    Matrix.Transport.interpRoot (S.actualChargeData hm hM k).histTree
      (S.actualChargeData hm hM k).choiceTree A
      (fun h c => B (extendHistory h c)) 0 =
        (S.actualChargeData hm hM k).histTree.eval A :=
  charge_interpRoot_zero S.K S.m S.M hm hM k A B hA hB

-- The actual recursive charge trees retain their new endpoint exactly.
example (S : CollarScan V I) (hm : 0 < S.m) (hM : 0 < S.M) (k : ℕ)
    {N : Type*} [Fintype N] [DecidableEq N]
    (A : History S.K S.m S.M k → Matrix N N ℂ)
    (B : History S.K S.m S.M (k + 1) → Matrix N N ℂ)
    (hA : ∀ h, (A h).PosDef) (hB : ∀ h, (B h).PosDef) :
    Matrix.Transport.interpRoot (S.actualChargeData hm hM k).histTree
      (S.actualChargeData hm hM k).choiceTree A
      (fun h c => B (extendHistory h c)) 1 =
        (S.actualChargeData hm hM (k + 1)).histTree.eval B :=
  charge_interpRoot_one S.K S.m S.M hm hM k A B hA hB

end TNLeanTest.ActualTransportedEntropy
