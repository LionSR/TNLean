/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualChargeEnergyBound

/-!
# Charge energy at zero capacity and zero good-history weight

The supplied-vector signature keeps the stronger geometric margin and the
interior interpolation parameter. Zero bands, zero anchor multiplicity and
zero good-history weight require no division or positive-capacity assumption.
-/

set_option autoImplicit false

open scoped BigOperators Matrix
open MeasureTheory Set TensorPower TensorPower.ReplicaTransport Entropy
open TNLean.PEPS.AreaLaw TNLean.PEPS.AreaLaw.Scan

noncomputable section

namespace TNLeanTest.ActualChargeEnergyBound

open Classical in
/-- The full supplied-vector statement has arbitrary positive auxiliary
sizes and every natural replica count, with no norm-one assumption. -/
theorem capstone_signature
    {Λ T : Finset (ℤ × ℤ)} {q R : ℕ} {J : ℝ} [NeZero q]
    [LinearOrder (AdmissibleSupport Λ R)]
    (hT : T.Nonempty) (S : CollarScan (Site Λ) (AdmissibleSupport Λ R))
    (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
    (aux : Bool → ℕ) [∀ b, NeZero (aux b)]
    (h : LocalHamiltonian Λ q R J) (Ω : StateSpace Λ q) (Δ : ℝ)
    {s L μ : ℕ} (hn : 2 ≤ S.n) (hs : s + 1 ≤ S.n * S.m)
    (hr : S.r₀ ≤ S.D) (hDpos : 1 ≤ S.D)
    (hmargin : 4 * (S.D + 2 * S.r₀) ≤ S.m)
    (hL : 8 * S.K * S.m ≤ L) (hC : 0 < S.C₁)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hmult : ∀ x, (Finset.univ.filter fun i ↦ S.anchor i = x).card ≤ μ)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    {a : ℝ} (ha : 0 ≤ a) (k : ℕ)
    (pre : (r : ℕ) → Config r
      (fun v ↦ Fin (augmentedDimensions (V := Site Λ) q aux v)) → ℂ)
    (hsym : pre k ∈ symmetricSubspace k
      (fun v ↦ Fin (augmentedDimensions (V := Site Λ) q aux v)))
    (hpre : pre k ≠ 0) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    let hm : 0 < S.m := by omega
    let hM : 0 < S.M := chargeSlotCount_pos hC (by omega) hDpos
    let n := augmentedDimensions (V := Site Λ) q aux
    let E := S.actualEnergyTerms h Ω Δ L aux
    let A : ℝ := 10 * S.K * S.n * S.D * μ
    let ℓ := transportLogDimBound q S.r₀
    let b := ∑ hist : History S.K S.m S.M s,
      if S.IsGoodOldHistory hist then 0 else historyWeight hist
    (S.actualChargeData hm hM s).energyError E (a / 2) k (pre k) p ≤
      (10 * (S.D : ℝ) / S.m) *
        ((1 - p) * A ^ (7 / 8 : ℝ) *
          (S.actualChargeEntropyDefect hm hM s n E (a / 2) k (pre k) p) ^ (1 / 8 : ℝ) +
          A * (2 * ℓ) ^ (1 / 8 : ℝ) / 2 * ((1 - p) * b + p)) :=
  CollarScan.actualCharge_energyError_le_domainGraph hT S hgraph hdepth aux h Ω Δ
    hn hs hr hDpos hmargin hL hC hrows hmult hclear ha k pre hsym hpre hp

open Classical in
/-- Zero bands give a zero charge energy bound for the actual transport. -/
theorem zero_band_energy
    {Λ T : Finset (ℤ × ℤ)} {q R : ℕ} {J : ℝ} [NeZero q]
    [LinearOrder (AdmissibleSupport Λ R)]
    (hT : T.Nonempty) (S : CollarScan (Site Λ) (AdmissibleSupport Λ R))
    (hK : S.K = 0) (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
    (aux : Bool → ℕ) [∀ b, NeZero (aux b)]
    (h : LocalHamiltonian Λ q R J) (Ω : StateSpace Λ q) (Δ : ℝ)
    {s L μ : ℕ} (hn : 2 ≤ S.n) (hs : s + 1 ≤ S.n * S.m)
    (hr : S.r₀ ≤ S.D) (hDpos : 1 ≤ S.D)
    (hmargin : 4 * (S.D + 2 * S.r₀) ≤ S.m)
    (hL : 8 * S.K * S.m ≤ L) (hC : 0 < S.C₁)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hmult : ∀ x, (Finset.univ.filter fun i ↦ S.anchor i = x).card ≤ μ)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    {a : ℝ} (ha : 0 ≤ a) (k : ℕ)
    (pre : (r : ℕ) → Config r
      (fun v ↦ Fin (augmentedDimensions (V := Site Λ) q aux v)) → ℂ)
    (hsym : pre k ∈ symmetricSubspace k
      (fun v ↦ Fin (augmentedDimensions (V := Site Λ) q aux v)))
    (hpre : pre k ≠ 0) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    let hm : 0 < S.m := by omega
    let hM : 0 < S.M := chargeSlotCount_pos hC (by omega) hDpos
    let E := S.actualEnergyTerms h Ω Δ L aux
    (S.actualChargeData hm hM s).energyError E (a / 2) k (pre k) p ≤ 0 := by
  have hbound := CollarScan.actualCharge_energyError_le_domainGraph hT S hgraph hdepth aux h Ω Δ
    hn hs hr hDpos hmargin hL hC hrows hmult hclear ha k pre hsym hpre hp
  dsimp only at hbound ⊢
  simpa [hK, Real.zero_rpow (by norm_num : (7 / 8 : ℝ) ≠ 0)] using hbound

open Classical in
/-- Zero anchor multiplicity gives the same zero bound without division. -/
theorem zero_multiplicity_energy
    {Λ T : Finset (ℤ × ℤ)} {q R : ℕ} {J : ℝ} [NeZero q]
    [LinearOrder (AdmissibleSupport Λ R)]
    (hT : T.Nonempty) (S : CollarScan (Site Λ) (AdmissibleSupport Λ R))
    (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
    (aux : Bool → ℕ) [∀ b, NeZero (aux b)]
    (h : LocalHamiltonian Λ q R J) (Ω : StateSpace Λ q) (Δ : ℝ)
    {s L μ : ℕ} (hn : 2 ≤ S.n) (hs : s + 1 ≤ S.n * S.m)
    (hr : S.r₀ ≤ S.D) (hDpos : 1 ≤ S.D)
    (hmargin : 4 * (S.D + 2 * S.r₀) ≤ S.m)
    (hL : 8 * S.K * S.m ≤ L) (hC : 0 < S.C₁)
    (hμ : μ = 0) (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hmult : ∀ x, (Finset.univ.filter fun i ↦ S.anchor i = x).card ≤ μ)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    {a : ℝ} (ha : 0 ≤ a) (k : ℕ)
    (pre : (r : ℕ) → Config r
      (fun v ↦ Fin (augmentedDimensions (V := Site Λ) q aux v)) → ℂ)
    (hsym : pre k ∈ symmetricSubspace k
      (fun v ↦ Fin (augmentedDimensions (V := Site Λ) q aux v)))
    (hpre : pre k ≠ 0) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    let hm : 0 < S.m := by omega
    let hM : 0 < S.M := chargeSlotCount_pos hC (by omega) hDpos
    let E := S.actualEnergyTerms h Ω Δ L aux
    (S.actualChargeData hm hM s).energyError E (a / 2) k (pre k) p ≤ 0 := by
  have hbound := CollarScan.actualCharge_energyError_le_domainGraph hT S hgraph hdepth aux h Ω Δ
    hn hs hr hDpos hmargin hL hC hrows hmult hclear ha k pre hsym hpre hp
  dsimp only at hbound ⊢
  simpa [hμ, Real.zero_rpow (by norm_num : (7 / 8 : ℝ) ≠ 0)] using hbound

open Classical in
/-- Zero replicas retain the same energy bound for a nonzero symmetric
supplied scalar vector and the same independently sized auxiliary factors. -/
theorem zero_replica_energy
    {Λ T : Finset (ℤ × ℤ)} {q R : ℕ} {J : ℝ} [NeZero q]
    [LinearOrder (AdmissibleSupport Λ R)]
    (hT : T.Nonempty) (S : CollarScan (Site Λ) (AdmissibleSupport Λ R))
    (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
    (aux : Bool → ℕ) [∀ b, NeZero (aux b)]
    (h : LocalHamiltonian Λ q R J) (Ω : StateSpace Λ q) (Δ : ℝ)
    {s L μ : ℕ} (hn : 2 ≤ S.n) (hs : s + 1 ≤ S.n * S.m)
    (hr : S.r₀ ≤ S.D) (hDpos : 1 ≤ S.D)
    (hmargin : 4 * (S.D + 2 * S.r₀) ≤ S.m)
    (hL : 8 * S.K * S.m ≤ L) (hC : 0 < S.C₁)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hmult : ∀ x, (Finset.univ.filter fun i ↦ S.anchor i = x).card ≤ μ)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    {a : ℝ} (ha : 0 ≤ a)
    (pre : (r : ℕ) → Config r
      (fun v ↦ Fin (augmentedDimensions (V := Site Λ) q aux v)) → ℂ)
    (hsym : pre 0 ∈ symmetricSubspace 0
      (fun v ↦ Fin (augmentedDimensions (V := Site Λ) q aux v)))
    (hpre : pre 0 ≠ 0) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    let hm : 0 < S.m := by omega
    let hM : 0 < S.M := chargeSlotCount_pos hC (by omega) hDpos
    let n := augmentedDimensions (V := Site Λ) q aux
    let E := S.actualEnergyTerms h Ω Δ L aux
    let A : ℝ := 10 * S.K * S.n * S.D * μ
    let ℓ := transportLogDimBound q S.r₀
    let b := ∑ hist : History S.K S.m S.M s,
      if S.IsGoodOldHistory hist then 0 else historyWeight hist
    (S.actualChargeData hm hM s).energyError E (a / 2) 0 (pre 0) p ≤
      (10 * (S.D : ℝ) / S.m) *
        ((1 - p) * A ^ (7 / 8 : ℝ) *
          (S.actualChargeEntropyDefect hm hM s n E (a / 2) 0 (pre 0) p) ^ (1 / 8 : ℝ) +
          A * (2 * ℓ) ^ (1 / 8 : ℝ) / 2 * ((1 - p) * b + p)) :=
  CollarScan.actualCharge_energyError_le_domainGraph hT S hgraph hdepth aux h Ω Δ
    hn hs hr hDpos hmargin hL hC hrows hmult hclear ha 0 pre hsym hpre hp

section FiniteRounds

variable {ι Θ : Type} [Fintype ι] [MeasurableSpace Θ]

open Classical in
/-- The denominator-free good-old theorem applies directly at capacity zero. -/
theorem zero_capacity_goodOld (R : ScanRound ι Θ) (k : ℕ) (p : ℝ)
    [∀ h, IsFiniteMeasure (R.μOld k p h)]
    (hw : ∀ h, 0 ≤ R.w h) (hsumw : ∑ h, R.w h = 1)
    (hmass : ∀ h, (R.μOld k p h).real univ = 1 / 2)
    (hη : ∀ i h, Measurable (R.etaOld i h))
    (hη0 : ∀ i h θ, 0 ≤ R.etaOld i h θ) {B : ℝ}
    (hηB : ∀ i h θ, R.etaOld i h θ ≤ B)
    (hcard : ∀ h, ((Finset.univ.filter fun i ↦ R.splitOld i h).card : ℝ) ≤ 0) :
    (∑ h, if R.good h then R.w h * ∑ i,
        (if R.splitOld i h then
          ∫ θ, R.etaOld i h θ ^ (1 / 8 : ℝ) ∂(R.μOld k p h) else 0)
      else 0) ≤ 0 := by
  have hbound := R.goodOld_le_capacity k p hw hsumw hmass hη hη0 hηB le_rfl hcard
  simpa [Real.zero_rpow (by norm_num : (7 / 8 : ℝ) ≠ 0)] using hbound

open Classical in
/-- Good histories may have zero weight even when the split capacity is
positive. The literal charge defect then vanishes and Hölder still applies. -/
theorem zero_good_weight (R : ScanRound ι Θ) (k : ℕ) (p : ℝ)
    [∀ h, IsFiniteMeasure (R.μOld k p h)]
    (hw : ∀ h, 0 ≤ R.w h) (hsumw : ∑ h, R.w h = 1)
    (hmass : ∀ h, (R.μOld k p h).real univ = 1 / 2)
    (hη : ∀ i h, Measurable (R.etaOld i h))
    (hη0 : ∀ i h θ, 0 ≤ R.etaOld i h θ) {B N : ℝ}
    (hηB : ∀ i h θ, R.etaOld i h θ ≤ B) (hN : 0 ≤ N)
    (hcard : ∀ h, ((Finset.univ.filter fun i ↦ R.splitOld i h).card : ℝ) ≤ N)
    (hzero : ∀ h, R.good h → R.w h = 0) :
    R.chargeDefect k p = 0 ∧
      (∑ h, if R.good h then R.w h * ∑ i,
          (if R.splitOld i h then
            ∫ θ, R.etaOld i h θ ^ (1 / 8 : ℝ) ∂(R.μOld k p h) else 0)
        else 0) ≤ 0 := by
  have hQ : R.chargeDefect k p = 0 := by
    unfold ScanRound.chargeDefect
    apply Finset.sum_eq_zero
    intro h _
    by_cases hg : R.good h
    · simp [hg, hzero h hg]
    · simp [hg]
  refine ⟨hQ, ?_⟩
  have hbound := R.goodOld_le_capacity k p hw hsumw hmass hη hη0 hηB hN hcard
  simpa [hQ, Real.zero_rpow (by norm_num : (1 / 8 : ℝ) ≠ 0)] using hbound

end FiniteRounds

end TNLeanTest.ActualChargeEnergyBound
