/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SourceRoughSelection
import TNLean.PEPS.AreaLaw.Scan.RoughSelectedDensity
import TNLean.PEPS.AreaLaw.Scan.BootstrapSelectedEnergy
import TNLean.PEPS.AreaLaw.Scan.BootstrapTypicalBudget
import TNLean.PEPS.AreaLaw.Scan.BootstrapScannerExponents
import TNLean.PEPS.AreaLaw.Scan.FixedWeightTransportSmallness
import TNLean.PEPS.AreaLaw.Scan.ScannerRoundedAdmissibility
import TNLean.PEPS.AreaLaw.Scan.TypicalReplicaAbsorption

/-!
# Original-state entropy improvement from the actual rough scanner

The physical source produces one truncated state, one typical spectral set and
one Schmidt--Bell label sequence. Actual selection, energy, and both rough
comparisons refer to the same charge point. The replica limit is taken at each
fixed physical instance, then the typical entropy is substituted and continuity
restores the original state and target. All constants and size thresholds are
chosen before the current exponent and every finite instance.

The hypotheses are the actual scanner geometry and current-exponent entropy
bounds on the original target and positive-depth prefixes. The conclusion has
the strictly improved exponent. No sharp moment premise, supplied low-energy
point, or improved-entropy premise occurs. Applying this to every weakly safe
rectangle and taking the uniform box supremum remains a separate bridge.

Source: OpenAI area-law manuscript, `08-scanner.tex`, lines 693--792,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Validation and inherited-dependency scope:
`docs/paper-gaps/arealaw2d_safe_box_collar_scope.tex`.
-/

noncomputable section
open Matrix TensorPower TensorPower.ReplicaTransport PermutationRepresentation Filter
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator Topology

open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open SpectralFilter

private theorem restored_entropy_le_of_selected_rough_comparisons
    {Λ : Finset (ℤ × ℤ)} {q : ℕ} (Ω Ωt : StateSpace Λ q) (hΩt : ‖Ωt‖ = 1)
    (X : Finset (Site Λ))
    (E : Finset (FiniteProduct.Configuration (fun _ : Site Λ ↦ Fin q) X))
    (w τ a Edef Bsh Bexc cont : ℝ)
    (hz : 0 < (reducedState_isHermitian Λ q Ωt X).spectralRestrictionMass E)
    (hE : ∀ i ∈ E,
      Real.exp (-regionalEntropy Λ q Ωt X - w) ≤
        (reducedState_isHermitian Λ q Ωt X).eigenvalues i ∧
      (reducedState_isHermitian Λ q Ωt X).eigenvalues i ≤
        Real.exp (-regionalEntropy Λ q Ωt X + w))
    (hτ : 0 < τ) (hτhalf : τ < 1 / 2) (ha : 0 < a) (hEdef : 0 ≤ Edef)
    (hsmall : 6 * (τ + Edef / τ) ≤ 1)
    (rU rL rE : ℕ → ℝ)
    (hrU : Tendsto rU atTop (𝓝 0)) (hrL : Tendsto rL atTop (𝓝 0))
    (hrE : Tendsto rE atTop (𝓝 0))
    (hcont : |regionalEntropy Λ q Ωt X - regionalEntropy Λ q Ω X| ≤ cont) :
    let β := fun _ : Site Λ ↦ Fin q
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (FiniteProduct.splitEquiv β X) Ωt
    let ψ : FiniteProduct.Configuration β Xᶜ × Fin E.card → ℂ := fun x ↦
      compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.2, x.1)
    let Sent := vonNeumannEntropy (Matrix.partialTraceLeft (Matrix.vecMulVec ψ (star ψ)))
      (Matrix.posSemidef_vecMulVec_self_star ψ).partialTraceLeft.isHermitian
    let z := (reducedState_isHermitian Λ q Ωt X).spectralRestrictionMass E
    (∀ᶠ k : ℕ in atTop, ∃ v δ : ℝ,
      δ ≤ Edef + rE k ∧
      v ≤ 2 * Real.log (E.card : ℝ) - Real.log z + 4 * Bsh / z + 4 * Bexc + rU k ∧
      4 * Sent - 6 * (τ * Real.log (E.card : ℝ) + Real.binEntropy τ / a) -
        3 * (δ / τ) * max 0 (2 * Sent) - rL k ≤ v) →
    regionalEntropy Λ q Ω X ≤
      7 * (w - Real.log z) - Real.log z + 4 * Bsh / z + 4 * Bexc +
        6 * Real.binEntropy τ / a + cont := by
  classical
  intro β ΩX ψ Sent z hselected
  let P := fun (k : ℕ) (v δ : ℝ) ↦
    δ ≤ Edef + rE k ∧
    v ≤ 2 * Real.log (E.card : ℝ) - Real.log z + 4 * Bsh / z + 4 * Bexc + rU k ∧
    4 * Sent - 6 * (τ * Real.log (E.card : ℝ) + Real.binEntropy τ / a) -
      3 * (δ / τ) * max 0 (2 * Sent) - rL k ≤ v
  have hchoice : ∀ k : ℕ, ∃ v δ : ℝ, (∃ v δ : ℝ, P k v δ) → P k v δ := by
    intro k
    by_cases hk : ∃ v δ : ℝ, P k v δ
    · obtain ⟨v, δ, hv⟩ := hk
      exact ⟨v, δ, fun _ ↦ hv⟩
    · exact ⟨0, 0, fun h ↦ False.elim (hk h)⟩
  choose values defects hchoice using hchoice
  have hpicked : ∀ᶠ k : ℕ in atTop, P k (values k) (defects k) :=
    hselected.mono fun k hk ↦ hchoice k hk
  have htyp := regionalEntropy_le_of_rough_typical_comparisons
    Ωt hΩt X E w hz hE (C := 3) (τ := τ) (a := a) (Edef := Edef)
    (Bsh := Bsh) (Bexc := Bexc) (F := values) (d := defects)
    (by norm_num) hτ hτhalf ha hEdef
    (by simpa only [show 2 * (3 : ℝ) = 6 by norm_num] using hsmall)
    hrU hrL hrE (hpicked.mono fun _ hk ↦ hk.1)
    (hpicked.mono fun _ hk ↦ hk.2.1)
    (hpicked.mono fun _ hk ↦ by
      simpa only [show 2 * (3 : ℝ) = 6 by norm_num] using hk.2.2)
  have ht := (abs_le.mp hcont).1
  norm_num only [show 2 * (3 : ℝ) = 6 by norm_num] at htyp
  linarith only [htyp, ht]

open Classical in
/-- The actual rough-only bootstrap improves the entropy exponent on the
original target. The source entropy premises retain the current exponent;
the output exponent is multiplied by `1 - ell e₀`. Source:
`08-scanner.tex`, lines 693--792. -/
theorem exists_sourceBootstrap_entropy_improvement
    {q : ℕ} [NeZero q] (hq : 1 ≤ q) (R : ℕ)
    {J Δ C_T C₁ e₀ Ce : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (hC_T : 0 ≤ C_T) (hC₁ : 0 < C₁) (multiplicity : ℕ)
    (hmultiplicity : 3 * (multiplicity : ℝ) ≤ C₁)
    (he₀ : (Exponents.boxError : ℝ) < e₀) (he₀₁ : e₀ < 1) (hCe : 0 ≤ Ce) :
    let he₀pos : 0 < e₀ := lt_trans (by norm_num [Exponents.boxError]) he₀
    let F := BootstrapParameters.scannerExponents e₀ he₀pos he₀₁
    ∃ Ctr Cout : ℝ, 0 < Ctr ∧ 0 < Cout ∧ ∃ N : ℕ, 2 ≤ N ∧
      ∀ η : ℝ, (Exponents.boxError : ℝ) < η → η ≤ e₀ →
      ∀ (Λ T : Finset (ℤ × ℤ)) [LinearOrder (AdmissibleSupport Λ R)]
        (hT : T.Nonempty) (h : LocalHamiltonian Λ q R J)
        (S : CollarScan (Site Λ) (AdmissibleSupport Λ R)) (E₀ : ℝ)
        (Ω : StateSpace Λ q),
        IsGappedGroundState Λ q h.operator E₀ Ω Δ →
        S.graph = domainGraph Λ → (∀ i, S.anchor i ∈ i.val) → N ≤ S.n →
        S.r₀ = roundedLogRadius Ctr S.n →
        S.m = F.m S.n → S.D = F.D S.n → S.K = F.K S.n →
        S.C₁ = C₁ → (T.card : ℝ) ≤ C_T * (S.n : ℝ) ^ 2 →
        S.depth = (fun x ↦ ambientDepth T hT x.val) →
        (∀ r : ℕ, 1 ≤ r → r ≤ F.L S.n →
          (ambientDilation T r \ ambientDilation T (r - 1)).card ≤ S.n) →
        (∀ x, (Finset.univ.filter fun i ↦ S.anchor i = x).card ≤ multiplicity) →
        (∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
          ((2 * F.L S.n + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) →
        regionalEntropy Λ q Ω (S.A.filter fun x ↦ x.val ∈ T) ≤
          Ce * (S.n : ℝ) ^ (1 + η) →
        (∀ j : ℕ, j ≤ F.L S.n →
          regionalEntropy Λ q Ω (positiveDepthPrefix S.A S.depth (j : ℤ)) ≤
            Ce * ((S.n : ℝ) * (F.L S.n : ℝ) ^ η + S.n)) →
        regionalEntropy Λ q Ω (S.A.filter fun x ↦ x.val ∈ T) ≤
          Cout * (S.n : ℝ) ^ (1 + (1 - BootstrapParameters.ell e₀) * η) := by
  intro he₀pos F
  obtain ⟨Ctr, Ctarget, ct, Cent, eent, Cen, een, hCtr, _, hct, hsource⟩ :=
    exists_sourceTarget_selected_actualCharge_rough_comparison
      hq R hJ hΔ hC_T hC₁ multiplicity hmultiplicity 100
  obtain ⟨C, Cl, hC, _, Ns, hNs, hsource⟩ := hsource F
  obtain ⟨Ct, Clt, hCt, _, hcap⟩ :=
    exists_transport_coefficients_log_bound hq hCtr.le Cent eent Cen een
  obtain ⟨Cδ, hCδ, Nd, _, hdensity⟩ :=
    F.exists_rough_selectedDensity_principal hq Ce C₁ Ct Clt hCe hC₁
      (zero_le_one.trans hCt)
  let g := Δ / positiveNormalization 1 (Δ / 2) J
  have hg : 0 < g := div_pos hΔ (positiveNormalization_pos 1 (Δ / 2) J)
  obtain ⟨Ne, _, henergy⟩ := exists_bootstrap_selected_energy_bound
    he₀pos he₀₁ C Cδ Cl Clt (g / 2) (zero_le_one.trans hC) hCδ.le (half_pos hg)
  obtain ⟨Nt, htarget⟩ := eventually_atTop.mp
    (eventually_abs_regionalEntropy_sub_le_of_truncation q hq g (C_T + 1) hg)
  obtain ⟨Na, _, hadmissible⟩ := F.exists_rounded_admissibility hCtr.le
  obtain ⟨Nsmall, _, hsmall⟩ :=
    F.exists_fixedWeightFour_transport_smallness hq hCtr.le hct
  obtain ⟨Nloss, _, hloss⟩ := exists_bootstrap_comparison_loss_threshold
    6 (1 + (g / 2)⁻¹) he₀pos he₀₁
  obtain ⟨Cout, hCout, Nb, _, hbudget⟩ :=
    exists_bootstrap_restored_entropy_budget he₀ he₀₁ hq Ce hCe
  obtain ⟨Ni, hinterval⟩ := eventually_atTop.mp (eventually_le_natCast_rpow F.nu_pos 4)
  obtain ⟨Nl, hlog⟩ := eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1)
  refine ⟨Ctr, Cout, hCtr, hCout,
    max Ns (max Nd (max Ne (max Nt (max Na (max Nsmall (max Nloss (max Nb (max Ni Nl)))))))),
    hNs.trans (le_max_left _ _), ?_⟩
  intro η hη hηe₀ Λ T _ hT h S E₀ Ω hgs hgraph hanchor hn hr hmScale hDScale hKScale
    hCeq hsize hdepth hrows hmult hclear htargetEntropy hprefix
  have hthresholds := hn
  simp only [max_le_iff] at hthresholds
  obtain ⟨hnS, hnD, hnE, hnT, hnA, hnSmall, hnLoss, hnB, hnI, hnLog⟩ := hthresholds
  have hn2 : 2 ≤ S.n := hNs.trans hnS
  have hn1 : (1 : ℝ) ≤ S.n := by exact_mod_cast ((by decide : 1 ≤ 2).trans hn2)
  have hnpos : (0 : ℝ) < S.n := zero_lt_one.trans_le hn1
  have hadm := hadmissible S.n hnA
  simp only [← hmScale, ← hDScale, ← hKScale, ← hr] at hadm
  obtain ⟨hrD, hDpos, hDm, _, _⟩ := hadm
  obtain ⟨hm, hM, hdata⟩ := hsource Λ T hT h S E₀ Ω hgs hgraph hanchor hnS
    hr hmScale hDScale hKScale hCeq hsize hdepth hrows hmult hclear
    Ce η hprefix hrD hDpos hDm
  let L := F.L S.n
  have hDExplicit : S.D = Nat.ceil ((S.n : ℝ) ^ BootstrapParameters.kappa e₀) :=
    hDScale
  have hKExplicit : S.K =
      Nat.floor ((S.n : ℝ) ^ (1 - BootstrapParameters.ell e₀)) /
        (8 * Nat.floor ((S.n : ℝ) ^ BootstrapParameters.mu e₀)) := hKScale
  have hLExplicit : L = Nat.floor ((S.n : ℝ) ^ (1 - BootstrapParameters.ell e₀)) := rfl
  let X := S.A.filter fun x ↦ x.val ∈ T
  let β := fun _ : Site Λ ↦ Fin q
  let w := (S.n : ℝ) ^ (3 / 5 : ℝ)
  let Bsh := Ce * ((S.n : ℝ) * (L : ℝ) ^ η + S.n) + (S.n : ℝ) ^ (-247 : ℝ)
  obtain ⟨hK, hKL, hcard, hX, eigen, Ωt, htrgs, he0, he, htrace, _, _, hwdata⟩ := hdata
  let E := Entropy.typicalSet (reducedState_isHermitian Λ q Ωt X).eigenvalues
    (regionalEntropy Λ q Ωt X) w
  let z := (reducedState_isHermitian Λ q Ωt X).spectralRestrictionMass E
  obtain ⟨hwindow, hd, hpdata⟩ := hwdata
  let : NeZero E.card := NeZero.of_pos hd
  let d := E.card
  let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (FiniteProduct.splitEquiv β X) Ωt
  let ψ : FiniteProduct.Configuration β Xᶜ × Fin d → ℂ := fun x ↦
    compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.2, x.1)
  let Sent := vonNeumannEntropy (Matrix.partialTraceLeft (Matrix.vecMulVec ψ (star ψ)))
    (Matrix.posSemidef_vecMulVec_self_star ψ).partialTraceLeft.isHermitian
  let dims := augmentedDimensions (V := Site Λ) q (fun _ ↦ d)
  let energy := S.actualEnergyTerms h Ω Δ L (fun _ ↦ d)
  obtain ⟨ell, hpre, hdim, hweights⟩ := hpdata
  let pre : (k : ℕ) → Config k (fun v ↦ Fin (dims v)) → ℂ := fun k ↦
    replicaPrevector Ωt d k (ell k) ∘ augmentedSumReplicaCopiesEquiv q d k
  let a := 4 / (S.K : ℝ)
  let logdim := transportLogDimBound q S.r₀
  have hsmallN := hsmall S.n hnSmall
  simp only [ScannerExponents.a, ← hKScale, ← hr] at hsmallN
  have ha : 0 < a := hsmallN.2.1
  obtain ⟨b, rem, Cb, cU, cR, Ci, cL, Cf,
      _, _, _, _, _, _, _, _, _, hrem, hlimU, hlimR, hlimL, hpoints⟩ :=
    hweights hsmallN.2.2
  have hΩt : ‖Ωt‖ = 1 := (Matrix.isGappedGroundState_iff.mp htrgs).1
  have hXcard : (X.card : ℝ) ≤ (C_T + 1) * (S.n : ℝ) ^ 2 :=
    (Nat.cast_le.mpr (Finset.card_le_card hX)).trans hcard
  have hcont := htarget S.n hnT Λ Ω Ωt hgs.1 hΩt X hXcard htrace
  have hSt : regionalEntropy Λ q Ωt X ≤
      Ce * (S.n : ℝ) ^ (1 + η) + (S.n : ℝ) ^ (-247 : ℝ) := by
    linarith [(abs_le.mp hcont).2]
  have hlogd : |Real.log (d : ℝ) - regionalEntropy Λ q Ωt X| ≤ w - Real.log z :=
    (abs_log_card_and_selectedSchmidtEntropy_sub_le Ωt hΩt X E w hwindow.2.2.1
      (fun i hi ↦ (hwindow.2.2.2.2.2 i hi).2)).1
  have hℓ1 : 1 ≤ logdim := by
    have hlq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
    dsimp only [logdim, transportLogDimBound]
    exact le_add_of_nonneg_right (by positivity)
  have hℓcap : logdim ≤ transportLogDimBound q (roundedLogRadius Ctr S.n) := by
    dsimp only [logdim]; rw [hr]
  have hG : Cent * logdim ^ eent ≤ Ct * Real.log (S.n : ℝ) ^ Clt :=
    (hcap S.n (hlog S.n hnLog) logdim hℓ1 hℓcap).1
  let epsilon := (S.n : ℝ) ^ (-F.nu)
  have hε : 0 < epsilon := Real.rpow_pos_of_pos hnpos _
  have hε2 : 2 * epsilon < 1 := by
    have hpow := hinterval S.n hnI
    have hid : epsilon * (S.n : ℝ) ^ F.nu = 1 := by
      dsimp only [epsilon]
      rw [← Real.rpow_add hnpos, neg_add_cancel, Real.rpow_zero]
    linarith only [hid, mul_le_mul_of_nonneg_left hpow hε.le]
  have hκη : F.kappa ≤ η :=
    (show BootstrapParameters.kappa e₀ ≤ (Exponents.boxError : ℝ) / 4 from
      min_le_right _ _).trans
      ((show (Exponents.boxError : ℝ) / 4 ≤ (Exponents.boxError : ℝ) by
        norm_num [Exponents.boxError]).trans hη.le)
  let delta := Cδ * epsilon⁻¹ *
    ((S.n : ℝ) ^ (η - F.mu) + a ^ (1 / 4 : ℝ) * Real.log (S.n : ℝ) ^ Clt)
  let density := fun (k : ℕ) (s : Fin (S.n * S.m)) (p : ℝ) ↦
    S.actualChargeEntropyDefect hm hM s.val dims energy (a / 2) k (pre k) p /
      (S.K * S.n * S.D : ℝ)
  let defect := fun (k : ℕ) (s : Fin (S.n * S.m)) (p : ℝ) ↦
    ((S.actualChargeScanRound hm hM s.val dims energy a pre).meanEnergy k p - eigen) / (g / 2)
  let cap := fun (k : ℕ) (s : Fin (S.n * S.m)) (p : ℝ) ↦
    C * (4 : ℝ) ^ 2 * (S.n : ℝ) ^ F.ell * (S.D : ℝ) ^ 2 * Real.log (S.n : ℝ) ^ Cl *
      ((1 - p) * (density k s p) ^ (1 / 8 : ℝ) +
        (1 - p) * (S.n : ℝ) ^ (-100 : ℝ) + p)
  let value := fun (k : ℕ) (s : Fin (S.n * S.m)) (p : ℝ) ↦
    -Real.log (Transport.filteredNormSq
      ((S.actualChargeData hm hM s.val).rootPath dims (a / 2) k p) (pre k)) / (k : ℝ)
  let Brough := 2 * Real.log (d : ℝ) - Real.log z +
    4 * (Bsh / z + (1 + 3 * (S.n : ℝ) * S.D * Real.log q))
  let keep := fun (k : ℕ) (s : Fin (S.n * S.m)) (p : ℝ) ↦
    0 ≤ defect k s p ∧ defect k s p ≤ (eigen + cap k s p + rem k) / (g / 2) ∧
      0 < Transport.filteredNormSq
        ((S.actualChargeData hm hM s.val).rootPath dims (a / 2) k p) (pre k) ∧
      value k s p ≤ Brough + Real.bellOverlapRemainder d cU S.K k ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
        4 * Sent - 6 * (τ * Real.log (d : ℝ) + Real.binEntropy τ / a) -
          3 * (defect k s p / τ) * max 0 (2 * Sent) -
            roughLowerRemainder S.K cL Cf ell Sent k ≤ value k s p
  have hstrong : ∀ᶠ k : ℕ in atTop,
      ∃ s : Fin (S.n * S.m), ∃ p ∈ Set.Icc epsilon (2 * epsilon),
        density k s p ≤ delta ∧ keep k s p := by
    have hclosure := hdensity S.n hnD
    simp only [← hmScale, ← hDScale, ← hKScale] at hclosure
    apply hclosure η hκη (regionalEntropy Λ q Ωt X) (Real.log (d : ℝ)) z Bsh
      (Cent * logdim ^ eent) hwindow.2.2.1 hwindow.2.1 hSt hlogd le_rfl hG
      (roughEndpointRemainder d cR S.K (Ci + (2 * S.n * S.m : ℕ) * Cb)) hlimR
    have hselected := hpoints epsilon (2 * epsilon) hε (by linarith) hε2
    filter_upwards [hselected] with k hk
    obtain ⟨s, p, hp, hQ, hkeep⟩ := hk
    refine ⟨s, p, hp, ?_, hkeep⟩
    have hKr : (0 : ℝ) < S.K := by exact_mod_cast (show 0 < S.K by omega)
    have hWa : a * (S.K : ℝ) = 4 := div_mul_cancel₀ 4 hKr.ne'
    have hrate : Cent * a * S.K * a ^ (1 / 4 : ℝ) * logdim ^ eent =
        (Cent * logdim ^ eent) * 4 * a ^ (1 / 4 : ℝ) := by
      calc
        _ = (Cent * logdim ^ eent) * (a * S.K) * a ^ (1 / 4 : ℝ) := by ring
        _ = _ := by rw [hWa]
    simp only [a, logdim] at hrate
    rw [hrate] at hQ
    simpa only [density, hCeq, show 2 * epsilon - epsilon = epsilon by ring,
      _root_.mul_assoc] using hQ
  let τ := (S.n : ℝ) ^ (-F.nu / 4)
  let Edef := (1 + (g / 2)⁻¹) * (S.n : ℝ) ^ (-F.nu / 2)
  obtain ⟨hτ, hτhalf, hsmallLoss⟩ := hloss S.n hnLoss
  have hrE : Tendsto (fun k ↦ rem k / (g / 2)) atTop (𝓝 0) := by
    simpa only [zero_div] using hrem.div_const (g / 2)
  let P := fun (k : ℕ) (v δ : ℝ) ↦
    δ ≤ Edef + rem k / (g / 2) ∧
      v ≤ 2 * Real.log (d : ℝ) - Real.log z + 4 * Bsh / z +
        4 * (1 + 3 * (S.n : ℝ) * S.D * Real.log q) +
          Real.bellOverlapRemainder d cU S.K k ∧
      4 * Sent - 6 * (τ * Real.log (d : ℝ) + Real.binEntropy τ / a) -
        3 * (δ / τ) * max 0 (2 * Sent) - roughLowerRemainder S.K cL Cf ell Sent k ≤ v
  have hselectedP : ∀ᶠ k : ℕ in atTop, ∃ v δ : ℝ, P k v δ := by
    filter_upwards [hstrong] with k hk
    obtain ⟨s, p, hp, hQ, hδ0, hδcap, _, hu, hl⟩ := hk
    have hQ0 : 0 ≤ density k s p := div_nonneg
      (S.actualChargeEntropyDefect_nonneg hm hM s.val dims energy ha.le k pre p) (by positivity)
    have henergyN := henergy S.n hnE η hηe₀
    dsimp only at henergyN
    rw [← hDExplicit, ← hKExplicit] at henergyN
    have hcapBound : (eigen + cap k s p) / (g / 2) ≤ Edef :=
      henergyN (density k s p) p eigen hQ0 hQ hp (hp.2.trans hε2.le)
        (he.trans (min_le_left _ _))
    refine ⟨value k s p, defect k s p, ?_, ?_, hl τ hτ hτhalf.le⟩
    · have hb : (eigen + cap k s p + rem k) / (g / 2) ≤
          Edef + rem k / (g / 2) := by
        rw [add_div]; exact _root_.add_le_add hcapBound le_rfl
      exact hδcap.trans hb
    · dsimp only [Brough] at hu
      simpa only [mul_add, mul_div_assoc, add_assoc] using hu
  have hrestored := restored_entropy_le_of_selected_rough_comparisons
    Ω Ωt hΩt X E w τ a Edef Bsh
      (1 + 3 * (S.n : ℝ) * S.D * Real.log q) ((S.n : ℝ) ^ (-247 : ℝ))
    hwindow.2.2.1 (fun i hi ↦ (hwindow.2.2.2.2.2 i hi).2)
    hτ hτhalf ha (by positivity) hsmallLoss
    (Real.bellOverlapRemainder d cU S.K) (roughLowerRemainder S.K cL Cf ell Sent)
    (fun k ↦ rem k / (g / 2)) hlimU hlimL hrE hcont hselectedP
  change regionalEntropy Λ q Ω X ≤
    7 * (w - Real.log z) - Real.log z + 4 * Bsh / z +
      4 * (1 + 3 * (S.n : ℝ) * S.D * Real.log q) +
        6 * Real.binEntropy τ / a + (S.n : ℝ) ^ (-247 : ℝ) at hrestored
  have hbudgetN := hbudget S.n hnB
  dsimp only at hbudgetN
  rw [← hKExplicit, ← hDExplicit, ← hLExplicit] at hbudgetN
  exact hbudgetN η hη hηe₀ (regionalEntropy Λ q Ω X) z τ hwindow.2.2.1 hwindow.2.1
    hτ.le (hτhalf.le.trans (by norm_num)) hrestored

end TNLean.PEPS.AreaLaw.Scan.CollarScan
