/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualTerminalPartitions
import TNLean.PEPS.AreaLaw.Scan.ActualGlobalReplicaEnergy
import TNLean.PEPS.AreaLaw.Scan.AugmentedRootCompression
import QICLean.Algebra.ProjectionRangeIsometry
import QICLean.Analysis.RegionalSharpLowerNorm

/-!
# Sharp lower bounds for the actual fill and charge roots

The original physical gap, both auxiliary labels and the original marginal
moments give a lower bound for each literal actual root. The energy defect
is the actual fill or charge excess mean energy in its normalized filtered
vector. The same supplied prevector is used throughout the finite horizon.
All terminal weights and the three signed physical entropies are retained.

The two polynomial constants precede the scanner, horizon, physical state,
moment bounds, copy number, labels and interpolation parameter. At metric
parameter a/2, the required moment conditions are 10a ≤ r and 10a ≤ 1.
No gap, label, moment or final geometric budget is constructed here.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`07-comparators.tex`, lines 550--651, and `08-scanner.tex`, lines 371--384,
416--451 and 755--769, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open Matrix TensorPower TensorPower.ReplicaTransport PermutationRepresentation
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open ActualTerminals

open Classical in
/-- The common terminal family supplies disjoint near/middle regions, ordered
nesting across bands, and the exact far complement for the sharp lower bound.
Source: `08-scanner.tex`, lines 83--154 and 416--451, revision adc7f124. -/
private theorem actualTerminal_sharpLower_geometry
    {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
    (S : CollarScan V I) (Horizon : ℕ) :
    let σ := terminalPartition S Horizon
    let Q := fun j g => receiving (σ j g) false
    let Y := fun j g => middle (σ j g)
    (∀ j g, Disjoint (Q j g) (Y j g)) ∧
      (∀ j j' g g', g < g' → Q j g ∪ Y j g ⊆ Q j' g') ∧
      (∀ j g, receiving (σ j g) true = (Q j g ∪ Y j g)ᶜ) := by
  classical
  intro σ Q Y
  have hdisj : ∀ j g, Disjoint (Q j g) (Y j g) := fun j g => by
    simp only [Q, Y, receiving, middle]
    exact Finset.disjoint_filter.mpr fun _ _ hx hy =>
      Option.noConfusion (hx.symm.trans hy)
  have hnest : ∀ j j' g g', g < g' → Q j g ∪ Y j g ⊆ Q j' g' := fun
    | Sum.inl ⟨_, hist⟩, Sum.inl ⟨_, hist'⟩, g, g', hgg' =>
      S.state_near_middle_subset_later_near hist hist' g g' hgg'
    | Sum.inl ⟨_, hist⟩, Sum.inr ⟨_, hist'⟩, g, g', hgg' =>
      S.state_near_middle_subset_later_old_near hist hist' g g' hgg'
    | Sum.inr ⟨_, hist⟩, Sum.inl ⟨_, hist'⟩, g, g', hgg' =>
      S.old_near_middle_subset_later_state_near hist hist' g g' hgg'
    | Sum.inr ⟨_, hist⟩, Sum.inr ⟨_, hist'⟩, g, g', hgg' =>
      S.oldChargeState_near_middle_subset_later_near hist hist' g g' hgg'
  have hfar (j : terminalFamily S.K S.m S.M Horizon) (g : Fin S.K) :
      receiving (σ j g) true = (Q j g ∪ Y j g)ᶜ := by
    ext x
    cases hx : σ j g x with
    | none => simp [Q, Y, receiving, middle, hx]
    | some side => cases side <;> simp [Q, Y, receiving, middle, hx]
  exact ⟨hdisj, hnest, hfar⟩

open Classical in
/-- The sharp finite-copy lower estimate for the actual fill and charge
interpolations. The physical gap and both label equations concern the same
supplied state and prevector. The defect is computed from the literal actual
mean energy, and normalization is proved for that same filtered vector.
The finite maximum includes zero, so no positive band-count premise is needed.
Source: `07-comparators.tex`, lines 550--651; `08-scanner.tex`, lines
371--384, 416--451 and 755--769, revision adc7f124. -/
theorem exists_actualScan_sharp_lower_norm
    {Λ : Finset (ℤ × ℤ)} {q d R : ℕ} {J : ℝ} [NeZero q] [NeZero d]
    [LinearOrder (AdmissibleSupport Λ R)] (a : ℝ) (ha : 0 < a) :
    ∃ c Cf : ℝ, 0 ≤ c ∧ 0 ≤ Cf ∧
      ∀ (S : CollarScan (Site Λ) (AdmissibleSupport Λ R))
        (hm : 0 < S.m) (hM : 0 < S.M) (Horizon : ℕ)
        (h : LocalHamiltonian Λ q R J) (Ω : StateSpace Λ q) (Δ : ℝ) (L : ℕ)
        (Ωt : StateSpace Λ q) (e₀ gap : ℝ),
      ‖Ωt‖ = 1 →
      ((∑ i, S.truncatedEnergyTerm h Ω Δ L i) - (e₀ : ℂ) • 1 -
        (gap : ℂ) • (1 - vecMulVec Ωt.ofLp (star Ωt.ofLp))).PosSemidef →
      0 < gap →
      let β := fun _ : Site Λ => Fin q
      let ι₀ := addedSiteSpace (addedSiteSpace β (Fin d)) (Fin d)
      let n := augmentedDimensions (V := Site Λ) q (fun _ => d)
      let σ := terminalPartition S Horizon
      let Q := fun j g => receiving (σ j g) false
      let Y := fun j g => middle (σ j g)
      ∀ K rMom : ℝ,
      (∀ (j : terminalFamily S.K S.m S.M Horizon) (g : Fin S.K)
          (b : Fin 3) (v : ℝ), |v| ≤ rMom →
        let U := FiniteProduct.regionalPhysicalRegion (Q j g) (Y j g) b
        Real.log (Entropy.surprisalMoment
          (FiniteProduct.reducedPure_posSemidef β Ωt U).isHermitian.eigenvalues v) ≤
            v * FiniteProduct.entropy β Ωt U + K * v ^ 2) →
      10 * a ≤ rMom → 10 * a ≤ 1 → 0 ≤ K →
      ∀ (pre : (k : ℕ) → Config k (fun v => Fin (n v)) → ℂ)
        (k : ℕ), 0 < k → pre k ≠ 0 → ‖WithLp.toLp 2 (pre k)‖ ≤ 1 →
      symProj (copyPerm ((v : Site Λ ⊕ Bool) → Fin (n v)) k) *ᵥ pre k = pre k →
      ∀ (ellC ellR : IrrepLabel (Equiv.Perm (Fin k))) (Sent ε : ℝ),
      let e := augmentedReplicaConfigurationEquiv (V := Site Λ) q d k
      labelProj (subsystemPerm k ι₀ {some none}) ellC *ᵥ (pre k ∘ e) = pre k ∘ e →
      labelProj (subsystemPerm k ι₀ {none}) ellR *ᵥ (pre k ∘ e) = pre k ∘ e →
      2 * (k : ℝ) * Sent - ε ≤ Real.log ellC.dim + Real.log ellR.dim →
      let entropyGap := fun j g =>
        FiniteProduct.entropy β Ωt (Q j g) +
          FiniteProduct.entropy β Ωt (Q j g ∪ Y j g)ᶜ -
          FiniteProduct.entropy β Ωt (Y j g)
      let gaps := (Finset.univ :
        Finset (terminalFamily S.K S.m S.M Horizon × Fin S.K)).image
          (fun j => entropyGap j.1 j.2)
      let gmax := (insert (0 : ℝ) gaps).max' (Finset.insert_nonempty _ _)
      let r := Real.log ((k : ℝ) + 1) + c * Real.log ((k : ℝ) + 2) + a * ε
      let b := ((k : ℝ) + 2) ^ (-Cf) / 2
      let lower := fun (Nsq μ : ℝ)
          (T : MeanTree (terminalFamily S.K S.m S.M Horizon)) =>
        0 < Nsq ∧ 0 ≤ (μ - e₀) / gap ∧
          ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
            let rate := fun g => 2 * Sent +
              (1 - τ) * (∑ j, T.weight j * entropyGap j g) -
                τ * (2 * Real.log (d : ℝ)) -
                (3 + 1 / a) * Real.binEntropy τ - 25 * K * a
            (1 / 2) * (∑ g,
              (a * (k : ℝ) * (rate g - (μ - e₀) / gap / τ *
                max 0 (2 * Sent + gmax)) -
                (2 * |r| + |Real.log b| + Real.log 2 + Real.log (3 / 2)))) ≤
              -Real.log Nsq
      ∀ (s : Fin Horizon) (p : ℝ),
        let Dfill := S.actualFillData hm hM s.val
        let Dcharge := S.actualChargeData hm hM s.val
        let Tfill := (Dfill.tree (Set.projIcc (0 : ℝ) 1 zero_le_one p)).map
          (fillTerminalIndex S.K S.m S.M Horizon s)
        let Tcharge := (Dcharge.tree (Set.projIcc (0 : ℝ) 1 zero_le_one p)).map
          (chargeTerminalIndex S.K S.m S.M Horizon s)
        (‖WithLp.toLp 2
            (Transport.filteredVector (Dfill.rootPath n (a / 2) k p) (pre k))‖ = 1 ∧
          lower (Transport.filteredNormSq (Dfill.rootPath n (a / 2) k p) (pre k))
            ((S.actualFillScanRound hm hM s.val n
              (S.actualEnergyTerms h Ω Δ L (fun _ => d)) a pre).meanEnergy k p) Tfill) ∧
        (‖WithLp.toLp 2
            (Transport.filteredVector (Dcharge.rootPath n (a / 2) k p) (pre k))‖ = 1 ∧
          lower (Transport.filteredNormSq (Dcharge.rootPath n (a / 2) k p) (pre k))
            ((S.actualChargeScanRound hm hM s.val n
              (S.actualEnergyTerms h Ω Δ L (fun _ => d)) a pre).meanEnergy k p) Tcharge) := by
  classical
  obtain ⟨c, Cf, hc, hCf, hlower⟩ :=
    exists_replicaMetric_symProj_bandProduct_sharp_lower_norm
      (fun _ : Site Λ => Fin q) (Fin d) (Fin d) (div_pos ha zero_lt_two)
  refine ⟨c, Cf, hc, hCf, ?_⟩
  intro S hm hM Horizon h Ω Δ L Ωt e₀ gap hΩt hgap hgap_pos β ι₀ n σ Q Y
    K rMom hmoment har haone hK pre k hk hpre hprenorm hsym ellC ellR Sent ε e
    hC hR hlabel entropyGap gaps gmax r b lower s p Dfill Dcharge Tfill Tcharge
  obtain ⟨hdisj, hnest, hfar⟩ := actualTerminal_sharpLower_geometry S Horizon
  obtain ⟨N, ZS, hZS, hZSZS⟩ :=
    (isStarProjection_symProj
      (copyPerm ((v : Site Λ ⊕ Bool) → Fin (n v)) k)).exists_matrix_range_isometry
  let ZO := ZS.submatrix e (id : Fin N → Fin N)
  have hZO : ZOᴴ * ZO = 1 :=
    Matrix.IsIsometry.reindex ZS hZS e.symm (Equiv.refl (Fin N))
  have hSymm : symProj (copyPerm ((o : Option (Option (Site Λ))) → ι₀ o) k) =
      (symProj (copyPerm ((v : Site Λ ⊕ Bool) → Fin (n v)) k)).submatrix e e := by
    simpa only [Matrix.reindex_apply, Equiv.symm_symm] using
      (symProj_of_intertwine e.symm
        (φ := copyPerm ((v : Site Λ ⊕ Bool) → Fin (n v)) k)
        (ψ := copyPerm ((o : Option (Option (Site Λ))) → ι₀ o) k)
        (fun perm x => funext fun j => rfl))
  have hZOZO : ZO * ZOᴴ =
      symProj (copyPerm ((o : Option (Option (Site Λ))) → ι₀ o) k) := by
    simpa only [ZO, Matrix.conjTranspose_submatrix, Equiv.coe_refl] using
      ((Matrix.submatrix_mul_equiv ZS ZSᴴ e (Equiv.refl (Fin N)) e).trans
        (congrArg (fun P : Matrix (Config k (fun v => Fin (n v)))
          (Config k (fun v => Fin (n v))) ℂ => P.submatrix e e) hZSZS)).trans hSymm.symm
  let ξ : EuclideanSpace ℂ (Config k ι₀) := WithLp.toLp 2 (pre k ∘ e)
  have hξ : ξ ≠ 0 := by
    intro hzero
    apply hpre
    funext x
    have hx : pre k (e (e.symm x)) = 0 :=
      congrArg (fun v : EuclideanSpace ℂ (Config k ι₀) => v (e.symm x)) hzero
    simpa only [Equiv.apply_symm_apply] using hx
  have hξnorm : ‖ξ‖ ≤ 1 :=
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e.symm).norm_map
      (WithLp.toLp 2 (pre k))).trans_le hprenorm
  have hsymO : symProj (copyPerm ((o : Option (Option (Site Λ))) → ι₀ o) k) *ᵥ ξ = ξ := by
    change symProj (copyPerm ((o : Option (Option (Site Λ))) → ι₀ o) k) *ᵥ
      (pre k ∘ e) = pre k ∘ e
    simpa only [hSymm, Matrix.submatrix_mulVec_equiv, Function.comp_assoc,
      Equiv.self_comp_symm, Function.comp_id] using
      congrArg (fun v : Config k (fun x => Fin (n x)) → ℂ => v ∘ e) hsym
  have hsmall : 20 * (a / 2) = 10 * a := by ring
  have hestimate (T : MeanTree (terminalFamily S.K S.m S.M Horizon)) :=
    hlower k N hk (∑ i, S.truncatedEnergyTerm h Ω Δ L i) Ωt.ofLp e₀ gap
      hgap hΩt hgap_pos ZO hZO hZOZO
      (terminalFamily S.K S.m S.M Horizon) S.K Q Y hdisj hnest K rMom hmoment
      (hsmall.symm ▸ har) (hsmall.symm ▸ haone) hK T ellC ellR Sent ε (1 / 4)
      hlabel (by norm_num) ξ hξ hξnorm hsymO hC hR
  have hbound {Hist : Type} [DecidableEq Hist] {Choice : Hist → Type}
      [∀ hist, DecidableEq (Choice hist)]
      (D : TransportData (Site Λ ⊕ Bool) S.K Hist Choice)
      (hD : D.IsAdmissible) (hcomm : D.CrossBandCommute n (a / 2) k)
      (f : (Σ hist, Option (Choice hist)) → terminalFamily S.K S.m S.M Horizon)
      (hparts : ∀ j g, D.leafPart j g = augmentedPartition (σ (f j) g))
      (μ : ℝ)
      (henergy : μ =
        let v := Transport.filteredVector (D.rootPath n (a / 2) k p) (pre k)
        let vO := v ∘ e
        (star vO ⬝ᵥ (globalReplicaMeanHamiltonian β (Fin d) (Fin d)
          (∑ i, S.truncatedEnergyTerm h Ω Δ L i) k *ᵥ vO)).re) :
      ‖WithLp.toLp 2
          (Transport.filteredVector (D.rootPath n (a / 2) k p) (pre k))‖ = 1 ∧
        lower (Transport.filteredNormSq (D.rootPath n (a / 2) k p) (pre k)) μ
          ((D.tree (Set.projIcc (0 : ℝ) 1 zero_le_one p)).map f) := by
    let T := D.tree (Set.projIcc (0 : ℝ) 1 zero_le_one p)
    let A := fun j g =>
      ((replicaMetric ι₀ (a / 2) k
          (insert (some none) ((Q (f j) g).image fun x => some (some x))))⁻¹ *
        (replicaMetric ι₀ (a / 2) k
          (insert none (((Q (f j) g ∪ Y (f j) g)ᶜ).image
            fun x => some (some x))))⁻¹ *
        replicaMetric ι₀ (a / 2) k ((Y (f j) g).image fun x => some (some x))) ^ 2
    let B := fun j g => ZOᴴ * A j g * ZO
    let M := (List.ofFn fun g : Fin S.K => T.eval (B · g)).prod
    let w := toEuclideanLin (M ^ (-(1 / 4) : ℝ)) (toEuclideanLin ZOᴴ ξ)
    let vO := toEuclideanLin ZO ((‖w‖⁻¹ : ℂ) • w)
    have he := hestimate (T.map f)
    simp only [MeanTree.eval_map] at he
    have hP (j : Σ hist, Option (Choice hist)) (g : Fin S.K) :
        (D.leafPart j g).P.image augmentedSiteEquiv.symm =
          insert (some none) ((Q (f j) g).image fun x => some (some x)) := by
      rw [hparts, augmentedPartition_eq_images]
      simp only [Finset.image_insert, Finset.image_image]
      rfl
    have hF (j : Σ hist, Option (Choice hist)) (g : Fin S.K) :
        (D.leafPart j g).F.image augmentedSiteEquiv.symm =
          insert none (((Q (f j) g ∪ Y (f j) g)ᶜ).image
            fun x => some (some x)) := by
      rw [hparts, augmentedPartition_eq_images]
      simp only [Finset.image_insert, Finset.image_image]
      change insert none ((receiving (σ (f j) g) true).image
        fun x => some (some x)) = _
      rw [hfar]
    have hY (j : Σ hist, Option (Choice hist)) (g : Fin S.K) :
        (D.leafPart j g).Y.image augmentedSiteEquiv.symm =
          (Y (f j) g).image (fun x => some (some x)) := by
      rw [hparts, augmentedPartition_eq_images]
      simp only [Finset.image_image]
      rfl
    have hroot :
        Transport.filteredNormSq (D.rootPath n (a / 2) k p) (pre k) = ‖w‖ ^ 2 ∧
        Transport.filteredVector (D.rootPath n (a / 2) k p) (pre k) =
          ZS *ᵥ ((‖w‖⁻¹ : ℂ) • w).ofLp := by
      have hr := (rootPath_augmented_compressed_bandProduct q d D hD
        (div_pos ha zero_lt_two).le k N hcomm ZS hZS hZSZS (pre k) hsym p).2.2.2
      simpa only [hP, hF, hY, T, A, B, M, w, ZO, ξ, e,
        toEuclideanLin, toLpLin_apply, WithLp.ofLp_toLp] using! hr
    have hvO :
        Transport.filteredVector (D.rootPath n (a / 2) k p) (pre k) ∘ e = vO.ofLp := by
      rw [hroot.2]
      rfl
    have henergyO : μ =
        (star vO ⬝ᵥ (globalReplicaMeanHamiltonian β (Fin d) (Fin d)
          (∑ i, S.truncatedEnergyTerm h Ω Δ L i) k *ᵥ vO)).re := by
      rw [henergy, hvO]
    have hvnorm : ‖vO‖ = 1 := he.2.1
    have hactualnorm : ‖WithLp.toLp 2
        (Transport.filteredVector (D.rootPath n (a / 2) k p) (pre k))‖ = 1 := by
      have hn := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e.symm).norm_map
        (WithLp.toLp 2 (Transport.filteredVector (D.rootPath n (a / 2) k p) (pre k)))
      have hnv : ‖WithLp.toLp 2
          (Transport.filteredVector (D.rootPath n (a / 2) k p) (pre k) ∘ e)‖ = 1 := by
        simpa only [hvO, WithLp.toLp_ofLp] using hvnorm
      exact hn.symm.trans hnv
    refine ⟨hactualnorm, ?_⟩
    change 0 < Transport.filteredNormSq (D.rootPath n (a / 2) k p) (pre k) ∧
      0 ≤ (μ - e₀) / gap ∧ _
    refine ⟨hroot.1.symm ▸ sq_pos_of_pos (norm_pos_iff.mpr he.1), ?_, ?_⟩
    · simpa only [henergyO] using he.2.2.1
    · intro τ hτ hτhalf
      have htwo : 2 * (a / 2) = a := by ring
      have hvariance : 50 * K * (a / 2) = 25 * K * a := by ring
      have hhalf : 2 * (1 / 4 : ℝ) = 1 / 2 := by norm_num
      simpa only [hroot.1, henergyO, htwo, hvariance, hhalf, Fintype.card_fin,
        ← two_mul, r, b, lower, entropyGap, gaps, gmax, T] using!
        he.2.2.2 τ hτ hτhalf
  exact
    ⟨hbound Dfill (S.actualFillData_isAdmissible hm hM s.val)
      (S.fillTransportData_crossBandCommute
        (historyMeanTree S.K S.m S.M hm hM s.val) n (div_pos ha zero_lt_two).le k)
      (fillTerminalIndex S.K S.m S.M Horizon s)
      (fun j g => actualFillData_leafPart_terminalPartition S hm hM Horizon s j g)
      _ (S.actualFillScanRound_meanEnergy_eq_globalReplicaMeanHamiltonian
        hm hM s.val h Ω Δ L a pre k p),
    hbound Dcharge (S.actualChargeData_isAdmissible hm hM s.val)
      (S.chargeTransportData_crossBandCommute
        (historyMeanTree S.K S.m S.M hm hM s.val)
        (fun _ => chargeChoiceTree S.K S.M hM) n (div_pos ha zero_lt_two).le k)
      (chargeTerminalIndex S.K S.m S.M Horizon s)
      (fun j g => actualChargeData_leafPart_terminalPartition S hm hM Horizon s j g)
      _ (S.actualChargeScanRound_meanEnergy_eq_globalReplicaMeanHamiltonian
        hm hM s.val h Ω Δ L a pre k p)⟩

end TNLean.PEPS.AreaLaw.Scan.CollarScan
