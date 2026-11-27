/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Representation.Bell.LabelDimensionRemainder
import TNLean.PEPS.AreaLaw.Scanner.Rounds.AugmentedReplicaPrevectorProperties
import TNLean.PEPS.AreaLaw.Scanner.Statuses.StatusMarginalMoments
import TNLean.PEPS.AreaLaw.Collar.Scales.Exponents
import QICLean.ManyBody.Entropy.Template.TwoFamilies
import TNLean.PEPS.AreaLaw.Scanner.Rounds.ActualTerminalPartitions
import TNLean.PEPS.AreaLaw.Scanner.Rounds.ActualScanMeasures
import TNLean.PEPS.AreaLaw.Scanner.Rounds.AugmentedRootCompression
import QICLean.Algebra.Hermitian.OrthogonalProjection
import QICLean.ManyBody.Replica.LowDefect.RegionalSharpLowerNorm

/-!
# The same supplied physical sequence in the sharp lower estimate

The nonzero, norm and label-dimension conclusions of the physical prevector
construction are consumed for the supplied sequence. Its symmetry and both
original auxiliary labels are derived for the literal augmented prevector.
The actual fill and charge lower rates retain their actual energy defects;
the polynomial and label remainder vanishes for this same sequence.
There is no new label choice and no small-energy assumption.

Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 130--153,
255--281 and 550--651; `08-scanner.tex`, lines 400--474, adc7f124.

It also contains the following results.

* `TNLean.PEPS.AreaLaw.Scan.CollarScan.exists_actualScan_sharp_lower_norm`: sharp lower bounds for
  the actual fill and charge roots.
-/

section ActualSharpLower

/-!
## Sharp lower bounds for the actual fill and charge roots

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

open ManyBody (AdmissibleSupport PlaneInteraction)

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
    exact Finset.disjoint_filter.mpr fun _ _ hx hy => by
      have hfalse : (some false : Option Bool) = none := hx.symm.trans hy
      cases hfalse
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
      ∀ (S : CollarScan ↥Λ (AdmissibleSupport Λ R))
        (hm : 0 < S.m) (hM : 0 < S.M) (Horizon : ℕ)
        (h : PlaneInteraction Λ q R) (_ : ∀ X, (h.term X).IsHermitian) (_ : ∀ X, ‖h.term X‖ ≤ J)
            (Ω : EuclideanSpace ℂ (↥Λ → Fin q)) (Δ : ℝ) (L : ℕ)
        (Ωt : EuclideanSpace ℂ (↥Λ → Fin q)) (e₀ gap : ℝ),
      ‖Ωt‖ = 1 →
      ((∑ i, S.truncatedEnergyTerm h Ω J Δ L i) - (e₀ : ℂ) • 1 -
        (gap : ℂ) • (1 - vecMulVec Ωt.ofLp (star Ωt.ofLp))).PosSemidef →
      0 < gap →
      let β := fun _ : ↥Λ => Fin q
      let ι₀ := addedSiteSpace (addedSiteSpace β (Fin d)) (Fin d)
      let n := augmentedDimensions (V := ↥Λ) q (fun _ => d)
      let σ := terminalPartition S Horizon
      let Q := fun j g => receiving (σ j g) false
      let Y := fun j g => middle (σ j g)
      ∀ K rMom : ℝ,
      (∀ (j : terminalFamily S.K S.m S.M Horizon) (g : Fin S.K)
          (b : Fin 3) (v : ℝ), |v| ≤ rMom →
        let U := ManyBody.regionalPhysicalRegion (Q j g) (Y j g) b
        Real.log (Entropy.surprisalMoment
          (ManyBody.regionState_posSemidef U Ωt).isHermitian.eigenvalues v) ≤
            v * ManyBody.regionEntropy Ωt U + K * v ^ 2) →
      10 * a ≤ rMom → 10 * a ≤ 1 → 0 ≤ K →
      ∀ (pre : (k : ℕ) → Config k (fun v => Fin (n v)) → ℂ)
        (k : ℕ), 0 < k → pre k ≠ 0 → ‖WithLp.toLp 2 (pre k)‖ ≤ 1 →
      symProj (copyPerm ((v : ↥Λ ⊕ Bool) → Fin (n v)) k) *ᵥ pre k = pre k →
      ∀ (ellC ellR : IrrepLabel (Equiv.Perm (Fin k))) (Sent ε : ℝ),
      let e := augmentedReplicaConfigurationEquiv (V := ↥Λ) q d k
      labelProj (subsystemPerm k ι₀ {some none}) ellC *ᵥ (pre k ∘ e) = pre k ∘ e →
      labelProj (subsystemPerm k ι₀ {none}) ellR *ᵥ (pre k ∘ e) = pre k ∘ e →
      2 * (k : ℝ) * Sent - ε ≤ Real.log ellC.dim + Real.log ellR.dim →
      let entropyGap := fun j g =>
        ManyBody.regionEntropy Ωt (Q j g) +
          ManyBody.regionEntropy Ωt (Q j g ∪ Y j g)ᶜ -
          ManyBody.regionEntropy Ωt (Y j g)
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
              (S.actualEnergyTerms h Ω J Δ L (fun _ => d)) a pre).meanEnergy k p) Tfill) ∧
        (‖WithLp.toLp 2
            (Transport.filteredVector (Dcharge.rootPath n (a / 2) k p) (pre k))‖ = 1 ∧
          lower (Transport.filteredNormSq (Dcharge.rootPath n (a / 2) k p) (pre k))
            ((S.actualChargeScanRound hm hM s.val n
              (S.actualEnergyTerms h Ω J Δ L (fun _ => d)) a pre).meanEnergy k p) Tcharge) := by
  classical
  obtain ⟨c, Cf, hc, hCf, hlower⟩ :=
    exists_replicaMetric_symProj_bandProduct_sharp_lower_norm
      (fun _ : ↥Λ => Fin q) (Fin d) (Fin d) (div_pos ha zero_lt_two)
  refine ⟨c, Cf, hc, hCf, ?_⟩
  intro S hm hM Horizon h hh hhJ Ω Δ L Ωt e₀ gap hΩt hgap hgap_pos β ι₀ n σ Q Y
    K rMom hmoment har haone hK pre k hk hpre hprenorm hsym ellC ellR Sent ε e
    hC hR hlabel entropyGap gaps gmax r b lower s p Dfill Dcharge Tfill Tcharge
  let : DecidableEq (Config k ι₀) := Fintype.decidablePiFintype
  obtain ⟨hdisj, hnest, hfar⟩ := actualTerminal_sharpLower_geometry S Horizon
  obtain ⟨N, ZS, hZS, hZSZS⟩ :=
    (isStarProjection_symProj
      (copyPerm ((v : ↥Λ ⊕ Bool) → Fin (n v)) k)).exists_matrix_range_isometry
  let ZO := ZS.submatrix e (id : Fin N → Fin N)
  have hZO : ZOᴴ * ZO = 1 :=
    Matrix.IsIsometry.reindex ZS hZS e.symm (Equiv.refl (Fin N))
  have hSymm : symProj (copyPerm ((o : Option (Option ↥Λ)) → ι₀ o) k) =
      (symProj (copyPerm ((v : ↥Λ ⊕ Bool) → Fin (n v)) k)).submatrix e e := by
    simpa only [Matrix.reindex_apply, Equiv.symm_symm] using
      (symProj_of_intertwine e.symm
        (φ := copyPerm ((v : ↥Λ ⊕ Bool) → Fin (n v)) k)
        (ψ := copyPerm ((o : Option (Option ↥Λ)) → ι₀ o) k)
        (fun perm x => funext fun j => rfl))
  have hZOZO : ZO * ZOᴴ =
      symProj (copyPerm ((o : Option (Option ↥Λ)) → ι₀ o) k) := by
    simpa only [ZO, Matrix.conjTranspose_submatrix, Equiv.coe_refl] using
      ((Matrix.submatrix_mul_equiv ZS ZSᴴ e (Equiv.refl (Fin N)) e).trans
        (congrArg (fun P : Matrix (Config k (fun v => Fin (n v)))
          (Config k (fun v => Fin (n v))) ℂ => P.submatrix e e) hZSZS)).trans hSymm.symm
  let ξ : EuclideanSpace ℂ (Config k ι₀) := WithLp.toLp 2 (pre k ∘ e)
  have hξ : ξ ≠ 0 := by
    intro hzero
    apply hpre
    funext x
    change pre k x = 0
    have hx : pre k (e (e.symm x)) = 0 :=
      congrArg (fun v : EuclideanSpace ℂ (Config k ι₀) => v (e.symm x)) hzero
    simpa only [Equiv.apply_symm_apply] using hx
  have hξnorm : ‖ξ‖ ≤ 1 :=
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e.symm).norm_map
      (WithLp.toLp 2 (pre k))).trans_le hprenorm
  have hsymO : symProj (copyPerm ((o : Option (Option ↥Λ)) → ι₀ o) k) *ᵥ ξ = ξ := by
    change symProj (copyPerm ((o : Option (Option ↥Λ)) → ι₀ o) k) *ᵥ
      (pre k ∘ e) = pre k ∘ e
    simpa only [hSymm, Matrix.submatrix_mulVec_equiv, Function.comp_assoc,
      Equiv.self_comp_symm, Function.comp_id] using
      congrArg (fun v : Config k (fun x => Fin (n x)) → ℂ => v ∘ e) hsym
  have hsmall : 20 * (a / 2) = 10 * a := by ring
  have hestimate (T : MeanTree (terminalFamily S.K S.m S.M Horizon)) :=
    hlower k N hk (∑ i, S.truncatedEnergyTerm h Ω J Δ L i) Ωt.ofLp e₀ gap
      hgap hΩt hgap_pos ZO hZO hZOZO
      (terminalFamily S.K S.m S.M Horizon) S.K Q Y hdisj hnest K rMom hmoment
      (hsmall.symm ▸ har) (hsmall.symm ▸ haone) hK T ellC ellR Sent ε (1 / 4)
      hlabel (by norm_num) ξ hξ hξnorm hsymO hC hR
  have hbound {Hist : Type} [DecidableEq Hist] {Choice : Hist → Type}
      [∀ hist, DecidableEq (Choice hist)]
      (D : TransportData (↥Λ ⊕ Bool) S.K Hist Choice)
      (hD : D.IsAdmissible) (hcomm : D.CrossBandCommute n (a / 2) k)
      (f : (Σ hist, Option (Choice hist)) → terminalFamily S.K S.m S.M Horizon)
      (hparts : ∀ j g, D.leafPart j g = augmentedPartition (σ (f j) g))
      (μ : ℝ)
      (henergy : μ =
        let v := Transport.filteredVector (D.rootPath n (a / 2) k p) (pre k)
        let vO := v ∘ e
        (star vO ⬝ᵥ (globalReplicaMeanHamiltonian β (Fin d) (Fin d)
          (∑ i, S.truncatedEnergyTerm h Ω J Δ L i) k *ᵥ vO)).re) :
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
          (∑ i, S.truncatedEnergyTerm h Ω J Δ L i) k *ᵥ vO)).re := by
      rw [henergy]
      dsimp only
      rw [hvO]
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
    · rw [henergyO]
      exact he.2.2.1
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

end

end ActualSharpLower

section ActualSharpLowerPrevector

open scoped Matrix.Norms.L2Operator

noncomputable section

open Matrix TensorPower TensorPower.ReplicaTransport PermutationRepresentation Filter
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder Topology

open ManyBody (AdmissibleSupport PlaneInteraction)

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open ActualTerminals

private theorem sharp_lower_rate_of_finite_copy {G k : ℕ}
    {a err Nsq : ℝ} (ha : 0 < a) (hk : 0 < k) (rate : Fin G → ℝ)
    (h : (1 / 2) * (∑ g, (a * (k : ℝ) * rate g - err)) ≤ -Real.log Nsq) :
    (a / 2) * (∑ g, (rate g - err / (a * (k : ℝ)))) ≤
      -Real.log Nsq / (k : ℝ) := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  apply (le_div_iff₀ hkpos).2
  calc
    ((a / 2) * (∑ g, (rate g - err / (a * (k : ℝ))))) * (k : ℝ) =
        (1 / 2) * (∑ g, (a * (k : ℝ) * rate g - err)) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro g _
      field_simp [ha.ne', hkpos.ne']
    _ ≤ -Real.log Nsq := h

open Classical in
/-- A regional moment bound uses the same reduced matrix in finite-product coordinates. -/
private theorem sharpLower_marginalMoment_finiteProduct
    {Λ : Finset (ℤ × ℤ)} {q : ℕ}
    (Ωt : EuclideanSpace ℂ (↥Λ → Fin q)) (U : Finset ↥Λ) (Kmom u : ℝ)
    (h : Real.log (Entropy.surprisalMoment
      (ManyBody.regionState_isHermitian U Ωt).eigenvalues u) ≤
        u * ManyBody.regionEntropy Ωt U + Kmom * u ^ 2) :
    Real.log (Entropy.surprisalMoment
      (ManyBody.regionState_posSemidef U Ωt).isHermitian.eigenvalues u) ≤
      u * ManyBody.regionEntropy Ωt U + Kmom * u ^ 2 := by
  exact h

open Classical in
/-- Completed and pre-charge status moments supply all three original physical marginals. -/
private theorem actualTerminal_sharpLower_moments
    {Λ : Finset (ℤ × ℤ)} {q : ℕ} {I : Type} [Fintype I] [LinearOrder I]
    (S : CollarScan ↥Λ I) (Ωt : EuclideanSpace ℂ (↥Λ → Fin q)) (Kmom rMom : ℝ)
    (hmom : ∀ (s : ℕ) (hist : History S.K S.m S.M s) (g : Fin S.K),
      (s ≤ S.n * S.m → ∀ Q ∈ statusMarginalRegions S.depth (S.state hist g),
        ∀ u : ℝ, |u| ≤ rMom →
          Real.log (Entropy.surprisalMoment
            (ManyBody.regionState_isHermitian Q Ωt).eigenvalues u) ≤
            u * ManyBody.regionEntropy Ωt Q + Kmom * u ^ 2) ∧
      (s + 1 ≤ S.n * S.m →
        ∀ Q ∈ statusMarginalRegions S.depth (S.oldChargeState hist g),
          ∀ u : ℝ, |u| ≤ rMom →
            Real.log (Entropy.surprisalMoment
              (ManyBody.regionState_isHermitian Q Ωt).eigenvalues u) ≤
              u * ManyBody.regionEntropy Ωt Q + Kmom * u ^ 2)) :
    let σ := terminalPartition S (S.n * S.m)
    let Q := fun j g => receiving (σ j g) false
    let Y := fun j g => middle (σ j g)
    ∀ j g (b : Fin 3) (u : ℝ), |u| ≤ rMom →
      let U := ManyBody.regionalPhysicalRegion (Q j g) (Y j g) b
      Real.log (Entropy.surprisalMoment
        (ManyBody.regionState_posSemidef U Ωt).isHermitian.eigenvalues u) ≤
          u * ManyBody.regionEntropy Ωt U + Kmom * u ^ 2 := by
  classical
  intro σ Q Y
  have hfar (j : terminalFamily S.K S.m S.M (S.n * S.m)) (g : Fin S.K) :
      receiving (σ j g) true = (Q j g ∪ Y j g)ᶜ := by
    ext x
    cases hx : σ j g x with
    | none => simp [Q, Y, receiving, middle, hx]
    | some side => cases side <;> simp [Q, Y, receiving, middle, hx]
  have hmomStatus : ∀ j g (U : Finset ↥Λ),
      U ∈ statusMarginalRegions S.depth (σ j g) →
      ∀ u : ℝ, |u| ≤ rMom →
        Real.log (Entropy.surprisalMoment
          (ManyBody.regionState_isHermitian U Ωt).eigenvalues u) ≤
          u * ManyBody.regionEntropy Ωt U + Kmom * u ^ 2 := fun
    | Sum.inl ⟨s, hist⟩, g, U, hU, u, hu =>
      (hmom s.val hist g).1 (Nat.le_of_lt_succ s.isLt) U hU u hu
    | Sum.inr ⟨s, hist⟩, g, U, hU, u, hu =>
      (hmom s.val hist g).2 (Nat.succ_le_of_lt s.isLt) U hU u hu
  intro j g b u hu U
  have hmem : U ∈ statusMarginalRegions S.depth (σ j g) := by
    fin_cases b
    · simp [U, ManyBody.regionalPhysicalRegion, statusMarginalRegions, Q]
    · simp [U, ManyBody.regionalPhysicalRegion, statusMarginalRegions, Y]
    · change (Q j g ∪ Y j g)ᶜ ∈ statusMarginalRegions S.depth (σ j g)
      rw [← hfar]
      simp [statusMarginalRegions]
  exact sharpLower_marginalMoment_finiteProduct Ωt U Kmom u
    (hmomStatus j g U hmem u hu)

open Classical in
/-- The fixed supplied prevector keeps its norm, symmetry and both auxiliary labels. -/
private theorem sharpLower_suppliedPrevector_properties
    {Λ : Finset (ℤ × ℤ)} (q d k : ℕ) (Ωt : EuclideanSpace ℂ (↥Λ → Fin q))
    (ell : IrrepLabel (Equiv.Perm (Fin k)))
    (hpre :
      let β := fun _ : ↥Λ => Fin q
      let ξ := WithLp.toLp 2 (replicaPrevector Ωt d k ell ∘
        globalReplicaCopiesEquiv β (Fin d) (Fin d) k)
      ξ ≠ 0 ∧ ‖ξ‖ ≤ 1) :
    let β := fun _ : ↥Λ => Fin q
    let n := augmentedDimensions (V := ↥Λ) q (fun _ => d)
    let pre : Config k (fun v => Fin (n v)) → ℂ :=
      replicaPrevector Ωt d k ell ∘ augmentedSumReplicaCopiesEquiv q d k
    let e := augmentedReplicaConfigurationEquiv (V := ↥Λ) q d k
    let ι₀ := addedSiteSpace (addedSiteSpace β (Fin d)) (Fin d)
    pre ≠ 0 ∧ ‖WithLp.toLp 2 pre‖ ≤ 1 ∧
      symProj (copyPerm ((v : ↥Λ ⊕ Bool) → Fin (n v)) k) *ᵥ pre = pre ∧
      labelProj (subsystemPerm k ι₀ {some none}) ell *ᵥ (pre ∘ e) = pre ∘ e ∧
      labelProj (subsystemPerm k ι₀ {none}) ell *ᵥ (pre ∘ e) = pre ∘ e := by
  classical
  intro β n pre e ι₀
  have hpreEq : pre ∘ e = replicaPrevector Ωt d k ell ∘
      globalReplicaCopiesEquiv β (Fin d) (Fin d) k := by
    simp only [pre, augmentedSumReplicaCopiesEquiv, Equiv.coe_trans,
      Function.comp_assoc, e, Equiv.symm_comp_self, Function.comp_id, β]
  have hprenonzero : pre ≠ 0 :=
    (augmentedReplicaPrevector_ne_zero_iff_global q d k Ωt ell).mpr hpre.1
  have hprenorm : ‖WithLp.toLp 2 pre‖ ≤ 1 :=
    (norm_augmentedReplicaPrevector_eq_global q d k Ωt ell).trans_le hpre.2
  have hsym : symProj (copyPerm ((v : ↥Λ ⊕ Bool) → Fin (n v)) k) *ᵥ pre = pre :=
    symProj_mulVec_augmentedReplicaPrevector q d k Ωt ell
  have haux := labelProj_globalReplicaCopiesEquiv_auxiliary β (Fin d) (Fin d)
    k ell ell
  have hfixed := replicaPrevector_auxiliary_label_fixed Ωt d k ell
  have hC : labelProj (subsystemPerm k ι₀ {some none}) ell *ᵥ
      (pre ∘ e) = pre ∘ e := by
    rw [hpreEq, ← haux.1]
    simpa only [Matrix.submatrix_mulVec_equiv, Function.comp_assoc,
      Equiv.self_comp_symm, Function.comp_id] using
      congrArg (fun v => v ∘ globalReplicaCopiesEquiv β (Fin d) (Fin d) k) hfixed.1
  have hR : labelProj (subsystemPerm k ι₀ {none}) ell *ᵥ
      (pre ∘ e) = pre ∘ e := by
    rw [hpreEq, ← haux.2]
    simpa only [Matrix.submatrix_mulVec_equiv, Function.comp_assoc,
      Equiv.self_comp_symm, Function.comp_id] using
      congrArg (fun v => v ∘ globalReplicaCopiesEquiv β (Fin d) (Fin d) k) hfixed.2
  exact ⟨hprenonzero, hprenorm, hsym, hC, hR⟩

open Classical in
/-- The original supplied Schmidt--Bell label sequence satisfies the actual
sharp lower rate with a vanishing replica remainder. The two sequence premises
are precisely the nonzero/norm and little-o conclusions of the accepted physical
prevector theorem; the auxiliary and symmetry equations are derived here.
All physical marginal moments concern the same unit state used in the gap.
The actual energy defect remains explicit at every interpolation.
Source: `07-comparators.tex`, lines 130--153, 255--281 and 550--651;
`08-scanner.tex`, lines 400--474, adc7f124. -/
theorem exists_actualScan_suppliedPrevector_sharp_lower
    {Λ : Finset (ℤ × ℤ)} {q d R : ℕ} {J : ℝ} [NeZero q] [NeZero d]
    [LinearOrder (AdmissibleSupport Λ R)]
    (S : CollarScan ↥Λ (AdmissibleSupport Λ R))
    (hm : 0 < S.m) (hM : 0 < S.M)
    (h : PlaneInteraction Λ q R) (hh : ∀ X, (h.term X).IsHermitian) (hhJ : ∀ X, ‖h.term X‖ ≤ J)
        (Ω : EuclideanSpace ℂ (↥Λ → Fin q)) (Δ : ℝ) (L : ℕ)
    (Ωt : EuclideanSpace ℂ (↥Λ → Fin q)) (e₀ gap : ℝ) (hΩt : ‖Ωt‖ = 1)
    (hgap : ((∑ i, S.truncatedEnergyTerm h Ω J Δ L i) - (e₀ : ℂ) • 1 -
      (gap : ℂ) • (1 - vecMulVec Ωt.ofLp (star Ωt.ofLp))).PosSemidef)
    (hgap_pos : 0 < gap)
    (a Kmom rMom : ℝ) (ha : 0 < a) (har : 10 * a ≤ rMom)
    (haone : 10 * a ≤ 1) (hK : 0 ≤ Kmom)
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))) (Sent : ℝ)
    (hpre : ∀ k : ℕ, 0 < k →
      let β := fun _ : ↥Λ => Fin q
      let ξ := WithLp.toLp 2 (replicaPrevector Ωt d k (ell k) ∘
        globalReplicaCopiesEquiv β (Fin d) (Fin d) k)
      ξ ≠ 0 ∧ ‖ξ‖ ≤ 1)
    (hdim : Asymptotics.IsLittleO atTop
      (fun k : ℕ => Real.log (ell k).dim - (k : ℝ) * Sent)
      (fun k : ℕ => (k : ℝ)))
    (hmom : ∀ (s : ℕ) (hist : History S.K S.m S.M s) (g : Fin S.K),
      (s ≤ S.n * S.m → ∀ Q ∈ statusMarginalRegions S.depth (S.state hist g),
        ∀ u : ℝ, |u| ≤ rMom →
          Real.log (Entropy.surprisalMoment
            (ManyBody.regionState_isHermitian Q Ωt).eigenvalues u) ≤
            u * ManyBody.regionEntropy Ωt Q + Kmom * u ^ 2) ∧
      (s + 1 ≤ S.n * S.m →
        ∀ Q ∈ statusMarginalRegions S.depth (S.oldChargeState hist g),
          ∀ u : ℝ, |u| ≤ rMom →
            Real.log (Entropy.surprisalMoment
              (ManyBody.regionState_isHermitian Q Ωt).eigenvalues u) ≤
              u * ManyBody.regionEntropy Ωt Q + Kmom * u ^ 2)) :
    let n := augmentedDimensions (V := ↥Λ) q (fun _ => d)
    let pre : (k : ℕ) → Config k (fun v => Fin (n v)) → ℂ := fun k =>
      replicaPrevector Ωt d k (ell k) ∘ augmentedSumReplicaCopiesEquiv q d k
    let σ := terminalPartition S (S.n * S.m)
    let Q := fun j g => receiving (σ j g) false
    let Y := fun j g => middle (σ j g)
    let entropyGap := fun j g =>
      ManyBody.regionEntropy Ωt (Q j g) +
        ManyBody.regionEntropy Ωt (Q j g ∪ Y j g)ᶜ -
        ManyBody.regionEntropy Ωt (Y j g)
    let gaps := (Finset.univ :
      Finset (terminalFamily S.K S.m S.M (S.n * S.m) × Fin S.K)).image
        (fun j => entropyGap j.1 j.2)
    let gmax := (insert (0 : ℝ) gaps).max' (Finset.insert_nonempty _ _)
    ∃ c Cf : ℝ, 0 ≤ c ∧ 0 ≤ Cf ∧
      Tendsto (sharpLowerRemainder a c Cf ell Sent) atTop (𝓝 0) ∧
      ∀ k : ℕ, 0 < k → ∀ (s : Fin (S.n * S.m)) (p : ℝ),
        let lower := fun (Nsq μ : ℝ)
            (T : MeanTree (terminalFamily S.K S.m S.M (S.n * S.m))) =>
          0 < Nsq ∧ 0 ≤ (μ - e₀) / gap ∧
            ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
              let rate := fun g => 2 * Sent +
                (1 - τ) * (∑ j, T.weight j * entropyGap j g) -
                  τ * (2 * Real.log (d : ℝ)) -
                  (3 + 1 / a) * Real.binEntropy τ - 25 * Kmom * a
              (a / 2) * (∑ g,
                (rate g - (μ - e₀) / gap / τ * max 0 (2 * Sent + gmax) -
                  sharpLowerRemainder a c Cf ell Sent k)) ≤
                -Real.log Nsq / (k : ℝ)
        let Dfill := S.actualFillData hm hM s.val
        let Dcharge := S.actualChargeData hm hM s.val
        let Tfill := (Dfill.tree (Set.projIcc (0 : ℝ) 1 zero_le_one p)).map
          (fillTerminalIndex S.K S.m S.M (S.n * S.m) s)
        let Tcharge := (Dcharge.tree (Set.projIcc (0 : ℝ) 1 zero_le_one p)).map
          (chargeTerminalIndex S.K S.m S.M (S.n * S.m) s)
        (‖WithLp.toLp 2
            (Transport.filteredVector (Dfill.rootPath n (a / 2) k p) (pre k))‖ = 1 ∧
          lower (Transport.filteredNormSq (Dfill.rootPath n (a / 2) k p) (pre k))
            ((S.actualFillScanRound hm hM s.val n
              (S.actualEnergyTerms h Ω J Δ L (fun _ => d)) a pre).meanEnergy k p) Tfill) ∧
        (‖WithLp.toLp 2
            (Transport.filteredVector (Dcharge.rootPath n (a / 2) k p) (pre k))‖ = 1 ∧
          lower (Transport.filteredNormSq (Dcharge.rootPath n (a / 2) k p) (pre k))
            ((S.actualChargeScanRound hm hM s.val n
              (S.actualEnergyTerms h Ω J Δ L (fun _ => d)) a pre).meanEnergy k p) Tcharge) := by
  classical
  intro n pre σ Q Y entropyGap gaps gmax
  obtain ⟨c, Cf, hc, hCf, hlower⟩ :=
    exists_actualScan_sharp_lower_norm (Λ := Λ) (q := q) (d := d) (R := R) (J := J) a ha
  refine ⟨c, Cf, hc, hCf,
    tendsto_sharpLowerRemainder_of_label_dimension ell Sent hdim a c Cf, ?_⟩
  have hmomQ := actualTerminal_sharpLower_moments S Ωt Kmom rMom hmom
  intro k hk s p lower Dfill Dcharge Tfill Tcharge
  obtain ⟨hprenonzero, hprenorm, hsym, hC, hR⟩ :=
    sharpLower_suppliedPrevector_properties q d k Ωt (ell k) (hpre k hk)
  obtain ⟨⟨hfnorm, hfpos, hfδ, hf⟩, ⟨hcnorm, hcpos, hcδ, hcharge⟩⟩ :=
    hlower S hm hM (S.n * S.m) h hh hhJ Ω Δ L Ωt e₀ gap hΩt hgap hgap_pos
      Kmom rMom hmomQ har haone hK pre k hk hprenonzero hprenorm hsym
      (ell k) (ell k) Sent (labelDimensionDefect ell Sent k) hC hR
      (labelDimensionDefect_label_bound ell Sent k).2 s p
  refine ⟨⟨hfnorm, hfpos, hfδ, ?_⟩, ⟨hcnorm, hcpos, hcδ, ?_⟩⟩
  · intro τ hτ hτhalf
    simpa only [sharpLowerRemainder] using
      sharp_lower_rate_of_finite_copy ha hk _ (hf τ hτ hτhalf)
  · intro τ hτ hτhalf
    simpa only [sharpLowerRemainder] using
      sharp_lower_rate_of_finite_copy ha hk _ (hcharge τ hτ hτhalf)

end TNLean.PEPS.AreaLaw.Scan.CollarScan

end

end ActualSharpLowerPrevector
