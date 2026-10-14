/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualTerminalPartitions
import TNLean.PEPS.AreaLaw.Scan.ActualGlobalReplicaEnergy
import TNLean.PEPS.AreaLaw.Scan.AugmentedRootCompression
import QICLean.Algebra.ProjectionRangeIsometry
import QICLean.Analysis.RegionalRoughLowerThree

/-!
# Rough lower bounds for the literal actual fill and charge roots

The total band weight is four. The comparison uses the original physical
unit state and gap, the same supplied prevector and the same auxiliary
label on C and R. The defect is the actual mean energy of its normalized
filtered vector. No marginal-moment premise or sharp smallness is used.

The polynomial constants precede the scanner, horizon, physical state,
copy number, label and interpolation parameter. The band count is fixed
before the constants; the scanner is required to have that band count.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`07-comparators.tex`, lines 153--169 and 585--651, and `08-scanner.tex`,
lines 371--384, 416--451 and 755--769, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The QIC comparison is the accepted
`Matrix.exists_replicaMetric_symProj_bandProduct_rough_lower_norm_three`,
QICLean revision `e44381d9054ba5c42c720624cb690b251ad21533`.
-/

noncomputable section

open Matrix TensorPower TensorPower.ReplicaTransport PermutationRepresentation
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open ActualTerminals

open Classical in
/-- The finite-copy rough lower estimate at total band weight four for the
literal actual fill and charge roots and their actual normalized energies.
The same supplied physical state, prevector and auxiliary label are retained.
Source: `07-comparators.tex`, lines 153--169 and 585--651;
`08-scanner.tex`, lines 371--384, 416--451 and 755--769, adc7f124. -/
theorem exists_actualScan_rough_lower_norm
    {Λ : Finset (ℤ × ℤ)} {q d R : ℕ} {J : ℝ} [NeZero q] [NeZero d]
    [LinearOrder (AdmissibleSupport Λ R)] (Kband : ℕ) (hKband : 8 ≤ Kband) :
    ∃ c Cf : ℝ, 0 ≤ c ∧ 0 ≤ Cf ∧
      ∀ (S : CollarScan (Site Λ) (AdmissibleSupport Λ R)), S.K = Kband →
      ∀ (hm : 0 < S.m) (hM : 0 < S.M) (Horizon : ℕ)
        (h : LocalHamiltonian Λ q R J) (Ω : StateSpace Λ q) (Δ : ℝ) (L : ℕ)
        (Ωt : StateSpace Λ q) (e₀ gap : ℝ),
      ‖Ωt‖ = 1 →
      ((∑ i, S.truncatedEnergyTerm h Ω Δ L i) - (e₀ : ℂ) • 1 -
        (gap : ℂ) • (1 - vecMulVec Ωt.ofLp (star Ωt.ofLp))).PosSemidef →
      0 < gap →
      let a := 4 / (Kband : ℝ)
      let n := augmentedDimensions (V := Site Λ) q (fun _ => d)
      ∀ (pre : (k : ℕ) → Config k (fun v => Fin (n v)) → ℂ)
        (k : ℕ), 0 < k → pre k ≠ 0 → ‖WithLp.toLp 2 (pre k)‖ ≤ 1 →
      symProj (copyPerm ((v : Site Λ ⊕ Bool) → Fin (n v)) k) *ᵥ pre k = pre k →
      ∀ (ell : IrrepLabel (Equiv.Perm (Fin k))) (Sent ε : ℝ),
      let β := fun _ : Site Λ => Fin q
      let ι₀ := addedSiteSpace (addedSiteSpace β (Fin d)) (Fin d)
      let e := augmentedReplicaConfigurationEquiv (V := Site Λ) q d k
      labelProj (subsystemPerm k ι₀ {some none}) ell *ᵥ (pre k ∘ e) = pre k ∘ e →
      labelProj (subsystemPerm k ι₀ {none}) ell *ᵥ (pre k ∘ e) = pre k ∘ e →
      2 * (k : ℝ) * Sent - ε ≤ Real.log ell.dim + Real.log ell.dim →
      let r := Real.log ((k : ℝ) + 1) + c * Real.log ((k : ℝ) + 2) + a * ε
      let remainder := ((Kband : ℝ) / 2 * (2 * |r| + Cf * Real.log ((k : ℝ) + 2) +
        2 * Real.log 2 + Real.log (3 / 2))) / (k : ℝ)
      let lower := fun (Nsq μ : ℝ) =>
        0 < Nsq ∧ 0 ≤ (μ - e₀) / gap ∧
          ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
            4 * Sent - 6 * (τ * Real.log (d : ℝ) + Real.binEntropy τ / a) -
              3 * (((μ - e₀) / gap) / τ) * max 0 (2 * Sent) - remainder ≤
                -Real.log Nsq / (k : ℝ)
      ∀ (s : Fin Horizon) (p : ℝ),
        let Dfill := S.actualFillData hm hM s.val
        let Dcharge := S.actualChargeData hm hM s.val
        (‖WithLp.toLp 2
            (Transport.filteredVector (Dfill.rootPath n (a / 2) k p) (pre k))‖ = 1 ∧
          lower (Transport.filteredNormSq (Dfill.rootPath n (a / 2) k p) (pre k))
            ((S.actualFillScanRound hm hM s.val n
              (S.actualEnergyTerms h Ω Δ L (fun _ => d)) a pre).meanEnergy k p)) ∧
        (‖WithLp.toLp 2
            (Transport.filteredVector (Dcharge.rootPath n (a / 2) k p) (pre k))‖ = 1 ∧
          lower (Transport.filteredNormSq (Dcharge.rootPath n (a / 2) k p) (pre k))
            ((S.actualChargeScanRound hm hM s.val n
              (S.actualEnergyTerms h Ω Δ L (fun _ => d)) a pre).meanEnergy k p)) := by
  classical
  obtain ⟨c, Cf, hc, hCf, hlower⟩ :=
    exists_replicaMetric_symProj_bandProduct_rough_lower_norm_three
      (fun _ : Site Λ => Fin q) d Kband hKband
  refine ⟨c, Cf, hc, hCf, ?_⟩
  intro S hSK hm hM Horizon h Ω Δ L Ωt e₀ gap hΩt hgap hgap_pos a n
    pre k hk hpre hprenorm hsym ell Sent ε β ι₀ e hC hR hlabel r remainder lower
    s p Dfill Dcharge
  subst Kband
  let : DecidableEq (Config k ι₀) := Fintype.decidablePiFintype
  have hKpos : (0 : ℝ) < S.K := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 8) hKband)
  have ha : 0 < a := div_pos (by norm_num) hKpos
  have htEq : 2 / (S.K : ℝ) = a / 2 := by dsimp only [a]; ring
  let σ := terminalPartition S Horizon
  let Q := fun j g => receiving (σ j g) false
  let Y := fun j g => middle (σ j g)
  have hdisj : ∀ j g, Disjoint (Q j g) (Y j g) := fun j g => by
    simp only [Q, Y, receiving, middle]
    exact Finset.disjoint_filter.mpr fun _ _ hx hy => by simp_all
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
    change pre k x = 0
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
  have hestimate (T : MeanTree (terminalFamily S.K S.m S.M Horizon)) :=
    hlower k N hk (∑ i, S.truncatedEnergyTerm h Ω Δ L i) Ωt.ofLp e₀ gap
      hgap hΩt hgap_pos ZO hZO hZOZO
      (terminalFamily S.K S.m S.M Horizon) Q Y hdisj hnest
      T ell Sent ε hlabel ξ hξ hξnorm hsymO hC hR
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
        lower (Transport.filteredNormSq (D.rootPath n (a / 2) k p) (pre k)) μ := by
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
    simp only [MeanTree.eval_map, htEq] at he
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
      simpa only [hroot.1, henergyO, r, remainder, lower, a, T] using!
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
