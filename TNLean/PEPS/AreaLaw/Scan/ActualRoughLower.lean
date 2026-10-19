/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualTerminalPartitions
import TNLean.PEPS.AreaLaw.Scan.ActualGlobalReplicaEnergy
import TNLean.PEPS.AreaLaw.Scan.AugmentedRootCompression
import QICLean.Algebra.ProjectionRangeIsometry
import QICLean.Analysis.RegionalRoughLowerNorm
import QICLean.Analysis.RoughLowerCoefficient

/-!
# The actual rough lower comparison at an arbitrary fixed band weight

The same supplied prevector and physical mean energy obey the rough lower
comparison for every positive per-band weight at most one half. The replica
remainder is uniform over the actual fill and charge points.

Source: the area-law manuscript, 07-comparators.tex, lines 97--169 and
585--651, and 08-scanner.tex, Proposition 9.2, lines 349--397.
-/

noncomputable section

open Matrix TensorPower TensorPower.ReplicaTransport PermutationRepresentation
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open ActualTerminals

open Classical in
/-- The actual finite-copy rough lower comparison at total weight W = a K.
The positive part retains arbitrary entropy parameter Sent.
Source: area-law manuscript, 07-comparators.tex, lines 97--169 and 585--651;
08-scanner.tex, Proposition 9.2, lines 349--397. -/
theorem exists_actualScan_rough_lower_norm_of_weight
    {Λ : Finset (ℤ × ℤ)} {q d R : ℕ} {J : ℝ} [NeZero q] [NeZero d]
    [LinearOrder (AdmissibleSupport Λ R)] (Kband : ℕ)
    (a : ℝ) (ha : 0 < a) (haSmall : a ≤ 1 / 2) :
    ∃ c Cf : ℝ, 0 ≤ c ∧ 0 ≤ Cf ∧
      ∀ (S : CollarScan (Site Λ) (AdmissibleSupport Λ R)), S.K = Kband →
      ∀ (hm : 0 < S.m) (hM : 0 < S.M) (Horizon : ℕ)
        (h : LocalHamiltonian Λ q R J) (Ω : StateSpace Λ q) (Δ : ℝ) (L : ℕ)
        (Ωt : StateSpace Λ q) (e₀ gap : ℝ),
      ‖Ωt‖ = 1 →
      ((∑ i, S.truncatedEnergyTerm h Ω Δ L i) - (e₀ : ℂ) • 1 -
        (gap : ℂ) • (1 - vecMulVec Ωt.ofLp (star Ωt.ofLp))).PosSemidef →
      0 < gap →
      let W := a * (Kband : ℝ)
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
            (W / 4) *
                (4 * Sent - 6 * (τ * Real.log (d : ℝ) + Real.binEntropy τ / a) -
                  3 * (((μ - e₀) / gap) / τ) * max 0 (2 * Sent)) - remainder ≤
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
    exists_replicaMetric_symProj_bandProduct_rough_lower_norm
      (fun _ : Site Λ => Fin q) (Fin d) (Fin d)
      (div_pos ha zero_lt_two) (by linarith only [haSmall])
  refine ⟨c, Cf, hc, hCf, ?_⟩
  intro S hSK hm hM Horizon h Ω Δ L Ωt e₀ gap hΩt hgap hgap_pos W n
    pre k hk hpre hprenorm hsym ell Sent ε β ι₀ e hC hR hlabel r remainder lower
    s p Dfill Dcharge
  subst Kband
  let : DecidableEq (Config k ι₀) := Fintype.decidablePiFintype
  let σ := terminalPartition S Horizon
  let Q := fun j g => receiving (σ j g) false
  let Y := fun j g => middle (σ j g)
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
  have hestimate (T : MeanTree (terminalFamily S.K S.m S.M Horizon)) :
      let metric := replicaMetric ι₀ (a / 2) k
      let leftRegion := fun j g => insert (some none) ((Q j g).image fun x => some (some x))
      let F := fun j g => insert none
        (((Q j g ∪ Y j g)ᶜ).image fun x => some (some x))
      let E := fun j g => (Y j g).image fun x => some (some x)
      let A := fun j g =>
        ((metric (leftRegion j g))⁻¹ * (metric (F j g))⁻¹ * metric (E j g)) ^ 2
      let B := fun j g => ZOᴴ * A j g * ZO
      let M := (List.ofFn fun g : Fin S.K => T.eval (B · g)).prod
      let w := toEuclideanLin (M ^ (-(1 / 4 : ℝ))) (toEuclideanLin ZOᴴ ξ)
      let φ := (‖w‖⁻¹ : ℂ) • w
      let v := toEuclideanLin ZO φ
      let δ := ((star v ⬝ᵥ (globalReplicaMeanHamiltonian β (Fin d) (Fin d)
        (∑ i, S.truncatedEnergyTerm h Ω Δ L i) k *ᵥ v)).re - e₀) / gap
      w ≠ 0 ∧ ‖v‖ = 1 ∧ 0 ≤ δ ∧
        ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
          (W / 4) *
              (4 * Sent - 6 * (τ * Real.log (d : ℝ) + Real.binEntropy τ / a) -
                3 * (δ / τ) * max 0 (2 * Sent)) - remainder ≤
            -Real.log (‖w‖ ^ 2) / (k : ℝ) := by
    intro metric leftRegion F E A B M w φ v δ
    have hraw :=
      hlower k N hk (∑ i, S.truncatedEnergyTerm h Ω Δ L i) Ωt.ofLp e₀ gap
        hgap hΩt hgap_pos ZO hZO hZOZO
        (terminalFamily S.K S.m S.M Horizon) S.K Q Y hdisj hnest
        T ell ell Sent ε (1 / 4 : ℝ) hlabel (by norm_num)
        ξ hξ hξnorm hsymO hC hR
    refine ⟨hraw.1, hraw.2.1, hraw.2.2.1, fun τ hτ hτhalf ↦ ?_⟩
    have hfloor : |Real.log (((k : ℝ) + 2) ^ (-Cf) / 2)| =
        Cf * Real.log ((k : ℝ) + 2) + Real.log 2 := by
      rw [Real.log_div
          (Real.rpow_pos_of_pos
            (add_pos_of_nonneg_of_pos (Nat.cast_nonneg k) zero_lt_two) (-Cf)).ne'
          two_ne_zero,
        Real.log_rpow (add_pos_of_nonneg_of_pos (Nat.cast_nonneg k) zero_lt_two),
        neg_mul, sub_eq_add_neg, ← neg_add, abs_neg,
        abs_of_nonneg (add_nonneg
          (mul_nonneg hCf (Real.log_nonneg
            (one_le_two.trans (le_add_of_nonneg_left (Nat.cast_nonneg k)))))
          (Real.log_nonneg one_le_two))]
    have hcoefficient := mul_le_mul_of_nonneg_left
      (Real.rough_lower_coefficient_three Sent (Real.log (d : ℝ))
        (Real.binEntropy τ) δ τ a (Real.log_natCast_nonneg d)
        (Real.binEntropy_nonneg hτ.le (hτhalf.trans (by norm_num)))
        hraw.2.2.1 hτ ha haSmall)
      (show 0 ≤ W / 4 from div_nonneg
        (mul_nonneg ha.le (Nat.cast_nonneg S.K)) (by norm_num))
    have hdiv :
        (2 * (1 / 4 : ℝ) * (S.K : ℝ) *
          (a * (k : ℝ) *
            (2 * Sent - τ * (Real.log (d : ℝ) + Real.log (d : ℝ)) -
              (3 + 1 / a) * Real.binEntropy τ - δ / τ * max 0 (2 * Sent)) -
            (2 * |r| + (Cf * Real.log ((k : ℝ) + 2) + Real.log 2) +
              Real.log 2 + Real.log (3 / 2)))) / (k : ℝ) ≤
            -Real.log (‖w‖ ^ 2) / (k : ℝ) := by
      simpa only [Fintype.card_fin, mul_div_cancel₀ a (two_ne_zero : (2 : ℝ) ≠ 0), hfloor, r] using
        div_le_div_of_nonneg_right (hraw.2.2.2 τ hτ hτhalf) (Nat.cast_nonneg (α := ℝ) k)
    have hnormalize (u : ℝ) :
        (2 * (1 / 4 : ℝ) * (S.K : ℝ) *
          (a * (k : ℝ) * u -
            (2 * |r| + (Cf * Real.log ((k : ℝ) + 2) + Real.log 2) +
              Real.log 2 + Real.log (3 / 2)))) / (k : ℝ) =
          W / 4 * (2 * u) - remainder := by
      dsimp only [W, remainder]
      field_simp [show (k : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hk)]
      ring
    rw [hnormalize] at hdiv
    simpa only [show (2 : ℝ) * 3 = 6 by norm_num] using
      (sub_le_sub_right hcoefficient remainder).trans hdiv
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
      simpa only [hroot.1, henergyO, r, remainder, lower, T] using!
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
  have hKpos : (0 : ℝ) < Kband := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 8) hKband)
  have ha : 0 < (4 : ℝ) / Kband := div_pos (by norm_num) hKpos
  have haSmall : (4 : ℝ) / Kband ≤ 1 / 2 := (div_le_iff₀ hKpos).2 (by
    have hK8 : (8 : ℝ) ≤ Kband := by exact_mod_cast hKband
    linarith)
  simpa only [div_mul_cancel₀ (4 : ℝ) (ne_of_gt hKpos),
    div_self (by norm_num : (4 : ℝ) ≠ 0), _root_.one_mul] using
    exists_actualScan_rough_lower_norm_of_weight (Λ := Λ) (q := q) (d := d)
      (R := R) (J := J) Kband (4 / (Kband : ℝ)) ha haSmall

end TNLean.PEPS.AreaLaw.Scan.CollarScan
