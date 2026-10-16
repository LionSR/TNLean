/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualRoughLower
import TNLean.PEPS.AreaLaw.Scan.ActualRoughLowerRemainder
import TNLean.PEPS.AreaLaw.Scan.AugmentedReplicaPrevectorProperties
import TNLean.PEPS.AreaLaw.TwoFamilies

/-!
# The same supplied physical sequence in the actual rough lower estimate

The supplied physical prevector and its supplied auxiliary labels are retained.
The comparison holds at every positive band weight at most one half; the
weight-four theorem is a specialization of this comparison.
Its nonzero/norm and little-o label conclusions are used directly; symmetry and
both auxiliary-label equations are derived for the literal augmented prevector.
The resulting root, normalized filtered vector and mean energy are the actual
fill or charge objects. No marginal-moment or small-energy hypothesis occurs.

Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 130--169,
255--281 and 585--651; `08-scanner.tex`, lines 400--474 and 755--769,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open Matrix TensorPower TensorPower.ReplicaTransport PermutationRepresentation Filter
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder Topology

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open ActualTerminals

open Classical in
/-- The same supplied physical prevector and labels satisfy the rough lower
comparison at every actual fill and charge point, with a common vanishing remainder.
Source: area-law manuscript, 07-comparators.tex, lines 97--169, 255--281 and
585--651; 08-scanner.tex, Proposition 9.2, lines 349--397. -/
theorem exists_actualScan_suppliedPrevector_rough_lower_of_weight
    {Λ : Finset (ℤ × ℤ)} {q d R : ℕ} {J : ℝ} [NeZero q] [NeZero d]
    [LinearOrder (AdmissibleSupport Λ R)] (Kband : ℕ)
    (a : ℝ) (ha : 0 < a) (haSmall : a ≤ 1 / 2) :
    ∃ c Cf : ℝ, 0 ≤ c ∧ 0 ≤ Cf ∧
      ∀ (S : CollarScan (Site Λ) (AdmissibleSupport Λ R)), S.K = Kband →
      ∀ (hm : 0 < S.m) (hM : 0 < S.M)
        (h : LocalHamiltonian Λ q R J) (Ω : StateSpace Λ q) (Δ : ℝ) (L : ℕ)
        (Ωt : StateSpace Λ q) (e₀ gap : ℝ),
      ‖Ωt‖ = 1 →
      ((∑ i, S.truncatedEnergyTerm h Ω Δ L i) - (e₀ : ℂ) • 1 -
        (gap : ℂ) • (1 - vecMulVec Ωt.ofLp (star Ωt.ofLp))).PosSemidef →
      0 < gap →
      ∀ (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))) (Sent : ℝ),
      (∀ k : ℕ, 0 < k →
        let β := fun _ : Site Λ => Fin q
        let ξ := WithLp.toLp 2 (replicaPrevector Ωt d k (ell k) ∘
          globalReplicaCopiesEquiv β (Fin d) (Fin d) k)
        ξ ≠ 0 ∧ ‖ξ‖ ≤ 1) →
      Asymptotics.IsLittleO atTop
        (fun k : ℕ => Real.log (ell k).dim - (k : ℝ) * Sent)
        (fun k : ℕ => (k : ℝ)) →
      let W := a * (Kband : ℝ)
      let n := augmentedDimensions (V := Site Λ) q (fun _ => d)
      let pre : (k : ℕ) → Config k (fun v => Fin (n v)) → ℂ := fun k =>
        replicaPrevector Ωt d k (ell k) ∘ augmentedSumReplicaCopiesEquiv q d k
      Tendsto (roughLowerRemainderAtWeight Kband a c Cf ell Sent) atTop (𝓝 0) ∧
      ∀ k : ℕ, 0 < k → ∀ (s : Fin (S.n * S.m)) (p : ℝ),
        let lower := fun (Nsq μ : ℝ) =>
          0 < Nsq ∧ 0 ≤ (μ - e₀) / gap ∧
            ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
              (W / 4) *
                  (4 * Sent - 6 * (τ * Real.log (d : ℝ) + Real.binEntropy τ / a) -
                    3 * (((μ - e₀) / gap) / τ) * max 0 (2 * Sent)) -
                  roughLowerRemainderAtWeight Kband a c Cf ell Sent k ≤
                    -Real.log Nsq / (k : ℝ)
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
    exists_actualScan_rough_lower_norm_of_weight (Λ := Λ) (q := q) (d := d) (R := R) (J := J)
      Kband a ha haSmall
  refine ⟨c, Cf, hc, hCf, ?_⟩
  intro S hSK hm hM h Ω Δ L Ωt e₀ gap hΩt hgap hgap_pos ell Sent hpre hdim
    W n pre
  let β := fun _ : Site Λ => Fin q
  refine ⟨tendsto_roughLowerRemainderAtWeight_of_label_dimension ell Sent hdim Kband a c Cf, ?_⟩
  intro k hk s p lower Dfill Dcharge
  let e := augmentedReplicaConfigurationEquiv (V := Site Λ) q d k
  have hpreEq : pre k ∘ e = replicaPrevector Ωt d k (ell k) ∘
      globalReplicaCopiesEquiv β (Fin d) (Fin d) k := by
    simp only [pre, augmentedSumReplicaCopiesEquiv, Equiv.coe_trans,
      Function.comp_assoc, e, Equiv.symm_comp_self, Function.comp_id, β]
  have hprenonzero : pre k ≠ 0 := by
    intro hz
    apply (hpre k hk).1
    change WithLp.toLp 2 (replicaPrevector Ωt d k (ell k) ∘
      globalReplicaCopiesEquiv β (Fin d) (Fin d) k) = 0
    rw [← hpreEq, hz]
    rfl
  have hprenorm : ‖WithLp.toLp 2 (pre k)‖ ≤ 1 := by
    have hn := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e.symm).norm_map
      (WithLp.toLp 2 (pre k))
    have hno : ‖WithLp.toLp 2 (pre k ∘ e)‖ ≤ 1 := by
      simpa only [hpreEq] using (hpre k hk).2
    exact hn.symm.trans_le hno
  have hsym : symProj (copyPerm ((v : Site Λ ⊕ Bool) → Fin (n v)) k) *ᵥ pre k = pre k :=
    symProj_mulVec_augmentedReplicaPrevector q d k Ωt (ell k)
  let ι₀ := addedSiteSpace (addedSiteSpace β (Fin d)) (Fin d)
  have haux := labelProj_globalReplicaCopiesEquiv_auxiliary β (Fin d) (Fin d)
    k (ell k) (ell k)
  have hfixed := replicaPrevector_auxiliary_label_fixed Ωt d k (ell k)
  have hC : labelProj (subsystemPerm k ι₀ {some none}) (ell k) *ᵥ
      (pre k ∘ e) = pre k ∘ e := by
    rw [hpreEq, ← haux.1]
    simpa only [Matrix.submatrix_mulVec_equiv, Function.comp_assoc,
      Equiv.self_comp_symm, Function.comp_id] using
      congrArg (fun v => v ∘ globalReplicaCopiesEquiv β (Fin d) (Fin d) k) hfixed.1
  have hR : labelProj (subsystemPerm k ι₀ {none}) (ell k) *ᵥ
      (pre k ∘ e) = pre k ∘ e := by
    rw [hpreEq, ← haux.2]
    simpa only [Matrix.submatrix_mulVec_equiv, Function.comp_assoc,
      Equiv.self_comp_symm, Function.comp_id] using
      congrArg (fun v => v ∘ globalReplicaCopiesEquiv β (Fin d) (Fin d) k) hfixed.2
  simpa only [roughLowerRemainderAtWeight] using!
    hlower S hSK hm hM (S.n * S.m) h Ω Δ L Ωt e₀ gap hΩt hgap hgap_pos
      pre k hk hprenonzero hprenorm hsym
      (ell k) Sent (roughLowerLabelDefect ell Sent k) hC hR
      (roughLowerLabelDefect_label_bound ell Sent k).2 s p


open Classical in
/-- The coefficient-three rough lower estimate for the same supplied physical
sequence, with a vanishing replica remainder common to every actual round and
interpolation. The polynomial constants are chosen before the scanner and state.
Source: `07-comparators.tex`, lines 130--169, 255--281 and 585--651;
`08-scanner.tex`, lines 400--474 and 755--769, adc7f124. -/
theorem exists_actualScan_suppliedPrevector_rough_lower
    {Λ : Finset (ℤ × ℤ)} {q d R : ℕ} {J : ℝ} [NeZero q] [NeZero d]
    [LinearOrder (AdmissibleSupport Λ R)] (Kband : ℕ) (hKband : 8 ≤ Kband) :
    ∃ c Cf : ℝ, 0 ≤ c ∧ 0 ≤ Cf ∧
      ∀ (S : CollarScan (Site Λ) (AdmissibleSupport Λ R)), S.K = Kband →
      ∀ (hm : 0 < S.m) (hM : 0 < S.M)
        (h : LocalHamiltonian Λ q R J) (Ω : StateSpace Λ q) (Δ : ℝ) (L : ℕ)
        (Ωt : StateSpace Λ q) (e₀ gap : ℝ),
      ‖Ωt‖ = 1 →
      ((∑ i, S.truncatedEnergyTerm h Ω Δ L i) - (e₀ : ℂ) • 1 -
        (gap : ℂ) • (1 - vecMulVec Ωt.ofLp (star Ωt.ofLp))).PosSemidef →
      0 < gap →
      ∀ (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))) (Sent : ℝ),
      (∀ k : ℕ, 0 < k →
        let β := fun _ : Site Λ => Fin q
        let ξ := WithLp.toLp 2 (replicaPrevector Ωt d k (ell k) ∘
          globalReplicaCopiesEquiv β (Fin d) (Fin d) k)
        ξ ≠ 0 ∧ ‖ξ‖ ≤ 1) →
      Asymptotics.IsLittleO atTop
        (fun k : ℕ => Real.log (ell k).dim - (k : ℝ) * Sent)
        (fun k : ℕ => (k : ℝ)) →
      let a := 4 / (Kband : ℝ)
      let _β := fun _ : Site Λ => Fin q
      let n := augmentedDimensions (V := Site Λ) q (fun _ => d)
      let pre : (k : ℕ) → Config k (fun v => Fin (n v)) → ℂ := fun k =>
        replicaPrevector Ωt d k (ell k) ∘ augmentedSumReplicaCopiesEquiv q d k
      Tendsto (roughLowerRemainder Kband c Cf ell Sent) atTop (𝓝 0) ∧
      ∀ k : ℕ, 0 < k → ∀ (s : Fin (S.n * S.m)) (p : ℝ),
        let lower := fun (Nsq μ : ℝ) =>
          0 < Nsq ∧ 0 ≤ (μ - e₀) / gap ∧
            ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
              4 * Sent - 6 * (τ * Real.log (d : ℝ) + Real.binEntropy τ / a) -
                3 * (((μ - e₀) / gap) / τ) * max 0 (2 * Sent) -
                  roughLowerRemainder Kband c Cf ell Sent k ≤
                    -Real.log Nsq / (k : ℝ)
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
  simpa only [roughLowerRemainder, roughLowerRemainderAtWeight,
    div_mul_cancel₀ (4 : ℝ) (ne_of_gt hKpos),
    div_self (by norm_num : (4 : ℝ) ≠ 0), _root_.one_mul] using!
    exists_actualScan_suppliedPrevector_rough_lower_of_weight
      (Λ := Λ) (q := q) (d := d) (R := R) (J := J) Kband (4 / (Kband : ℝ))
      (div_pos (by norm_num) hKpos)
      ((div_le_iff₀ hKpos).2 (by
        have hK8 : (8 : ℝ) ≤ Kband := by exact_mod_cast hKband
        linarith))

end TNLean.PEPS.AreaLaw.Scan.CollarScan
