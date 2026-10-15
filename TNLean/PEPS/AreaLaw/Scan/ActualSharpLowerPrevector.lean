/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualSharpLower
import TNLean.PEPS.AreaLaw.Scan.ActualSharpLowerRemainder
import TNLean.PEPS.AreaLaw.Scan.AugmentedReplicaPrevectorProperties
import TNLean.PEPS.AreaLaw.Scan.StatusMarginalMoments
import TNLean.PEPS.AreaLaw.TwoFamilies

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
-/

noncomputable section

open Matrix TensorPower TensorPower.ReplicaTransport PermutationRepresentation Filter
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder Topology

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
    (Ωt : StateSpace Λ q) (U : Finset (Site Λ)) (Kmom u : ℝ)
    (h : Real.log (Entropy.surprisalMoment
      (reducedState_isHermitian Λ q Ωt U).eigenvalues u) ≤
        u * regionalEntropy Λ q Ωt U + Kmom * u ^ 2) :
    Real.log (Entropy.surprisalMoment
      (FiniteProduct.reducedPure_posSemidef
        (fun _ : Site Λ => Fin q) Ωt U).isHermitian.eigenvalues u) ≤
      u * FiniteProduct.entropy (fun _ : Site Λ => Fin q) Ωt U + Kmom * u ^ 2 := by
  classical
  let β := fun _ : Site Λ => Fin q
  have hEigen := congrArg (fun A : {A : Matrix (FiniteProduct.Configuration β U)
      (FiniteProduct.Configuration β U) ℂ // A.IsHermitian} => A.2.eigenvalues)
    (Subtype.ext
      (a1 := ⟨reducedState Λ q Ωt U, reducedState_isHermitian Λ q Ωt U⟩)
      (a2 := ⟨FiniteProduct.reducedPure β Ωt U,
        (FiniteProduct.reducedPure_posSemidef β Ωt U).isHermitian⟩)
      (reducedState_eq_finiteProduct Λ q Ωt U))
  change Real.log (Entropy.surprisalMoment
    (FiniteProduct.reducedPure_posSemidef β Ωt U).isHermitian.eigenvalues u) ≤
      u * FiniteProduct.entropy β Ωt U + Kmom * u ^ 2
  rw [← hEigen, ← regionalEntropy_eq_finiteProduct Λ q Ωt U]
  exact h

open Classical in
/-- Completed and pre-charge status moments supply all three original physical marginals. -/
private theorem actualTerminal_sharpLower_moments
    {Λ : Finset (ℤ × ℤ)} {q : ℕ} {I : Type} [Fintype I] [LinearOrder I]
    (S : CollarScan (Site Λ) I) (Ωt : StateSpace Λ q) (Kmom rMom : ℝ)
    (hmom : ∀ (s : ℕ) (hist : History S.K S.m S.M s) (g : Fin S.K),
      (s ≤ S.n * S.m → ∀ Q ∈ statusMarginalRegions S.depth (S.state hist g),
        ∀ u : ℝ, |u| ≤ rMom →
          Real.log (Entropy.surprisalMoment
            (reducedState_isHermitian Λ q Ωt Q).eigenvalues u) ≤
            u * regionalEntropy Λ q Ωt Q + Kmom * u ^ 2) ∧
      (s + 1 ≤ S.n * S.m →
        ∀ Q ∈ statusMarginalRegions S.depth (S.oldChargeState hist g),
          ∀ u : ℝ, |u| ≤ rMom →
            Real.log (Entropy.surprisalMoment
              (reducedState_isHermitian Λ q Ωt Q).eigenvalues u) ≤
              u * regionalEntropy Λ q Ωt Q + Kmom * u ^ 2)) :
    let β := fun _ : Site Λ => Fin q
    let σ := terminalPartition S (S.n * S.m)
    let Q := fun j g => receiving (σ j g) false
    let Y := fun j g => middle (σ j g)
    ∀ j g (b : Fin 3) (u : ℝ), |u| ≤ rMom →
      let U := FiniteProduct.regionalPhysicalRegion (Q j g) (Y j g) b
      Real.log (Entropy.surprisalMoment
        (FiniteProduct.reducedPure_posSemidef β Ωt U).isHermitian.eigenvalues u) ≤
          u * FiniteProduct.entropy β Ωt U + Kmom * u ^ 2 := by
  classical
  intro β σ Q Y
  have hfar (j : terminalFamily S.K S.m S.M (S.n * S.m)) (g : Fin S.K) :
      receiving (σ j g) true = (Q j g ∪ Y j g)ᶜ := by
    ext x
    cases hx : σ j g x with
    | none => simp [Q, Y, receiving, middle, hx]
    | some side => cases side <;> simp [Q, Y, receiving, middle, hx]
  have hmomStatus : ∀ j g (U : Finset (Site Λ)),
      U ∈ statusMarginalRegions S.depth (σ j g) →
      ∀ u : ℝ, |u| ≤ rMom →
        Real.log (Entropy.surprisalMoment
          (reducedState_isHermitian Λ q Ωt U).eigenvalues u) ≤
          u * regionalEntropy Λ q Ωt U + Kmom * u ^ 2 := fun
    | Sum.inl ⟨s, hist⟩, g, U, hU, u, hu =>
      (hmom s.val hist g).1 (Nat.le_of_lt_succ s.isLt) U hU u hu
    | Sum.inr ⟨s, hist⟩, g, U, hU, u, hu =>
      (hmom s.val hist g).2 (Nat.succ_le_of_lt s.isLt) U hU u hu
  intro j g b u hu U
  have hmem : U ∈ statusMarginalRegions S.depth (σ j g) := by
    fin_cases b
    · simp [U, FiniteProduct.regionalPhysicalRegion, statusMarginalRegions, Q]
    · simp [U, FiniteProduct.regionalPhysicalRegion, statusMarginalRegions, Y]
    · change (Q j g ∪ Y j g)ᶜ ∈ statusMarginalRegions S.depth (σ j g)
      rw [← hfar]
      simp [statusMarginalRegions]
  exact sharpLower_marginalMoment_finiteProduct Ωt U Kmom u
    (hmomStatus j g U hmem u hu)

open Classical in
/-- The fixed supplied prevector keeps its norm, symmetry and both auxiliary labels. -/
private theorem sharpLower_suppliedPrevector_properties
    {Λ : Finset (ℤ × ℤ)} (q d k : ℕ) (Ωt : StateSpace Λ q)
    (ell : IrrepLabel (Equiv.Perm (Fin k)))
    (hpre :
      let β := fun _ : Site Λ => Fin q
      let ξ := WithLp.toLp 2 (replicaPrevector Ωt d k ell ∘
        globalReplicaCopiesEquiv β (Fin d) (Fin d) k)
      ξ ≠ 0 ∧ ‖ξ‖ ≤ 1) :
    let β := fun _ : Site Λ => Fin q
    let n := augmentedDimensions (V := Site Λ) q (fun _ => d)
    let pre : Config k (fun v => Fin (n v)) → ℂ :=
      replicaPrevector Ωt d k ell ∘ augmentedSumReplicaCopiesEquiv q d k
    let e := augmentedReplicaConfigurationEquiv (V := Site Λ) q d k
    let ι₀ := addedSiteSpace (addedSiteSpace β (Fin d)) (Fin d)
    pre ≠ 0 ∧ ‖WithLp.toLp 2 pre‖ ≤ 1 ∧
      symProj (copyPerm ((v : Site Λ ⊕ Bool) → Fin (n v)) k) *ᵥ pre = pre ∧
      labelProj (subsystemPerm k ι₀ {some none}) ell *ᵥ (pre ∘ e) = pre ∘ e ∧
      labelProj (subsystemPerm k ι₀ {none}) ell *ᵥ (pre ∘ e) = pre ∘ e := by
  classical
  intro β n pre e ι₀
  have hpreEq : pre ∘ e = replicaPrevector Ωt d k ell ∘
      globalReplicaCopiesEquiv β (Fin d) (Fin d) k := by
    simp only [pre, augmentedSumReplicaCopiesEquiv, Equiv.coe_trans,
      Function.comp_assoc, e, Equiv.symm_comp_self, Function.comp_id, β]
  have hprenonzero : pre ≠ 0 := by
    intro hz
    apply hpre.1
    change WithLp.toLp 2 (replicaPrevector Ωt d k ell ∘
      globalReplicaCopiesEquiv β (Fin d) (Fin d) k) = 0
    rw [← hpreEq, hz]
    rfl
  have hprenorm : ‖WithLp.toLp 2 pre‖ ≤ 1 := by
    have hn := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e.symm).norm_map
      (WithLp.toLp 2 pre)
    have hno : ‖WithLp.toLp 2 (pre ∘ e)‖ ≤ 1 := by
      rw [hpreEq]
      exact hpre.2
    exact hn.symm.trans_le hno
  have hsym : symProj (copyPerm ((v : Site Λ ⊕ Bool) → Fin (n v)) k) *ᵥ pre = pre :=
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

**Scope restriction (supplied-sequence lower rate):** The gap and original-state
status moments are hypotheses, together with the supplied sequence's nonzero/norm
and label-dimension conclusions. Its actual energy defect is retained; common-point
comparison and final source-scale absorption are not established here. See
`docs/paper-gaps/arealaw2d_actual_sharp_lower_scope.tex`.
Source: `07-comparators.tex`, lines 130--153, 255--281 and 550--651;
`08-scanner.tex`, lines 400--474, adc7f124. -/
theorem exists_actualScan_suppliedPrevector_sharp_lower
    {Λ : Finset (ℤ × ℤ)} {q d R : ℕ} {J : ℝ} [NeZero q] [NeZero d]
    [LinearOrder (AdmissibleSupport Λ R)]
    (S : CollarScan (Site Λ) (AdmissibleSupport Λ R))
    (hm : 0 < S.m) (hM : 0 < S.M)
    (h : LocalHamiltonian Λ q R J) (Ω : StateSpace Λ q) (Δ : ℝ) (L : ℕ)
    (Ωt : StateSpace Λ q) (e₀ gap : ℝ) (hΩt : ‖Ωt‖ = 1)
    (hgap : ((∑ i, S.truncatedEnergyTerm h Ω Δ L i) - (e₀ : ℂ) • 1 -
      (gap : ℂ) • (1 - vecMulVec Ωt.ofLp (star Ωt.ofLp))).PosSemidef)
    (hgap_pos : 0 < gap)
    (a Kmom rMom : ℝ) (ha : 0 < a) (har : 10 * a ≤ rMom)
    (haone : 10 * a ≤ 1) (hK : 0 ≤ Kmom)
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))) (Sent : ℝ)
    (hpre : ∀ k : ℕ, 0 < k →
      let β := fun _ : Site Λ => Fin q
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
            (reducedState_isHermitian Λ q Ωt Q).eigenvalues u) ≤
            u * regionalEntropy Λ q Ωt Q + Kmom * u ^ 2) ∧
      (s + 1 ≤ S.n * S.m →
        ∀ Q ∈ statusMarginalRegions S.depth (S.oldChargeState hist g),
          ∀ u : ℝ, |u| ≤ rMom →
            Real.log (Entropy.surprisalMoment
              (reducedState_isHermitian Λ q Ωt Q).eigenvalues u) ≤
              u * regionalEntropy Λ q Ωt Q + Kmom * u ^ 2)) :
    let β := fun _ : Site Λ => Fin q
    let n := augmentedDimensions (V := Site Λ) q (fun _ => d)
    let pre : (k : ℕ) → Config k (fun v => Fin (n v)) → ℂ := fun k =>
      replicaPrevector Ωt d k (ell k) ∘ augmentedSumReplicaCopiesEquiv q d k
    let σ := terminalPartition S (S.n * S.m)
    let Q := fun j g => receiving (σ j g) false
    let Y := fun j g => middle (σ j g)
    let entropyGap := fun j g =>
      FiniteProduct.entropy β Ωt (Q j g) +
        FiniteProduct.entropy β Ωt (Q j g ∪ Y j g)ᶜ -
        FiniteProduct.entropy β Ωt (Y j g)
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
              (S.actualEnergyTerms h Ω Δ L (fun _ => d)) a pre).meanEnergy k p) Tfill) ∧
        (‖WithLp.toLp 2
            (Transport.filteredVector (Dcharge.rootPath n (a / 2) k p) (pre k))‖ = 1 ∧
          lower (Transport.filteredNormSq (Dcharge.rootPath n (a / 2) k p) (pre k))
            ((S.actualChargeScanRound hm hM s.val n
              (S.actualEnergyTerms h Ω Δ L (fun _ => d)) a pre).meanEnergy k p) Tcharge) := by
  classical
  intro β n pre σ Q Y entropyGap gaps gmax
  obtain ⟨c, Cf, hc, hCf, hlower⟩ :=
    exists_actualScan_sharp_lower_norm (Λ := Λ) (q := q) (d := d) (R := R) (J := J) a ha
  refine ⟨c, Cf, hc, hCf,
    tendsto_sharpLowerRemainder_of_label_dimension ell Sent hdim a c Cf, ?_⟩
  have hmomQ := actualTerminal_sharpLower_moments S Ωt Kmom rMom hmom
  intro k hk s p lower Dfill Dcharge Tfill Tcharge
  obtain ⟨hprenonzero, hprenorm, hsym, hC, hR⟩ :=
    sharpLower_suppliedPrevector_properties q d k Ωt (ell k) (hpre k hk)
  obtain ⟨⟨hfnorm, hfpos, hfδ, hf⟩, ⟨hcnorm, hcpos, hcδ, hcharge⟩⟩ :=
    hlower S hm hM (S.n * S.m) h Ω Δ L Ωt e₀ gap hΩt hgap hgap_pos
      Kmom rMom hmomQ har haone hK pre k hk hprenonzero hprenorm hsym
      (ell k) (ell k) Sent (sharpLowerLabelDefect ell Sent k) hC hR
      (sharpLowerLabelDefect_label_bound ell Sent k).2 s p
  refine ⟨⟨hfnorm, hfpos, hfδ, ?_⟩, ⟨hcnorm, hcpos, hcδ, ?_⟩⟩
  · intro τ hτ hτhalf
    simpa only [sharpLowerRemainder] using
      sharp_lower_rate_of_finite_copy ha hk _ (hf τ hτ hτhalf)
  · intro τ hτ hτhalf
    simpa only [sharpLowerRemainder] using
      sharp_lower_rate_of_finite_copy ha hk _ (hcharge τ hτ hτhalf)

end TNLean.PEPS.AreaLaw.Scan.CollarScan
