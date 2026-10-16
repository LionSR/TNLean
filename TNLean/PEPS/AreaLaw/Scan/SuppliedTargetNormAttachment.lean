/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SuppliedTargetStatusMoments
import TNLean.PEPS.AreaLaw.Scan.SharpSmallness
import TNLean.PEPS.AreaLaw.Scan.ActualSharpUpper
import TNLean.PEPS.AreaLaw.Scan.ActualSharpLowerPrevector
import TNLean.PEPS.AreaLaw.Scan.ActualRoughLowerPrevector

/-!
# Norm estimates for the supplied physical charge state

The truncated ground vector, typical set and label sequence are supplied by
physical charge selection. Three norm estimates are uniform over all charge
rounds and interpolation parameters. Together with the rough upper estimate
retained by that selection, they give all four comparisons at the same point.
The sharp estimates retain their stated marginal smallness condition.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
Proposition 9.2, `08-scanner.tex`, lines 349–397, and Proposition 8.1,
`07-comparators.tex`, lines 97–169, 383–418 and 550–651, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open Matrix TensorPower TensorPower.ReplicaTransport PermutationRepresentation Filter
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator Topology

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open ActualTerminals SpectralFilter

open Classical in
/-- Three uniform norm estimates attach to the same supplied physical data.
The source radius smallness gives the rough estimate; the two sharp estimates
add precisely the source marginal smallness condition. The selected rough upper
estimate is retained separately when this theorem is applied at the selected point.
Source: Proposition 9.2, `08-scanner.tex`, lines 349–397. -/
theorem exists_suppliedTarget_actualCharge_norm_bounds
    {q : ℕ} [NeZero q] (hq : 1 ≤ q) (R : ℕ) {Cr : ℝ} (hCr : 0 < Cr) :
    ∃ CB : ℝ, 0 < CB ∧
      ∀ (Λ T : Finset (ℤ × ℤ)) [LinearOrder (AdmissibleSupport Λ R)]
        (hT : T.Nonempty) (S : CollarScan (Site Λ) (AdmissibleSupport Λ R)),
        S.graph = domainGraph Λ →
        S.depth = (fun x ↦ ambientDepth T hT x.val) →
        (∀ i, S.anchor i ∈ i.val) →
        ∀ (hm : 0 < S.m) (hM : 0 < S.M), 0 < S.K →
        ∀ L : ℕ, 2 ≤ S.n →
        S.r₀ = ⌈Cr * Real.log (S.n : ℝ) ^ 2⌉₊ →
        S.r₀ ≤ S.D → 1 ≤ S.D → 4 * S.D ≤ S.m → 8 * S.K * S.m ≤ L →
        (∀ j : ℕ, 1 ≤ j → j ≤ L →
          (ambientDilation T j \ ambientDilation T (j - 1)).card ≤ S.n) →
        (∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
          ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) →
        let B := CB * ((S.n : ℝ) * S.D * Real.log (S.n : ℝ) ^ 12)
        1 ≤ B ∧
          ∀ {J Δ : ℝ} (h : LocalHamiltonian Λ q R J) (Ω : StateSpace Λ q),
            0 < Δ → ‖Ω‖ = 1 →
            let g := Δ / positiveNormalization 1 (Δ / 2) J
            let C₀ := 512 * Real.exp 1 * (2 / g)
            let c₀ := 1 / (32 * Real.sqrt (1 + 2 / g))
            ∀ (e : ℝ) (Ωt : StateSpace Λ q),
              IsGappedGroundState Λ q (∑ i, S.truncatedEnergyTerm h Ω Δ L i)
                e Ωt (g / 2) →
              let X := S.A.filter fun x ↦ x.val ∈ T
              let β := fun _ : Site Λ ↦ Fin q
              ∀ (E : Finset (FiniteProduct.Configuration β X)) (hd : 0 < E.card),
              letI : NeZero E.card := ⟨Nat.ne_of_gt hd⟩
              let d := E.card
              let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
                (FiniteProduct.splitEquiv β X) Ωt
              let z := Matrix.IsHermitian.spectralRestrictionMass
                (posSemidef_vecMulVec_self_star ΩX).partialTraceRight.isHermitian E
              0 < z →
              let ψ : FiniteProduct.Configuration β Xᶜ × Fin d → ℂ := fun x ↦
                compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.2, x.1)
              let Sent := vonNeumannEntropy (Matrix.partialTraceLeft (Matrix.vecMulVec ψ
                (star ψ))) (Matrix.posSemidef_vecMulVec_self_star ψ).partialTraceLeft.isHermitian
              ∀ ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k)),
              (∀ k : ℕ, 0 < k →
                let ξ := WithLp.toLp 2 (replicaPrevector Ωt d k (ell k) ∘
                  globalReplicaCopiesEquiv β (Fin d) (Fin d) k)
                ξ ≠ 0 ∧ ‖ξ‖ ≤ 1) →
              (∀ᶠ k : ℕ in atTop,
                (2 * (((k + 1) ^ (d ^ 2) : ℕ) : ℝ))⁻¹ ≤
                  ‖WithLp.toLp 2
                    (((1 : Matrix (Fin k → FiniteProduct.Configuration β Xᶜ)
                      (Fin k → FiniteProduct.Configuration β Xᶜ) ℂ) ⊗ₖ
                      labelProj (copyPerm (Fin d) k) (ell k)) *ᵥ
                      (fun x : (Fin k → FiniteProduct.Configuration β Xᶜ) ×
                        (Fin k → Fin d) ↦ ∏ i, ψ (x.1 i, x.2 i)))‖ ^ 2) →
              Asymptotics.IsLittleO atTop
                (fun k : ℕ ↦ Real.log (ell k).dim - (k : ℝ) * Sent)
                (fun k : ℕ ↦ (k : ℝ)) →
              let dims := augmentedDimensions (V := Site Λ) q (fun _ ↦ d)
              let energy := S.actualEnergyTerms h Ω Δ L (fun _ ↦ d)
              let pre : (k : ℕ) → Config k (fun v ↦ Fin (dims v)) → ℂ := fun k ↦
                replicaPrevector Ωt d k (ell k) ∘ augmentedSumReplicaCopiesEquiv q d k
              let σ := terminalPartition S (S.n * S.m)
              let Q := fun j band ↦ receiving (σ j band) false
              let Y := fun j band ↦ middle (σ j band)
              let gpre := fun j band ↦ FiniteProduct.entropy β Ωt (Q j band) +
                FiniteProduct.entropy β Ωt (Q j band ∪ Y j band)ᶜ -
                  FiniteProduct.entropy β Ωt (Y j band)
              let gpost := fun j band ↦
                regionalEntropy Λ q Ωt (positiveNear S.depth (σ j band)) +
                  regionalEntropy Λ q Ωt (positiveNearMiddle S.depth (σ j band)) -
                    regionalEntropy Λ q Ωt (middle (σ j band))
              let gaps := (Finset.univ :
                Finset (terminalFamily S.K S.m S.M (S.n * S.m) × Fin S.K)).image
                  (fun j ↦ gpre j.1 j.2)
              let gmax := (insert (0 : ℝ) gaps).max' (Finset.insert_nonempty _ _)
              ∀ W : ℝ, 1 ≤ W →
              let a := W / (S.K : ℝ)
              a * (S.r₀ : ℝ) ^ 2 ≤ 1 / 2 →
              (∃ cR CfR : ℝ, 0 ≤ cR ∧ 0 ≤ CfR ∧
                Tendsto (roughLowerRemainderAtWeight S.K a cR CfR ell Sent)
                  atTop (𝓝 0) ∧
                ∀ k : ℕ, 0 < k → ∀ (s : Fin (S.n * S.m)) (p : ℝ),
                  let D := S.actualChargeData hm hM s.val
                  let Nsq := Transport.filteredNormSq (D.rootPath dims (a / 2) k p) (pre k)
                  let μ := (S.actualChargeScanRound hm hM s.val dims energy a pre).meanEnergy k p
                  let defect := (μ - e) / (g / 2)
                  ‖WithLp.toLp 2
                    (Transport.filteredVector (D.rootPath dims (a / 2) k p) (pre k))‖ = 1 ∧
                  0 < Nsq ∧ 0 ≤ defect ∧
                  ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
                    (W / 4) *
                        (4 * Sent - 6 * (τ * Real.log (d : ℝ) + Real.binEntropy τ / a) -
                          3 * (defect / τ) * max 0 (2 * Sent)) -
                        roughLowerRemainderAtWeight S.K a cR CfR ell Sent k ≤
                          -Real.log Nsq / (k : ℝ)) ∧
              (a * Real.sqrt B ≤ min c₀ 1 / 10 →
                ∃ cU cL CfL : ℝ, 0 ≤ cU ∧ 0 ≤ cL ∧ 0 ≤ CfL ∧
                  Tendsto (Real.bellOverlapRemainder d cU S.K) atTop (𝓝 0) ∧
                  Tendsto (sharpLowerRemainder a cL CfL ell Sent) atTop (𝓝 0) ∧
                  ∀ᶠ k : ℕ in atTop, ∀ (s : Fin (S.n * S.m)) (p : ℝ),
                    let D := S.actualChargeData hm hM s.val
                    let tree := (D.tree (Set.projIcc (0 : ℝ) 1 zero_le_one p)).map
                      (chargeTerminalIndex S.K S.m S.M (S.n * S.m) s)
                    let Nsq := Transport.filteredNormSq (D.rootPath dims (a / 2) k p) (pre k)
                    let μ :=
                      (S.actualChargeScanRound hm hM s.val dims energy a pre).meanEnergy k p
                    let defect := (μ - e) / (g / 2)
                    0 < Nsq ∧
                    -Real.log Nsq / (k : ℝ) ≤
                      2 * Real.log (d : ℝ) - Real.log z +
                        (a / 2) * (∑ band, ∑ j, tree.weight j * gpost j band) +
                          6 * (S.K : ℝ) * (C₀ * B) * a ^ 2 -
                            (S.K : ℝ) / 2 * Real.log z +
                              Real.bellOverlapRemainder d cU S.K k ∧
                    ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
                      let rate := fun band ↦ 2 * Sent +
                        (1 - τ) * (∑ j, tree.weight j * gpre j band) -
                          τ * (2 * Real.log (d : ℝ)) -
                          (3 + 1 / a) * Real.binEntropy τ - 25 * (C₀ * B) * a
                      (a / 2) * (∑ band,
                        (rate band - defect / τ * max 0 (2 * Sent + gmax) -
                          sharpLowerRemainder a cL CfL ell Sent k)) ≤
                            -Real.log Nsq / (k : ℝ)) := by
  obtain ⟨CB, hCB, hmoments⟩ := exists_suppliedTarget_statusMarginal_moment_bounds hq R hCr.le
  refine ⟨CB, hCB, ?_⟩
  intro Λ T _ hT S hgraph hdepth hanchor hm hM hK L hn hradius hr hDpos hD hL hrows hclear B
  obtain ⟨hB, hmom⟩ := hmoments Λ T hT S hgraph hdepth hanchor L hn hradius
    hr hDpos hD hL hrows hclear
  refine ⟨hB, ?_⟩
  intro J Δ h Ω hΔ hΩ g C₀ c₀ e Ωt hgs X β E hd d ΩX z hz ψ Sent ell
    hpre hmass hdim dims energy pre σ Q Y gpre gpost gaps gmax W hW a haradius
  obtain ⟨hC₀, hc₀, hmomBound⟩ := hmom h Ω hΔ hΩ e Ωt hgs
  have htr := Matrix.isGappedGroundState_iff.mp hgs
  have hgap : 0 < g / 2 := half_pos (div_pos hΔ (positiveNormalization_pos 1 (Δ / 2) J))
  have ha : 0 < a := div_pos (lt_of_lt_of_le zero_lt_one hW) (Nat.cast_pos.mpr hK)
  have hr₀ : 1 ≤ S.r₀ := hradius.symm ▸ Nat.one_le_ceil_iff.mpr
    (mul_pos hCr (sq_pos_of_pos (Real.log_pos (by exact_mod_cast (show 1 < S.n from hn)))))
  have haHalf : a ≤ 1 / 2 :=
    (le_mul_of_one_le_right ha.le (one_le_pow₀ (by exact_mod_cast hr₀))).trans haradius
  let : NeZero d := NeZero.of_pos hd
  obtain ⟨cR, CfR, hcR, hCfR, hrough⟩ :=
    exists_actualScan_suppliedPrevector_rough_lower_of_weight
      (Λ := Λ) (q := q) (d := d) (R := R) (J := J) S.K a ha haHalf
  obtain ⟨hlimR, hlowerR⟩ := hrough S rfl hm hM h Ω Δ L Ωt e (g / 2)
    htr.1 htr.2.2 hgap ell Sent hpre hdim
  refine ⟨⟨cR, CfR, hcR, hCfR, hlimR, fun k hk s p ↦ ?_⟩, ?_⟩
  · simpa only [show a * (S.K : ℝ) = W from
      div_mul_cancel₀ W (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hK))] using (hlowerR k hk s p).2
  · intro hsharp
    obtain ⟨har10, haone10⟩ := sharpSmallness_le_moment_radius hB hsharp
    obtain ⟨cU, hcU, hlimU, hupper⟩ :=
      eventually_actualScan_suppliedPrevector_sharp_upper hT S hdepth hm hM
        a (C₀ * B) (c₀ / Real.sqrt B) ha
        (by linarith only [har10, ha]) (by linarith only [haone10, ha])
        L hL Ωt htr.1 E ell hmomBound hz hmass
    obtain ⟨cL, CfL, hcL, hCfL, hlimL, hlowerL⟩ :=
      exists_actualScan_suppliedPrevector_sharp_lower S hm hM h Ω Δ L Ωt e (g / 2)
        htr.1 htr.2.2 hgap a (C₀ * B) (c₀ / Real.sqrt B) ha har10 haone10
        (mul_nonneg hC₀.le (zero_le_one.trans hB)) ell Sent hpre hdim hmomBound
    refine ⟨cU, cL, CfL, hcU, hcL, hCfL, hlimU, hlimL, ?_⟩
    filter_upwards [hupper, eventually_gt_atTop (0 : ℕ)] with k hu hk
    intro s p
    exact ⟨(hu s.val (Nat.succ_le_of_lt s.isLt) p).2.1,
      (hu s.val (Nat.succ_le_of_lt s.isLt) p).2.2, (hlowerL k hk s p).2.2.2.2⟩

end TNLean.PEPS.AreaLaw.Scan.CollarScan
