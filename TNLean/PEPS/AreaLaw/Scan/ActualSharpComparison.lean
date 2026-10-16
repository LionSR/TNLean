/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualSharpUpper
import TNLean.PEPS.AreaLaw.Scan.ActualSharpLowerPrevector
import TNLean.PEPS.AreaLaw.Scan.SharpComparisonSubtraction

/-!
# The sharp comparison at every actual charge point

The actual sharp upper and lower rates use the same physical state, spectral
set, supplied label sequence, augmented prevector and charge root. Their
terminal trees and weights are identical. Subtraction preserves the selected
entropy, actual energy defect and every finite-replica error explicitly.

The common replica threshold precedes the charge stage and parameter. The
result therefore applies to stages and parameters selected separately at
each replica count without taking a limit of those choices.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`07-comparators.tex`, lines 171--202; `08-scanner.tex`, lines 881--911,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open Matrix TensorPower TensorPower.ReplicaTransport PermutationRepresentation Filter
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator Topology

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open ActualTerminals

open Classical in
/-- Subtract the two actual rates at the same charge point, retaining the
literal terminal-tree weights. The selected auxiliary entropy is that of the
same compressed typical state used by the mass and label-dimension premises.
Only the physical gap, moments and existing prevector conclusions are supplied;
no norm comparison or bound on the actual defect is assumed.
The auxiliary nonzero-dimension instance follows from the positive spectral
mass and is supplied explicitly to type the actual sphere-valued scan rounds.
Source: `08-scanner.tex`, lines 881--911. -/
theorem eventually_actualCharge_suppliedPrevector_sharp_comparison
    {Λ T : Finset (ℤ × ℤ)} {q R : ℕ} {J : ℝ} [NeZero q]
    [LinearOrder (AdmissibleSupport Λ R)] (hT : T.Nonempty)
    (S : CollarScan (Site Λ) (AdmissibleSupport Λ R))
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
    (hm : 0 < S.m) (hM : 0 < S.M) (hKpos : 0 < S.K)
    (h : LocalHamiltonian Λ q R J) (Ω : StateSpace Λ q) (Δ : ℝ)
    (L : ℕ) (hL : 8 * S.K * S.m ≤ L)
    (Ωt : StateSpace Λ q) (e₀ gap : ℝ) (hΩt : ‖Ωt‖ = 1)
    (hgap : ((∑ i, S.truncatedEnergyTerm h Ω Δ L i) - (e₀ : ℂ) • 1 -
      (gap : ℂ) • (1 - vecMulVec Ωt.ofLp (star Ωt.ofLp))).PosSemidef)
    (hgap_pos : 0 < gap)
    (a Kmom rMom : ℝ) (ha : 0 < a) (har : 10 * a ≤ rMom)
    (haone : 10 * a ≤ 1) (hKmom : 0 ≤ Kmom)
    (E : Finset (FiniteProduct.Configuration (fun _ : Site Λ ↦ Fin q)
      (S.A.filter fun x ↦ x.val ∈ T)))
    [NeZero E.card]
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k)))
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
    let X := S.A.filter fun x ↦ x.val ∈ T
    let β := fun _ : Site Λ ↦ Fin q
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (FiniteProduct.splitEquiv β X) Ωt
    let z := Matrix.IsHermitian.spectralRestrictionMass
      (posSemidef_vecMulVec_self_star ΩX).partialTraceRight.isHermitian E
    0 < z →
    let d := E.card
    let ψ : FiniteProduct.Configuration β Xᶜ × Fin d → ℂ := fun x ↦
      compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.2, x.1)
    let Sent := vonNeumannEntropy (Matrix.partialTraceLeft (Matrix.vecMulVec ψ (star ψ)))
      (Matrix.posSemidef_vecMulVec_self_star ψ).partialTraceLeft.isHermitian
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
    let pre : (k : ℕ) → Config k (fun v ↦ Fin (dims v)) → ℂ := fun k ↦
      replicaPrevector Ωt d k (ell k) ∘ augmentedSumReplicaCopiesEquiv q d k
    let σ := terminalPartition S (S.n * S.m)
    let Q := fun j g ↦ receiving (σ j g) false
    let Y := fun j g ↦ middle (σ j g)
    let gpre := fun j g ↦
      FiniteProduct.entropy β Ωt (Q j g) +
        FiniteProduct.entropy β Ωt (Q j g ∪ Y j g)ᶜ -
        FiniteProduct.entropy β Ωt (Y j g)
    let gpost := fun j g ↦
      regionalEntropy Λ q Ωt (positiveNear S.depth (σ j g)) +
        regionalEntropy Λ q Ωt (positiveNearMiddle S.depth (σ j g)) -
        regionalEntropy Λ q Ωt (middle (σ j g))
    let gaps := (Finset.univ :
      Finset (terminalFamily S.K S.m S.M (S.n * S.m) × Fin S.K)).image
        (fun j ↦ gpre j.1 j.2)
    let gmax := (insert (0 : ℝ) gaps).max' (Finset.insert_nonempty _ _)
    let W := a * (S.K : ℝ)
    ∃ cU cL Cf : ℝ, 0 ≤ cU ∧ 0 ≤ cL ∧ 0 ≤ Cf ∧
      Tendsto (Real.bellOverlapRemainder d cU S.K) atTop (𝓝 0) ∧
      Tendsto (sharpLowerRemainder a cL Cf ell Sent) atTop (𝓝 0) ∧
      ∀ᶠ k : ℕ in atTop, ∀ (s : Fin (S.n * S.m)) (p : ℝ),
        let D := S.actualChargeData hm hM s.val
        let tree := (D.tree (Set.projIcc (0 : ℝ) 1 zero_le_one p)).map
          (chargeTerminalIndex S.K S.m S.M (S.n * S.m) s)
        let Gpre := (∑ g, ∑ j, tree.weight j * gpre j g) / (S.K : ℝ)
        let Gpost := (∑ g, ∑ j, tree.weight j * gpost j g) / (S.K : ℝ)
        let μ := (S.actualChargeScanRound hm hM s.val dims
          (S.actualEnergyTerms h Ω Δ L (fun _ ↦ d)) a pre).meanEnergy k p
        let δ := (μ - e₀) / gap
        0 < Transport.filteredNormSq (D.rootPath dims (a / 2) k p) (pre k) ∧
          0 ≤ δ ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
            2 * Sent + Gpre - Gpost ≤
              2 * (2 * Real.log (d : ℝ) - Real.log z) / W +
                τ * Gpre + 2 * τ * Real.log (d : ℝ) +
                (3 + 1 / a) * Real.binEntropy τ + 37 * Kmom * a - Real.log z / a +
                δ / τ * max 0 (2 * Sent + gmax) +
                2 * Real.bellOverlapRemainder d cU S.K k / W +
                  sharpLowerRemainder a cL Cf ell Sent k := by
  classical
  intro X β ΩX z hz d ψ Sent hpre hmass hdim dims pre σ Q Y gpre gpost gaps gmax W
  have har6 : 6 * a ≤ rMom := (show 6 * a ≤ 10 * a by linarith).trans har
  have haone6 : 6 * a ≤ 1 := (show 6 * a ≤ 10 * a by linarith).trans haone
  obtain ⟨cU, hcU, hlimU, hupper⟩ :=
    eventually_actualScan_suppliedPrevector_sharp_upper hT S hdepth hm hM
      a Kmom rMom ha har6 haone6 L hL Ωt hΩt E ell hmom hz hmass
  obtain ⟨cL, Cf, hcL, hCf, hlimL, hlower⟩ :=
    exists_actualScan_suppliedPrevector_sharp_lower S hm hM h Ω Δ L Ωt e₀ gap
      hΩt hgap hgap_pos a Kmom rMom ha har haone hKmom ell Sent hpre hdim hmom
  have hKr : (0 : ℝ) < S.K := Nat.cast_pos.mpr hKpos
  have hW : 0 < W := mul_pos ha hKr
  refine ⟨cU, cL, Cf, hcU, hcL, hCf, hlimU, hlimL, ?_⟩
  filter_upwards [hupper, eventually_gt_atTop 0] with k hupperK hk
  intro s p D tree Gpre Gpost μ δ
  have hs : s.val + 1 ≤ S.n * S.m := Nat.succ_le_of_lt s.isLt
  obtain ⟨hN, hU⟩ := (hupperK s.val hs p).2
  obtain ⟨_, _, hδ, hLower⟩ := (hlower k hk s p).2
  refine ⟨hN, hδ, ?_⟩
  intro τ hτ hτhalf
  have hpreSum : (∑ g, ∑ j, tree.weight j * gpre j g) = (S.K : ℝ) * Gpre :=
    (mul_div_cancel₀ _ hKr.ne').symm
  have hpostSum : (∑ g, ∑ j, tree.weight j * gpost j g) = (S.K : ℝ) * Gpost :=
    (mul_div_cancel₀ _ hKr.ne').symm
  let rate := -Real.log (Transport.filteredNormSq (D.rootPath dims (a / 2) k p) (pre k)) /
    (k : ℝ)
  let rU := Real.bellOverlapRemainder d cU S.K k
  let rL := sharpLowerRemainder a cL Cf ell Sent k
  have hupperRate : rate ≤ 2 * Real.log (d : ℝ) - Real.log z + W / 2 * Gpost +
      6 * W * Kmom * a - W / (2 * a) * Real.log z + rU := by
    have hcoeff : W / (2 * a) = (S.K : ℝ) / 2 := by
      dsimp only [W]
      field_simp [ha.ne']
    change rate ≤ 2 * Real.log (d : ℝ) - Real.log z +
      (a / 2) * (∑ g, ∑ j, tree.weight j * gpost j g) +
        6 * (S.K : ℝ) * Kmom * a ^ 2 - (S.K : ℝ) / 2 * Real.log z + rU at hU
    rw [hpostSum] at hU
    rw [hcoeff]
    convert hU using 1
    dsimp only [W]
    ring
  have hlowerRate : W / 2 *
      (2 * Sent + (1 - τ) * Gpre - 2 * τ * Real.log (d : ℝ) -
        (3 + 1 / a) * Real.binEntropy τ - 25 * Kmom * a -
          δ / τ * max 0 (2 * Sent + gmax)) - W / 2 * rL ≤ rate := by
    have hLowerτ := hLower τ hτ hτhalf
    change (a / 2) * (∑ g,
      (2 * Sent + (1 - τ) * (∑ j, tree.weight j * gpre j g) -
        τ * (2 * Real.log (d : ℝ)) - (3 + 1 / a) * Real.binEntropy τ -
          25 * Kmom * a - δ / τ * max 0 (2 * Sent + gmax) - rL)) ≤ rate at hLowerτ
    convert hLowerτ using 1
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    rw [hpreSum]
    dsimp only [W]
    ring
  have hcompare := sharp_comparison_subtraction ha hW hτ Sent Gpre Gpost
    (Real.log (d : ℝ)) (Real.log z) Kmom δ (max 0 (2 * Sent + gmax))
    rate rU (W / 2 * rL) hlowerRate hupperRate
  have hremainders : 2 * (rU + W / 2 * rL) / W = 2 * rU / W + rL := by
    field_simp [hW.ne']
  simpa only [hremainders, rU, rL, add_assoc] using hcompare

end TNLean.PEPS.AreaLaw.Scan.CollarScan
