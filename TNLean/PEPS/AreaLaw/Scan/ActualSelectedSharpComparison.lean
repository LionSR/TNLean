/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualSharpComparison
import TNLean.PEPS.AreaLaw.Scan.ActualSelectedChargeDensityEnergy

/-!
# Sharp subtraction at the same selected actual charge point

The selector's charge stage and parameter are retained. The actual energy
coefficient cap is evaluated there, and its normalized defect bound replaces
the actual defect in the uniform sharp comparison. Neither the label sequence
nor any terminal probability is changed. All remaining physical entropy,
scale and replica errors are displayed.

The inputs are the exact conclusions of the preceding actual selector,
accepted density-energy coefficient theorem, and actual sharp comparison.
This is their composition, without a final density-power estimate or a
new construction of the common physical state.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 480--533 and 881--911, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open Matrix TensorPower TensorPower.ReplicaTransport PermutationRepresentation Filter
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator Topology

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open SpectralFilter ActualTerminals

open Classical in
/-- Evaluate the uniform actual sharp comparison at the selector's literal
point and substitute its density-form energy cap. The three premises are
respectively the existing selector/transport output, the accepted coefficient
cap, and the preceding same-prevector sharp comparison. This theorem is a
conditional composition: all three supplied conclusions must be instantiated
with the same physical data. The remaining scale and entropy bounds are explicit.
Source: `08-scanner.tex`, lines 480--533 and 881--911. -/
theorem eventually_exists_selected_actualCharge_sharp_comparison
    {Λ : Finset (ℤ × ℤ)} {q d R : ℕ} {J Δ : ℝ} [NeZero q] [NeZero d]
    [LinearOrder (AdmissibleSupport Λ R)]
    (S : CollarScan (Site Λ) (AdmissibleSupport Λ R))
    (hm : 0 < S.m) (hM : 0 < S.M) (hKpos : 0 < S.K)
    (h : LocalHamiltonian Λ q R J) (Ω Ωt : StateSpace Λ q) (L : ℕ)
    (hΔ : 0 < Δ) (a : ℝ) (ha : 0 < a)
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k)))
    (Sent e₀ Kmom z Cen een C Cl P cU cL Cf p₀ p₁ : ℝ)
    (rem selectionBound : ℕ → ℝ) :
    let β := fun _ : Site Λ ↦ Fin q
    let dims := augmentedDimensions (V := Site Λ) q (fun _ ↦ d)
    let pre : (k : ℕ) → Config k (fun v ↦ Fin (dims v)) → ℂ := fun k ↦
      replicaPrevector Ωt d k (ell k) ∘ augmentedSumReplicaCopiesEquiv q d k
    let E := S.actualEnergyTerms h Ω Δ L (fun _ ↦ d)
    let ℓ := transportLogDimBound q S.r₀
    let g := Δ / positiveNormalization 1 (Δ / 2) J
    let W := a * (S.K : ℝ)
    let σ := terminalPartition S (S.n * S.m)
    let near := fun j band ↦ receiving (σ j band) false
    let middleRegion := fun j band ↦ middle (σ j band)
    let gpre := fun j band ↦
      FiniteProduct.entropy β Ωt (near j band) +
        FiniteProduct.entropy β Ωt (near j band ∪ middleRegion j band)ᶜ -
        FiniteProduct.entropy β Ωt (middleRegion j band)
    let gpost := fun j band ↦
      regionalEntropy Λ q Ωt (positiveNear S.depth (σ j band)) +
        regionalEntropy Λ q Ωt (positiveNearMiddle S.depth (σ j band)) -
        regionalEntropy Λ q Ωt (middle (σ j band))
    let gaps := (Finset.univ :
      Finset (terminalFamily S.K S.m S.M (S.n * S.m) × Fin S.K)).image
        (fun j ↦ gpre j.1 j.2)
    let gmax := (insert (0 : ℝ) gaps).max' (Finset.insert_nonempty _ _)
    let tree := fun (s : Fin (S.n * S.m)) (p : ℝ) ↦
      ((S.actualChargeData hm hM s.val).tree (Set.projIcc (0 : ℝ) 1 zero_le_one p)).map
        (chargeTerminalIndex S.K S.m S.M (S.n * S.m) s)
    let Gpre := fun s p ↦ (∑ band, ∑ j, (tree s p).weight j * gpre j band) / (S.K : ℝ)
    let Gpost := fun s p ↦ (∑ band, ∑ j, (tree s p).weight j * gpost j band) / (S.K : ℝ)
    let Q := fun k (s : Fin (S.n * S.m)) p ↦
      S.actualChargeEntropyDefect hm hM s.val dims E (a / 2) k (pre k) p
    let δ := fun k (s : Fin (S.n * S.m)) p ↦
      ((S.actualChargeScanRound hm hM s.val dims E a pre).meanEnergy k p - e₀) / (g / 2)
    let error := fun k (s : Fin (S.n * S.m)) p ↦
      (S.actualChargeData hm hM s.val).energyError E (a / 2) k (pre k) p
    let cap := fun k (s : Fin (S.n * S.m)) p ↦
      C * W ^ 2 * (S.n : ℝ) ^ (Exponents.scannerEll : ℝ) *
        (S.D : ℝ) ^ 2 * (Real.log S.n) ^ Cl *
          ((1 - p) * (Q k s p / (S.K * S.n * S.D : ℝ)) ^ (1 / 8 : ℝ) +
            (1 - p) * (S.n : ℝ) ^ (-P) + p)
    (∀ k : ℕ, 0 < k → ∃ s : Fin (S.n * S.m), ∃ p ∈ Set.Icc p₀ p₁,
      Q k s p ≤ selectionBound k ∧
        δ k s p ≤ (e₀ + Cen * a ^ 2 * ℓ ^ een * error k s p + rem k) / (g / 2)) →
    (∀ (k : ℕ), 0 < k → ∀ (s : Fin (S.n * S.m)) (p : ℝ), p ∈ Set.Icc p₀ p₁ →
      |Cen| * a ^ 2 * ℓ ^ een * error k s p ≤ cap k s p) →
    (∀ᶠ k : ℕ in atTop, ∀ (s : Fin (S.n * S.m)) (p : ℝ),
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
        2 * Sent + Gpre s p - Gpost s p ≤
          2 * (2 * Real.log (d : ℝ) - Real.log z) / W +
            τ * Gpre s p + 2 * τ * Real.log (d : ℝ) +
            (3 + 1 / a) * Real.binEntropy τ + 37 * Kmom * a - Real.log z / a +
            δ k s p / τ * max 0 (2 * Sent + gmax) +
            2 * Real.bellOverlapRemainder d cU S.K k / W +
              sharpLowerRemainder a cL Cf ell Sent k) →
    ∀ᶠ k : ℕ in atTop, ∃ s : Fin (S.n * S.m), ∃ p ∈ Set.Icc p₀ p₁,
      Q k s p ≤ selectionBound k ∧
        δ k s p ≤ (e₀ + cap k s p + rem k) / (g / 2) ∧
        ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
          2 * Sent + Gpre s p - Gpost s p ≤
            2 * (2 * Real.log (d : ℝ) - Real.log z) / W +
              τ * Gpre s p + 2 * τ * Real.log (d : ℝ) +
              (3 + 1 / a) * Real.binEntropy τ + 37 * Kmom * a - Real.log z / a +
              ((e₀ + cap k s p + rem k) / (g / 2)) / τ * max 0 (2 * Sent + gmax) +
              2 * Real.bellOverlapRemainder d cU S.K k / W +
                sharpLowerRemainder a cL Cf ell Sent k := by
  classical
  intro β dims pre E ℓ g W σ near middleRegion gpre gpost gaps gmax tree Gpre Gpost
    Q δ error cap hselected hcoefficient hcomparison
  have hKr : (0 : ℝ) < S.K := Nat.cast_pos.mpr hKpos
  have hW : 0 < W := mul_pos ha hKr
  have hweight : W / (S.K : ℝ) = a := by
    dsimp only [W]
    field_simp [hKr.ne']
  filter_upwards [hcomparison, eventually_gt_atTop 0] with k hcomparisonK hk
  obtain ⟨s, p, hp, hQ, henergy⟩ := hselected k hk
  have hcap : δ k s p ≤ (e₀ + cap k s p + rem k) / (g / 2) := by
    have hbound := S.actualCharge_defect_le_of_density_energy_bound hm hM s.val h Ω L
      hΔ W Cen een C Cl P (rem k) e₀ hW.le pre k p
    simp only [hweight] at hbound
    exact hbound henergy (hcoefficient k hk s p hp)
  refine ⟨s, p, hp, hQ, hcap, ?_⟩
  intro τ hτ hτhalf
  have hmassLoss := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hcap hτ.le) (le_max_left (0 : ℝ) (2 * Sent + gmax))
  have hsharp := hcomparisonK s p τ hτ hτhalf
  linarith only [hsharp, hmassLoss]

end TNLean.PEPS.AreaLaw.Scan.CollarScan
