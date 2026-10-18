/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualSelectedChargeEnergy
import TNLean.PEPS.AreaLaw.Scan.ActualChargeEnergyCoefficients
import QICLean.Representation.ReplicaTransport.Energy

/-!
# The actual selected defect in density coordinates

The actual energy error is nonnegative, so the signed transport coefficient
can be replaced by its absolute value. The concrete coefficient bound from
`exists_actualCharge_energy_coefficients` then gives the explicit density
and bad-history costs at the same charge point. No new point is selected.

This consumer retains that accepted coefficient inequality as an explicit
premise. Its outer constant/threshold construction and rounded-scale premises
are exactly those of the accepted theorem. No final density-power bound or
ground-energy decay is assumed here.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 492--533 and 839--865, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open Matrix Set TensorPower TensorPower.ReplicaTransport
open scoped BigOperators Matrix ComplexOrder MatrixOrder
open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open SpectralFilter

private theorem actualCharge_energyError_nonneg
    {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
    (S : CollarScan V I) (hm : 0 < S.m) (hM : 0 < S.M) (s : ℕ)
    (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)] (E : EnergyTerms (V ⊕ Bool) n I)
    {a : ℝ} (ha : 0 ≤ a) (k : ℕ)
    (pre : Config k (fun v ↦ Fin (n v)) → ℂ) (p : ℝ) :
    0 ≤ (S.actualChargeData hm hM s).energyError E (a / 2) k pre p := by
  classical
  let D := S.actualChargeData hm hM s
  let T := D.tree (Set.projIcc (0 : ℝ) 1 zero_le_one p)
  have hadm : D.IsAdmissible := S.actualChargeData_isAdmissible hm hM s
  have ha2 : 0 ≤ a / 2 := div_nonneg ha (by norm_num)
  have hcomm : D.CrossBandCommute n (a / 2) k :=
    S.chargeTransportData_crossBandCommute
      (historyMeanTree S.K S.m S.M hm hM s)
      (fun _ ↦ chargeChoiceTree S.K S.M hM) n ha2 k
  change 0 ≤ D.energyError E (a / 2) k pre p
  unfold TransportData.energyError
  refine Finset.sum_nonneg fun i _ ↦ mul_nonneg ?_ ?_
  · exact Finset.sum_nonneg fun j _ ↦ T.weight_nonneg j
  · refine Finset.sum_nonneg fun j _ ↦ mul_nonneg (T.weight_nonneg j) ?_
    refine MeasureTheory.integral_nonneg fun u ↦ mul_nonneg
      (Real.sinhRatioDensity_pos ⟨by norm_num, by norm_num⟩ u).le ?_
    exact realCoherentIntegral_nonneg _
      (D.posSemidef_state hadm ha2 hcomm pre p j u)
      (fun _ ↦ rpow_one_div_eight_nonneg _)

open Classical in
/-- Combine the selected actual excess-energy estimate with the literal
density-form coefficient cap. `htransport` is the energy conclusion at the
point selected by `actualCharges_selection_energy_domainGraph`.
`hcoefficient` is the exact conclusion of
`exists_actualCharge_energy_coefficients` at that same point.
The state, charge stage, parameter and prevector are not changed.
Source: `08-scanner.tex`, lines 492--533 and 839--865. -/
theorem actualCharge_defect_le_of_density_energy_bound
    {Λ : Finset (ℤ × ℤ)} {q d R : ℕ} {J Δ : ℝ} [NeZero q] [NeZero d]
    [LinearOrder (AdmissibleSupport Λ R)]
    (S : CollarScan (Site Λ) (AdmissibleSupport Λ R))
    (hm : 0 < S.m) (hM : 0 < S.M) (s : ℕ)
    (h : LocalHamiltonian Λ q R J) (Ω : StateSpace Λ q) (L : ℕ)
    (hΔ : 0 < Δ) (W Cen een C Cl P rem e₀ : ℝ) (hW : 0 ≤ W)
    (pre : (k : ℕ) → Config k
      (fun v ↦ Fin (augmentedDimensions (V := Site Λ) q (fun _ ↦ d) v)) → ℂ)
    (k : ℕ) (p : ℝ) :
    let a := W / (S.K : ℝ)
    let dims := augmentedDimensions (V := Site Λ) q (fun _ ↦ d)
    let E := S.actualEnergyTerms h Ω Δ L (fun _ ↦ d)
    let ℓ := transportLogDimBound q S.r₀
    let g := Δ / positiveNormalization 1 (Δ / 2) J
    let μ := (S.actualChargeScanRound hm hM s dims E a pre).meanEnergy k p
    let err := (S.actualChargeData hm hM s).energyError E (a / 2) k (pre k) p
    let Q := S.actualChargeEntropyDefect hm hM s dims E (a / 2) k (pre k) p
    let cap := C * W ^ 2 * (S.n : ℝ) ^ (Exponents.scannerEll : ℝ) *
      (S.D : ℝ) ^ 2 * (Real.log S.n) ^ Cl *
        ((1 - p) * (Q / (S.K * S.n * S.D : ℝ)) ^ (1 / 8 : ℝ) +
          (1 - p) * (S.n : ℝ) ^ (-P) + p)
    (μ - e₀) / (g / 2) ≤
      (e₀ + Cen * a ^ 2 * ℓ ^ een * err + rem) / (g / 2) →
    |Cen| * a ^ 2 * ℓ ^ een * err ≤ cap →
    (μ - e₀) / (g / 2) ≤ (e₀ + cap + rem) / (g / 2) := by
  classical
  intro a dims E ℓ g μ err Q cap htransport hcoefficient
  have ha : 0 ≤ a := div_nonneg hW (Nat.cast_nonneg S.K)
  have herr : 0 ≤ err := S.actualCharge_energyError_nonneg hm hM s dims E ha k (pre k) p
  have hℓ : 0 ≤ ℓ := zero_le_one.trans (one_le_transportLogDimBound (NeZero.pos q) S.r₀)
  have hcoef : Cen * a ^ 2 * ℓ ^ een * err ≤ |Cen| * a ^ 2 * ℓ ^ een * err := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_abs_self Cen) (sq_nonneg a))
        (Real.rpow_nonneg hℓ een)) herr
  have hg : 0 < g := div_pos hΔ (positiveNormalization_pos 1 (Δ / 2) J)
  exact htransport.trans (div_le_div_of_nonneg_right
    (_root_.add_le_add (_root_.add_le_add le_rfl (hcoef.trans hcoefficient)) le_rfl)
    (half_pos hg).le)

end TNLean.PEPS.AreaLaw.Scan.CollarScan
