/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.Truncation.RegionalBarrierResidual
import QICLean.Spectral.Filter.SoftTruncationCommutingFamily
import QICLean.Spectral.LowEnergy.ShiftedLowEnergyCoordinates
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.SoftTruncation.FiveRegionSoftStructure
import QICLean.Spectral.Eigenvalue.GroundEnergyBounds
import QICLean.Spectral.LowEnergy.Cluster
import QICLean.Spectral.LowEnergy.Coordinates
import QICLean.Spectral.Perturbation.ClusterNormPerturbation
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.MPO.SoftTruncationMPOAccuracy
import QICLean.Spectral.Perturbation.GroundShiftSpectralComparison

/-!
# Simultaneous residuals for actual regional soft replacements

The same common interior is used after every selected replacement. The local boundary
consists of the original bonds; its actual cardinality determines the reverse threshold.
This conditional auxiliary to ALVV, arXiv:1602.08828v2, `lem:exp-approx` and
`t:aisefficient`, lines 1195–1255 and 1373–1392, is to be applied with the physically
constructed regional minima and soft ground-energy cap. It assumes no residual or gap.

## Two physical residuals for simultaneous estimated-center soft replacements

The original nearest-neighbour chain determines all five regional minima, the original
low-energy space and the actual simultaneous soft Hamiltonian. The estimated centers may
range throughout the source's ten-unit lower interval. The threshold retains the actual
number of crossing bonds and selected replacements.

These are corrected auxiliary bounds for ALVV, arXiv:1602.08828v2, `def:soft-trunc`,
`lem:exp-approx` and `t:aisefficient`, lines 1178–1255 and 1373–1392. They do not assert
the false printed uniform energy estimate, the printed cluster estimate or the complete
efficient-filter parameter theorem. See `docs/paper-gaps/alvv16_soft_regional_residuals.tex`
and `docs/paper-gaps/alvv16_cluster_approximation.tex`.

## Physical soft clusters and their actual Hermitian approximants

The regional minima, centered original Hamiltonian and simultaneous soft
replacement are constructed once from the original local interactions.
Both physical restricted residuals are retained. An original spectral gap
and explicit scalar residual budgets derive the exact soft cluster; a
separate global Hermitian approximation then has its own invariant low
cluster, of the original ground-space dimension.

This is a corrected auxiliary for ALVV, arXiv:1602.08828v2,
`lem:exp-approx` and `t:aisefficient`, lines 1195–1255 and 1373–1420.
**Scope restriction (one-sided centers and explicit precision):** Regional
estimates lie in the actual ten-unit lower interval. Physical residuals
and the two norm-perturbation window losses remain explicit numerical
conditions. No uniform choice of soft scale or order, measurable adaptive
energy estimates or running time is asserted. See
`docs/paper-gaps/alvv16_soft_regional_residuals.tex` and
`docs/paper-gaps/alvv16_cluster_approximation.tex`.

## Spectral comparisons and an MPO for the same physical soft Hamiltonian

The original interactions construct all regional ground data, the actual estimated-center
soft Hamiltonian and its low-energy residuals. Its normalized ground vector derives the
energy shift and both buffered low-space comparisons. A separate approximation of exactly
that same matrix gives actual Hermitian tensors on the nonempty physical chain.

These corrected auxiliaries support ALVV, arXiv:1602.08828v2, `t:aisefficient`,
lines 1373–1392. The interaction-label cluster bound, independent scale at least three times
order, explicit tensor bond and spectral window count remain visible. No polynomial GEN
or running-time claim is made; see `docs/paper-gaps/alvv16_cluster_approximation.tex` and
`docs/paper-gaps/alvv16_soft_regional_residuals.tex`.
-/

section

open ManyBody (interval)

open Matrix
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open ManyBody.BondInteraction (five_region_original_bond_data
  pairwise_commute_sum_internal_consecutive_regions)

namespace TNLean.MPS.AreaLaw.ALVV

/-- A denominator of at least two gives a coefficient proportional to the actual
boundary cardinality. Auxiliary to ALVV, arXiv:1602.08828v2, `lem:exp-approx`,
lines 1195–1255. -/
private theorem tail_coefficient_le {c d T U : ℝ} (hc : 0 ≤ c) (hd : 2 ≤ d) :
    (Real.exp (-(1 / 8) * (T - U) - 1) / (1 / 8)) * ((2 * c) / d) ≤
      (8 * c) * Real.exp (-(T - U) / 8) := by
  have hratio : (2 * c) / d ≤ c := by
    apply (div_le_iff₀ (by linarith only [hd] : 0 < d)).mpr
    nlinarith only [hc, hd]
  calc
    _ ≤ (Real.exp (-(1 / 8) * (T - U) - 1) / (1 / 8)) * c :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = (8 * c) * Real.exp (-(T - U) / 8) * Real.exp (-1) := by
      rw [show -(1 / 8 : ℝ) * (T - U) - 1 = -(T - U) / 8 + -1 by ring, Real.exp_add]
      ring
    _ ≤ (8 * c) * Real.exp (-(T - U) / 8) * 1 :=
      mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by norm_num)) (by positivity)
    _ = _ := mul_one _

open Classical in
/-- The reverse residual for simultaneous estimated-center soft replacements of
consecutive regions. The interior and all projection floors are constructed from the
original regional sums. Only the soft ground-energy cap is supplied to this auxiliary;
the physical five-region corollary derives it from the original Hamiltonian.
ALVV, arXiv:1602.08828v2, `lem:exp-approx` and `t:aisefficient`,
lines 1195–1255 and 1373–1392. -/
theorem norm_simultaneous_soft_reverse_residual
    {L q v : ℕ} (k : Fin (v + 1) → ℕ) (hk : Monotone k)
    (J : Finset (Fin (L - 1)))
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1)
    (e p : Fin v → ℝ) (S : Finset (Fin v)) (t : ℝ) (m : ℕ)
    (ht : 0 < t) (hm : 2 ≤ m)
    (hpl : ∀ j ∈ S, e j - 10 ≤ p j) (hpu : ∀ j ∈ S, p j ≤ e j)
    (he : ∀ j, ((∑ i ∈ Finset.univ.filter
      (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ), Φ.term i) -
        (e j : ℂ) • 1).PosSemidef) :
    let I := fun j : Fin v ↦ Finset.univ.filter
      (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ)
    let A := fun j : Fin v ↦ ∑ i ∈ I j, Φ.term i
    let Y := ∑ i ∈ J, Φ.term i
    let H := (∑ j, (A j - (e j : ℂ) • 1)) + Y
    let B := ∑ j, ((if j ∈ S then (p j : ℂ) • 1 +
      cfc (Real.softTruncation t m) (A j - (p j : ℂ) • 1) else A j) - (e j : ℂ) • 1)
    let G := B + Y
    let D := 10 * (S.card : ℝ)
    ∀ (basis : OrthonormalBasis (Fin L → Fin q) ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
      (a : (Fin L → Fin q) → ℝ),
      (∀ v, toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) G (basis v) =
        (a v : ℂ) • basis v) →
      ∀ mu eta T : ℝ, mu ≤ (J.card : ℝ) → 0 ≤ eta →
      let U := 2 * (eta + D + 3 * (J.card : ℝ) + 2)
      U ≤ t → U ≤ T →
      ‖(toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) (H - G)).domRestrict
        (Submodule.spectralSpanLE basis a (mu + eta))‖ ≤
        (S.card : ℝ) * ((8 * (J.card : ℝ)) * Real.exp (-(T - U) / 8) +
          (t / (m : ℝ)) * (T / t) ^ m) := by
  intro I A Y H B G D basis a hEigen mu eta T hmu heta U hscale hT
  have hm' : 1 ≤ m := by omega
  have hA (j : Fin v) : (A j).IsHermitian :=
    (posSemidef_sum _ fun i _ ↦ (h0 i).posSemidef).isHermitian
  have hcomm : Pairwise fun i j : Fin v ↦ Commute (A i) (A j) :=
    pairwise_commute_sum_internal_consecutive_regions k hk Φ
  obtain ⟨_hBpos, _hBle, hBA, hproj⟩ := softTruncation_commuting_family_bounds
    A e p S hA (fun j ↦ le_iff.mpr (he j)) hpl hpu hcomm t m ht hm'
  let C : ℝ := J.card
  let b0 := U - (t / (m : ℝ)) * (U / t) ^ m
  let W := Submodule.spectralSpanLE basis a (mu + eta)
  have hC0 : 0 ≤ C := by positivity
  have hD0 : 0 ≤ D := by positivity
  have hU0 : 0 ≤ U := by dsimp only [U]; positivity
  have hT0 : 0 ≤ T := hU0.trans hT
  have hshift (v : Fin L → Fin q) :
      toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
        ((B + (D : ℂ) • 1) + ∑ i ∈ J, Φ.term i) (basis v) =
        ((a v + D : ℝ) : ℂ) • basis v := by
    have hid : (B + (D : ℂ) • 1) + Y = G + (D : ℂ) • 1 := by
      dsimp only [G]
      abel
    change toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
      ((B + (D : ℂ) • 1) + Y) (basis v) = _
    rw [hid, map_add, map_smul, _root_.add_apply,
      _root_.smul_apply, map_one, one_apply_eq_self,
      hEigen v, Complex.ofReal_add, add_smul]
  have hW : Submodule.spectralSpanLE basis
      (fun v ↦ a v + D) (mu + eta + D) = W := by
    simpa only [sub_neg_eq_add] using Submodule.spectralSpanLE_sub
      basis a (-D) (mu + eta)
  have hsingle (j : Fin v) (hj : j ∈ S) :
      ‖(toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
        (A j - (p j : ℂ) • 1 -
          cfc (Real.softTruncation t m) (A j - (p j : ℂ) • 1))).domRestrict W‖ ≤
        (8 * C) * Real.exp (-(T - U) / 8) + (t / (m : ℝ)) * (T / t) ^ m := by
    have hScard : 1 ≤ S.card := Finset.card_pos.mpr ⟨j, hj⟩
    have hD10 : 10 ≤ D := by dsimp only [D]; exact_mod_cast Nat.mul_le_mul_left 10 hScard
    have haux : 0 ≤ eta + D + 3 * C - 6 := by linarith only [heta, hD10, hC0]
    have hscale' : 2 * ((eta + D + 3 * C - 6) + 8) ≤ t := by
      change 2 * (eta + D + 3 * C + 2) ≤ t at hscale
      linarith only [hscale]
    have hfloor := (Real.softTruncation_reverse_barrier_margin t m
      (eta + D + 3 * C - 6) 0 0 hm haux (by norm_num) (by norm_num) hscale').2.1
    have hfloor' : eta + D + 3 * C + 2 ≤ b0 := by
      dsimp only [b0, U]
      convert hfloor using 1 <;> ring
    have hdenom : 2 ≤ b0 - (mu + eta + D) - 2 * C := by
      change mu ≤ C at hmu
      linarith only [hfloor', hmu]
    have hgap : 2 * (J.card : ℝ) < b0 - (mu + eta + D) := by
      change 2 ≤ b0 - (mu + eta + D) - 2 * (J.card : ℝ) at hdenom
      linarith only [hdenom]
    have hp : (p j : ℂ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ≤ A j := by
      have hpe : (p j : ℂ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ≤
          (e j : ℂ) • 1 := by
        simpa only [Complex.coe_smul] using smul_le_smul_of_nonneg_right (hpu j hj)
          (zero_le_one : (0 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ≤ 1)
      exact hpe.trans (le_iff.mpr (he j))
    have hcomm' : Commute (B + (D : ℂ) • 1) (A j) :=
      (hBA j).add_left ((Commute.one_left (A j)).smul_left (D : ℂ))
    have htail := norm_soft_residual_low_of_barrier (I j) J Φ
      (fun i _ ↦ h0 i) (fun i _ ↦ h1 i) (B + (D : ℂ) • 1)
      (p j) (p j + U) b0 (mu + eta + D) (1 / 8) t T m hp
      (by norm_num) (by norm_num) ht hm' hT0
      (_root_.add_le_add (le_refl (p j)) hT) hcomm' (hproj j hj U hU0)
      basis (fun v ↦ a v + D) hshift hgap
    rw [hW] at htail
    have hdiff : (p j + T) - (p j + U) = T - U := by ring
    rw [hdiff] at htail
    exact htail.trans (_root_.add_le_add (tail_coefficient_le hC0 hdenom) (le_refl _))
  let F := fun j ↦ (p j : ℂ) • 1 +
    cfc (Real.softTruncation t m) (A j - (p j : ℂ) • 1)
  have hsum := norm_centered_clipping_discrepancy_domRestrict_le_sum
    A F (fun j ↦ (e j : ℂ)) S W
  have hdiff : H - G = (∑ j, (A j - (e j : ℂ) • 1)) - B := by
    dsimp only [H, G]
    abel
  rw [hdiff]
  refine hsum.trans ?_
  calc
    _ ≤ ∑ _j ∈ S, ((8 * C) * Real.exp (-(T - U) / 8) +
        (t / (m : ℝ)) * (T / t) ^ m) := by
      apply Finset.sum_le_sum
      intro j hj
      have hid : A j - F j = A j - (p j : ℂ) • 1 -
          cfc (Real.softTruncation t m) (A j - (p j : ℂ) • 1) := by
        dsimp only [F]
        abel
      rw [hid]
      exact hsingle j hj
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]


open Classical in
/-- The original-side residual for the same simultaneous estimated-center replacements.
The original common positive interior gives the projection floor; the ten-unit center
error is included in the cutoff margin. Auxiliary to ALVV, arXiv:1602.08828v2,
`lem:exp-approx` and `t:aisefficient`, lines 1195–1255 and 1373–1392. -/
theorem norm_simultaneous_soft_original_residual
    {L q v : ℕ} (k : Fin (v + 1) → ℕ) (hk : Monotone k)
    (J : Finset (Fin (L - 1)))
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1)
    (e p : Fin v → ℝ) (S : Finset (Fin v)) (t : ℝ) (m : ℕ)
    (ht : 0 < t) (hm : 1 ≤ m)
    (hpl : ∀ j ∈ S, e j - 10 ≤ p j) (hpu : ∀ j ∈ S, p j ≤ e j)
    (he : ∀ j, ((∑ i ∈ Finset.univ.filter
      (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ), Φ.term i) -
        (e j : ℂ) • 1).PosSemidef) :
    let I := fun j : Fin v ↦ Finset.univ.filter
      (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ)
    let A := fun j : Fin v ↦ ∑ i ∈ I j, Φ.term i
    let Y := ∑ i ∈ J, Φ.term i
    let Braw := ∑ j, (A j - (e j : ℂ) • 1)
    let H := Braw + Y
    let B := ∑ j, ((if j ∈ S then (p j : ℂ) • 1 +
      cfc (Real.softTruncation t m) (A j - (p j : ℂ) • 1) else A j) - (e j : ℂ) • 1)
    let G := B + Y
    ∀ (basis : OrthonormalBasis (Fin L → Fin q) ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
      (a : (Fin L → Fin q) → ℝ),
      (∀ v, toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) H (basis v) =
        (a v : ℂ) • basis v) →
      ∀ E eta T : ℝ, E ≤ (J.card : ℝ) → 0 ≤ eta →
      eta + 3 * (J.card : ℝ) + 12 ≤ T →
      ‖(toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) (H - G)).domRestrict
        (Submodule.spectralSpanLE basis a (E + eta))‖ ≤
        (S.card : ℝ) * ((8 * (J.card : ℝ)) *
          Real.exp (-(T - eta - 3 * (J.card : ℝ) - 12) / 8) +
          (t / (m : ℝ)) * (T / t) ^ m) := by
  intro I A Y Braw H B G basis a hEigen E eta T hE heta hT
  let C : ℝ := J.card
  let u := eta + 3 * C + 2
  let W := Submodule.spectralSpanLE basis a (E + eta)
  have hC0 : 0 ≤ C := by positivity
  have hu0 : 0 ≤ u := by dsimp only [u]; positivity
  have hT0 : 0 ≤ T := by change eta + 3 * C + 12 ≤ T at hT; linarith only [hT, heta, hC0]
  have hA (j : Fin v) : (A j).IsHermitian :=
    (posSemidef_sum _ fun i _ ↦ (h0 i).posSemidef).isHermitian
  have hcomm : Pairwise fun i j : Fin v ↦ Commute (A i) (A j) :=
    pairwise_commute_sum_internal_consecutive_regions k hk Φ
  have hdenom : 2 ≤ u - (E + eta) - 2 * C := by
    change E ≤ C at hE
    dsimp only [u]
    linarith only [hE]
  have hgap : 2 * (J.card : ℝ) < u - (E + eta) := by
    change 2 ≤ u - (E + eta) - 2 * (J.card : ℝ) at hdenom
    linarith only [hdenom]
  have hsingle (j : Fin v) (hj : j ∈ S) :
      ‖(toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
        (A j - (p j : ℂ) • 1 -
          cfc (Real.softTruncation t m) (A j - (p j : ℂ) • 1))).domRestrict W‖ ≤
        (8 * C) * Real.exp (-(T - eta - 3 * C - 12) / 8) +
          (t / (m : ℝ)) * (T / t) ^ m := by
    have hp : (p j : ℂ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ≤ A j := by
      have hpe : (p j : ℂ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ≤
          (e j : ℂ) • 1 := by
        simpa only [Complex.coe_smul] using smul_le_smul_of_nonneg_right (hpu j hj)
          (zero_le_one : (0 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ≤ 1)
      exact hpe.trans (le_iff.mpr (he j))
    have hBA : Commute Braw (A j) := by
      simpa only [Finset.notMem_empty, ite_false] using
        commute_centered_partially_clipped_sum A e 0 ∅ hcomm j
    have hproj : u • spectralProjectionGE (A j) (e j + u) ≤ Braw := by
      simpa only [Finset.notMem_empty, ite_false] using
        spectralProjectionGE_le_centered_partially_clipped_sum A e u u ∅ hA
          (fun j ↦ le_iff.mpr (he j)) hu0 le_rfl j
    have hcut : e j + u ≤ p j + T := by
      have hpj := hpl j hj
      change eta + 3 * C + 12 ≤ T at hT
      dsimp only [u]
      linarith only [hpj, hT]
    have htail := norm_soft_residual_low_of_barrier (I j) J Φ
      (fun i _ ↦ h0 i) (fun i _ ↦ h1 i) Braw
      (p j) (e j + u) u (E + eta) (1 / 8) t T m hp
      (by norm_num) (by norm_num) ht hm hT0 hcut hBA hproj
      basis a hEigen hgap
    have hcoeff := tail_coefficient_le (T := p j + T) (U := e j + u) hC0 hdenom
    have hexp : Real.exp (-((p j + T) - (e j + u)) / 8) ≤
        Real.exp (-(T - eta - 3 * C - 12) / 8) := by
      apply Real.exp_le_exp.mpr
      have hpj := hpl j hj
      dsimp only [u]
      linarith only [hpj]
    exact htail.trans (_root_.add_le_add
      (hcoeff.trans (mul_le_mul_of_nonneg_left hexp (by positivity))) (le_refl _))
  let F := fun j ↦ (p j : ℂ) • 1 +
    cfc (Real.softTruncation t m) (A j - (p j : ℂ) • 1)
  have hsum := norm_centered_clipping_discrepancy_domRestrict_le_sum
    A F (fun j ↦ (e j : ℂ)) S W
  have hdiff : H - G = (∑ j, (A j - (e j : ℂ) • 1)) - B := by
    dsimp only [H, G, Braw]
    abel
  rw [hdiff]
  refine hsum.trans ?_
  calc
    _ ≤ ∑ _j ∈ S, ((8 * C) * Real.exp (-(T - eta - 3 * C - 12) / 8) +
        (t / (m : ℝ)) * (T / t) ^ m) := by
      apply Finset.sum_le_sum
      intro j hj
      have hid : A j - F j = A j - (p j : ℂ) • 1 -
          cfc (Real.softTruncation t m) (A j - (p j : ℂ) • 1) := by
        dsimp only [F]
        abel
      rw [hid]
      exact hsingle j hj
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

end TNLean.MPS.AreaLaw.ALVV

end

section

open ManyBody (interval)

open Matrix
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw.ALVV

open Classical in
/-- The same actual simultaneous soft Hamiltonian has original-side and reverse residual
bounds, uniformly over estimated regional centers in their full ten-unit lower intervals.
Regional minima and original ground data precede every soft choice; the constructed soft
ground data precede every spectral width and tail cutoff. Auxiliary to ALVV,
arXiv:1602.08828v2, `def:soft-trunc`, `lem:exp-approx` and `t:aisefficient`,
lines 1178–1255 and 1373–1392. No successful approximation, gap or denominator is assumed. -/
theorem exists_five_region_soft_residuals {L q k1 k2 k3 k4 : ℕ}
    (hq : 0 < q) (h12 : k1 ≤ k2) (h23 : k2 ≤ k3)
    (h34 : k3 ≤ k4) (h4L : k4 ≤ L)
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1) :
    let k : Fin 6 → ℕ := ![0, k1, k2, k3, k4, L]
    let I := fun j : Fin 5 ↦ Finset.univ.filter
      (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ)
    let A := fun j : Fin 5 ↦ Φ.partialHamiltonian (I j)
    let J := Finset.univ.filter
      (fun i : Fin (L - 1) ↦ i.val + 1 ∈ ({k1, k2, k3, k4} : Finset ℕ))
    let Y := Φ.partialHamiltonian J
    J.card ≤ 4 ∧ ∃ (e : Fin 5 → ℝ) (x z : (Fin L → Fin q) → ℂ) (E : ℝ),
      star x ⬝ᵥ x = 1 ∧ (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
      (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧
      let H := Φ.hamiltonian - (((∑ j, e j) : ℝ) : ℂ) • 1
      star z ⬝ᵥ z = 1 ∧ H *ᵥ z = (E : ℂ) • z ∧
      (H - (E : ℂ) • 1).PosSemidef ∧ 0 ≤ E ∧ E ≤ (J.card : ℝ) ∧
      H.IsHermitian ∧
      ∃ (bH : OrthonormalBasis (Fin L → Fin q) ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
        (aH : (Fin L → Fin q) → ℝ),
        (∀ v, toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) H (bH v) =
          (aH v : ℂ) • bH v) ∧ ∀ (S : Finset (Fin 5)) (p : Fin 5 → ℝ) (t : ℝ) (m : ℕ),
        (∀ j ∈ S, e j - 10 ≤ p j) → (∀ j ∈ S, p j ≤ e j) → 0 < t → 2 ≤ m →
        let B := ∑ j, ((if j ∈ S then (p j : ℂ) • 1 +
          cfc (Real.softTruncation t m) (A j - (p j : ℂ) • 1) else A j) - (e j : ℂ) • 1)
        let D := 10 * (S.card : ℝ)
        let G := B + Y
        ∃ (mu : ℝ) (w : (Fin L → Fin q) → ℂ), G.IsHermitian ∧
          (B + (D : ℂ) • 1).PosSemidef ∧ G ≤ H ∧ star w ⬝ᵥ w = 1 ∧
          G *ᵥ w = (mu : ℂ) • w ∧ (G - (mu : ℂ) • 1).PosSemidef ∧
          -D ≤ mu ∧ mu ≤ E ∧ mu ≤ (J.card : ℝ) ∧
          ∃ (bG : OrthonormalBasis (Fin L → Fin q) ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
            (aG : (Fin L → Fin q) → ℝ),
            (∀ v, toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) G (bG v) =
              (aG v : ℂ) • bG v) ∧
          (∀ eta T : ℝ, 0 ≤ eta → eta + 3 * (J.card : ℝ) + 12 ≤ T →
            ‖(toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) (H - G)).domRestrict
              (Submodule.spectralSpanLE bH aH (E + eta))‖ ≤
              (S.card : ℝ) * ((8 * (J.card : ℝ)) *
                Real.exp (-(T - eta - 3 * (J.card : ℝ) - 12) / 8) +
                (t / (m : ℝ)) * (T / t) ^ m)) ∧
          (∀ eta T : ℝ, 0 ≤ eta →
            let U := 2 * (eta + D + 3 * (J.card : ℝ) + 2)
            U ≤ t → U ≤ T →
            ‖(toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) (H - G)).domRestrict
              (Submodule.spectralSpanLE bG aG (mu + eta))‖ ≤
              (S.card : ℝ) * ((8 * (J.card : ℝ)) * Real.exp (-(T - U) / 8) +
                (t / (m : ℝ)) * (T / t) ^ m)) := by
  intro k I A J Y
  obtain ⟨hJ, e, x, z, E, hx, hxe, he, hHY, _hBraw, hz, hHz,
      hE, hE0, hEC, hH, hfamily⟩ :=
    exists_five_region_soft_structure hq h12 h23 h34 h4L Φ h0 h1
  refine ⟨hJ, e, x, z, E, hx, hxe, he, hz, hHz, hE, hE0, hEC, hH,
    hH.eigenvectorBasis, hH.eigenvalues, hH.toEuclideanCLM_eigenvectorBasis, ?_⟩
  intro S p t m hpl hpu ht hm B D G
  have hm' : 1 ≤ m := by omega
  obtain ⟨mu, w, hG, hBpos, hGH, hw, hGw, hGlow, hmuD, hmuE, hmuC, _hBA, _hproj⟩ :=
    hfamily S p t m hpl hpu ht hm'
  have hk : Monotone k := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    fin_cases i <;> simp [k] <;> omega
  refine ⟨mu, w, hG, hBpos, hGH, hw, hGw, hGlow, hmuD, hmuE, hmuC,
    hG.eigenvectorBasis, hG.eigenvalues, hG.toEuclideanCLM_eigenvectorBasis, ?_, ?_⟩
  · intro eta T heta hT
    have hEigenH (v : Fin L → Fin q) :
        toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
          ((∑ j, (A j - (e j : ℂ) • 1)) + Y) (hH.eigenvectorBasis v) =
          (hH.eigenvalues v : ℂ) • hH.eigenvectorBasis v := by
      rw [← hHY]
      exact hH.toEuclideanCLM_eigenvectorBasis v
    have hres := norm_simultaneous_soft_original_residual k hk J Φ h0 h1
      e p S t m ht hm' hpl hpu he hH.eigenvectorBasis hH.eigenvalues hEigenH
        E eta T hEC heta hT
    have hdiff : ((∑ j, (A j - (e j : ℂ) • 1)) + Y) - G =
        (Φ.hamiltonian - (((∑ j, e j) : ℝ) : ℂ) • 1) - G := by
      rw [← hHY]
    rw [← hdiff]
    exact hres
  · intro eta T heta U hscale hT
    have hres := norm_simultaneous_soft_reverse_residual k hk J Φ h0 h1
      e p S t m ht hm hpl hpu he hG.eigenvectorBasis hG.eigenvalues
        hG.toEuclideanCLM_eigenvectorBasis mu eta T hmuC heta hscale hT
    have hdiff : ((∑ j, (A j - (e j : ℂ) • 1)) + Y) - G =
        (Φ.hamiltonian - (((∑ j, e j) : ℝ) : ℂ) • 1) - G := by
      rw [← hHY]
    rw [← hdiff]
    exact hres

end TNLean.MPS.AreaLaw.ALVV

end

section

open ManyBody (interval)

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw.ALVV

open Classical in
/-- One actual soft residual construction derives its low cluster from
primitive original spectral data and explicit scalar budgets. Every
Hermitian global norm approximant then has its own separated low cluster
and both directed comparisons to the original full ground space. The
regional minima, ground energies, actual eigenbases and both original
residual conclusions are retained, rather than selected a second time.
Auxiliary to ALVV, arXiv:1602.08828v2, `t:aisefficient`, lines 1373–1420. -/
theorem exists_five_region_soft_clusters {L q k1 k2 k3 k4 : ℕ}
    (hq : 0 < q) (h12 : k1 ≤ k2) (h23 : k2 ≤ k3)
    (h34 : k3 ≤ k4) (h4L : k4 ≤ L)
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1) :
    let k : Fin 6 → ℕ := ![0, k1, k2, k3, k4, L]
    let I := fun j : Fin 5 ↦ Finset.univ.filter
      (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ)
    let A := fun j : Fin 5 ↦ Φ.partialHamiltonian (I j)
    let J := Finset.univ.filter
      (fun i : Fin (L - 1) ↦ i.val + 1 ∈ ({k1, k2, k3, k4} : Finset ℕ))
    let Y := Φ.partialHamiltonian J
    J.card ≤ 4 ∧ ∃ (e : Fin 5 → ℝ) (x z : (Fin L → Fin q) → ℂ) (E : ℝ),
      star x ⬝ᵥ x = 1 ∧ (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
      (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧
      let H := Φ.hamiltonian - (((∑ j, e j) : ℝ) : ℂ) • 1
      star z ⬝ᵥ z = 1 ∧ H *ᵥ z = (E : ℂ) • z ∧
      (H - (E : ℂ) • 1).PosSemidef ∧ 0 ≤ E ∧ E ≤ (J.card : ℝ) ∧
      H.IsHermitian ∧
      ∃ (bH : OrthonormalBasis (Fin L → Fin q) ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
        (aH : (Fin L → Fin q) → ℝ),
        (∀ v, toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) H (bH v) =
          (aH v : ℂ) • bH v) ∧ ∀ (S : Finset (Fin 5)) (p : Fin 5 → ℝ) (t : ℝ) (m : ℕ),
        (∀ j ∈ S, e j - 10 ≤ p j) → (∀ j ∈ S, p j ≤ e j) → 0 < t → 2 ≤ m →
        let B := ∑ j, ((if j ∈ S then (p j : ℂ) • 1 +
          cfc (Real.softTruncation t m) (A j - (p j : ℂ) • 1) else A j) - (e j : ℂ) • 1)
        let D := 10 * (S.card : ℝ)
        let G := B + Y
        ∃ (mu : ℝ) (w : (Fin L → Fin q) → ℂ), G.IsHermitian ∧
          (B + (D : ℂ) • 1).PosSemidef ∧ G ≤ H ∧ star w ⬝ᵥ w = 1 ∧
          G *ᵥ w = (mu : ℂ) • w ∧ (G - (mu : ℂ) • 1).PosSemidef ∧
          -D ≤ mu ∧ mu ≤ E ∧ mu ≤ (J.card : ℝ) ∧
          ∃ (bG : OrthonormalBasis (Fin L → Fin q) ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
            (aG : (Fin L → Fin q) → ℝ),
            (∀ v, toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) G (bG v) =
              (aG v : ℂ) • bG v) ∧
          (∀ eta T : ℝ, 0 ≤ eta → eta + 3 * (J.card : ℝ) + 12 ≤ T →
            ‖(toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) (H - G)).domRestrict
              (Submodule.spectralSpanLE bH aH (E + eta))‖ ≤
              (S.card : ℝ) * ((8 * (J.card : ℝ)) *
                Real.exp (-(T - eta - 3 * (J.card : ℝ) - 12) / 8) +
                (t / (m : ℝ)) * (T / t) ^ m)) ∧
          (∀ eta T : ℝ, 0 ≤ eta →
            let U := 2 * (eta + D + 3 * (J.card : ℝ) + 2)
            U ≤ t → U ≤ T →
            ‖(toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) (H - G)).domRestrict
              (Submodule.spectralSpanLE bG aG (mu + eta))‖ ≤
              (S.card : ℝ) * ((8 * (J.card : ℝ)) * Real.exp (-(T - U) / 8) +
                (t / (m : ℝ)) * (T / t) ^ m)) ∧
          (let Hraw := Φ.hamiltonian
          let hRaw : Hraw.IsHermitian :=
            (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
          ∀ mu0 g tau T0 T1 : ℝ, mu0 ∈ spectrum ℝ Hraw → 0 < g →
            0 < tau → tau ≤ 1 →
            (∀ z ∈ spectrum ℝ Hraw, z = mu0 ∨ mu0 + g ≤ z) →
            let etaR := E - mu + 19 * g / 20
            let U := 2 * (etaR + D + 3 * (J.card : ℝ) + 2)
            g / 40 + 3 * (J.card : ℝ) + 12 ≤ T0 → U ≤ t → U ≤ T1 →
            let rhoO := (S.card : ℝ) * ((8 * (J.card : ℝ)) *
              Real.exp (-(T0 - g / 40 - 3 * (J.card : ℝ) - 12) / 8) +
              (t / (m : ℝ)) * (T0 / t) ^ m)
            let rhoR := (S.card : ℝ) * ((8 * (J.card : ℝ)) *
              Real.exp (-(T1 - U) / 8) + (t / (m : ℝ)) * (T1 / t) ^ m)
            rhoO ≤ tau * g / 1000000 → rhoR ≤ tau * g / 1000000 →
            let original := Submodule.spectralSpanLE hRaw.eigenvectorBasis hRaw.eigenvalues mu0
            let soft := Submodule.spectralSpanLE bG aG (E + g / 20)
            E + ∑ j, e j = mu0 ∧
              soft = Submodule.spectralSpanLE bG aG (E + 19 * g / 20) ∧
              Module.finrank ℂ soft = Module.finrank ℂ original ∧
              Submodule.IsCloseTo (tau / 200 : ℝ) soft original ∧
              Submodule.IsCloseTo (tau / 200 : ℝ) original soft ∧
            ∀ (Bhat : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
              (hBhat : Bhat.IsHermitian) (xi : ℝ), 0 < xi → ‖G - Bhat‖ ≤ xi →
              let V := ‖G‖ + xi
              let nLo := ⌈((E + g / 20) - min (E + g / 20 - 1) (-V)) / (2 * xi)⌉₊
              let nHi := ⌈((E + 3 * g / 4) - min (E + 3 * g / 4 - 1) (-V)) / (2 * xi)⌉₊
              let deltaLo := (nLo : ℝ) * (2 * xi) ^ 2 / (g / 5 + xi) ^ 2
              let deltaHi := (nHi : ℝ) * (2 * xi) ^ 2 / (g / 5 + xi) ^ 2
              deltaLo < 1 → deltaHi < 1 →
              let target := Submodule.spectralSpanLE hBhat.eigenvectorBasis hBhat.eigenvalues
                (E + g / 4)
              target = Submodule.spectralSpanLE hBhat.eigenvectorBasis hBhat.eigenvalues
                  (E + 3 * g / 4) ∧
                Module.finrank ℂ target = Module.finrank ℂ original ∧
                Submodule.IsCloseTo (2 * (deltaLo + tau / 200)) target original ∧
                Submodule.IsCloseTo (2 * (deltaHi + tau / 200)) original target) := by
  intro k I A J Y
  obtain ⟨hJ, e, x, z, E, hx, hxe, he, hz, hHz, hE, hE0, hEC,
    hH, bH, aH, hEigH, hfamily⟩ :=
    exists_five_region_soft_residuals hq h12 h23 h34 h4L Φ h0 h1
  refine ⟨hJ, e, x, z, E, hx, hxe, he, hz, hHz, hE, hE0, hEC,
    hH, bH, aH, hEigH, ?_⟩
  intro S p t m hpl hpu ht hm B D G
  obtain ⟨mu, w, hG, hBpos, hGH, hw, hGw, hGlow, hmuD, hmuE, hmuC,
    bG, aG, hEigG, hforward, hreverse⟩ := hfamily S p t m hpl hpu ht hm
  change G.IsHermitian at hG
  refine ⟨mu, w, hG, hBpos, hGH, hw, hGw, hGlow, hmuD, hmuE, hmuC,
    bG, aG, hEigG, hforward, hreverse, ?_⟩
  clear hfamily
  intro Hraw hRaw mu0 g tau T0 T1 hmu0 hg htau htau1 hgap
    etaR U hT0 hUt hUT1 rhoO rhoR hsmallO hsmallR original soft
  let : Nonempty (Fin L → Fin q) := ⟨fun _ ↦ ⟨0, hq⟩⟩
  obtain ⟨hgroundShift, hrawEigen, hrawGap⟩ := hRaw.original_basis_centered_gap_data
    mu0 g (∑ j, e j) E hmu0 hgap hg z hz hHz hE
  have hspan (cutoff : ℝ) := Submodule.spectralSpanLE_eq_of_eigenbases
    bH hRaw.eigenvectorBasis aH (fun j ↦ hRaw.eigenvalues j - ∑ i, e i)
    hEigH hrawEigen cutoff
  have hOriginal : Submodule.spectralSpanLE hRaw.eigenvectorBasis
      (fun j ↦ hRaw.eigenvalues j - ∑ i, e i) E = original := by
    simpa only [show mu0 - ∑ i, e i = E by linarith only [hgroundShift]] using
      Submodule.spectralSpanLE_sub hRaw.eigenvectorBasis hRaw.eigenvalues (∑ j, e j) mu0
  have hresO : ‖(toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
      (Hraw - (((∑ j, e j) : ℝ) : ℂ) • 1) -
      toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) G).domRestrict
        (Submodule.spectralSpanLE hRaw.eigenvectorBasis
          (fun j ↦ hRaw.eigenvalues j - ∑ i, e i) (E + g / 40))‖ ≤
      tau * g / 1000000 := by
    rw [← hspan (E + g / 40)]
    simpa only [map_sub] using
      (hforward (g / 40) T0 (by positivity) hT0).trans hsmallO
  have hresR : ‖(toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
      (Hraw - (((∑ j, e j) : ℝ) : ℂ) • 1) -
      toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) G).domRestrict
        (Submodule.spectralSpanLE bG aG (E + 19 * g / 20))‖ ≤
      tau * g / 1000000 := by
    rw [show E + 19 * g / 20 = mu + etaR by dsimp only [etaR]; ring]
    simpa only [map_sub] using
      (hreverse etaR T1 (by dsimp only [etaR]; linarith only [hmuE, hg])
        hUt hUT1).trans hsmallR
  obtain ⟨hcluster, hdim, hsoftRaw, hrawSoft, _hwindow, _hspectrum⟩ :=
    Submodule.low_spectral_cluster_of_scaled_restricted_residuals
      (toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
        (Hraw - (((∑ j, e j) : ℝ) : ℂ) • 1))
      (toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) G)
      hRaw.eigenvectorBasis bG (fun j ↦ hRaw.eigenvalues j - ∑ i, e i) aG
      hrawEigen hEigG E g (tau * g / 1000000) tau hg htau htau1
      (by positivity) le_rfl hrawGap hresO hresR
  rw [hOriginal] at hdim hsoftRaw hrawSoft
  refine ⟨hgroundShift.symm, hcluster, hdim, hsoftRaw, hrawSoft, ?_⟩
  intro Bhat hBhat xi hxi herr V nLo nHi deltaLo deltaHi hLo hHi target
  have hcanonical (cutoff : ℝ) := Submodule.spectralSpanLE_eq_of_eigenbases
    hG.eigenvectorBasis bG hG.eigenvalues aG hG.toEuclideanCLM_eigenvectorBasis hEigG cutoff
  have hcanCluster :
      Submodule.spectralSpanLE hG.eigenvectorBasis hG.eigenvalues (E + g / 20) =
        Submodule.spectralSpanLE hG.eigenvectorBasis hG.eigenvalues (E + 19 * g / 20) := by
    simpa only [hcanonical (E + g / 20), hcanonical (E + 19 * g / 20)] using hcluster
  have hApprox := hG.spectral_cluster_of_norm_sub_le hBhat
    (E + g / 20) (E + g / 4) (E + 3 * g / 4) (E + 19 * g / 20) xi
    (by linarith only [hg]) (by linarith only [hg]) (by linarith only [hg])
    hxi herr hcanCluster
  simp only [hcanonical (E + g / 20),
    show (E + g / 4) - (E + g / 20) = g / 5 by ring,
    show (E + 19 * g / 20) - (E + 3 * g / 4) = g / 5 by ring] at hApprox
  obtain ⟨hTarget, hdimTarget, hTargetSoft, hSoftTarget, _hTargetWindow⟩ := hApprox hLo hHi
  have hTargetOriginal : Submodule.IsCloseTo (2 * (deltaLo + tau / 200)) target original := by
    convert hTargetSoft.trans_weighted (θ := 1) hsoftRaw (by positivity) (by norm_num) using 1
    ring
  have hOriginalTarget : Submodule.IsCloseTo (2 * (deltaHi + tau / 200)) original target := by
    convert hrawSoft.trans_weighted (θ := 1) hSoftTarget (by positivity) (by norm_num) using 1
    ring
  exact ⟨hTarget, hdimTarget.trans
    ((congrArg (fun P : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)) ↦
      Module.finrank ℂ P) (hcanonical (E + g / 20))).trans hdim),
    hTargetOriginal, hOriginalTarget⟩

end TNLean.MPS.AreaLaw.ALVV

end

section

open Matrix
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw.ALVV

open Classical in
/-- The actual simultaneous estimated-center soft Hamiltonian has both physical residuals,
a derived ground-energy shift, both directed buffered spectral comparisons and an actual
Hermitian MPO approximation. Regional and soft ground data precede all comparison parameters
and the requested MPO accuracy. The represented chain has N+1 sites. Corrected auxiliary to
ALVV, arXiv:1602.08828v2, `t:aisefficient`, lines 1373–1392; no efficient-GEN conclusion. -/
theorem exists_five_region_soft_representation {N q k1 k2 k3 k4 : ℕ}
    (hq : 0 < q) (h12 : k1 ≤ k2) (h23 : k2 ≤ k3)
    (h34 : k3 ≤ k4) (h4L : k4 ≤ N + 1)
    (Φ : ManyBody.BondInteraction (N + 1) q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1) :
    let k : Fin 6 → ℕ := ![0, k1, k2, k3, k4, N + 1]
    let I := fun j : Fin 5 ↦ Finset.univ.filter
      (fun i : Fin N ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ)
    let A := fun j : Fin 5 ↦ Φ.partialHamiltonian (I j)
    let J := Finset.univ.filter
      (fun i : Fin N ↦ i.val + 1 ∈ ({k1, k2, k3, k4} : Finset ℕ))
    let Y := Φ.partialHamiltonian J
    J.card ≤ 4 ∧ ∃ (e : Fin 5 → ℝ) (x z : (Fin (N + 1) → Fin q) → ℂ) (E : ℝ),
      star x ⬝ᵥ x = 1 ∧ (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
      (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧
      let H := Φ.hamiltonian - (((∑ j, e j) : ℝ) : ℂ) • 1
      star z ⬝ᵥ z = 1 ∧ H *ᵥ z = (E : ℂ) • z ∧
      (H - (E : ℂ) • 1).PosSemidef ∧ 0 ≤ E ∧ E ≤ (J.card : ℝ) ∧
      H.IsHermitian ∧
      ∃ (bH : OrthonormalBasis (Fin (N + 1) → Fin q) ℂ (EuclideanSpace ℂ (Fin (N + 1) → Fin q)))
        (aH : (Fin (N + 1) → Fin q) → ℝ),
        (∀ v, toEuclideanCLM (n := Fin (N + 1) → Fin q) (𝕜 := ℂ) H (bH v) =
          (aH v : ℂ) • bH v) ∧ ∀ (S : Finset (Fin 5)) (p : Fin 5 → ℝ) (t : ℝ) (m : ℕ),
        (∀ j ∈ S, e j - 10 ≤ p j) → (∀ j ∈ S, p j ≤ e j) → 0 < t → 2 ≤ m →
        let B := ∑ j, ((if j ∈ S then (p j : ℂ) • 1 +
          cfc (Real.softTruncation t m) (A j - (p j : ℂ) • 1) else A j) - (e j : ℂ) • 1)
        let D := 10 * (S.card : ℝ)
        let G := B + Y
        ∃ (mu : ℝ) (w : (Fin (N + 1) → Fin q) → ℂ), G.IsHermitian ∧
          (B + (D : ℂ) • 1).PosSemidef ∧ G ≤ H ∧ star w ⬝ᵥ w = 1 ∧
          G *ᵥ w = (mu : ℂ) • w ∧ (G - (mu : ℂ) • 1).PosSemidef ∧
          -D ≤ mu ∧ mu ≤ E ∧ mu ≤ (J.card : ℝ) ∧
          ∃ (bG : OrthonormalBasis (Fin (N + 1) → Fin q) ℂ (EuclideanSpace ℂ (Fin (N + 1) → Fin q)))
            (aG : (Fin (N + 1) → Fin q) → ℝ),
            (∀ v, toEuclideanCLM (n := Fin (N + 1) → Fin q) (𝕜 := ℂ) G (bG v) =
              (aG v : ℂ) • bG v) ∧
          (∀ eta T : ℝ, 0 ≤ eta → eta + 3 * (J.card : ℝ) + 12 ≤ T →
            ‖(toEuclideanCLM (n := Fin (N + 1) → Fin q) (𝕜 := ℂ) (H - G)).domRestrict
              (Submodule.spectralSpanLE bH aH (E + eta))‖ ≤
              (S.card : ℝ) * ((8 * (J.card : ℝ)) *
                Real.exp (-(T - eta - 3 * (J.card : ℝ) - 12) / 8) +
                (t / (m : ℝ)) * (T / t) ^ m)) ∧
          (∀ eta T : ℝ, 0 ≤ eta →
            let U := 2 * (eta + D + 3 * (J.card : ℝ) + 2)
            U ≤ t → U ≤ T →
            ‖(toEuclideanCLM (n := Fin (N + 1) → Fin q) (𝕜 := ℂ) (H - G)).domRestrict
              (Submodule.spectralSpanLE bG aG (mu + eta))‖ ≤
              (S.card : ℝ) * ((8 * (J.card : ℝ)) * Real.exp (-(T - U) / 8) +
                (t / (m : ℝ)) * (T / t) ^ m)) ∧
          (∀ eta T hwin wbuf : ℝ, 0 ≤ eta → 0 < hwin → 0 < wbuf →
            let U := 2 * (eta + D + 3 * (J.card : ℝ) + 2)
            U ≤ t → U ≤ T → eta + 3 * (J.card : ℝ) + 12 ≤ T →
            let rhoH := (S.card : ℝ) * ((8 * (J.card : ℝ)) *
              Real.exp (-(T - eta - 3 * (J.card : ℝ) - 12) / 8) +
              (t / (m : ℝ)) * (T / t) ^ m)
            let rhoG := (S.card : ℝ) * ((8 * (J.card : ℝ)) * Real.exp (-(T - U) / 8) +
              (t / (m : ℝ)) * (T / t) ^ m)
            let count := ⌈(eta + hwin) / (2 * hwin)⌉₊
            0 ≤ E - mu ∧ E - mu ≤ rhoG ∧
              Submodule.IsCloseTo ((count : ℝ) * (rhoH + hwin) ^ 2 / (wbuf + hwin) ^ 2)
                (Submodule.spectralSpanLE bG aG (mu + eta + rhoG + wbuf))
                (Submodule.spectralSpanLE bH aH (E + eta)) ∧
              Submodule.IsCloseTo ((count : ℝ) * (rhoG + hwin) ^ 2 / (wbuf + hwin) ^ 2)
                (Submodule.spectralSpanLE bH aH (E + eta + wbuf))
                (Submodule.spectralSpanLE bG aG (mu + eta))) ∧
          (∀ xi : ℝ, 0 < xi → 3 * (m : ℝ) ≤ t →
            let delta := xi / (max 1 S.card : ℕ)
            let W := t * (2 : ℝ) ^ (m + 1)
            let b := 2 * (Real.exp (1 / 3 : ℝ) - 1)
            let r := max 1 ⌈(Real.log (max 1 ((N : ℝ) ^ 2)) -
              Real.log (Real.log (1 + delta / W))) / (-Real.log b)⌉₊
            let D0 := 1 + N * q ^ 2
            let bond := D0 + ((D0 + (r ^ 2 * q ^ r) * (m + 1)) * 2) * S.card
            ∃ tensors : Fin (N + 1) → MPOTensor q bond,
              (MPOTensor.traceChainOperator tensors 1).IsHermitian ∧
              ‖G - MPOTensor.traceChainOperator tensors 1‖ ≤ xi) := by
  intro k I A J Y
  obtain ⟨hJ, e, x, z, E, hx, hxe, he, hz, hHz, hE, hE0, hEC,
      hH, bH, aH, hEigH, hfamily⟩ :=
    exists_five_region_soft_residuals hq h12 h23 h34 h4L Φ h0 h1
  let H := Φ.hamiltonian - (((∑ j, e j) : ℝ) : ℂ) • 1
  refine ⟨hJ, e, x, z, E, hx, hxe, he, hz, hHz, hE, hE0, hEC, hH, bH, aH, hEigH, ?_⟩
  intro S p t m hpl hpu ht hm B D G
  obtain ⟨mu, w, hG, hBpos, hGH, hw, hGw, hGlow, hmuD, hmuE, hmuC,
      bG, aG, hEigG, hforward, hreverse⟩ := hfamily S p t m hpl hpu ht hm
  refine ⟨mu, w, hG, hBpos, hGH, hw, hGw, hGlow, hmuD, hmuE, hmuC,
    bG, aG, hEigG, hforward, hreverse, ?_, ?_⟩
  · intro eta T hwin wbuf heta hhwin hwbuf U hscale hT hTorig rhoH rhoG count
    let v : EuclideanSpace ℂ (Fin (N + 1) → Fin q) :=
      (EuclideanSpace.equiv (Fin (N + 1) → Fin q) ℂ).symm w
    have hvnorm : ‖v‖ = 1 := by
      have hsquare := re_star_dotProduct_self_eq_norm_sq w
      rw [hw] at hsquare
      change (1 : ℝ) = ‖v‖ ^ 2 at hsquare
      nlinarith only [hsquare, norm_nonneg v]
    have hvEigen : toEuclideanCLM (n := Fin (N + 1) → Fin q) (𝕜 := ℂ) G v =
        (mu : ℂ) • v := by
      change (EuclideanSpace.equiv (Fin (N + 1) → Fin q) ℂ).symm (G *ᵥ w) = _
      have hGw' : G *ᵥ w = (mu : ℂ) • w := hGw
      rw [hGw', map_smul]
    exact ground_shift_and_isCloseTo_pair_of_restricted_residuals H G
      E mu eta rhoH rhoG hwin wbuf hE hGlow bH bG aH aG hEigH hEigG
      v hvnorm hvEigen hmuE heta hhwin hwbuf
      (hforward eta T heta hTorig) (hreverse eta T heta hscale hT)
  · intro xi hxi hscale delta W b r D0 bond
    let F := fun j : Fin 5 ↦ (p j : ℂ) • 1 +
      cfc (Real.softTruncation t m) (A j - (p j : ℂ) • 1)
    let Braw := ∑ j, (A j - (e j : ℂ) • 1)
    obtain ⟨_hk, _hR, _hsA, _hA, _hY, _hYC, _hJ, hsumraw⟩ :=
      ManyBody.BondInteraction.five_region_original_bond_data (N + 1) q k1 k2 k3 k4
        h12 h23 h34 h4L Φ h0 h1
    change Φ.hamiltonian = (∑ j, A j) + Y at hsumraw
    have hcenter : H = Braw + Y := by
      dsimp only [H, Braw]
      rw [hsumraw, Finset.sum_sub_distrib]
      push_cast
      rw [Finset.sum_smul]
      abel
    have hdiff : Braw - B = ∑ j ∈ S, (A j - F j) :=
      sum_centered_sub_partially_replaced_eq A F (fun j ↦ (e j : ℂ) • 1) S
    have hGsum : G = H + ∑ j ∈ S, (F j - A j) := by
      calc
        _ = (Braw + Y) - (Braw - B) := by dsimp only [G]; abel
        _ = H - ∑ j ∈ S, (A j - F j) := by rw [← hcenter, hdiff]
        _ = _ := by rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]; abel
    have hs' (i : Fin N) : ManyBody.IsSupportedOn (X := fun _ ↦ Fin q)
        (Φ.term i) {i.castSucc, i.succ} := Φ.term_mem_supportedOperators_chainBond i
    have hherm (i : Fin N) : (Φ.term i).IsHermitian := (h0 i).posSemidef.isHermitian
    have hnorm (i : Fin N) : ‖Φ.term i‖ ≤ 1 :=
      (CStarAlgebra.norm_le_one_iff_of_nonneg (Φ.term i) (h0 i)).mpr (h1 i)
    have hlo (j : Fin 5) (hj : j ∈ S) : (p j : ℂ) • 1 ≤ A j := by
      have hpe : (p j : ℝ) • (1 : Matrix (Fin (N + 1) → Fin q)
          (Fin (N + 1) → Fin q) ℂ) ≤ (e j : ℝ) • 1 :=
        smul_le_smul_of_nonneg_right (hpu j hj) zero_le_one
      have heA : (e j : ℝ) • (1 : Matrix (Fin (N + 1) → Fin q)
          (Fin (N + 1) → Fin q) ℂ) ≤ A j := by
        have heAj : (A j - (e j : ℂ) • 1).PosSemidef := he j
        have heA' : (e j : ℂ) • (1 : Matrix (Fin (N + 1) → Fin q)
            (Fin (N + 1) → Fin q) ℂ) ≤ A j := Matrix.le_iff.mpr heAj
        simpa only [Complex.coe_smul] using heA'
      simpa only [Complex.coe_smul] using hpe.trans heA
    obtain ⟨tensors, _hM, hMT, herr⟩ :=
      exists_selected_regional_softTruncations_hermitian_mpo_of_accuracy
        (by omega : 1 ≤ q) (by omega : 0 < m) Φ.term hs' hherm hnorm I p S
        t xi (-∑ j, e j) hlo hscale hxi
    have hmatrix : Φ.hamiltonian + (((-∑ j, e j) : ℝ) : ℂ) • 1 +
        ∑ j ∈ S, (F j - A j) = G := by
      rw [hGsum]
      dsimp only [H]
      rw [Complex.ofReal_neg, neg_smul]
      abel
    refine ⟨tensors, hMT, ?_⟩
    rw [← hmatrix]
    exact herr

end TNLean.MPS.AreaLaw.ALVV

end
