/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.RegionalBarrierResidual
import TNLean.MPS.AreaLaw.FiveRegionHamiltonian
import QICLean.Analysis.SoftTruncationCommutingFamily
import QICLean.Analysis.ShiftedLowEnergyCoordinates

/-!
# Simultaneous residuals for actual regional soft replacements

The same common interior is used after every selected replacement. The local boundary
consists of the original bonds; its actual cardinality determines the reverse threshold.
This conditional auxiliary to ALVV, arXiv:1602.08828v2, `lem:exp-approx` and
`t:aisefficient`, lines 1195–1255 and 1373–1392, is to be applied with the physically
constructed regional minima and soft ground-energy cap. It assumes no residual or gap.
-/

open Matrix
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

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
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    (e p : Fin v → ℝ) (S : Finset (Fin v)) (t : ℝ) (m : ℕ)
    (ht : 0 < t) (hm : 2 ≤ m)
    (hpl : ∀ j ∈ S, e j - 10 ≤ p j) (hpu : ∀ j ∈ S, p j ≤ e j)
    (he : ∀ j, ((∑ i ∈ Finset.univ.filter
      (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ), h i) -
        (e j : ℂ) • 1).PosSemidef) :
    let I := fun j : Fin v ↦ Finset.univ.filter
      (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ)
    let A := fun j : Fin v ↦ ∑ i ∈ I j, h i
    let Y := ∑ i ∈ J, h i
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
    pairwise_commute_sum_internal_consecutive_regions k hk h hs
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
        ((B + (D : ℂ) • 1) + ∑ i ∈ J, h i) (basis v) =
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
    have htail := norm_soft_residual_low_of_barrier (I j) J h
      (fun i _ ↦ hs i) (fun i _ ↦ h0 i) (fun i _ ↦ h1 i) (B + (D : ℂ) • 1)
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
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    (e p : Fin v → ℝ) (S : Finset (Fin v)) (t : ℝ) (m : ℕ)
    (ht : 0 < t) (hm : 1 ≤ m)
    (hpl : ∀ j ∈ S, e j - 10 ≤ p j) (hpu : ∀ j ∈ S, p j ≤ e j)
    (he : ∀ j, ((∑ i ∈ Finset.univ.filter
      (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ), h i) -
        (e j : ℂ) • 1).PosSemidef) :
    let I := fun j : Fin v ↦ Finset.univ.filter
      (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ)
    let A := fun j : Fin v ↦ ∑ i ∈ I j, h i
    let Y := ∑ i ∈ J, h i
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
    pairwise_commute_sum_internal_consecutive_regions k hk h hs
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
    have htail := norm_soft_residual_low_of_barrier (I j) J h
      (fun i _ ↦ hs i) (fun i _ ↦ h0 i) (fun i _ ↦ h1 i) Braw
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
