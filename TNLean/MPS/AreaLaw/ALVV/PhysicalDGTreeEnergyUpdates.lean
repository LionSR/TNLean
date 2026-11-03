/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalDGInterleavedTree
import TNLean.MPS.AreaLaw.ALVV.SoftWordNodeEnergy

/-!
# Energy updates on the actual interleaved interval tree

The calibrated construction selects its targets, operator families and retained
spaces once. Each long node then admits the corrected one-sided energy update
on its own literal one-word child image. No second operator family or space
tree is selected for the energy calculation.

This is an auxiliary to ALVV, arXiv:1602.08828v2, Figure `fig:algo1`,
line 1631, and its energy argument at line 1807.
**Local fix (same-family one-sided update):** This construction uses the
calibrated hard-clipped family and the corrected raw compressed minimum minus
three. It does not identify that family with literal soft Generate or assert
a running-time bound. See
`docs/paper-gaps/alvv16_soft_regional_energy_centering.tex`.
-/

open Matrix
open scoped BigOperators TensorProduct ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- The actual interleaved tree retains its original spaces, targets and
families while acquiring the one-sided node energy callback. At every long
node, all child estimates of width 49/16 yield an actual raw compression
update of the same width. Corrected auxiliary to ALVV,
arXiv:1602.08828v2, Figure `fig:algo1`, line 1631, and line 1807. -/
theorem exists_physical_dg_interleaved_tree_with_energy_updates :
    ∃ Ctail C Kref : ℝ, 21 ≤ Ctail ∧ 21 ≤ C ∧ 0 < Kref ∧ ∀ (L q : ℕ),
    ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
      (_hsupp : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
        (h i) (interval L i.val (i.val + 2)))
      (h0 : ∀ i, 0 ≤ h i) (_h1 : ∀ i, h i ≤ 1) (mu nu gamma : ℝ),
    0 < gamma →
    let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i, h i
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    mu ∈ spectrum ℝ H → nu ∈ spectrum ℝ H → mu < nu →
    (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
    let rG := Module.finrank ℂ G
    let g := min gamma 1
    let m := max q 50
    let w := 1 + Real.log (rG : ℝ) + 2 * Real.log ((L : ℝ) + 1)
    let v := 1 + Real.log (m : ℝ) + Real.log (1 / g) + Real.log (1 + w)
    let ell := Nat.ceil (C * (v ^ 6 / g + Real.sqrt w * v ^ 3 / Real.sqrt g))
    let D := (m * ell ^ 2) ^ (22 * ell)
    let s := Nat.ceil (4096 * (rG : ℝ) * (Real.log (D : ℝ) + w))
    let a := 3 / (32 * (D : ℝ) ^ 12 * (s : ℝ) ^ 5)
    let tau := a ^ 2 / 1048576
    let epsilon := 200 * tau
    let t := Ctail * (1 + Real.log (1 / g) + Real.log (1 / tau))
    let Delta := (1 / 200000 : ℝ) / (D : ℝ) ^ 12
    21 ≤ ell ∧ 2 ≤ D ∧ 1 ≤ s ∧ 0 < a ∧ a ≤ 1 / 100 ∧
      0 < epsilon ∧ epsilon ≤ 1 ∧ 21 ≤ t ∧
      (288 * Real.exp (11 / 8)) * Real.exp (-(t - g) / 8) ≤ epsilon * g / 1000000 ∧
      (D : ℝ) ^ 12 * Delta < 1 / 100000 ∧
    let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
    let bref := 16 + Real.log (1 / g) + Real.log (32 * (rG : ℝ) * ((L : ℝ) + 1) / tau)
    ∃ B : ℕ, 1 ≤ B ∧
      Real.log (B : ℝ) ≤
        Kref * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * bref ^ (3 / 4 : ℝ) * u) *
          (1 + Real.log bref) ∧
    ∃ U : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)),
      Module.finrank ℂ U = rG ∧
      (∀ z ∈ U, IsOpenMPS L q (rG ^ 2 * B) (fun x ↦ z x)) ∧
    let Dref := rG ^ 2 * B
    let xiMax := a / (256 * (Dref : ℝ) * Real.sqrt ((L : ℝ) + 1))
    0 < xiMax ∧
    let width := 4 * ell
    ∃ hwidth : 1 ≤ width, ∃ hq : 0 < q,
    ∃ (T : LongIntervalIndex L width →
        Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
      (N : LongIntervalIndex L width → ℕ)
      (F : ∀ J : LongIntervalIndex L width,
        Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
          EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)),
      (∀ J, N J ≤ D ^ 2) ∧
      (∀ J, Module.finrank ℂ (T J) = rG ∧
        Submodule.IsCloseTo tau (T J) G ∧ Submodule.IsCloseTo tau G (T J) ∧
        Submodule.IsCloseTo (4 * tau) (T J) U ∧
        Submodule.IsCloseTo (4 * tau) U (T J) ∧
        (∀ (power : ℕ)
          (S : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))) (delta : ℝ),
          Submodule.IsViable delta S
            ((T J).map (Entropy.regionTensorCoordinates q
              (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap) → delta < 1 →
          let grow := ⨆ w : Fin power → Fin (N J),
            S.map ((List.ofFn (fun j ↦ F J (w j))).prod : _ →ₗ[ℂ] _)
          Module.finrank ℂ grow ≤ (D ^ 2) ^ power * Module.finrank ℂ S ∧
            Submodule.IsViable (Delta ^ power / (1 - delta) ^ 2) grow
              ((T J).map (Entropy.regionTensorCoordinates q
                (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap))) ∧
      ∀ xi : ℝ, 0 < xi → xi ≤ xiMax →
      ∃ operation : IntervalMergeOperation L q,
        (∀ (p r : ℕ), p ≤ r → r ≤ L →
          let S := balancedIntervalSpace operation width hwidth p r
          Submodule.IsViable (3 / 200 : ℝ) S
            (G.map (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap) ∧
          Module.finrank ℂ S ≤ D ^ 6 * s ^ 3 ∧
          IsIntervalSpanWithRankBound L q p r (D ^ 6 * s ^ 3) xi S) ∧
        (∀ (J : LongIntervalIndex L width) (k : ℕ)
          (hpk : J.val.1 ≤ k) (hkr : k ≤ J.val.2),
          let S1 := balancedIntervalSpace operation width hwidth J.val.1 k
          let S2 := balancedIntervalSpace operation width hwidth k J.val.2
          ∃ U : Matrix.unitaryGroup
            (Fin (Module.finrank ℂ (adjacentIntervalMerge L q
              J.val.1 k J.val.2 hpk hkr S1 S2))) ℂ,
            operation J.val.1 k J.val.2 hpk hkr S1 S2 =
              sampledIntervalInterleavedTrim L q J.val.1 J.val.2 D s (F J) xi
                (adjacentIntervalMerge L q J.val.1 k J.val.2 hpk hkr S1 S2) U) ∧
        ∀ (J : LongIntervalIndex L width) (k : ℕ)
          (hpk : J.val.1 ≤ k) (hkr : k ≤ J.val.2),
          let S1 := balancedIntervalSpace operation width hwidth J.val.1 k
          let S2 := balancedIntervalSpace operation width hwidth k J.val.2
          ALVV.HasSoftWordNodeEnergyUpdate
            (u := J.val.1 + ell) (v := J.val.2 - ell) hq hpk hkr h (F J) S1 S2 := by
  classical
  obtain ⟨Ctail, C, Kref, hCtail, hC, hKref, hfactory⟩ :=
    exists_physical_dg_interleaved_interval_tree_with_word_powers
  refine ⟨Ctail, C, Kref, hCtail, hC, hKref, ?_⟩
  intro L q h hsupp h0 h1 mu nu gamma hgamma H hH hmu hnu hmunu hgap
    G rG g m w v ell D s a tau epsilon t Delta
  obtain ⟨hell, hD, hs, ha, haSmall, hepsilon, hepsilon1, ht, htail, htradeoff,
    B, hB, hlogB, Uref, hdimU, hUMPS, hxiMax, hwidth, T, N, F,
    hN, htargets, htrees⟩ :=
    hfactory L q h hsupp h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
  change 21 ≤ ell at hell
  refine ⟨hell, hD, hs, ha, haSmall, hepsilon, hepsilon1, ht, htail, htradeoff, ?_⟩
  intro u bref
  refine ⟨B, hB, hlogB, Uref, hdimU, hUMPS, ?_⟩
  intro Dref xiMax
  refine ⟨hxiMax, ?_⟩
  intro width
  have hq : 0 < q := lt_of_lt_of_le (by decide : 0 < 2)
    (hH.two_le_local_dimension_of_two_spectral_values hmu hnu (ne_of_lt hmunu))
  let : Nonempty (Fin L → Fin q) := ⟨fun _ ↦ ⟨0, hq⟩⟩
  obtain ⟨j, hj⟩ := hH.spectrum_real_eq_range_eigenvalues ▸ hmu
  have hminle : minEigenvalue hH ≤ mu := by
    simpa only [hj] using minEigenvalue_le hH j
  obtain ⟨i, hi⟩ := minEigenvalue_achieved hH
  have hmin : minEigenvalue hH = mu := by
    rcases hgap _ (hH.eigenvalues_mem_spectrum_real i) with heq | hle
    · exact hi.symm.trans heq
    · rw [hi] at hle
      linarith only [hminle, hle, hgamma]
  have hcount : 50 * ell ^ 2 ≤ D := by
    have hbase : 1 ≤ m * ell ^ 2 := by
      have hm : 50 ≤ m := Nat.le_max_right q 50
      have he : 1 ≤ ell ^ 2 := Nat.one_le_pow 2 ell (by omega)
      nlinarith only [hm, he]
    have hpow : m * ell ^ 2 ≤ D := le_self_pow hbase (by omega : 22 * ell ≠ 0)
    exact (Nat.mul_le_mul_right (ell ^ 2) (Nat.le_max_right q 50)).trans hpow
  refine ⟨hwidth, hq, T, N, F, hN, htargets, ?_⟩
  intro xi hxi hxiMax
  obtain ⟨operation, hspaces, hnodes⟩ := htrees xi hxi hxiMax
  refine ⟨operation, hspaces, hnodes, ?_⟩
  intro J k hpk hkr S1 S2
  have hlong : 4 * ell < J.val.2 - J.val.1 := J.property.2.2
  have hlu : J.val.1 ≤ J.val.1 + ell := by omega
  have huv : J.val.1 + ell ≤ J.val.2 - ell := by omega
  have hvr : J.val.2 - ell ≤ J.val.2 := Nat.sub_le _ _
  have hleft : J.val.1 + ell - J.val.1 ≤ 2 * ell := by omega
  have hright : J.val.2 - (J.val.2 - ell) ≤ 2 * ell := by omega
  obtain ⟨hdimT, _hTG, hGT, _hTU, _hUT, hwords⟩ := htargets J
  have hdimRaw : Module.finrank ℂ (T J) = Module.finrank ℂ
      (Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu) := hdimT
  have hdimCanonical : Module.finrank ℂ (T J) = Module.finrank ℂ
      (Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues (minEigenvalue hH)) :=
    Eq.mpr (congrArg (fun c ↦ Module.finrank ℂ (T J) = Module.finrank ℂ
      (Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues c)) hmin) hdimRaw
  have hGTRaw : Submodule.IsCloseTo tau
      (Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu) (T J) := hGT
  have hGTCanonical : Submodule.IsCloseTo tau
      (Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues (minEigenvalue hH))
      (T J) := Eq.mpr (congrArg (fun c ↦ Submodule.IsCloseTo tau
        (Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues c) (T J)) hmin) hGTRaw
  have hone (S : Submodule ℂ (EuclideanSpace ℂ
      (interval L J.val.1 J.val.2 → Fin q)))
      (hS : Submodule.IsViable (1 / 4 : ℝ) S ((T J).map
        (Entropy.regionTensorCoordinates q
          (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap)) :
      let grow := ⨆ word : Fin 1 → Fin (N J),
        S.map ((List.ofFn (fun j ↦ F J (word j))).prod : _ →ₗ[ℂ] _)
      Module.finrank ℂ grow ≤ D ^ 2 * Module.finrank ℂ S ∧
        Submodule.IsViable ((1 / (200000 * (D : ℝ) ^ 12)) / (1 - (1 / 4 : ℝ)) ^ 2)
          grow ((T J).map (Entropy.regionTensorCoordinates q
            (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap) := by
    simpa only [pow_one, Delta, div_div] using hwords 1 S (1 / 4) hS (by norm_num)
  have hS1Raw : Submodule.IsViable (3 / 200 : ℝ) S1
      ((Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu).map
        (Entropy.regionTensorCoordinates q (interval L J.val.1 k)).toLinearEquiv.toLinearMap) :=
    (hspaces J.val.1 k hpk (hkr.trans J.property.2.1)).1
  have hS2Raw : Submodule.IsViable (3 / 200 : ℝ) S2
      ((Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu).map
        (Entropy.regionTensorCoordinates q (interval L k J.val.2)).toLinearEquiv.toLinearMap) :=
    (hspaces k J.val.2 hkr J.property.2.1).1
  have hS1Canonical := Eq.mpr (congrArg (fun c ↦
    Submodule.IsViable (3 / 200 : ℝ) S1
    ((Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues c).map
      (Entropy.regionTensorCoordinates q (interval L J.val.1 k)).toLinearEquiv.toLinearMap)) hmin)
    hS1Raw
  have hS2Canonical := Eq.mpr (congrArg (fun c ↦
    Submodule.IsViable (3 / 200 : ℝ) S2
    ((Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues c).map
      (Entropy.regionTensorCoordinates q (interval L k J.val.2)).toLinearEquiv.toLinearMap)) hmin)
    hS2Raw
  exact ALVV.exists_soft_word_node_energy_update hq hlu huv hvr J.property.2.1
    hleft hright hell hD hcount hs h hsupp h0 h1 (T J) (F J)
    hdimCanonical hGTCanonical hone k hpk hkr S1 S2 hS1Canonical hS2Canonical

end TNLean.MPS.AreaLaw
