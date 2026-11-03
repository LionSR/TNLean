/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalDGInterleavedFamily
import TNLean.MPS.AreaLaw.IntervalFamilyTrimmingIteration
import QICLean.Analysis.InterleavedStoppingParameters

/-!
# Actual finite interleaved interval filtering and trimming

The original chain chooses its clipped target and actual family before every
input space. Every round acts on the preceding actual space and collectively
trims that image with the same radius and common reference. The calibrated
scalar envelope bounds all rounds and reaches error `1/200` for the clipped
target and `3/200` for the original full ground space. The recorded weighted
ranks refer to the actual last collective trim.

This supports ALVV, arXiv:1602.08828v2, Figure `fig:merge-prime`,
lines 1668–1670, and the degenerate-ground-space induction, lines 1797–1805.
The initial successful sample and recursive tree remain separate.

**Scope restriction (long intervals and capped gap):** The intervals have
length greater than `4 * ell`, with quantitative dependence on `min gamma 1`.
See `docs/paper-gaps/alvv16_approximation_parameters.tex`.

**Local fix (assignment and integer rounds):** Every successor acts on the
current space, and the larger upper integer logarithm reserves one final
exit round. The same note records the source assignment and rounding issues.
No adaptive probability or printed running time is asserted.

The family is polynomial in the actual hard-clipped Hamiltonian. Retaining its
word bounds does not identify it with the soft family in the printed Generate
procedure. This distinction is recorded in
`docs/paper-gaps/alvv16_approximation_parameters.tex`.
-/

open scoped TensorProduct ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- Actual interleaved image-and-trim iterates converge at a fully derived
integer count. The physical target, family and common reference precede
every radius and viable input. No numerical filter, reference, or stopping
condition is supplied. Supporting ALVV, arXiv:1602.08828v2,
Figure `fig:merge-prime`, lines 1668–1670, and lines 1797–1805.
The ordered-word bounds retain these same chosen operators and target,
including the separate energy candidate of Figure `fig:algo1`, line 1631.
-/
theorem exists_physical_dg_interleaved_interval_iterates_with_word_powers :
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
    0 < xiMax ∧ ∀ (p endR : ℕ), p ≤ endR → endR ≤ L → 4 * ell < endR - p →
      ∃ (T : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) (N : ℕ)
        (F : Fin N → EuclideanSpace ℂ (interval L p endR → Fin q) →L[ℂ]
          EuclideanSpace ℂ (interval L p endR → Fin q)),
        N ≤ D ^ 2 ∧ Module.finrank ℂ T = rG ∧
        Submodule.IsCloseTo tau T G ∧ Submodule.IsCloseTo tau G T ∧
        Submodule.IsCloseTo (4 * tau) T U ∧ Submodule.IsCloseTo (4 * tau) U T ∧
        (∀ (power : ℕ)
          (S : Submodule ℂ (EuclideanSpace ℂ (interval L p endR → Fin q))) (delta : ℝ),
          Submodule.IsViable delta S
            (T.map (Entropy.regionTensorCoordinates q
              (interval L p endR)).toLinearEquiv.toLinearMap) → delta < 1 →
          let grow := ⨆ w : Fin power → Fin N,
            S.map ((List.ofFn (fun j ↦ F (w j))).prod : _ →ₗ[ℂ] _)
          Module.finrank ℂ grow ≤ (D ^ 2) ^ power * Module.finrank ℂ S ∧
            Submodule.IsViable (Delta ^ power / (1 - delta) ^ 2) grow
              (T.map (Entropy.regionTensorCoordinates q
                (interval L p endR)).toLinearEquiv.toLinearMap)) ∧
        ∀ xi : ℝ, 0 < xi → xi ≤ xiMax →
        ∀ S0 : Submodule ℂ (EuclideanSpace ℂ (interval L p endR → Fin q)),
        Module.finrank ℂ S0 ≤ s →
        Submodule.IsViable (1 - a) S0
          (T.map (Entropy.regionTensorCoordinates q
            (interval L p endR)).toLinearEquiv.toLinearMap) →
        let power := Nat.clog D (D ^ 2 * s)
        let err : ℕ → ℝ := fun j ↦
          ((fun z : ℝ ↦ Delta * z / (1 - z + Delta * z) + a / 16)^[j]) (1 - a)
        let output := intervalFamilyTrimIterate L q p endR F xi S0 power
        (∀ j, 0 ≤ err j ∧ err j < 1 ∧
          Submodule.IsViable (err j) (intervalFamilyTrimIterate L q p endR F xi S0 j)
            (T.map (Entropy.regionTensorCoordinates q
              (interval L p endR)).toLinearEquiv.toLinearMap)) ∧
        Module.finrank ℂ output ≤ D ^ 6 * s ^ 3 ∧
        IsIntervalSpanWithRankBound L q p endR (D ^ 6 * s ^ 3) xi output ∧
        Submodule.IsViable (1 / 200 : ℝ) output
          (T.map (Entropy.regionTensorCoordinates q
            (interval L p endR)).toLinearEquiv.toLinearMap) ∧
        Submodule.IsViable (3 / 200 : ℝ) output
          (G.map (Entropy.regionTensorCoordinates q
            (interval L p endR)).toLinearEquiv.toLinearMap) := by
  classical
  obtain ⟨Ctail, C, Kref, hCtail, hC, hKref, hfamily⟩ :=
    exists_physical_dg_interleaved_filter_family_with_word_powers
  refine ⟨Ctail, C, Kref, hCtail, hC, hKref, ?_⟩
  intro L q h hsupp h0 h1 mu nu gamma hgamma H hH hmu hnu hmunu hgap
    G rG g m w v ell D s a tau epsilon t Delta
  obtain ⟨hell, hD, hs, ha, haSmall, hepsilon, hepsilon1, ht, htail, htradeoff,
    B, hB, hlogB, U, hdimU, hUMPS, hxiMax, hinterval⟩ :=
    hfamily L q h hsupp h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
  change 2 ≤ D at hD
  change 1 ≤ s at hs
  refine ⟨hell, hD, hs, ha, haSmall, hepsilon, hepsilon1, ht, htail, htradeoff, ?_⟩
  intro u bref
  refine ⟨B, hB, hlogB, U, hdimU, hUMPS, ?_⟩
  intro Dref xiMax
  refine ⟨hxiMax, ?_⟩
  intro p endR hpr hrL hlong
  obtain ⟨T, N, F, hN, hdimT, hTG, hGT, hTU, hUT, hwords, hstep⟩ := hinterval p endR hpr hrL hlong
  clear hfamily hinterval
  refine ⟨T, N, F, hN, hdimT, hTG, hGT, hTU, hUT, hwords, ?_⟩
  intro xi hxi hxiMax S0 hSdim hS0 power err output
  have herr0 : err 0 = 1 - a := rfl
  have herrStep (j : ℕ) :
      err (j + 1) = Delta * err j / (1 - err j + Delta * err j) + a / 16 := by
    exact Function.iterate_succ_apply' _ j (1 - a)
  obtain ⟨herrRange, herrFinal⟩ := Real.interleaved_trim_power_sequence_stops
    D s hD hs err herr0 herrStep
  have hviable (j : ℕ) :
      Submodule.IsViable (err j) (intervalFamilyTrimIterate L q p endR F xi S0 j)
        (T.map (Entropy.regionTensorCoordinates q
          (interval L p endR)).toLinearEquiv.toLinearMap) := by
    induction j with
    | zero => exact hS0
    | succ j ih =>
      have hv := (hstep xi hxi hxiMax (err j) (herrRange j).1 (herrRange j).2 _ ih).2.2.1
      rw [← herrStep j] at hv
      exact hv
  have hcount : N ^ power * Module.finrank ℂ S0 ≤ D ^ 6 * s ^ 3 := by
    calc
      _ ≤ (D ^ 2) ^ power * s := Nat.mul_le_mul (Nat.pow_le_pow_left hN power) hSdim
      _ = (D ^ power) ^ 2 * s := congrArg (fun x : ℕ ↦ x * s) (pow_right_comm D 2 power)
      _ ≤ _ := (Nat.viable_node_power_bounds hD hs).2.2.2
  have hpower2 : 2 ≤ power := (Nat.viable_node_power_bounds hD hs).1
  have hpower : 1 ≤ power := by omega
  have hpk : power - 1 + 1 = power := Nat.sub_add_cancel hpower
  have hranks := isIntervalSpanWithRankBound_intervalFamilyTrimIterate_succ hxi F S0 (power - 1)
  rw [hpk] at hranks
  obtain ⟨n, hn, vectors, hspan, hrank⟩ := hranks
  have hrecorded : IsIntervalSpanWithRankBound L q p endR (D ^ 6 * s ^ 3) xi output := by
    refine ⟨n, hn.trans hcount, vectors, hspan, ?_⟩
    intro j hj i
    exact (hrank j hj i).trans (by exact_mod_cast hcount)
  have htarget : Submodule.IsViable (1 / 200 : ℝ) output
      (T.map (Entropy.regionTensorCoordinates q
        (interval L p endR)).toLinearEquiv.toLinearMap) := (hviable power).of_le herrFinal
  have hTGmap : Submodule.IsCloseTo tau
      (T.map (Entropy.regionTensorCoordinates q (interval L p endR)).toLinearEquiv.toLinearMap)
      (G.map (Entropy.regionTensorCoordinates q (interval L p endR)).toLinearEquiv.toLinearMap) :=
    (Submodule.isCloseTo_map_iff (Entropy.regionTensorCoordinates q
      (interval L p endR))).mpr hTG
  have hGtarget : Submodule.IsViable (2 * ((1 / 200 : ℝ) + tau)) output
      (G.map (Entropy.regionTensorCoordinates q (interval L p endR)).toLinearEquiv.toLinearMap) :=
    Submodule.IsCloseTo.trans htarget hTGmap (by norm_num)
  have htau : tau ≤ 1 / 10000 := by
    have haSq : a ^ 2 ≤ 1 / 10000 := by nlinarith only [ha, haSmall]
    dsimp only [tau]
    linarith only [haSq]
  refine ⟨fun j ↦ ⟨(herrRange j).1, (herrRange j).2, hviable j⟩,
    (finrank_intervalFamilyTrimIterate_le F xi S0 power).trans hcount,
    hrecorded, htarget, hGtarget.of_le ?_⟩
  linarith only [htau]

/-- The original conclusion follows by forgetting the additional ordered-word
bounds of the same physical family. Supporting ALVV, arXiv:1602.08828v2,
Figure `fig:merge-prime`, lines 1668–1670; the separate energy candidate uses
this same family as in Figure `fig:algo1`, line 1631. -/
theorem exists_physical_dg_interleaved_interval_iterates :
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
    0 < xiMax ∧ ∀ (p endR : ℕ), p ≤ endR → endR ≤ L → 4 * ell < endR - p →
      ∃ (T : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) (N : ℕ)
        (F : Fin N → EuclideanSpace ℂ (interval L p endR → Fin q) →L[ℂ]
          EuclideanSpace ℂ (interval L p endR → Fin q)),
        N ≤ D ^ 2 ∧ Module.finrank ℂ T = rG ∧
        Submodule.IsCloseTo tau T G ∧ Submodule.IsCloseTo tau G T ∧
        Submodule.IsCloseTo (4 * tau) T U ∧ Submodule.IsCloseTo (4 * tau) U T ∧
        ∀ xi : ℝ, 0 < xi → xi ≤ xiMax →
        ∀ S0 : Submodule ℂ (EuclideanSpace ℂ (interval L p endR → Fin q)),
        Module.finrank ℂ S0 ≤ s →
        Submodule.IsViable (1 - a) S0
          (T.map (Entropy.regionTensorCoordinates q
            (interval L p endR)).toLinearEquiv.toLinearMap) →
        let power := Nat.clog D (D ^ 2 * s)
        let err : ℕ → ℝ := fun j ↦
          ((fun z : ℝ ↦ Delta * z / (1 - z + Delta * z) + a / 16)^[j]) (1 - a)
        let output := intervalFamilyTrimIterate L q p endR F xi S0 power
        (∀ j, 0 ≤ err j ∧ err j < 1 ∧
          Submodule.IsViable (err j) (intervalFamilyTrimIterate L q p endR F xi S0 j)
            (T.map (Entropy.regionTensorCoordinates q
              (interval L p endR)).toLinearEquiv.toLinearMap)) ∧
        Module.finrank ℂ output ≤ D ^ 6 * s ^ 3 ∧
        IsIntervalSpanWithRankBound L q p endR (D ^ 6 * s ^ 3) xi output ∧
        Submodule.IsViable (1 / 200 : ℝ) output
          (T.map (Entropy.regionTensorCoordinates q
            (interval L p endR)).toLinearEquiv.toLinearMap) ∧
        Submodule.IsViable (3 / 200 : ℝ) output
          (G.map (Entropy.regionTensorCoordinates q
            (interval L p endR)).toLinearEquiv.toLinearMap) := by
  classical
  obtain ⟨Ctail, C, Kref, hCtail, hC, hKref, hfamily⟩ :=
    exists_physical_dg_interleaved_interval_iterates_with_word_powers
  refine ⟨Ctail, C, Kref, hCtail, hC, hKref, ?_⟩
  intro L q h hsupp h0 h1 mu nu gamma hgamma H hH hmu hnu hmunu hgap
    G rG g m w v ell D s a tau epsilon t Delta
  obtain ⟨hell, hD, hs, ha, haSmall, hepsilon, hepsilon1, ht, htail, htradeoff,
    B, hB, hlogB, U, hdimU, hUMPS, hxiMax, hinterval⟩ :=
    hfamily L q h hsupp h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
  refine ⟨hell, hD, hs, ha, haSmall, hepsilon, hepsilon1, ht, htail, htradeoff, ?_⟩
  intro u bref
  refine ⟨B, hB, hlogB, U, hdimU, hUMPS, ?_⟩
  intro Dref xiMax
  refine ⟨hxiMax, ?_⟩
  intro p endR hpr hrL hlong
  obtain ⟨T, N, F, hN, hdimT, hTG, hGT, hTU, hUT, _hwords, hconclusion⟩ :=
    hinterval p endR hpr hrL hlong
  exact ⟨T, N, F, hN, hdimT, hTG, hGT, hTU, hUT, hconclusion⟩

end TNLean.MPS.AreaLaw
