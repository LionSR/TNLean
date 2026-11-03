/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalDGInterleavedIteration
import TNLean.MPS.AreaLaw.AdjacentIntervalMerge
import QICLean.Analysis.ViableSubspaceSamplingEvent
import QICLean.Analysis.ViableNodeSamplingParameters

/-!
# One actual sampled and interleaved physical parent

For each fixed pair of child spaces, a measurable Haar event certifies the
actual sample followed by successive family applications and collective trims.
The physical family and common reference precede the children, their merged
dimension, the retained sample dimension and the Haar unitary. The nominal
sample bound is fixed by the chain and the failure target `(L+1)^(-2)`.

This supports ALVV, arXiv:1602.08828v2, `l:rs`, lines 530–558,
Figure `fig:merge-prime`, lines 1668–1670, and lines 1797–1805.
No jointly measurable adaptive tree or running-time claim is made.

**Scope restriction (long intervals and capped gap):** The intervals have
length greater than `4 * ell`, with quantitative dependence on `min gamma 1`.
See `docs/paper-gaps/alvv16_approximation_parameters.tex`.

**Local fix (assignment and integer rounds):** Each round acts on its current
space, with the larger integer stopping count documented in the same note.

**Local fix (complex sphere net count):** The fixed-input failure event uses
the corrected net radius and exponent described at
https://sirui-lu.com/QICLean/paper-gaps/alvv16_random_sampling_net_count.pdf.

The family is polynomial in the actual hard-clipped Hamiltonian. Retaining its
word bounds does not identify it with the soft family in the printed Generate
procedure. This distinction is recorded in
`docs/paper-gaps/alvv16_approximation_parameters.tex`.
-/

open scoped TensorProduct ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory

namespace TNLean.MPS.AreaLaw

/-- The actual Haar sample followed by literal interleaved family images
and collective trims. Supporting ALVV, arXiv:1602.08828v2,
Figure `fig:merge-prime`, lines 1668–1670. -/
noncomputable def sampledIntervalInterleavedTrim (L q p r D s : ℕ) {N : ℕ}
    (F : Fin N → EuclideanSpace ℂ (interval L p r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L p r → Fin q)) (xi : ℝ)
    (W : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)))
    (U : Matrix.unitaryGroup (Fin (Module.finrank ℂ W)) ℂ) :
    Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)) :=
  let A := Finset.univ.map (Fin.castLEEmb (Nat.min_le_right s (Module.finrank ℂ W)))
  let sample := Submodule.randomSubspace (stdOrthonormalBasis ℂ W) A U
  intervalFamilyTrimIterate L q p r F xi sample (Nat.clog D (D ^ 2 * s))

/-- For each fixed pair of viable children, the actual physical sample and
interleaved output satisfy the fixed failure bound. All physical scales,
targets, families and the common reference are constructed before the
children and unitary; no sampling or stopping hypothesis is supplied.
Supporting ALVV, arXiv:1602.08828v2, `l:rs`, lines 530–558,
Figure `fig:merge-prime`, lines 1668–1670, and lines 1797–1805.
The ordered-word bounds retain these same chosen operators and target,
including the separate energy candidate of Figure `fig:algo1`, line 1631.
-/
theorem exists_physical_dg_interleaved_interval_node_event_with_word_powers :
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
        ∀ (k : ℕ) (hpk : p ≤ k) (hkr : k ≤ endR),
        ∀ (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L p k → Fin q)))
          (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k endR → Fin q))),
        Submodule.IsViable (3 / 200 : ℝ) S1
          (G.map (Entropy.regionTensorCoordinates q (interval L p k)).toLinearEquiv.toLinearMap) →
        Submodule.IsViable (3 / 200 : ℝ) S2
          (G.map (Entropy.regionTensorCoordinates q
            (interval L k endR)).toLinearEquiv.toLinearMap) →
        Module.finrank ℂ S1 ≤ D ^ 6 * s ^ 3 →
        Module.finrank ℂ S2 ≤ D ^ 6 * s ^ 3 →
        let W := adjacentIntervalMerge L q p k endR hpk hkr S1 S2
        let Q := Module.finrank ℂ W
        let beta : ℝ := 1 / ((L : ℝ) + 1) ^ 2
        ∃ Good : Set (Matrix.unitaryGroup (Fin Q) ℂ),
          MeasurableSet Good ∧ Good.Nonempty ∧
          Matrix.unitaryHaar (Fin Q) Goodᶜ ≤ ENNReal.ofReal beta ∧
          1 - ENNReal.ofReal beta ≤ Matrix.unitaryHaar (Fin Q) Good ∧
          ∀ U ∈ Good,
            let output := sampledIntervalInterleavedTrim L q p endR D s F xi W U
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
    B, hB, hlogB, Uref, hdimU, hUMPS, hxiMax, hinterval⟩ :=
    hfamily L q h hsupp h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
  change 2 ≤ D at hD
  change 1 ≤ s at hs
  refine ⟨hell, hD, hs, ha, haSmall, hepsilon, hepsilon1, ht, htail, htradeoff, ?_⟩
  intro u bref
  refine ⟨B, hB, hlogB, Uref, hdimU, hUMPS, ?_⟩
  intro Dref xiMax
  refine ⟨hxiMax, ?_⟩
  intro p endR hpr hrL hlong
  obtain ⟨T, N, F, hN, hdimT, hTG, hGT, hTU, hUT, hwords, hiterate⟩ :=
    hinterval p endR hpr hrL hlong
  clear hfamily hinterval
  refine ⟨T, N, F, hN, hdimT, hTG, hGT, hTU, hUT, hwords, ?_⟩
  intro xi hxi hxiMax k hpk hkr S1 S2 hS1 hS2 hd1 hd2 W Q beta
  let coords := Entropy.regionTensorCoordinates q (interval L p endR)
  have hG : G ≠ ⊥ := hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl
  have hrG : 1 ≤ rG := Submodule.one_le_finrank_iff.mpr hG
  have hmerged := isViable_adjacentIntervalMerge hpk hkr G S1 S2 hS1 hS2
  have hGmap : G.map coords.toLinearEquiv.toLinearMap ≠ ⊥ :=
    (Submodule.map_ne_bot_iff (e := coords.toLinearEquiv)).mpr hG
  have hW : W ≠ ⊥ :=
    Submodule.isViable_ne_bot_of_target_ne_bot hmerged (by norm_num) hGmap
  have hQ0 : 0 < Q := Nat.zero_lt_of_lt (Submodule.one_le_finrank_iff.mpr hW)
  have hQ : Q ≤ D ^ 12 * s ^ 6 := by
    calc
      _ ≤ Module.finrank ℂ S1 * Module.finrank ℂ S2 :=
        finrank_adjacentIntervalMerge_le hpk hkr S1 S2
      _ ≤ (D ^ 6 * s ^ 3) * (D ^ 6 * s ^ 3) := Nat.mul_le_mul hd1 hd2
      _ = _ := by ring
  have htau : tau ≤ 1 / 10000 := by
    have haSq : a ^ 2 ≤ 1 / 10000 := by nlinarith only [ha, haSmall]
    dsimp only [tau]
    linarith only [haSq]
  have hGTmap : Submodule.IsCloseTo tau
      (G.map coords.toLinearEquiv.toLinearMap) (T.map coords.toLinearEquiv.toLinearMap) :=
    (Submodule.isCloseTo_map_iff coords).mpr hGT
  have hWT : Submodule.IsViable (1 / 4 : ℝ) W (T.map coords.toLinearEquiv.toLinearMap) := by
    apply (Submodule.IsCloseTo.trans hmerged hGTmap (by norm_num)).of_le
    linarith only [htau]
  obtain ⟨Good, hGood, hbad, hprob, hsample⟩ :=
    Submodule.exists_measurable_randomSubspace_min_event (stdOrthonormalBasis ℂ W) s
      hWT (by norm_num)
  have hdimTc : Module.finrank ℂ (T.map coords.toLinearEquiv.toLinearMap) = rG := by
    rw [LinearEquiv.finrank_map_eq]
    exact hdimT
  rw [hdimTc] at hbad hprob
  have hL : 1 ≤ (L : ℝ) + 1 := by
    have h : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    linarith only [h]
  have hbeta : 0 < beta := by dsimp only [beta]; positivity
  have hbeta1 : beta ≤ 1 := by
    dsimp only [beta]
    exact (div_le_one (by positivity)).mpr (one_le_pow₀ hL)
  have hlogbeta : Real.log (1 / beta) = 2 * Real.log ((L : ℝ) + 1) := by
    dsimp only [beta]
    rw [one_div_div, div_one, Real.log_pow]
    norm_num
  have hscale : 1 + Real.log (rG : ℝ) + Real.log (D : ℝ) + Real.log (1 / beta) =
      Real.log (D : ℝ) + w := by
    rw [hlogbeta]
    dsimp only [w]
    ring
  have hsampling := Real.viable_node_uniform_sampling_size hD hrG hbeta hbeta1
  rw [hscale] at hsampling
  obtain ⟨_hs, _hsUpper, hexpBeta, hfailure⟩ := hsampling
  have hfail := (hfailure Q hQ).trans hexpBeta
  have hprobBeta := (tsub_le_tsub_left (ENNReal.ofReal_le_ofReal hfail) 1).trans hprob
  have hLNat : 1 ≤ L := by omega
  have hLgt : (1 : ℝ) < (L : ℝ) + 1 := by
    have h : (1 : ℝ) ≤ L := by exact_mod_cast hLNat
    linarith only [h]
  have hbetaStrict : beta < 1 := by
    dsimp only [beta]
    apply (div_lt_one (by positivity)).mpr
    nlinarith only [hLgt]
  have hbetaENN : ENNReal.ofReal beta < 1 := by
    simpa only [ENNReal.ofReal_one] using
      (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).mpr hbetaStrict
  have hnonempty : Good.Nonempty := nonempty_of_measure_ne_zero
    (ne_of_gt (lt_of_lt_of_le (tsub_pos_iff_lt.mpr hbetaENN) hprobBeta))
  refine ⟨Good, hGood, hnonempty, hbad.trans (ENNReal.ofReal_le_ofReal hfail), hprobBeta, ?_⟩
  intro U hU output
  let A := Finset.univ.map (Fin.castLEEmb (Nat.min_le_right s Q))
  let sample := Submodule.randomSubspace (stdOrthonormalBasis ℂ W) A U
  have hsampleDim : Module.finrank ℂ sample ≤ s := by
    rw [Submodule.finrank_randomSubspace]
    simp only [A, Finset.card_map, Finset.card_univ, Fintype.card_fin]
    exact Nat.min_le_left s Q
  have hoverlap : a ≤ (1 - (1 / 4 : ℝ)) * (min s Q : ℕ) / (8 * Q) := by
    simpa only [a, mul_assoc] using
      Real.viable_node_sample_overlap_lower hD hs hQ0 hQ (delta := (1 / 4 : ℝ)) le_rfl
  have hsampleViable : Submodule.IsViable (1 - a) sample
      (T.map coords.toLinearEquiv.toLinearMap) :=
    (hsample U hU).of_le (by linarith only [hoverlap])
  exact (hiterate xi hxi hxiMax sample hsampleDim hsampleViable).2

/-- The original conclusion follows by forgetting the additional ordered-word
bounds of the same physical family. Supporting ALVV, arXiv:1602.08828v2,
Figure `fig:merge-prime`, lines 1668–1670; the separate energy candidate uses
this same family as in Figure `fig:algo1`, line 1631. -/
theorem exists_physical_dg_interleaved_interval_node_event :
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
        ∀ (k : ℕ) (hpk : p ≤ k) (hkr : k ≤ endR),
        ∀ (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L p k → Fin q)))
          (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k endR → Fin q))),
        Submodule.IsViable (3 / 200 : ℝ) S1
          (G.map (Entropy.regionTensorCoordinates q (interval L p k)).toLinearEquiv.toLinearMap) →
        Submodule.IsViable (3 / 200 : ℝ) S2
          (G.map (Entropy.regionTensorCoordinates q
            (interval L k endR)).toLinearEquiv.toLinearMap) →
        Module.finrank ℂ S1 ≤ D ^ 6 * s ^ 3 →
        Module.finrank ℂ S2 ≤ D ^ 6 * s ^ 3 →
        let W := adjacentIntervalMerge L q p k endR hpk hkr S1 S2
        let Q := Module.finrank ℂ W
        let beta : ℝ := 1 / ((L : ℝ) + 1) ^ 2
        ∃ Good : Set (Matrix.unitaryGroup (Fin Q) ℂ),
          MeasurableSet Good ∧ Good.Nonempty ∧
          Matrix.unitaryHaar (Fin Q) Goodᶜ ≤ ENNReal.ofReal beta ∧
          1 - ENNReal.ofReal beta ≤ Matrix.unitaryHaar (Fin Q) Good ∧
          ∀ U ∈ Good,
            let output := sampledIntervalInterleavedTrim L q p endR D s F xi W U
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
    exists_physical_dg_interleaved_interval_node_event_with_word_powers
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
