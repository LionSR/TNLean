/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalDGCanonicalJointProbability
import TNLean.MPS.AreaLaw.PhysicalDGAutomaticRefinement
import QICLean.Analysis.Parameter.InterleavedOutputPolynomialBound

/-!
# Ritz and MPS output from the same successful canonical root

One physical family is chosen before the accuracy and all random seeds.
A common threshold is then selected for the canonical tree and its literal
final filter-and-trim refinement. Every successful seed uses its own
actual root unchanged. Its terminal Ritz space has the prescribed dimension
and two-sided closeness, with one polynomial MPS bond for its entire span.
The same bound holds for every vector in the initial native root.

Source: ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, lines 1777–1817.
**Scope restriction (coarse polynomial bound and physical construction):**
The block leaves, fixed failure scale, hard-clipped families, capped gap,
and larger integer parent count are retained. See
`docs/paper-gaps/alvv16_approximation_parameters.tex`.
**Local fix (normalized final gain):** Final refinement uses the corrected
raw-filter gain and accuracy-dependent count documented in
`docs/paper-gaps/alvv16_final_filter_gain.tex`. No measurable Ritz-basis
selection or running time is asserted.
-/

open ManyBody (interval)

open MeasureTheory
open scoped ENNReal InnerProductSpace TensorProduct ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- The same successful canonical root is refined literally and its actual
compressed Ritz space has a uniform polynomial all-span MPS bound. The
physical family precedes accuracy and seeds; the polynomial coefficient
and natural degree precede length, multiplicity, accuracy and seeds.
Supporting ALVV, arXiv:1602.08828v2, `t:alg1`, lines 1777–1817,
within the stated physical and quantitative scope. -/
theorem exists_physical_dg_canonical_ritz_polynomial_approximation :
    ∃ Ctail Cscale Ktree Kfinal : ℝ,
    21 ≤ Ctail ∧ 21 ≤ Cscale ∧ 0 < Ktree ∧ 0 < Kfinal ∧
    ∀ (q : ℕ) (gamma : ℝ), 0 < gamma →
    ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ,
    ∀ (L : ℕ),
    ∀ (Φ : ManyBody.BondInteraction L q)
      (h0 : ∀ i, 0 ≤ Φ.term i) (_h1 : ∀ i, Φ.term i ≤ 1) (mu nu : ℝ),
    let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Φ.hamiltonian
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
    let ell := Nat.ceil (Cscale * (v ^ 6 / g + Real.sqrt w * v ^ 3 / Real.sqrt g))
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
    ∃ Btree : ℕ, 1 ≤ Btree ∧
      Real.log (Btree : ℝ) ≤
        Ktree * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * bref ^ (3 / 4 : ℝ) * u) *
          (1 + Real.log bref) ∧
    ∃ Utree : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)),
      Module.finrank ℂ Utree = rG ∧
      (∀ z ∈ Utree, IsOpenMPS L q (rG ^ 2 * Btree) (fun x ↦ z x)) ∧
    let Dref := rG ^ 2 * Btree
    let xiMax := a / (256 * (Dref : ℝ) * Real.sqrt ((L : ℝ) + 1))
    0 < xiMax ∧
    let width := 4 * ell
    ∃ hwidth : 1 ≤ width,
    ∃ (T : LongIntervalIndex L width →
        Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
      (N : LongIntervalIndex L width → ℕ)
      (F : ∀ J : LongIntervalIndex L width,
        Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
          EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)),
      (∀ J, N J ≤ D ^ 2) ∧
      (∀ J, Module.finrank ℂ (T J) = rG ∧
        Submodule.IsCloseTo tau (T J) G ∧ Submodule.IsCloseTo tau G (T J) ∧
        Submodule.IsCloseTo (4 * tau) (T J) Utree ∧
        Submodule.IsCloseTo (4 * tau) Utree (T J) ∧
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
      let Dtree := Dref * Nat.ceil (1 / a)
      let A := ‖H‖ - mu
      let c := gamma / A
      let Kraw := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) (1 - ‖H‖⁻¹ • H)
      ∀ eta : ℝ, 0 < eta →
      let rho := eta * gamma / (2 * A + eta * gamma)
      let n := Nat.ceil (4 / c * Real.log (1 / rho)) + 1
      let epsilonFinal := c ^ 2 * rho / 32768
      let bfinal := 16 + Real.log (1 / g) +
        Real.log (32 * (rG : ℝ) * ((L : ℝ) + 1) / epsilonFinal)
      ∃ Bfinal : ℕ, 1 ≤ Bfinal ∧
        Real.log (Bfinal : ℝ) ≤
          Kfinal * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * bfinal ^ (3 / 4 : ℝ) * u) *
            (1 + Real.log bfinal) ∧
      let b := rG ^ 2 * Bfinal
      let Dcommon := max Dtree b
      let Nfinal := Nat.ceil (100 * (D : ℝ) ^ 12 / (c * rho))
      let xi := 1 / (1000 * ((Dcommon * Nfinal : ℕ) : ℝ) * Real.sqrt ((L : ℝ) + 1))
      ∃ Ufinal : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)),
        Module.finrank ℂ Ufinal = rG ∧
        Submodule.IsCloseTo epsilonFinal Ufinal G ∧ Submodule.IsCloseTo epsilonFinal G Ufinal ∧
        (∀ z ∈ Ufinal, IsOpenMPS L q b (fun x ↦ z x)) ∧
        0 < xi ∧ xi ≤ xiMax ∧
        Real.sqrt ((L : ℝ) * (rG : ℝ) * (b : ℝ)) * xi <
          eta / (10000 * (D : ℝ) ^ 12) ∧
      (∀ (seed : IntervalSamplingChoices L q) (p r : ℕ), p ≤ r → r ≤ L →
        let S := balancedIntervalSpace (canonicalIntervalSamplingOperation D s N F xi seed)
          width hwidth p r
        Module.finrank ℂ S ≤ D ^ 6 * s ^ 3 ∧
          IsIntervalSpanWithRankBound L q p r (D ^ 6 * s ^ 3) xi S) ∧
      let Good := canonicalIntervalSamplingTreeGood D s hwidth N F xi G (3 / 200 : ℝ) 0 L
      let failureBound : ℝ≥0∞ := ((L - 1 : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (1 / ((L : ℝ) + 1) ^ 2)
      MeasurableSet Good ∧ intervalSamplingMeasure L q Goodᶜ ≤ failureBound ∧
        1 - failureBound ≤ intervalSamplingMeasure L q Good ∧
      let Bout : ℕ := 1000000 * (Dcommon * Nfinal) ^ 2 * (L + 1) * (D ^ 6 * s ^ 3) ^ 2
      (Bout : ℝ) ≤ C * (((L : ℝ) + 1) * ((rG : ℝ) + 1) * (1 + 1 / eta)) ^ k ∧
      ∀ seed ∈ Good,
        let S0 := balancedIntervalSpace (canonicalIntervalSamplingOperation D s N F xi seed)
          width hwidth 0 L
        let W0 := nativeFullIntervalSpace L q S0
        Submodule.IsCloseTo (3 / 200 : ℝ) W0 G ∧
          (∀ z ∈ W0, IsOpenMPS L q Bout (fun x ↦ z x)) ∧
        let S := fullIntervalFilterTrimIterate L q Kraw xi S0 n
        let W := nativeFullIntervalSpace L q S
        let R := W.ritzSubspace (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH) rG
        0 < n ∧ Submodule.IsCloseTo rho W G ∧ Module.finrank ℂ S ≤ D ^ 6 * s ^ 3 ∧
          R ≤ W ∧ Module.finrank ℂ R = rG ∧
          Submodule.IsCloseTo (eta / 2) G R ∧ Submodule.IsCloseTo (eta / 2) R G ∧
          ∀ z ∈ R, IsOpenMPS L q Bout (fun x ↦ z x) := by
  classical
  refine exists_physical_dg_canonical_tree_joint_probability.elim fun Ctail hspec ↦
    hspec.elim fun Cscale hspec ↦ hspec.elim fun Ktree hspec ↦ hspec.elim fun hCtail hspec ↦
    hspec.elim fun hCscale hspec ↦ hspec.elim fun hKtree hspec ↦ ?_
  have hfactory := hspec
  refine exists_physical_dg_automatic_same_candidate_refinement.elim fun Kfinal hspec ↦
    hspec.elim fun hKfinal hspec ↦ ?_
  have hauto := hspec
  refine ⟨Ctail, Cscale, Ktree, Kfinal, hCtail, hCscale, hKtree, hKfinal, ?_⟩
  intro q gamma hgamma
  let g := min gamma 1
  let m := max q 50
  let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
  let U0 := 1 + Real.log (m : ℝ) + Real.log (1 / g)
  let Alog := 22 * (Cscale + 1) * (14 + 2 * Real.log (Cscale + 1))
  let KD := Alog * ((U0 + 17) ^ 7 / g + (U0 + 17) ^ 4 / Real.sqrt g)
  have hg : 0 < g := lt_min hgamma (by norm_num)
  have hg1 : g ≤ 1 := min_le_right gamma 1
  have hgInv : 1 ≤ 1 / g := (le_div_iff₀ hg).mpr (by simpa using hg1)
  have hu : 0 ≤ u := by
    dsimp only [u]
    linarith [Real.log_natCast_nonneg q, Real.log_nonneg hgInv]
  have hU0 : 1 ≤ U0 := by
    dsimp only [U0]
    linarith [Real.log_natCast_nonneg m, Real.log_nonneg hgInv]
  have hlogCscale : 0 ≤ Real.log (Cscale + 1) :=
    Real.log_nonneg (by linarith only [hCscale])
  have hAlog : 0 ≤ Alog := by dsimp only [Alog]; positivity
  have hU17 : 0 ≤ U0 + 17 := by linarith only [hU0]
  have hKD : 0 ≤ KD := by dsimp only [KD]; positivity
  have :=
    Real.exists_interleaved_output_polynomial_bound_with_constants
      gamma g u Ktree Kfinal KD hgamma hg hg1 hu hKtree.le hKfinal.le hKD
  refine this.elim fun C hspec ↦ hspec.elim fun hC hspec ↦ hspec.elim fun _hlogC hspec ↦
    hspec.elim fun k hspec ↦ hspec.elim fun _hk hspec ↦ ?_
  have hpoly := hspec
  refine ⟨C, hC, k, ?_⟩
  intro L Φ h0 h1 mu nu H hH hmu hnu hmunu hgap G rG
    g0 m0 w v ell D s a tau epsilon t Delta
  have hfactoryL := hfactory L q Φ h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
  refine hfactoryL.elim fun hell hspec ↦ hspec.elim fun hD2 hspec ↦ hspec.elim fun hs hspec ↦
    hspec.elim fun ha hspec ↦ hspec.elim fun haSmall hspec ↦ hspec.elim fun hepsilon hspec ↦
    hspec.elim fun hepsilon1 hspec ↦ hspec.elim fun ht hspec ↦ hspec.elim fun htail hspec ↦
    hspec.elim fun htradeoff hspec ↦ hspec.elim fun Btree hspec ↦ hspec.elim fun hBtree hspec ↦
    hspec.elim fun hlogBtree hspec ↦ hspec.elim fun Utree hspec ↦ hspec.elim fun hdimUtree hspec ↦
    hspec.elim fun hUtreeMPS hspec ↦ hspec.elim fun hxiMax hspec ↦ hspec.elim fun hwidth hspec ↦
    hspec.elim fun T hspec ↦ hspec.elim fun N hspec ↦ hspec.elim fun F hspec ↦
    hspec.elim fun hN hspec ↦ hspec.elim fun htargets hspec ↦ ?_
  have hxiFamily := hspec
  refine ⟨hell, hD2, hs, ha, haSmall, hepsilon, hepsilon1, ht, htail, htradeoff, ?_⟩
  intro u0 bref
  refine ⟨Btree, hBtree, hlogBtree, Utree, hdimUtree, hUtreeMPS, ?_⟩
  intro Dref xiMax
  refine ⟨hxiMax, ?_⟩
  intro width
  refine ⟨hwidth, T, N, F, hN, htargets, ?_⟩
  intro Dtree A c Kraw eta heta rho n epsilonFinal bfinal
  have hrG : 1 ≤ rG := Submodule.one_le_finrank_iff.mpr
    (hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl)
  have hDref : 1 ≤ Dref := by
    simpa only [Dref, one_mul] using Nat.mul_le_mul (Nat.one_le_pow 2 rG hrG) hBtree
  have hNtree : 1 ≤ Nat.ceil (1 / a) := Nat.one_le_ceil_iff.mpr (one_div_pos.mpr ha)
  have hDtree : 1 ≤ Dtree := by
    simpa only [Dtree, one_mul] using Nat.mul_le_mul hDref hNtree
  have hD1 : 1 ≤ D := (by decide : 1 ≤ 2).trans hD2
  have hNtreeR : 1 / a ≤ (Nat.ceil (1 / a) : ℝ) := Nat.le_ceil _
  have haN : 1 ≤ a * (Nat.ceil (1 / a) : ℝ) := by
    have hb := (div_le_iff₀ ha).mp hNtreeR
    nlinarith only [hb]
  have hDref0 : (0 : ℝ) < Dref := by exact_mod_cast (Nat.zero_lt_one.trans_le hDref)
  have hNtree0 : (0 : ℝ) < Nat.ceil (1 / a) :=
    by exact_mod_cast (Nat.zero_lt_one.trans_le hNtree)
  have hroot : 0 < Real.sqrt ((L : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have hradius : 1 / (1000 * (Dtree : ℝ) * Real.sqrt ((L : ℝ) + 1)) ≤ xiMax := by
    dsimp only [Dtree, xiMax]
    simp only [Nat.cast_mul]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hb := mul_le_mul_of_nonneg_right haN (mul_pos hDref0 hroot).le
    nlinarith only [hb, (mul_pos hDref0 hroot).le]
  have :=
    hauto L q Φ h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
      Dtree D hDtree hD1 eta heta
  refine this.elim fun Bfinal hspec ↦ hspec.elim fun hBfinal hspec ↦
    hspec.elim fun hlogBfinal hspec ↦ ?_
  have hfinal := hspec
  refine ⟨Bfinal, hBfinal, hlogBfinal, ?_⟩
  intro b Dcommon Nfinal xi
  refine hfinal.elim fun Ufinal hspec ↦ hspec.elim fun hdimUfinal hspec ↦
    hspec.elim fun hUG hspec ↦ hspec.elim fun hGU hspec ↦ hspec.elim fun hUfinalMPS hspec ↦
    hspec.elim fun hxi hspec ↦ hspec.elim fun hxiCoarse hspec ↦ hspec.elim fun hxiSource hspec ↦ ?_
  have hterminal := hspec
  have hxiTree : xi ≤ xiMax := hxiCoarse.trans hradius
  refine ⟨Ufinal, hdimUfinal, hUG, hGU, hUfinalMPS, hxi, hxiTree, hxiSource, ?_⟩
  have := hxiFamily xi hxi hxiTree
  refine this.elim fun hprofile hspec ↦ ?_
  have hGood := hspec
  refine ⟨hprofile, ?_⟩
  intro Good failureBound
  refine hGood.elim fun hGoodMeasurable hspec ↦ hspec.elim fun hfailure hspec ↦ ?_
  have hsuccess := hspec
  refine ⟨hGoodMeasurable, hfailure, hsuccess, ?_⟩
  intro Bout
  have hL1 : (1 : ℝ) ≤ (L : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg L)
  have hw : 1 ≤ w := by
    dsimp only [w]
    linarith only [Real.log_natCast_nonneg rG, Real.log_nonneg hL1]
  have :=
    Real.interleaved_filter_scale_count_bounds Cscale m g w
      hCscale (Nat.le_max_right q 50) hg hg1 hw
  refine this.elim fun _hellCount hspec ↦ hspec.elim fun _hfirst hspec ↦
    hspec.elim fun _hsecond hspec ↦ hspec.elim fun _hupper hspec ↦ hspec.elim fun _hbase hspec ↦ ?_
  have hrawLog := hspec
  have hlogD : Real.log (D : ℝ) ≤ KD * w :=
    Real.interleaved_log_bound_le_linear Alog g U0 w (Real.log (D : ℝ))
      hAlog hg hU0 hw hrawLog
  have :=
    Real.interleaved_sample_size_bounds rG L D hrG hD2
  refine this.elim fun _hwSample hspec ↦ hspec.elim fun _hsSample hspec ↦
    hspec.elim fun hsUpper hspec ↦ ?_
  have _hsLog := hspec
  have :=
    physical_dg_normalized_ground_filter_spec Φ h0 mu nu gamma hgamma hmu hnu hmunu hgap
  refine this.elim fun _hM hspec ↦ hspec.elim fun hA hspec ↦ hspec.elim fun hc hspec ↦
    hspec.elim fun hc1 hspec ↦ hspec.elim fun _hfix hspec ↦ hspec.elim fun _hKGo hspec ↦ ?_
  have _hhigh := hspec
  change 0 < A at hA
  change 0 < c at hc
  change gamma / A ≤ 1 at hc1
  have hgammaA : gamma ≤ A := (div_le_one hA).mp hc1
  have hmu0 : 0 ≤ mu := spectrum_nonneg_of_nonneg
    (show 0 ≤ H from Finset.sum_nonneg fun i _ ↦ h0 i) hmu
  have hAL : A ≤ (L : ℝ) + 1 := by
    calc
      A ≤ ‖H‖ := sub_le_self _ hmu0
      _ ≤ ∑ _i : Fin (L - 1), (1 : ℝ) :=
        norm_sum_le_of_le Finset.univ fun i _ ↦
          (CStarAlgebra.norm_le_one_iff_of_nonneg (Φ.term i) (h0 i)).mpr (h1 i)
      _ = ((L - 1 : ℕ) : ℝ) := by simp
      _ ≤ (L : ℝ) + 1 := by exact_mod_cast (show L - 1 ≤ L + 1 by omega)
  have hbound : (Bout : ℝ) ≤
      C * (((L : ℝ) + 1) * ((rG : ℝ) + 1) * (1 + 1 / eta)) ^ k :=
    hpoly L rG D s A eta hrG hD1 hs hgammaA hAL heta hlogD hsUpper
      Btree Bfinal hBtree hBfinal hlogBtree hlogBfinal
  refine ⟨hbound, ?_⟩
  intro seed hgood S0 W0
  have hrootProfile := hprofile seed 0 L (Nat.zero_le L) le_rfl
  have hcloseRoot : Submodule.IsCloseTo (3 / 200 : ℝ) W0 G :=
    (isViable_fullInterval_iff_isCloseTo S0 G).mp hgood.1
  have hrho : 0 < rho :=
    (Real.viable_refinement_error_parameters hgamma hgammaA heta).2.2.1
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (Nat.zero_lt_one.trans_le hD1)
  have hNfinal : 1 ≤ Nfinal := Nat.one_le_ceil_iff.mpr (by positivity)
  have hDcommon : 1 ≤ Dcommon := hDtree.trans (Nat.le_max_left Dtree b)
  have hDN : 1 ≤ Dcommon * Nfinal := by
    simpa only [one_mul] using Nat.mul_le_mul hDcommon hNfinal
  have hrootMPS : ∀ z ∈ W0, IsOpenMPS L q Bout (fun x ↦ z x) := by
    intro z hz
    exact isOpenMPS_of_mem_nativeFullIntervalSpace_of_trimming_rank_bound hDN hrootProfile.2 hz
  refine ⟨hcloseRoot, hrootMPS, ?_⟩
  apply hterminal (D ^ 6 * s ^ 3) S0 hrootProfile.1 hcloseRoot

end TNLean.MPS.AreaLaw
