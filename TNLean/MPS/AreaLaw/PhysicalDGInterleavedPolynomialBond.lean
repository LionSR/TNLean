/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalDGInterleavedApproximation
import QICLean.Analysis.InterleavedOutputPolynomialBound

/-!
# A uniform polynomial bond for the actual interleaved Ritz output

The coefficient and natural degree precede length, ground multiplicity and
requested precision at fixed local dimension and gap. The actual filter count
is allowed to depend on length and ground multiplicity through its calibrated
logarithmic scale. The proof selects the same Ritz space already constructed
from the literal interleaved tree root and its final raw-filter/trim iterates.
No independent MPS approximation or older one-final-trim root is substituted.

This supports ALVV, arXiv:1602.08828v2, `t:alg1`, lines 1777–1817.

**Scope restriction (interleaved witness and coarse polynomial bound):**
The block leaves, fixed nominal sampling/failure scale, capped gap and larger
integer parent count of the actual interleaved construction are retained.
This is a polynomial consequence of its honest length-dependent count; it is
not identified with the printed sharp physical profile. No adaptive joint
probability, source energy-estimation invariant or running time is asserted.
See `docs/paper-gaps/alvv16_approximation_parameters.tex`.

**Local fix (final gain and count):** The final refinement uses the corrected
normalized-gain recurrence and its projection-accuracy count. See
`docs/paper-gaps/alvv16_final_filter_gain.tex`.
-/

open scoped InnerProductSpace TensorProduct ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- The actual interleaved-tree Ritz output has one uniform polynomial
all-span MPS bond at fixed local dimension and gap. Its count depends on
length and ground multiplicity, and every numerical condition is derived.
The proof extracts that SAME previously constructed Ritz output. Supporting
ALVV, arXiv:1602.08828v2, `t:alg1`, lines 1777–1817, in the stated scope. -/
theorem exists_physical_dg_interleaved_ritz_polynomial_approximation_with_constants :
    ∃ Cdegree : ℝ, 0 < Cdegree ∧ ∀ (q : ℕ) (gamma : ℝ), 0 < gamma →
    ∃ C : ℝ, 0 < C ∧
      Real.log (max C 1) ≤ Cdegree *
        (1 + Real.log (max q 50 : ℕ) + Real.log (1 / min gamma 1)) ^ 10 /
          (min gamma 1) ^ 2 ∧ ∃ k : ℕ,
      (k : ℝ) ≤ Cdegree *
        (1 + Real.log (max q 50 : ℕ) + Real.log (1 / min gamma 1)) ^ 10 /
          (min gamma 1) ^ 2 ∧ ∀ (L : ℕ)
      (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
      (_hsupp : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
        (h i) (interval L i.val (i.val + 2)))
      (h0 : ∀ i, 0 ≤ h i) (_h1 : ∀ i, h i ≤ 1) (mu nu : ℝ),
      let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i, h i
      let hH : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      mu ∈ spectrum ℝ H → nu ∈ spectrum ℝ H → mu < nu →
      (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
      let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
      let r := Module.finrank ℂ G
      ∀ eta : ℝ, 0 < eta → ∃ B : ℕ,
        (B : ℝ) ≤ C * (((L : ℝ) + 1) * ((r : ℝ) + 1) * (1 + 1 / eta)) ^ k ∧
        ∃ R : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)),
          Module.finrank ℂ R = r ∧ Submodule.IsCloseTo (eta / 2) G R ∧
          Submodule.IsCloseTo (eta / 2) R G ∧
          ∀ z ∈ R, IsOpenMPS L q B (fun x ↦ z x) := by
  classical
  obtain ⟨Ctail, Cscale, Ktree, Kref, _hCtail, hCscale, hKtree, hKref, hconstruct⟩ :=
    exists_physical_dg_interleaved_tree_ritz_approximation
  let Alog := 22 * (Cscale + 1) * (14 + 2 * Real.log (Cscale + 1))
  let CK := Alog * (18 ^ 7 + 18 ^ 4)
  let K := max Ktree Kref
  let Cdegree := 10 * (24 * (2 * CK + 1) + 21) * (6 * K + 1) + 60 * (2 * CK + 1) + 43
  have hlogC : 0 ≤ Real.log (Cscale + 1) := Real.log_nonneg (by linarith only [hCscale])
  have hAlog : 0 ≤ Alog := by dsimp only [Alog]; positivity
  have hCK : 0 ≤ CK := by dsimp only [CK]; positivity
  have hK : 0 ≤ K := hKtree.le.trans (le_max_left Ktree Kref)
  have hCdegree : 0 < Cdegree := by dsimp only [Cdegree]; positivity
  let Ccoefficient := 70000000 * (K + 1) * (CK + 4)
  let Cboth := max Cdegree Ccoefficient
  have hCboth : 0 < Cboth := hCdegree.trans_le (le_max_left _ _)
  refine ⟨Cboth, hCboth, ?_⟩
  intro q gamma hgamma
  let g := min gamma 1
  let m := max q 50
  let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
  let U0 := 1 + Real.log (m : ℝ) + Real.log (1 / g)
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
  have hU17 : 0 ≤ U0 + 17 := by linarith only [hU0]
  have hKD : 0 ≤ KD := by dsimp only [KD]; positivity
  have huU : u ≤ U0 := by
    have hqm : Real.log (q : ℝ) ≤ Real.log (m : ℝ) := by
      by_cases hq : q = 0
      · simpa only [hq, Nat.cast_zero, Real.log_zero] using Real.log_natCast_nonneg m
      · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hq)
          (by exact_mod_cast Nat.le_max_left q 50)
    dsimp only [u, U0]
    linarith only [hqm]
  have hcount : KD ≤ CK * U0 ^ 7 / g :=
    Real.interleaved_count_coefficient_le Alog U0 g hAlog hU0 hg hg1
  obtain ⟨C, hC, hlogCbound, k, hk, hpoly⟩ :=
    Real.exists_interleaved_output_polynomial_bound_with_constants
    gamma g u Ktree Kref KD hgamma hg hg1 hu hKtree.le hKref.le hKD
  refine ⟨C, hC, ?_, k, ?_, ?_⟩
  · have hloggU : Real.log (1 / g) ≤ U0 := by
      dsimp only [U0]
      linarith [Real.log_natCast_nonneg m]
    have hcoefficient := Real.interleaved_log_coefficient_bound_le
      U0 u gamma g K KD CK hU0 hu huU hg hg1 (min_le_left gamma 1)
      hloggU hK hKD hCK hcount
    change Real.log (max C 1) ≤ Cboth * U0 ^ 10 / g ^ 2
    exact hlogCbound.trans (hcoefficient.trans (by
      apply div_le_div_of_nonneg_right _ (sq_nonneg g)
      exact mul_le_mul_of_nonneg_right (le_max_right Cdegree Ccoefficient) (by positivity)))
  · rw [hk]
    have hdegree := Real.interleaved_output_polynomial_degree_le
      U0 u g K KD CK hU0 hu huU hg hg1 hK hKD hCK hcount
    exact hdegree.trans (by
      apply div_le_div_of_nonneg_right _ (sq_nonneg g)
      exact mul_le_mul_of_nonneg_right (le_max_left Cdegree Ccoefficient) (by positivity))
  intro L h hsupp h0 h1 mu nu H hH hmu hnu hmunu hgap G r eta heta
  let w := 1 + Real.log (r : ℝ) + 2 * Real.log ((L : ℝ) + 1)
  let v := U0 + Real.log (1 + w)
  let ell := Nat.ceil (Cscale * (v ^ 6 / g + Real.sqrt w * v ^ 3 / Real.sqrt g))
  let D := (m * ell ^ 2) ^ (22 * ell)
  let s := Nat.ceil (4096 * (r : ℝ) * (Real.log (D : ℝ) + w))
  let a := 3 / (32 * (D : ℝ) ^ 12 * (s : ℝ) ^ 5)
  let A := ‖H‖ - mu
  let c := gamma / A
  let Kraw := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) (1 - ‖H‖⁻¹ • H)
  let rho := eta * gamma / (2 * A + eta * gamma)
  let n := Nat.ceil (4 / c * Real.log (1 / rho)) + 1
  have hr : 1 ≤ r := Submodule.one_le_finrank_iff.mpr
    (hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl)
  have hL1 : (1 : ℝ) ≤ (L : ℝ) + 1 := by
    have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    linarith only [hL0]
  have hw : 1 ≤ w := by
    dsimp only [w]
    linarith [Real.log_natCast_nonneg r, Real.log_nonneg hL1]
  have hm50 : 50 ≤ m := Nat.le_max_right q 50
  obtain ⟨_hell, _hfirst, _hsecond, _hupper, _hbase, hrawLog⟩ :=
    Real.interleaved_filter_scale_count_bounds Cscale m g w hCscale hm50 hg hg1 hw
  have hlogD : Real.log (D : ℝ) ≤ KD * w :=
    Real.interleaved_log_bound_le_linear Alog g U0 w (Real.log (D : ℝ))
      hAlog hg hU0 hw hrawLog
  obtain ⟨hell, hD2, hs, _ha, _haSmall, _hepsilon, _hepsilon1, _ht, _htail, _htrade,
    Btree, hBtree, hlogBtree, _Utree, _hdimU, _hUMPS, _hxiMax, hfamilies⟩ :=
    hconstruct L q h hsupp h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
  have hD : 1 ≤ D := (by decide : 1 ≤ 2).trans hD2
  obtain ⟨_hw, _hs, hsUpper, _hsLog⟩ := Real.interleaved_sample_size_bounds r L D hr hD2
  obtain ⟨_hM, hA, _hc, hc1, _hfix, _hKGo, _hhigh⟩ :=
    physical_dg_normalized_ground_filter_spec h h0 mu nu gamma hgamma hmu hnu hmunu hgap
  change 0 < A at hA
  have hgammaA : gamma ≤ A := (div_le_one hA).mp hc1
  have hmu0 : 0 ≤ mu := spectrum_nonneg_of_nonneg
    (show 0 ≤ H from Finset.sum_nonneg fun i _ ↦ h0 i) hmu
  have hnorm : ‖H‖ ≤ (L : ℝ) + 1 := by
    have hb : ‖H‖ ≤ ((L - 1 : ℕ) : ℝ) := by
      simpa using norm_sum_le_of_le (Finset.univ : Finset (Fin (L - 1)))
        (fun i _ ↦ (CStarAlgebra.norm_le_one_iff_of_nonneg (h i) (h0 i)).mpr (h1 i))
    exact hb.trans (by exact_mod_cast (show L - 1 ≤ L + 1 by omega))
  have hAL : A ≤ (L : ℝ) + 1 := by dsimp only [A]; linarith only [hnorm, hmu0]
  let Dref := r ^ 2 * Btree
  let width := 4 * ell
  obtain ⟨hwidth, _Nfam, _F, _hNfam, hprecision⟩ := hfamilies
  obtain ⟨Bfinal, hBfinal, hlogBfinal, hfinal⟩ := hprecision eta heta
  let b := r ^ 2 * Bfinal
  let Dcommon := max (Dref * Nat.ceil (1 / a)) b
  let Nfinal := Nat.ceil (100 * (D : ℝ) ^ 12 / (c * rho))
  let xi := 1 / (1000 * ((Dcommon * Nfinal : ℕ) : ℝ) * Real.sqrt ((L : ℝ) + 1))
  obtain ⟨_Ufinal, _hdimUfinal, _hUG, _hGU, _hFinalMPS, _hxi, _hxiTree, _hxiSource,
    operation, _hspaces, _hliteral, hroot⟩ := hfinal
  let S0 := balancedIntervalSpace operation width hwidth 0 L
  let S := fullIntervalFilterTrimIterate L q Kraw xi S0 n
  let W := nativeFullIntervalSpace L q S
  let R := W.ritzSubspace (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH) r
  obtain ⟨_hrootClose, _hrootMPS, hterminal⟩ := hroot
  obtain ⟨_hn, _hcloseW, _hdimS, _hRW, hdimR, hGR, hRG, hMPS⟩ := hterminal
  let count := D ^ 6 * s ^ 3
  let Bout := 1000000 * (Dcommon * Nfinal) ^ 2 * (L + 1) * count ^ 2
  have hbound : (Bout : ℝ) ≤ C * (((L : ℝ) + 1) * ((r : ℝ) + 1) * (1 + 1 / eta)) ^ k :=
    hpoly L r D s A eta hr hD hs hgammaA hAL heta hlogD hsUpper
      Btree Bfinal hBtree hBfinal hlogBtree hlogBfinal
  exact ⟨Bout, hbound, R, hdimR, hGR, hRG, hMPS⟩

/-- The actual interleaved-tree Ritz output has one uniform polynomial
all-span MPS bond at fixed local dimension and gap. Its count depends on
length and ground multiplicity, and every numerical condition is derived.
The proof extracts that SAME previously constructed Ritz output. Supporting
ALVV, arXiv:1602.08828v2, `t:alg1`, lines 1777–1817, in the stated scope. -/
theorem exists_physical_dg_interleaved_ritz_polynomial_approximation_with_degree :
    ∃ Cdegree : ℝ, 0 < Cdegree ∧ ∀ (q : ℕ) (gamma : ℝ), 0 < gamma →
    ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ,
      (k : ℝ) ≤ Cdegree *
        (1 + Real.log (max q 50 : ℕ) + Real.log (1 / min gamma 1)) ^ 10 /
          (min gamma 1) ^ 2 ∧ ∀ (L : ℕ)
      (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
      (_hsupp : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
        (h i) (interval L i.val (i.val + 2)))
      (h0 : ∀ i, 0 ≤ h i) (_h1 : ∀ i, h i ≤ 1) (mu nu : ℝ),
      let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i, h i
      let hH : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      mu ∈ spectrum ℝ H → nu ∈ spectrum ℝ H → mu < nu →
      (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
      let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
      let r := Module.finrank ℂ G
      ∀ eta : ℝ, 0 < eta → ∃ B : ℕ,
        (B : ℝ) ≤ C * (((L : ℝ) + 1) * ((r : ℝ) + 1) * (1 + 1 / eta)) ^ k ∧
        ∃ R : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)),
          Module.finrank ℂ R = r ∧ Submodule.IsCloseTo (eta / 2) G R ∧
          Submodule.IsCloseTo (eta / 2) R G ∧
          ∀ z ∈ R, IsOpenMPS L q B (fun x ↦ z x) := by
  obtain ⟨Cdegree, hCdegree, houtput⟩ :=
    exists_physical_dg_interleaved_ritz_polynomial_approximation_with_constants
  refine ⟨Cdegree, hCdegree, ?_⟩
  intro q gamma hgamma
  obtain ⟨C, hC, _hlogC, k, hk, hbound⟩ := houtput q gamma hgamma
  exact ⟨C, hC, k, hk, hbound⟩

/-- The actual interleaved-tree Ritz output has one uniform polynomial
all-span MPS bond at fixed local dimension and gap. Its count depends on
length and ground multiplicity, and every numerical condition is derived.
The proof extracts that SAME previously constructed Ritz output. Supporting
ALVV, arXiv:1602.08828v2, `t:alg1`, lines 1777–1817, in the stated scope. -/
theorem exists_physical_dg_interleaved_ritz_polynomial_approximation
    (q : ℕ) (gamma : ℝ) (hgamma : 0 < gamma) :
    ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, ∀ (L : ℕ)
      (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
      (_hsupp : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
        (h i) (interval L i.val (i.val + 2)))
      (h0 : ∀ i, 0 ≤ h i) (_h1 : ∀ i, h i ≤ 1) (mu nu : ℝ),
      let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i, h i
      let hH : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      mu ∈ spectrum ℝ H → nu ∈ spectrum ℝ H → mu < nu →
      (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
      let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
      let r := Module.finrank ℂ G
      ∀ eta : ℝ, 0 < eta → ∃ B : ℕ,
        (B : ℝ) ≤ C * (((L : ℝ) + 1) * ((r : ℝ) + 1) * (1 + 1 / eta)) ^ k ∧
        ∃ R : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)),
          Module.finrank ℂ R = r ∧ Submodule.IsCloseTo (eta / 2) G R ∧
          Submodule.IsCloseTo (eta / 2) R G ∧
          ∀ z ∈ R, IsOpenMPS L q B (fun x ↦ z x) := by
  obtain ⟨_Cdegree, _hCdegree, houtput⟩ :=
    exists_physical_dg_interleaved_ritz_polynomial_approximation_with_degree
  obtain ⟨C, hC, k, _hk, hbound⟩ := houtput q gamma hgamma
  exact ⟨C, hC, k, hbound⟩

end TNLean.MPS.AreaLaw
