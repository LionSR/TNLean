/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalDGTreeApproximation
import QICLean.Analysis.RefinementOutputPolynomialBound

/-!
# A uniform polynomial bond for the actual recursive Ritz output

For fixed local dimension and gap, the coefficient and natural exponent precede the chain
length, ground multiplicity and requested precision. The space is the literal Ritz output
of the existing common-threshold recursive construction, not a space selected from an
independent approximation theorem. This supports ALVV, arXiv:1602.08828v2, `t:alg1`,
lines 1777–1817.

**Scope restriction (modified tree, capped gap and witness existence):** the leaves are full
blocks of length at most four times the chosen scale and every long node has one final
collective trim. The capped gap and the constructed-witness scope of the parent theorem
are retained. No adaptive probability, source energy-estimation invariant or running time
is asserted. See `docs/paper-gaps/alvv16_approximation_parameters.tex` and
`docs/paper-gaps/alvv16_final_filter_gain.tex`.
-/

open Matrix
open scoped InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- The actual modified-tree Ritz output has a uniform polynomial all-span MPS bond for
fixed local dimension and spectral gap. The coefficient and integer exponent are chosen
before length, ground multiplicity and requested error. The proof extracts the same Ritz
space and its recorded bond from the explicit parent construction. Supporting ALVV,
arXiv:1602.08828v2, `t:alg1`, lines 1777–1817, with the stated modified-tree scope. -/
theorem exists_physical_dg_tree_ritz_polynomial_approximation
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
          ∀ w ∈ R, IsOpenMPS L q B (fun x ↦ w x) := by
  classical
  obtain ⟨Ctree, Ktree, Kref, hCtree, hKtree, hKref, hconstruct⟩ :=
    exists_physical_dg_tree_ritz_approximation
  let g := min gamma 1
  let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
  let m := max q 50
  let v := 1 + Real.log (m : ℝ) + Real.log (1 / g)
  let ell : ℕ := Nat.ceil (Ctree * v ^ 2 / g)
  let Dfilter := (m * ell ^ 2) ^ (22 * ell)
  have hg : 0 < g := lt_min hgamma (by norm_num)
  have hg1 : g ≤ 1 := min_le_right gamma 1
  have hgInv : 1 ≤ 1 / g := (le_div_iff₀ hg).mpr (by simpa using hg1)
  have hlogq : 0 ≤ Real.log (q : ℝ) := by
    by_cases hq : q = 0
    · simp [hq]
    · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hq)
  have hu : 0 ≤ u := by
    dsimp only [u]
    linarith [Real.log_nonneg hgInv]
  have hm : 1 ≤ m := (by decide : 1 ≤ 50).trans (Nat.le_max_right q 50)
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hv : 1 ≤ v := by
    dsimp only [v]
    linarith [Real.log_nonneg hmR, Real.log_nonneg hgInv]
  have hell1 : 1 ≤ ell := by
    have hCpos : 0 < Ctree := lt_of_lt_of_le zero_lt_one hCtree
    have hvpos : 0 < v := lt_of_lt_of_le zero_lt_one hv
    have hpos : 0 < Ctree * v ^ 2 / g := by positivity
    exact Nat.ceil_pos.mpr hpos
  have hbase : 1 ≤ m * ell ^ 2 := by
    simpa only [one_mul] using Nat.mul_le_mul hm (Nat.one_le_pow 2 ell hell1)
  have hDfilter : 1 ≤ Dfilter := Nat.one_le_pow (22 * ell) (m * ell ^ 2) hbase
  obtain ⟨C, hC, k, hpoly⟩ := Real.exists_refinement_output_polynomial_bound
    gamma g u Ktree Kref Dfilter hgamma hg hg1 hu hKtree.le hKref.le hDfilter
  refine ⟨C, hC, k, ?_⟩
  intro L h hsupp h0 h1 mu nu H hH hmu hnu hmunu hgap G r eta heta
  let A := ‖H‖ - mu
  let c := gamma / A
  let Kraw := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) (1 - ‖H‖⁻¹ • H)
  let rho := eta * gamma / (2 * A + eta * gamma)
  let n := Nat.ceil (4 / c * Real.log (1 / rho)) + 1
  have hr : 1 ≤ r := Submodule.one_le_finrank_iff.mpr
    (hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl)
  obtain ⟨_hM, hA, _hc, hc1, _hfix, _hKGo, _hhigh⟩ :=
    physical_dg_normalized_ground_filter_spec h h0 mu nu gamma hgamma hmu hnu hmunu hgap
  change 0 < A at hA
  change gamma / A ≤ 1 at hc1
  have hgammaA : gamma ≤ A := (div_le_one hA).mp hc1
  have hmu0 : 0 ≤ mu := spectrum_nonneg_of_nonneg
    (show 0 ≤ H from Finset.sum_nonneg fun i _ ↦ h0 i) hmu
  have hnorm : ‖H‖ ≤ (L : ℝ) + 1 := by
    calc
      _ ≤ ∑ i, ‖h i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin (L - 1), (1 : ℝ) := Finset.sum_le_sum fun i _ ↦
        (CStarAlgebra.norm_le_one_iff_of_nonneg (h i) (h0 i)).mpr (h1 i)
      _ = ((L - 1 : ℕ) : ℝ) := by simp
      _ ≤ _ := by exact_mod_cast (show L - 1 ≤ L + 1 by omega)
  have hAL : A ≤ (L : ℝ) + 1 := by dsimp only [A]; linarith only [hnorm, hmu0]
  obtain ⟨_hell, _hlogD, Btree, hBtree, hlogBtree, hfamilies⟩ :=
    hconstruct L q h hsupp h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
  let Dtree := r ^ 2 * Btree
  let width := 4 * ell
  have hwidth : 1 ≤ width := by dsimp only [width]; omega
  obtain ⟨_Nfam, _F, _hNfam, hprecision⟩ := hfamilies
  obtain ⟨B, hB, hlogB, hfinal⟩ := hprecision eta heta
  let b := r ^ 2 * B
  let Dcommon := max Dtree b
  let N := Nat.ceil (100 * (Dfilter : ℝ) ^ 12 / (c * rho))
  let xi := 1 / (1000 * ((Dcommon * N : ℕ) : ℝ) * Real.sqrt ((L : ℝ) + 1))
  obtain ⟨_Uref, _hdimU, _hUG, _hGU, _hUMPS, _hxi, _hxiTree, _hxiSource, hterminal⟩ := hfinal
  let sampleLog := 1 + Real.log (r : ℝ) + Real.log (Dfilter : ℝ) + Real.log (1 / (1 / 2 : ℝ))
  let s := Nat.ceil (4096 * (r : ℝ) * sampleLog)
  let count := Dfilter ^ 6 * s ^ 3
  obtain ⟨hsample, operation, _hliteral, _hspaces, hritz⟩ :=
    hterminal (1 / 2) (by norm_num) (by norm_num)
  let S0 := balancedIntervalSpace operation width hwidth 0 L
  let S := fullIntervalFilterTrimIterate L q Kraw xi S0 n
  let W := nativeFullIntervalSpace L q S
  let R := W.ritzSubspace (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH) r
  obtain ⟨_hn, _hcloseW, _hdimS, _hRW, hdimR, hGR, hRG, hMPS⟩ := hritz
  have hsample' : (s : ℝ) ≤ 4097 * (r : ℝ) *
      (1 + Real.log (r : ℝ) + Real.log (Dfilter : ℝ) + Real.log 2) := by
    have hsample0 : (s : ℝ) ≤ 4097 * (r : ℝ) * sampleLog := hsample
    simpa only [sampleLog, one_div_div, div_one] using hsample0
  have hbond := hpoly L r A eta hr hgammaA hAL heta Btree B hBtree hB
    hlogBtree hlogB s hsample'
  exact ⟨1000000 * (Dcommon * N) ^ 2 * (L + 1) * count ^ 2,
    hbond, R, hdimR, hGR, hRG, hMPS⟩

end TNLean.MPS.AreaLaw
