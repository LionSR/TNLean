/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.Parameter.RefinementOutputPolynomialBound
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.DegenerateGround.PhysicalDGFilterTrimming
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.DegenerateGround.PhysicalDGTreeParameters

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

It also contains the following results.

* `TNLean.MPS.AreaLaw.exists_physical_dg_tree_ritz_approximation`: ground-space approximation from
  the same physical recursive root.
-/

open ManyBody (interval)

section PhysicalDGTreeApproximation

/-!
## Ground-space approximation from the same physical recursive root

The original Hamiltonian supplies the actual improving families before the
precision, common trimming threshold, sampling size and child spaces.
The threshold is used at every long parent and in every final raw-filter
iterate. The initial candidate is the actual balanced recursive root.
The final output is its literal refined-space Ritz extraction, with the
original ground-space dimension and one MPS bound for the entire output.

This supports ALVV, arXiv:1602.08828v2, `t:alg1`, lines 1777–1817.
No initial or final viable-space witness, reference, operator family or
trial energy is supplied as a hypothesis.

**Scope restriction (modified tree, capped gap and witness existence):**
The leaves are full blocks of length at most `4 * ell`, each long node has
one final collective trim, and the reference bound uses `min gamma 1`.
This constructs recursive witnesses; it does not assert adaptive sampling
probability, the source energy-estimation invariant or running time.
See `docs/paper-gaps/alvv16_approximation_parameters.tex`.

**Local fix (normalized gain):** The final iteration count is explicit in
the internal projection target `rho`, which is chosen to control the Ritz
energy. It is not identified with the count printed in the source.
See `docs/paper-gaps/alvv16_final_filter_gain.tex`.
-/

open scoped InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- The full original ground space has an approximate Ritz space obtained
from the actual common-threshold recursive root and its literal final
raw-filter-and-trim iterates. All numerical filter, reference, threshold
and trial-energy conditions are derived. The same physical families work
before every requested precision and sampling-size parameter. The stated
modified-tree and witness-existence scope remains explicit.
Supporting ALVV, arXiv:1602.08828v2, `t:alg1`, lines 1777–1817. -/
theorem exists_physical_dg_tree_ritz_approximation :
    ∃ C Ktree Kref : ℝ, 1 ≤ C ∧ 0 < Ktree ∧ 0 < Kref ∧ ∀ (L q : ℕ),
    ∀ (Φ : ManyBody.BondInteraction L q)
      (h0 : ∀ i, 0 ≤ Φ.term i) (_h1 : ∀ i, Φ.term i ≤ 1) (mu nu gamma : ℝ),
    0 < gamma →
    let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Φ.hamiltonian
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    mu ∈ spectrum ℝ H → nu ∈ spectrum ℝ H → mu < nu →
    (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
    let rG := Module.finrank ℂ G
    let g := min gamma 1
    let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
    let A := ‖H‖ - mu
    let c := gamma / A
    let Kraw := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) (1 - ‖H‖⁻¹ • H)
    let epsilonTree : ℝ := 1 / 10000
    let btree := 16 + Real.log (1 / g) +
      Real.log (32 * (rG : ℝ) * ((L : ℝ) + 1) / epsilonTree)
    let m := max q 50
    let v := 1 + Real.log (m : ℝ) + Real.log (1 / g)
    let ell : ℕ := Nat.ceil (C * v ^ 2 / g)
    let Dfilter := (m * ell ^ 2) ^ (22 * ell)
    ∃ _hell : 21 ≤ ell,
    Real.log (Dfilter : ℝ) ≤
      22 * (C + 1) * (6 + 2 * Real.log (C + 1)) / g * v ^ 3 ∧
    ∃ Btree : ℕ, 1 ≤ Btree ∧
    Real.log (Btree : ℝ) ≤
      Ktree * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * btree ^ (3 / 4 : ℝ) * u) *
        (1 + Real.log btree) ∧
    let Dtree := rG ^ 2 * Btree
    let width := 4 * ell
    let hwidth : 1 ≤ width := by omega
    ∃ (Nfam : LongIntervalIndex L width → ℕ)
      (F : ∀ J : LongIntervalIndex L width,
        Fin (Nfam J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
          EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)),
      (∀ J, Nfam J ≤ Dfilter ^ 2) ∧
      ∀ eta : ℝ, 0 < eta →
      let rho := eta * gamma / (2 * A + eta * gamma)
      let n := Nat.ceil (4 / c * Real.log (1 / rho)) + 1
      let epsilonRef := c ^ 2 * rho / 32768
      let bref := 16 + Real.log (1 / g) +
        Real.log (32 * (rG : ℝ) * ((L : ℝ) + 1) / epsilonRef)
      ∃ B : ℕ, 1 ≤ B ∧
      Real.log (B : ℝ) ≤
        Kref * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * bref ^ (3 / 4 : ℝ) * u) *
          (1 + Real.log bref) ∧
      let b := rG ^ 2 * B
      let Dcommon := max Dtree b
      let N := Nat.ceil (100 * (Dfilter : ℝ) ^ 12 / (c * rho))
      let xi := 1 / (1000 * ((Dcommon * N : ℕ) : ℝ) * Real.sqrt ((L : ℝ) + 1))
      ∃ Uref : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)),
        Module.finrank ℂ Uref = rG ∧
        Submodule.IsCloseTo epsilonRef Uref G ∧ Submodule.IsCloseTo epsilonRef G Uref ∧
        (∀ w ∈ Uref, IsOpenMPS L q b (fun x ↦ w x)) ∧
        0 < xi ∧
        xi ≤ 1 / (1000 * (Dtree : ℝ) * Real.sqrt ((L : ℝ) + 1)) ∧
        Real.sqrt ((L : ℝ) * (rG : ℝ) * (b : ℝ)) * xi <
          eta / (10000 * (Dfilter : ℝ) ^ 12) ∧
        ∀ beta : ℝ, 0 < beta → beta < 1 →
        let sampleLog := 1 + Real.log (rG : ℝ) + Real.log (Dfilter : ℝ) + Real.log (1 / beta)
        let s := Nat.ceil (4096 * (rG : ℝ) * sampleLog)
        let count := Dfilter ^ 6 * s ^ 3
        (s : ℝ) ≤ 4097 * (rG : ℝ) * sampleLog ∧
        ∃ operation : IntervalMergeOperation L q,
          (∀ (J : LongIntervalIndex L width) (k : ℕ) (hpk : J.val.1 ≤ k) (hkr : k ≤ J.val.2)
            (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 k → Fin q)))
            (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k J.val.2 → Fin q))),
            Submodule.IsViable (3 / 200 : ℝ) S1
              (G.map (Entropy.regionTensorCoordinates q
                (interval L J.val.1 k)).toLinearEquiv.toLinearMap) →
            Submodule.IsViable (3 / 200 : ℝ) S2
              (G.map (Entropy.regionTensorCoordinates q
                (interval L k J.val.2)).toLinearEquiv.toLinearMap) →
            Module.finrank ℂ S1 ≤ count → Module.finrank ℂ S2 ≤ count →
            ∃ V : Matrix.unitaryGroup
              (Fin (Module.finrank ℂ (adjacentIntervalMerge L q
                J.val.1 k J.val.2 hpk hkr S1 S2))) ℂ,
              operation J.val.1 k J.val.2 hpk hkr S1 S2 =
                sampledIntervalTrim L q J.val.1 J.val.2 (F J)
                  (Nat.clog Dfilter (Dfilter ^ 2 * s)) s xi
                  (adjacentIntervalMerge L q J.val.1 k J.val.2 hpk hkr S1 S2) V) ∧
          (∀ p r : ℕ, p ≤ r → r ≤ L →
            let S := balancedIntervalSpace operation width hwidth p r
            Submodule.IsViable (3 / 200 : ℝ) S
              (G.map (Entropy.regionTensorCoordinates q
                (interval L p r)).toLinearEquiv.toLinearMap) ∧
            Module.finrank ℂ S ≤ count ∧ IsIntervalSpanWithRankBound L q p r count xi S) ∧
          let S0 := balancedIntervalSpace operation width hwidth 0 L
          let S := fullIntervalFilterTrimIterate L q Kraw xi S0 n
          let W := nativeFullIntervalSpace L q S
          let R := W.ritzSubspace (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH) rG
          0 < n ∧ Submodule.IsCloseTo rho W G ∧ Module.finrank ℂ S ≤ count ∧
            R ≤ W ∧ Module.finrank ℂ R = rG ∧
            Submodule.IsCloseTo (eta / 2) G R ∧ Submodule.IsCloseTo (eta / 2) R G ∧
            ∀ w ∈ R, IsOpenMPS L q
              (1000000 * (Dcommon * N) ^ 2 * (L + 1) * count ^ 2) (fun x ↦ w x) := by
  classical
  obtain ⟨C, Ktree, hC, hKtree, htree⟩ := exists_physical_dg_interval_tree_of_le_radius
  obtain ⟨Kref, hKref, hrefine⟩ := exists_physical_dg_automatic_same_candidate_refinement
  refine ⟨C, Ktree, Kref, hC, hKtree, hKref, ?_⟩
  intro L q Φ h0 h1 mu nu gamma hgamma H hH hmu hnu hmunu hgap
    G rG g u A c Kraw epsilonTree btree m v ell Dfilter
  obtain ⟨hell, hlogD, Btree, hBtree, hlogBtree, hfamilies⟩ :=
    htree L q Φ h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
  refine ⟨hell, hlogD, Btree, hBtree, hlogBtree, ?_⟩
  intro Dtree width hwidth
  have hrG : 1 ≤ rG := Submodule.one_le_finrank_iff.mpr
    (hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl)
  have hDtree : 1 ≤ Dtree := by
    dsimp only [Dtree]
    simpa only [one_mul] using Nat.mul_le_mul (Nat.one_le_pow 2 rG hrG) hBtree
  have hm : 1 ≤ m := (by decide : 1 ≤ 50).trans (Nat.le_max_right q 50)
  have hbase : 1 ≤ m * ell ^ 2 := by
    simpa only [one_mul] using Nat.mul_le_mul hm (Nat.one_le_pow 2 ell (by omega))
  have hDfilter : 1 ≤ Dfilter := Nat.one_le_pow (22 * ell) (m * ell ^ 2) hbase
  obtain ⟨Nfam, F, hNfam, hparents⟩ := hfamilies
  refine ⟨Nfam, F, hNfam, ?_⟩
  intro eta heta rho n epsilonRef bref
  obtain ⟨B, hB, hlogB, hfinal⟩ :=
    hrefine L q Φ h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
      Dtree Dfilter hDtree hDfilter eta heta
  refine ⟨B, hB, hlogB, ?_⟩
  intro b Dcommon N xi
  obtain ⟨Uref, hdimU, hUG, hGU, hUMPS, hxi, hxiTree, hxiSource, hterminal⟩ := hfinal
  refine ⟨Uref, hdimU, hUG, hGU, hUMPS, hxi, hxiTree, hxiSource, ?_⟩
  intro beta hbeta hbeta1 sampleLog s count
  obtain ⟨hscount, operation, hliteral, hspaces⟩ := hparents xi hxi hxiTree beta hbeta hbeta1
  refine ⟨hscount, operation, hliteral, hspaces, ?_⟩
  let S0 := balancedIntervalSpace operation width hwidth 0 L
  have hroot := hspaces 0 L (Nat.zero_le L) le_rfl
  have hcloseRoot : Submodule.IsCloseTo (3 / 200 : ℝ) (nativeFullIntervalSpace L q S0) G :=
    (isViable_fullInterval_iff_isCloseTo S0 G).mp hroot.1
  exact hterminal count S0 hroot.2.1 hcloseRoot

end TNLean.MPS.AreaLaw

end PhysicalDGTreeApproximation

section PhysicalDGTreePolynomialBond

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
      (Φ : ManyBody.BondInteraction L q)
      (h0 : ∀ i, 0 ≤ Φ.term i) (_h1 : ∀ i, Φ.term i ≤ 1) (mu nu : ℝ),
      let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Φ.hamiltonian
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
  intro L Φ h0 h1 mu nu H hH hmu hnu hmunu hgap G r eta heta
  let A := ‖H‖ - mu
  let c := gamma / A
  let Kraw := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) (1 - ‖H‖⁻¹ • H)
  let rho := eta * gamma / (2 * A + eta * gamma)
  let n := Nat.ceil (4 / c * Real.log (1 / rho)) + 1
  have hr : 1 ≤ r := Submodule.one_le_finrank_iff.mpr
    (hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl)
  obtain ⟨_hM, hA, _hc, hc1, _hfix, _hKGo, _hhigh⟩ :=
    physical_dg_normalized_ground_filter_spec Φ h0 mu nu gamma hgamma hmu hnu hmunu hgap
  change 0 < A at hA
  change gamma / A ≤ 1 at hc1
  have hgammaA : gamma ≤ A := (div_le_one hA).mp hc1
  have hmu0 : 0 ≤ mu := spectrum_nonneg_of_nonneg
    (show 0 ≤ H from Finset.sum_nonneg fun i _ ↦ h0 i) hmu
  have hnorm : ‖H‖ ≤ (L : ℝ) + 1 := by
    calc
      _ ≤ ∑ i, ‖Φ.term i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin (L - 1), (1 : ℝ) := Finset.sum_le_sum fun i _ ↦
        (CStarAlgebra.norm_le_one_iff_of_nonneg (Φ.term i) (h0 i)).mpr (h1 i)
      _ = ((L - 1 : ℕ) : ℝ) := by simp
      _ ≤ _ := by exact_mod_cast (show L - 1 ≤ L + 1 by omega)
  have hAL : A ≤ (L : ℝ) + 1 := by dsimp only [A]; linarith only [hnorm, hmu0]
  obtain ⟨_hell, _hlogD, Btree, hBtree, hlogBtree, hfamilies⟩ :=
    hconstruct L q Φ h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
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

end PhysicalDGTreePolynomialBond
