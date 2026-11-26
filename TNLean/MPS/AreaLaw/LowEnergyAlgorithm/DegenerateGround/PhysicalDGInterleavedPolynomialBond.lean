/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.Parameter.InterleavedOutputPolynomialBound
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.DegenerateGround.PhysicalDGInterleavedNode
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.DegenerateGround.PhysicalDGFilterTrimming

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

It also contains the following results.

* `TNLean.MPS.AreaLaw.exists_physical_dg_interleaved_tree_ritz_approximation`: native MPS and Ritz
  extraction from the same interleaved tree root.
-/

open ManyBody (interval)
open scoped InnerProductSpace TensorProduct ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

section PhysicalDGInterleavedApproximation

/-!
## Native MPS and Ritz extraction from the same interleaved tree root

The common radius is chosen first, then the actual interleaved tree is
constructed at that radius. Its full-interval root is read in native chain
coordinates and refined by literal raw-filter and collective-trim iterates.
The final output is the compressed Ritz space of that actual terminal space.
Both the initial root and final output retain an all-span MPS bound, including
the extra recorded-generator factor. No independent MPS approximant or older
one-final-trim tree is substituted.

This supports ALVV, arXiv:1602.08828v2, Figure `fig:merge-prime`,
lines 1668–1670, and final refinement, lines 1809–1817.

**Scope restriction (interleaved witness tree and quantitative profile):**
The full leaves have length at most `4 * ell`, the fixed nominal sample scale
uses `(L+1)^(-2)`, the count depends on length and ground multiplicity, and
the reference estimates use `min gamma 1`. The larger integer parent count
and these distinctions are documented in
`docs/paper-gaps/alvv16_approximation_parameters.tex`. No adaptive probability,
source energy-estimation invariant or running-time claim is made.

**Local fix (normalized final gain):** The final raw-filter count is explicit
in the projection target `rho`, and is not identified with the printed count.
See `docs/paper-gaps/alvv16_final_filter_gain.tex`.
-/

/-- The actual interleaved tree and its final refinement use one common
radius. Native MPS representations belong to that same root and to its
literal terminal-space Ritz extraction. All numerical, reference, initial
closeness and trial-energy conditions are derived. Supporting ALVV,
arXiv:1602.08828v2, Figure `fig:merge-prime`, lines 1668–1670,
and `t:alg1`, lines 1809–1817, within the stated quantitative scope. -/
theorem exists_physical_dg_interleaved_tree_ritz_approximation :
    ∃ Ctail C Ktree Kfinal : ℝ,
    21 ≤ Ctail ∧ 21 ≤ C ∧ 0 < Ktree ∧ 0 < Kfinal ∧ ∀ (L q : ℕ),
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
        Ktree * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * bref ^ (3 / 4 : ℝ) * u) *
          (1 + Real.log bref) ∧
    ∃ U : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)),
      Module.finrank ℂ U = rG ∧
      (∀ z ∈ U, IsOpenMPS L q (rG ^ 2 * B) (fun x ↦ z x)) ∧
    let Dref := rG ^ 2 * B
    let xiMax := a / (256 * (Dref : ℝ) * Real.sqrt ((L : ℝ) + 1))
    0 < xiMax ∧
    let width := 4 * ell
    ∃ hwidth : 1 ≤ width,
    ∃ (N : LongIntervalIndex L width → ℕ)
      (F : ∀ J : LongIntervalIndex L width,
        Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
          EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)),
      (∀ J, N J ≤ D ^ 2) ∧
      let Ntree := Nat.ceil (1 / a)
      let ETree := Dref * Ntree
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
      let Dcommon := max ETree b
      let Nfinal := Nat.ceil (100 * (D : ℝ) ^ 12 / (c * rho))
      let xi := 1 / (1000 * ((Dcommon * Nfinal : ℕ) : ℝ) * Real.sqrt ((L : ℝ) + 1))
      ∃ Ufinal : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)),
        Module.finrank ℂ Ufinal = rG ∧
        Submodule.IsCloseTo epsilonFinal Ufinal G ∧ Submodule.IsCloseTo epsilonFinal G Ufinal ∧
        (∀ z ∈ Ufinal, IsOpenMPS L q b (fun x ↦ z x)) ∧
        0 < xi ∧ xi ≤ xiMax ∧
        Real.sqrt ((L : ℝ) * (rG : ℝ) * (b : ℝ)) * xi <
          eta / (10000 * (D : ℝ) ^ 12) ∧
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
          ∃ V : Matrix.unitaryGroup
            (Fin (Module.finrank ℂ (adjacentIntervalMerge L q
              J.val.1 k J.val.2 hpk hkr S1 S2))) ℂ,
            operation J.val.1 k J.val.2 hpk hkr S1 S2 =
              sampledIntervalInterleavedTrim L q J.val.1 J.val.2 D s (F J) xi
                (adjacentIntervalMerge L q J.val.1 k J.val.2 hpk hkr S1 S2) V) ∧
        let S0 := balancedIntervalSpace operation width hwidth 0 L
        let W0 := nativeFullIntervalSpace L q S0
        let bond := 1000000 * (Dcommon * Nfinal) ^ 2 * (L + 1) * (D ^ 6 * s ^ 3) ^ 2
        Submodule.IsCloseTo (3 / 200 : ℝ) W0 G ∧
        (∀ z ∈ W0, IsOpenMPS L q bond (fun x ↦ z x)) ∧
        let S := fullIntervalFilterTrimIterate L q Kraw xi S0 n
        let W := nativeFullIntervalSpace L q S
        let R := W.ritzSubspace (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH) rG
        0 < n ∧ Submodule.IsCloseTo rho W G ∧ Module.finrank ℂ S ≤ D ^ 6 * s ^ 3 ∧
          R ≤ W ∧ Module.finrank ℂ R = rG ∧
          Submodule.IsCloseTo (eta / 2) G R ∧ Submodule.IsCloseTo (eta / 2) R G ∧
          ∀ z ∈ R, IsOpenMPS L q bond (fun x ↦ z x) := by
  classical
  obtain ⟨Ctail, C, Ktree, hCtail, hC, hKtree, htree⟩ :=
    exists_physical_dg_interleaved_interval_tree
  obtain ⟨Kfinal, hKfinal, hrefine⟩ := exists_physical_dg_automatic_same_candidate_refinement
  refine ⟨Ctail, C, Ktree, Kfinal, hCtail, hC, hKtree, hKfinal, ?_⟩
  intro L q Φ h0 h1 mu nu gamma hgamma H hH hmu hnu hmunu hgap
    G rG g m w v ell D s a tau epsilon t Delta
  obtain ⟨hell, hD, hs, ha, haSmall, hepsilon, hepsilon1, ht, htail, htradeoff,
    B, hB, hlogB, Utree, hdimUtree, hUMPS, hxiMax, hfamilies⟩ :=
    htree L q Φ h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
  refine ⟨hell, hD, hs, ha, haSmall, hepsilon, hepsilon1, ht, htail, htradeoff, ?_⟩
  intro u bref
  refine ⟨B, hB, hlogB, Utree, hdimUtree, hUMPS, ?_⟩
  intro Dref xiMax
  refine ⟨hxiMax, ?_⟩
  intro width
  obtain ⟨hwidth, Nfam, F, hNfam, hparents⟩ := hfamilies
  refine ⟨hwidth, Nfam, F, hNfam, ?_⟩
  intro Ntree ETree A c Kraw eta heta rho n epsilonFinal bfinal
  have hrG : 1 ≤ rG := Submodule.one_le_finrank_iff.mpr
    (hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl)
  have hDref : 1 ≤ Dref := by
    simpa only [Dref, one_mul] using Nat.mul_le_mul (Nat.one_le_pow 2 rG hrG) hB
  have hNtree : 1 ≤ Ntree := Nat.one_le_ceil_iff.mpr (one_div_pos.mpr ha)
  have hETree : 1 ≤ ETree := by simpa only [ETree, one_mul] using Nat.mul_le_mul hDref hNtree
  have hD1 : 1 ≤ D := (by decide : 1 ≤ 2).trans hD
  have hNtreeR : 1 / a ≤ (Ntree : ℝ) := Nat.le_ceil _
  have haN : 1 ≤ a * (Ntree : ℝ) := by
    have hb := (div_le_iff₀ ha).mp hNtreeR
    nlinarith only [hb]
  have hDref0 : (0 : ℝ) < Dref := by exact_mod_cast (show 0 < Dref by omega)
  have hNtree0 : (0 : ℝ) < Ntree := by exact_mod_cast (show 0 < Ntree by omega)
  have hroot : 0 < Real.sqrt ((L : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have hradius : 1 / (1000 * (ETree : ℝ) * Real.sqrt ((L : ℝ) + 1)) ≤ xiMax := by
    dsimp only [ETree, xiMax]
    simp only [Nat.cast_mul]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hb := mul_le_mul_of_nonneg_right haN (mul_pos hDref0 hroot).le
    nlinarith only [hb, (mul_pos hDref0 hroot).le]
  obtain ⟨Bfinal, hBfinal, hlogBfinal, hfinal⟩ :=
    hrefine L q Φ h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
      ETree D hETree hD1 eta heta
  refine ⟨Bfinal, hBfinal, hlogBfinal, ?_⟩
  intro b Dcommon Nfinal xi
  obtain ⟨Ufinal, hdimUfinal, hUG, hGU, hUfinalMPS, hxi, hxiCoarse, hxiSource, hterminal⟩ :=
    hfinal
  have hxiTree : xi ≤ xiMax := hxiCoarse.trans hradius
  refine ⟨Ufinal, hdimUfinal, hUG, hGU, hUfinalMPS, hxi, hxiTree, hxiSource, ?_⟩
  obtain ⟨operation, hspaces, hliteral⟩ := hparents xi hxi hxiTree
  refine ⟨operation, hspaces, hliteral, ?_⟩
  intro S0 W0 bond
  have hroot := hspaces 0 L (Nat.zero_le L) le_rfl
  have hcloseRoot : Submodule.IsCloseTo (3 / 200 : ℝ) W0 G :=
    (isViable_fullInterval_iff_isCloseTo S0 G).mp hroot.1
  have hEN : 1 ≤ Dcommon * Nfinal := by
    by_contra hneg
    have hz : Dcommon * Nfinal = 0 := by omega
    have hxiZero : xi = 0 := by simp only [xi, hz, Nat.cast_zero, mul_zero, zero_mul, div_zero]
    exact hxi.ne' hxiZero
  have hrootMPS : ∀ z ∈ W0, IsOpenMPS L q bond (fun x ↦ z x) := by
    intro z hz
    exact isOpenMPS_of_mem_nativeFullIntervalSpace_of_trimming_rank_bound hEN hroot.2.2 hz
  refine ⟨hcloseRoot, hrootMPS, ?_⟩
  exact hterminal (D ^ 6 * s ^ 3) S0 hroot.2.1 hcloseRoot

end PhysicalDGInterleavedApproximation

section PhysicalDGInterleavedPolynomialBond

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
  intro L Φ h0 h1 mu nu H hH hmu hnu hmunu hgap G r eta heta
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
    hconstruct L q Φ h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
  have hD : 1 ≤ D := (by decide : 1 ≤ 2).trans hD2
  obtain ⟨_hw, _hs, hsUpper, _hsLog⟩ := Real.interleaved_sample_size_bounds r L D hr hD2
  obtain ⟨_hM, hA, _hc, hc1, _hfix, _hKGo, _hhigh⟩ :=
    physical_dg_normalized_ground_filter_spec Φ h0 mu nu gamma hgamma hmu hnu hmunu hgap
  change 0 < A at hA
  have hgammaA : gamma ≤ A := (div_le_one hA).mp hc1
  have hmu0 : 0 ≤ mu := spectrum_nonneg_of_nonneg
    (show 0 ≤ H from Finset.sum_nonneg fun i _ ↦ h0 i) hmu
  have hnorm : ‖H‖ ≤ (L : ℝ) + 1 := by
    have hb : ‖H‖ ≤ ((L - 1 : ℕ) : ℝ) := by
      simpa [H, ManyBody.Interaction.hamiltonian] using
        norm_sum_le_of_le (Finset.univ : Finset (Fin (L - 1)))
          (fun i _ ↦ (CStarAlgebra.norm_le_one_iff_of_nonneg (Φ.term i) (h0 i)).mpr (h1 i))
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
          ∀ z ∈ R, IsOpenMPS L q B (fun x ↦ z x) := by
  obtain ⟨_Cdegree, _hCdegree, houtput⟩ :=
    exists_physical_dg_interleaved_ritz_polynomial_approximation_with_degree
  obtain ⟨C, hC, k, _hk, hbound⟩ := houtput q gamma hgamma
  exact ⟨C, hC, k, hbound⟩

end PhysicalDGInterleavedPolynomialBond

end TNLean.MPS.AreaLaw
