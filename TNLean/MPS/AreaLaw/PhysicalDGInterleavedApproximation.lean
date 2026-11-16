/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalDGInterleavedTree
import TNLean.MPS.AreaLaw.PhysicalDGAutomaticRefinement

/-!
# Native MPS and Ritz extraction from the same interleaved tree root

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

open scoped InnerProductSpace TensorProduct ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- The actual interleaved tree and its final refinement use one common
radius. Native MPS representations belong to that same root and to its
literal terminal-space Ritz extraction. All numerical, reference, initial
closeness and trial-energy conditions are derived. Supporting ALVV,
arXiv:1602.08828v2, Figure `fig:merge-prime`, lines 1668–1670,
and `t:alg1`, lines 1809–1817, within the stated quantitative scope. -/
theorem exists_physical_dg_interleaved_tree_ritz_approximation :
    ∃ Ctail C Ktree Kfinal : ℝ,
    21 ≤ Ctail ∧ 21 ≤ C ∧ 0 < Ktree ∧ 0 < Kfinal ∧ ∀ (L q : ℕ),
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
  intro L q h hsupp h0 h1 mu nu gamma hgamma H hH hmu hnu hmunu hgap
    G rG g m w v ell D s a tau epsilon t Delta
  obtain ⟨hell, hD, hs, ha, haSmall, hepsilon, hepsilon1, ht, htail, htradeoff,
    B, hB, hlogB, Utree, hdimUtree, hUMPS, hxiMax, hfamilies⟩ :=
    htree L q h hsupp h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
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
    hrefine L q h hsupp h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
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

end TNLean.MPS.AreaLaw
