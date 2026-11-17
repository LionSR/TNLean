/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ALVV.FrustrationFreeTreeFamily
import TNLean.MPS.AreaLaw.ALVV.UniqueGroundStateTree
import TNLean.MPS.AreaLaw.FullIntervalViability
import TNLean.MPS.AreaLaw.IntervalSamplingTree
import TNLean.MPS.AreaLaw.PhysicalDGAutomaticRefinement
import TNLean.MPS.AreaLaw.PhysicalDGIntervalTrimming
import QICLean.Analysis.ViableNodeLeafCount
import QICLean.Analysis.ViableTrimmingRadius

/-!
# A merge tree of length-independent node dimension for a unique frustration-free ground state

ALVV, arXiv:1602.08828v2, Theorem `t:unique`, lines 1829–1855, treats a frustration-free
nearest-neighbour chain with a unique ground state `Γ` and spectral gap `γ`. Its improvement
over Theorem `t:alg1` is that the viable space at every node of the merge tree has dimension
independent of the chain length.

This file proves that dimension bound with the families of the source. On every long interval
the merge tree uses the frustration-free family of Theorem `t:aisff`, lines 1580–1609, in the
word form of the merge, lines 1662–1677, and in the coordinates of the tree. At every node it
has a `3/200`-viable space for `ℂ Γ` of dimension at most `D⁶ s³`, where `D = (d ℓ²)^{22ℓ}` is
the parameter of Theorem `t:aisff` and `s` depends only on `D` and a sampling parameter `β`;
neither depends on `L`. The literal raw-filter-and-trim iterates of its root give a line
mutually `η/2`-close to `ℂ Γ` of matrix product states.

**Scope restriction (tree witness):** the per-node bound is `D⁶ s³` rather than the source's
`D s²`; the tree is a recursive witness, with no sampling probability; the bond dimension of the
output grows with `L`, through the trimming threshold; and the chain has at least one site and
local dimension at least two. See `docs/paper-gaps/alvv16_unique_ground_state_tree.tex`.
-/

open Matrix
open scoped InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw.ALVV

open TNLean.MPS.AreaLaw TNLean.Lattice

/-- A nonempty chain of local dimension at least two whose kernel is a line has a positive
spectral value above a gap. Auxiliary to ALVV, arXiv:1602.08828v2, Theorem `t:unique`,
lines 1829–1855. -/
theorem exists_pos_mem_spectrum_of_unique_ground_state {L q : ℕ} (hq : 2 ≤ q) (hL : 1 ≤ L)
    {H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ} (hH : H.IsHermitian) {gamma : ℝ}
    (hgamma : 0 < gamma) (Γ : EuclideanSpace ℂ (Fin L → Fin q))
    (huniq : ∀ x : EuclideanSpace ℂ (Fin L → Fin q), H *ᵥ x.ofLp = 0 → x ∈ ℂ ∙ Γ)
    (hgap : ∀ z ∈ spectrum ℝ H, z = 0 ∨ gamma ≤ z) :
    ∃ nu ∈ spectrum ℝ H, 0 < nu := by
  by_contra hnot
  push Not at hnot
  have hzero : hH.eigenvalues = 0 := by
    funext j
    have hmem := hH.eigenvalues_mem_spectrum_real j
    rcases hgap _ hmem with h | h
    · exact h
    · exact absurd (hnot _ hmem) (not_le.mpr (hgamma.trans_le h))
  have hH0 : H = 0 := hH.eigenvalues_eq_zero_iff.mp hzero
  have htop : (⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) ≤ ℂ ∙ Γ := by
    intro x _
    exact huniq x (by simp [hH0])
  have hle := Submodule.finrank_mono htop
  rw [finrank_top, finrank_euclideanSpace, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin] at hle
  have hspan : Module.finrank ℂ (ℂ ∙ Γ) ≤ 1 := by
    simpa using finrank_span_le_card (R := ℂ) ({Γ} : Set (EuclideanSpace ℂ (Fin L → Fin q)))
  have hpow : q ≤ q ^ L := Nat.le_self_pow (by omega) q
  omega

open Classical in
/-- **The merge tree with the frustration-free family for a unique ground state.** Let
`H = ∑ hᵢ` be a nearest-neighbour chain of `L ≥ 1` sites of local dimension `q ≥ 2` with
`0 ≤ hᵢ ≤ 1`, frustration free with ground state `Γ ≠ 0` (`H Γ = 0`), unique (every vector of
the kernel is a multiple of `Γ`), and with spectral gap `γ > 0` (every other spectral value is
at least `γ`). With the universal constant `A ≥ 1` of Theorem `t:aisff`, put `g = min (γ, 1)`,
`d = max (q, 2)`, `u = 1 + log d + log (1/g)`, `ℓ = ⌈A u² / g⌉`, `D = (d ℓ²)^{22ℓ}` and leaf width
`4ℓ`. On every long interval the frustration-free family of Theorem `t:aisff` is fixed: at most
`D²` operators, each of operator Schmidt rank at most `(d² + 4)^{ℓ² + 1}` at every cut. For every
`η > 0` and `0 < β < 1`, with `s = ⌈4096 (1 + log D + log (1/β))⌉` and `count = D⁶ s³`, there is
a merge tree whose long parents are literal sampled-and-trimmed merges with these families,
whose node spaces are all `3/200`-viable for `ℂ Γ` of dimension at most `count`, and whose root,
after its raw-filter-and-trim iterates and Ritz extraction, gives a line mutually `η/2`-close to
`ℂ Γ` of matrix product states. Neither `D` nor `count` depends on `L`.

Existence form of ALVV, arXiv:1602.08828v2, Theorem `t:unique`, lines 1829–1855, under the
scope restriction of this module; the running time is not formalized. -/
theorem exists_unique_ground_state_tree_ritz_approximation :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (L q : ℕ), 2 ≤ q → 1 ≤ L →
    ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
      (_hsupp : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
        (h i) (interval L i.val (i.val + 2)))
      (h0 : ∀ i, 0 ≤ h i) (_h1 : ∀ i, h i ≤ 1) (gamma : ℝ), 0 < gamma →
    ∀ Γ : EuclideanSpace ℂ (Fin L → Fin q),
    let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i, h i
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    Γ ≠ 0 → H *ᵥ Γ.ofLp = 0 →
    (∀ x : EuclideanSpace ℂ (Fin L → Fin q), H *ᵥ x.ofLp = 0 → x ∈ ℂ ∙ Γ) →
    (∀ z ∈ spectrum ℝ H, z = 0 ∨ gamma ≤ z) →
    let G := ℂ ∙ Γ
    let g := min gamma 1
    let Kraw := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) (1 - ‖H‖⁻¹ • H)
    let d := max q 2
    let u : ℝ := 1 + Real.log (d : ℝ) + Real.log (1 / g)
    let ℓ : ℕ := ⌈A * u ^ 2 / g⌉₊
    let D : ℕ := (d * ℓ ^ 2) ^ (22 * ℓ)
    let width := 4 * ℓ
    ∃ hwidth : 1 ≤ width,
    ∃ (Nfam : LongIntervalIndex L width → ℕ)
      (W : ∀ J : LongIntervalIndex L width, Fin (Nfam J) →
        Matrix (interval L J.val.1 J.val.2 → Fin q) (interval L J.val.1 J.val.2 → Fin q) ℂ),
      (∀ J, Nfam J ≤ D ^ 2) ∧
      (∀ J j c, operatorSchmidtRank ((W J j).reindex
        (sheetSplit q (Finset.univ.filter fun v : ↥(interval L J.val.1 J.val.2) ↦
          (v : Fin L) ∈ interval L 0 c))
        (sheetSplit q (Finset.univ.filter fun v : ↥(interval L J.val.1 J.val.2) ↦
          (v : Fin L) ∈ interval L 0 c))) ≤ (d ^ 2 + 4) ^ (ℓ ^ 2 + 1)) ∧
      let F := fun (J : LongIntervalIndex L width) (j : Fin (Nfam J)) ↦
        Matrix.toEuclideanCLM (𝕜 := ℂ) (n := interval L J.val.1 J.val.2 → Fin q) (W J j)
      ∀ eta : ℝ, 0 < eta → ∀ beta : ℝ, 0 < beta → beta < 1 →
      let s := Nat.ceil (4096 * (1 + Real.log (D : ℝ) + Real.log (1 / beta)))
      let count := D ^ 6 * s ^ 3
      ∃ (xi : ℝ) (n Bout : ℕ) (operation : IntervalMergeOperation L q), 0 < xi ∧
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
                (Nat.clog D (D ^ 2 * s)) s xi
                (adjacentIntervalMerge L q J.val.1 k J.val.2 hpk hkr S1 S2) V) ∧
        (∀ p r : ℕ, p ≤ r → r ≤ L →
          let S := balancedIntervalSpace operation width hwidth p r
          Submodule.IsViable (3 / 200 : ℝ) S
            (G.map (Entropy.regionTensorCoordinates q
              (interval L p r)).toLinearEquiv.toLinearMap) ∧
          Module.finrank ℂ S ≤ count) ∧
        let S0 := balancedIntervalSpace operation width hwidth 0 L
        let S := fullIntervalFilterTrimIterate L q Kraw xi S0 n
        let W := nativeFullIntervalSpace L q S
        let R := W.ritzSubspace (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH) 1
        Module.finrank ℂ S ≤ count ∧ R ≤ W ∧ Module.finrank ℂ R = 1 ∧
          Submodule.IsCloseTo (eta / 2) G R ∧ Submodule.IsCloseTo (eta / 2) R G ∧
          ∀ w ∈ R, IsOpenMPS L q Bout (fun x ↦ w x) := by
  classical
  obtain ⟨A, hA, hff⟩ := exists_frustrationFree_improving_family_words_regionTensorCoordinates
  obtain ⟨Kt, -, htrimAll⟩ := exists_physical_dg_interval_collective_trimming_bound
  obtain ⟨Kref, -, hrefine⟩ := exists_physical_dg_automatic_same_candidate_refinement
  refine ⟨A, hA, ?_⟩
  intro L q hq hL h hsupp h0 h1 gamma hgamma Γ H hH hΓ0 hΓ huniq hgap
    G g Kraw d u ℓ D width
  obtain ⟨nu, hnu, hnu0⟩ :=
    exists_pos_mem_spectrum_of_unique_ground_state hq hL hH hgamma Γ huniq hgap
  have hGeq := spectralSpanLE_zero_eq_span_singleton hH hgamma Γ hΓ huniq hgap
  have hmu := zero_mem_spectrum_of_mulVec_eq_zero hH hgamma Γ hΓ0 hΓ hgap
  have hgap' : ∀ z ∈ spectrum ℝ H, z = 0 ∨ 0 + gamma ≤ z := by
    simpa only [zero_add] using hgap
  have hrank : Module.finrank ℂ (ℂ ∙ Γ) = 1 := finrank_span_singleton hΓ0
  have hdq : d = q := max_eq_left hq
  have hg : 0 < g := lt_min hgamma one_pos
  have hg1 : g ≤ 1 := min_le_right gamma 1
  have hu : 1 ≤ u := by
    have h2 : (1 : ℝ) ≤ d := by exact_mod_cast (le_max_right q 2).trans' (by norm_num)
    have := Real.log_nonneg h2
    have := Real.log_nonneg (one_le_one_div hg hg1)
    dsimp only [u]
    linarith
  have hℓ : 1 ≤ ℓ := by
    apply Nat.one_le_iff_ne_zero.mpr
    apply ne_of_gt
    apply Nat.ceil_pos.mpr
    have hu2 : 1 ≤ u ^ 2 := one_le_pow₀ hu
    have : 0 < A * u ^ 2 := by positivity
    positivity
  have hd2 : 2 ≤ d := le_max_right q 2
  have hD : 2 ≤ D := by
    have hbase : 2 ≤ d * ℓ ^ 2 :=
      hd2.trans (by simpa only [mul_one] using Nat.mul_le_mul_left d (Nat.one_le_pow 2 ℓ hℓ))
    exact Nat.one_lt_pow (by omega) (by omega)
  have hwidth : 1 ≤ width := by simp only [width]; omega
  refine ⟨hwidth, ?_⟩
  have hfam : ∀ J : LongIntervalIndex L width, ∃ (N : ℕ)
      (W : Fin N → Matrix (interval L J.val.1 J.val.2 → Fin q)
        (interval L J.val.1 J.val.2 → Fin q) ℂ) (Δ : ℝ),
      N ≤ D ^ 2 ∧ 0 < Δ ∧ (D : ℝ) ^ 12 * Δ ≤ 1 / 100000 ∧
      (∀ j c, operatorSchmidtRank ((W j).reindex
        (sheetSplit q (Finset.univ.filter fun v : ↥(interval L J.val.1 J.val.2) ↦
          (v : Fin L) ∈ interval L 0 c))
        (sheetSplit q (Finset.univ.filter fun v : ↥(interval L J.val.1 J.val.2) ↦
          (v : Fin L) ∈ interval L 0 c))) ≤ (d ^ 2 + 4) ^ (ℓ ^ 2 + 1)) ∧
      ∀ (k : ℕ) (S : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)))
        (δ : ℝ),
        Submodule.IsViable δ S (G.map (Entropy.regionTensorCoordinates q
          (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap) → δ < 1 →
        Submodule.IsViable (Δ ^ k / (1 - δ) ^ 2)
          (⨆ w : Fin k → Fin N, S.map ((List.ofFn fun j ↦
            Matrix.toEuclideanCLM (𝕜 := ℂ) (n := interval L J.val.1 J.val.2 → Fin q)
              (W (w j))).prod :
              EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →ₗ[ℂ]
                EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)))
          (G.map (Entropy.regionTensorCoordinates q
            (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap) := fun J ↦
    (hff L q J.val.1 J.val.2 J.property.1 J.property.2.1 h hsupp h0 h1 gamma hgamma Γ
      hΓ huniq hgap).2.2
  choose Nfam W Δ hN hΔ hbudget hrankW himprove using hfam
  refine ⟨Nfam, W, hN, hrankW, ?_⟩
  intro F eta heta beta hbeta hbeta1 s count
  have hrankG : Module.finrank ℂ G = 1 := hrank
  have hG : G ≠ ⊥ := (Submodule.span_singleton_eq_bot.not).mpr hΓ0
  -- the reference for collective trimming, at the error `1/10000`
  obtain ⟨Btree, hBtree, -, htrim⟩ := htrimAll L q h hsupp h0 h1 0 nu gamma hgamma hmu hnu
    hnu0 hgap' (1 / 10000) (by norm_num) (by norm_num)
  dsimp only at htrim
  rw [hGeq, hrank] at htrim
  -- the final refinement, before the tree
  have key := hrefine L q h hsupp h0 h1 0 nu gamma hgamma hmu hnu hnu0 hgap' Btree D hBtree
    (by omega) eta heta
  dsimp only at key
  rw [hGeq, hrank] at key
  obtain ⟨B, -, -, -, -, -, -, -, hxi, hxiTree, -, hterminal⟩ := key
  set xi := 1 / (1000 * (((max Btree (1 ^ 2 * B)) * ⌈100 * (D : ℝ) ^ 12 /
    (gamma / (‖∑ i, h i‖ - 0) * (eta * gamma / (2 * (‖∑ i, h i‖ - 0) + eta * gamma)))⌉₊ :
      ℕ) : ℝ) * Real.sqrt ((L : ℝ) + 1))
  have hroot1 : 1 ≤ Real.sqrt ((L : ℝ) + 1) := Real.one_le_sqrt.mpr
    (by linarith only [(Nat.cast_nonneg L : (0 : ℝ) ≤ (L : ℝ))])
  have hxi1 : xi ≤ 1 := by
    refine hxiTree.trans ?_
    have hB1 : (1 : ℝ) ≤ Btree := by exact_mod_cast hBtree
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [one_le_mul_of_one_le_of_one_le hB1 hroot1]
  -- sampling size
  obtain ⟨hs1, -, -, -⟩ := Real.viable_node_uniform_sampling_size hD (le_refl 1) hbeta hbeta1.le
  simp only [Nat.cast_one, Real.log_one, add_zero, mul_one] at hs1
  have hleaf : q ^ width ≤ count := by
    have := Nat.viable_tree_leaf_count_le (le_max_left q 2) hd2 hℓ hs1
    simpa only [width, count, D, d] using this
  have htree := exists_balanced_sampled_interval_tree (rG := 1) hwidth (by omega : 1 ≤ q) hD
    le_rfl G hxi hxi1 Nfam F hN hbeta hbeta1
  simp only [Nat.cast_one, Real.log_one, add_zero, mul_one] at htree
  obtain ⟨operation, hliteral, hspaces⟩ := htree hleaf (by
    intro J k hpk hkr S1 S2 hS1 hS2 hd1 hd2'
    obtain ⟨Good, -, hbad, -, himages⟩ :=
      exists_measurable_interval_word_image_event hpk hkr hD hs1 G G hG (le_refl 0)
        (by norm_num) (Submodule.isCloseTo_of_le le_rfl le_rfl)
        (Submodule.isCloseTo_of_le le_rfl le_rfl) (hΔ J).le (hbudget J) (F J) (hN J)
        (fun a S δ hS hδ ↦ himprove J a S δ hS hδ) S1 S2 hS1 hS2 hd1 hd2'
    rw [LinearEquiv.finrank_map_eq, hrankG] at hbad
    simp only [mul_one] at hbad
    refine ⟨Good, hbad, ?_⟩
    intro U hU
    obtain ⟨-, hviableV⟩ := himages U hU
    have hs1R : (1 : ℝ) ≤ s := by exact_mod_cast hs1
    have hden : (1 : ℝ) ≤ (s : ℝ) ^ 2 := one_le_pow₀ hs1R
    have hratio : (1024 / 9 : ℝ) * (1 / 100000) / (s : ℝ) ^ 2 ≤
        (1024 / 9 : ℝ) * (1 / 100000) := by
      apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hden)).mpr
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hden
        (by norm_num : (0 : ℝ) ≤ (1024 / 9 : ℝ) * (1 / 100000))
    have hsmall : Submodule.IsViable (1 / 400 : ℝ)
        (Submodule.sampledWordImage (F J) (Nat.clog D (D ^ 2 * s)) s
          (adjacentIntervalMerge L q J.val.1 k J.val.2 hpk hkr S1 S2) U)
        (G.map (Entropy.regionTensorCoordinates q
          (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap) :=
      hviableV.of_le (by linarith only [hratio])
    have htrimmed := htrim J.val.1 J.val.2 J.property.1 J.property.2.1 _ (1 / 400)
      (by norm_num) xi hxi hsmall
    apply htrimmed.of_le
    have hradius := Real.viable_node_trimming_radius_budget (L := L) (D := Btree)
      (show J.val.2 - J.val.1 - 1 ≤ L by omega) hBtree
    have hbudgetMax := hradius.2
    have hstep : 4 * xi * Real.sqrt (((J.val.2 - J.val.1 - 1 : ℕ) : ℝ) * (Btree : ℝ) ^ 2) ≤
        1 / 250 :=
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxiTree (by norm_num))
        (Real.sqrt_nonneg _)).trans hbudgetMax
    simp only [one_pow, one_mul, Nat.cast_one]
    linarith only [hstep])
  have hroot := hspaces 0 L (Nat.zero_le L) le_rfl
  have hcloseRoot := (isViable_fullInterval_iff_isCloseTo _ G).mp hroot.1
  obtain ⟨-, -, hdimS, hRW, hdimR, hGR, hRG, hmps⟩ := hterminal count _ hroot.2.1 hcloseRoot
  exact ⟨xi, _, _, operation, hxi, hliteral, fun p r hpr hrL ↦
    ⟨(hspaces p r hpr hrL).1, (hspaces p r hpr hrL).2.1⟩, hdimS, hRW, hdimR, hGR, hRG, hmps⟩

end TNLean.MPS.AreaLaw.ALVV
