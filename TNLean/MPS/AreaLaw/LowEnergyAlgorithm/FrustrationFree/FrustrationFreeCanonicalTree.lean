/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.FrustrationFree.FrustrationFreeTree
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.DegenerateGround.DGCanonicalNodeEvent
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTree.CanonicalWordTrimTree

/-!
# Success probability of the merge tree for a unique frustration-free ground state

ALVV, arXiv:1602.08828v2, Theorem `t:unique`, lines 1829–1855, runs the merge tree of
Theorem `t:alg1` with the frustration-free family of Theorem `t:aisff`, lines 1580–1609, sampling
afresh at every merge. This file proves that the randomly sampled tree succeeds on a measurable
event: with one independent rank-independent Haar coordinate for every interval, every node has
dimension at most `count = D^{2k} s ≤ D² s²` for every coordinate, the root and all internal nodes
are `3/200`-viable for `ℂ Γ` outside a set of measure at most `(L - 1) β`, and on the success event
the raw-filter-and-trim iterates of the root with a Ritz extraction give a line of matrix product
states mutually `η/2`-close to `ℂ Γ`. Here `s = ⌈4096 (1 + log D + log (1/β))⌉`. For fixed `β`
neither `D` nor `count` depends on `L`; at a fixed whole-tree failure probability, such as
`β = 1/L²`, `s` and `count` grow like `log L`, so no uniform constant node dimension follows at that
confidence.

**Local fix (sampling parametrization):** in the maintainer's reading of the arXiv v2 text, §6.2,
Theorem 6.1 (`t:alg1`) and its proof state overall success probability at least `1 - 1/n`, derived
by a union bound from a per-merge failure probability at most `1/n²`; Theorem 6.2 (`t:unique`)
states success at least `1 - 1/n`. The bound `(L - 1) β` is that union bound for an arbitrary
per-merge failure `β`; the parameter `β` and the sampling envelope
`s = ⌈4096 (1 + log D + log (1/β))⌉` are a sufficient parametrization chosen by the formalization,
not the source's formula. For `L ≥ 2`, the choice `β = 1/L²` is the source's per-merge bound and
gives overall failure `(L - 1)/L² < 1/L`; for `L ≤ 1` the tree is a single short leaf and the bound
is `0`. The identification of this tree with the source's algorithm, its output and its running time
is not proved. See `docs/paper-gaps/alvv16_unique_ground_state_tree.tex`.

**Local fix (rounding of the number of rounds):** `k = ⌈⌈log_D s⌉ / 2⌉`, as in
`FrustrationFreeTree`; see `docs/paper-gaps/alvv16_unique_ground_state_tree.tex`. The local fixes
of the frustration-free family recorded in `FrustrationFreeTree` (the norm of the replaced chain
and bond dimension, `docs/paper-gaps/alvv16_ff_truncated_norm.tex`, and the viability boundary)
apply unchanged.

**Scope restriction (block leaves and one final trim):** leaves are full blocks of length at most
`4 ℓ`; each long node applies one collective trim after its `k` rounds; the bond dimension of the
output grows with `L`, through the trimming threshold; and the chain has at least one site and
local dimension at least two. See `docs/paper-gaps/alvv16_unique_ground_state_tree.tex`.
-/

open ManyBody (interval)

open Matrix
open scoped BigOperators TensorProduct ComplexOrder MatrixOrder Matrix.Norms.L2Operator ENNReal
open MeasureTheory

namespace TNLean.MPS.AreaLaw.ALVV

open TNLean.MPS.AreaLaw

/-- **Success probability of the merge tree for a unique frustration-free ground state.** Under
the hypotheses and with the parameters of `exists_unique_ground_state_tree_ritz_approximation`,
for every `η > 0` and `0 < β < 1` there are a trimming radius `ξ > 0`, a number of refinement
rounds and an output bond dimension, all fixed before the coordinates, such that the canonical
tree with `k` rounds and one collective trim has every node of dimension at most `count` for
every coordinate, and outside a measurable set of measure at most `(L - 1) β` its root and
internal nodes are `3/200`-viable for `ℂ Γ` and the refinement of its root gives a line of matrix
product states mutually `η/2`-close to `ℂ Γ`.

ALVV, arXiv:1602.08828v2, Theorem `t:unique`, lines 1829–1855, in its probabilistic form, under
the markers of this module; the running time is not formalized. -/
theorem exists_unique_ground_state_canonical_tree_ritz_approximation :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (L q : ℕ), 2 ≤ q → 1 ≤ L →
    ∀ (Φ : ManyBody.BondInteraction L q)
      (h0 : ∀ i, 0 ≤ Φ.term i) (_h1 : ∀ i, Φ.term i ≤ 1) (gamma : ℝ), 0 < gamma →
    ∀ Γ : EuclideanSpace ℂ (Fin L → Fin q),
    let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Φ.hamiltonian
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
        (ManyBody.cutEquiv (fun _ ↦ Fin q)
            (Finset.univ.filter fun v : ↥(interval L J.val.1 J.val.2) ↦
          (v : Fin L) ∈ interval L 0 c))
        (ManyBody.cutEquiv (fun _ ↦ Fin q)
            (Finset.univ.filter fun v : ↥(interval L J.val.1 J.val.2) ↦
          (v : Fin L) ∈ interval L 0 c))) ≤ (d ^ 2 + 4) ^ (ℓ ^ 2 + 1)) ∧
      let F := fun (J : LongIntervalIndex L width) (j : Fin (Nfam J)) ↦
        Matrix.toEuclideanCLM (𝕜 := ℂ) (n := interval L J.val.1 J.val.2 → Fin q) (W J j)
      ∀ eta : ℝ, 0 < eta → ∀ beta : ℝ, 0 < beta → beta < 1 →
      let s := Nat.ceil (4096 * (1 + Real.log (D : ℝ) + Real.log (1 / beta)))
      let k := (Nat.clog D s + 1) / 2
      let count := D ^ (2 * k) * s
      count ≤ D ^ 2 * s ^ 2 ∧
      ∃ (xi : ℝ) (n Bout : ℕ), 0 < xi ∧
        (∀ (U : IntervalSamplingChoices L q) (p r : ℕ), p ≤ r → r ≤ L →
          Module.finrank ℂ (balancedIntervalSpace (canonicalWordTrimOperation Nfam F k s xi U)
            width hwidth p r) ≤ count) ∧
        let Good := canonicalWordTrimTreeGood hwidth Nfam F k s xi G (3 / 200)
        MeasurableSet Good ∧
        intervalSamplingMeasure L q Goodᶜ ≤ ((L - 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal beta ∧
        ∀ U ∈ Good,
          let S0 := balancedIntervalSpace (canonicalWordTrimOperation Nfam F k s xi U)
            width hwidth 0 L
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
  intro L q hq hL Φ h0 h1 gamma hgamma Γ H hH hΓ0 hΓ huniq hgap
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
        (ManyBody.cutEquiv (fun _ ↦ Fin q)
            (Finset.univ.filter fun v : ↥(interval L J.val.1 J.val.2) ↦
          (v : Fin L) ∈ interval L 0 c))
        (ManyBody.cutEquiv (fun _ ↦ Fin q)
            (Finset.univ.filter fun v : ↥(interval L J.val.1 J.val.2) ↦
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
    (hff L q J.val.1 J.val.2 J.property.1 J.property.2.1 Φ h0 h1 gamma hgamma Γ
      hΓ huniq hgap).2.2
  choose Nfam W Δ hN hΔ hbudget hrankW himprove using hfam
  refine ⟨Nfam, W, hN, hrankW, ?_⟩
  intro F eta heta beta hbeta hbeta1 s k count
  have hrankG : Module.finrank ℂ G = 1 := hrank
  have hG : G ≠ ⊥ := (Submodule.span_singleton_eq_bot.not).mpr hΓ0
  -- the reference for collective trimming, at the error `1/10000`
  obtain ⟨Btree, hBtree, -, htrim⟩ := htrimAll L q Φ h0 h1 0 nu gamma hgamma hmu hnu
    hnu0 hgap' (1 / 10000) (by norm_num) (by norm_num)
  dsimp only at htrim
  rw [hGeq, hrank] at htrim
  -- the final refinement, before the tree
  have key := hrefine L q Φ h0 h1 0 nu gamma hgamma hmu hnu hnu0 hgap' Btree D hBtree
    (by omega) eta heta
  dsimp only at key
  rw [hGeq, hrank] at key
  obtain ⟨B, -, -, -, -, -, -, -, hxi, hxiTree, -, hterminal⟩ := key
  set xi := 1 / (1000 * (((max Btree (1 ^ 2 * B)) * ⌈100 * (D : ℝ) ^ 12 /
    (gamma / (‖Φ.hamiltonian‖ - 0) * (eta * gamma / (2 * (‖Φ.hamiltonian‖ - 0) + eta * gamma)))⌉₊ :
      ℕ) : ℝ) * Real.sqrt ((L : ℝ) + 1))
  have hroot1 : 1 ≤ Real.sqrt ((L : ℝ) + 1) := Real.one_le_sqrt.mpr
    (by linarith only [(Nat.cast_nonneg L : (0 : ℝ) ≤ (L : ℝ))])
  have hxi1 : xi ≤ 1 := by
    refine hxiTree.trans ?_
    have hB1 : (1 : ℝ) ≤ Btree := by exact_mod_cast hBtree
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [one_le_mul_of_one_le_of_one_le hB1 hroot1]
  -- sampling size and the number of rounds
  obtain ⟨hs1, -, hfail64, hfailure⟩ :=
    Real.viable_node_uniform_sampling_size hD (le_refl 1) hbeta hbeta1.le
  simp only [Nat.cast_one, Real.log_one, add_zero, mul_one] at hs1 hfail64 hfailure
  have hs2 : 2 ≤ s := by
    have hlogD : 0 ≤ Real.log (D : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ D))
    have hlogb : 0 ≤ Real.log (1 / beta) :=
      Real.log_nonneg (by rw [le_div_iff₀ hbeta]; linarith)
    have hceil := Nat.le_ceil (4096 * (1 + Real.log (D : ℝ) + Real.log (1 / beta)))
    have : (2 : ℝ) ≤ s := le_trans (by nlinarith) hceil
    exact_mod_cast this
  obtain ⟨hk1, hsk, hkD⟩ := merge_rounds_bounds hD hs2
  have hcount2 : count ≤ D ^ 2 * s ^ 2 := by
    calc count = D ^ (2 * k) * s := rfl
      _ ≤ (D ^ 2 * s) * s := Nat.mul_le_mul_right s hkD
      _ = D ^ 2 * s ^ 2 := by ring
  refine ⟨hcount2, ?_⟩
  have hcountsq : count * count ≤ D ^ 12 * s ^ 6 := by
    calc count * count ≤ (D ^ 2 * s ^ 2) * (D ^ 2 * s ^ 2) := Nat.mul_le_mul hcount2 hcount2
      _ = D ^ 4 * s ^ 4 := by ring
      _ ≤ D ^ 12 * s ^ 6 := Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) (by norm_num))
          (Nat.pow_le_pow_right (by omega) (by norm_num))
  have hleaf : q ^ width ≤ count := by
    have hqD : q ^ width ≤ D := by
      calc q ^ width = q ^ (4 * ℓ) := rfl
        _ ≤ q ^ (22 * ℓ) := Nat.pow_le_pow_right (by omega) (by omega)
        _ ≤ (d * ℓ ^ 2) ^ (22 * ℓ) := Nat.pow_le_pow_left
          ((le_max_left q 2).trans (by
            simpa only [mul_one] using Nat.mul_le_mul_left d (Nat.one_le_pow 2 ℓ hℓ))) _
    calc q ^ width ≤ D := hqD
      _ ≤ D ^ (2 * k) := Nat.le_self_pow (by omega) D
      _ ≤ D ^ (2 * k) * s := Nat.le_mul_of_pos_right _ (by omega)
  have hprofile := finrank_balancedIntervalSpace_canonicalWordTrimOperation_le hwidth
    (by omega : 1 ≤ q) Nfam F hN hxi.le hxi1 hleaf le_rfl
  have hself : Submodule.IsCloseTo 0 G G := by
    rw [Submodule.isCloseTo_iff]
    intro t ht
    rw [Submodule.starProjection_eq_self_iff.mpr ht, sub_zero, one_mul]
  -- the fixed-child failure bound of one canonical parent
  have hnode : ∀ (J : LongIntervalIndex L width) (m : ℕ) (hpm : J.val.1 ≤ m)
      (hmr : m ≤ J.val.2)
      (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 m → Fin q)))
      (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L m J.val.2 → Fin q))),
      Submodule.IsViable (3 / 200 : ℝ) S1
        (G.map (Entropy.regionTensorCoordinates q
          (interval L J.val.1 m)).toLinearEquiv.toLinearMap) →
      Submodule.IsViable (3 / 200 : ℝ) S2
        (G.map (Entropy.regionTensorCoordinates q
          (interval L m J.val.2)).toLinearEquiv.toLinearMap) →
      Module.finrank ℂ S1 ≤ count → Module.finrank ℂ S2 ≤ count →
      Matrix.rankUnitaryHaar (Fintype.card (interval L J.val.1 J.val.2 → Fin q))
        {v | ¬Submodule.IsViable (3 / 200 : ℝ)
          (canonicalSampledIntervalWordTrim L q J.val.1 J.val.2 (F J) k s xi
            (adjacentIntervalMerge L q J.val.1 m J.val.2 hpm hmr S1 S2) v)
          (G.map (Entropy.regionTensorCoordinates q
            (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap)} ≤
        ENNReal.ofReal beta := by
    intro J m hpm hmr S1 S2 hS1 hS2 hd1 hd2'
    have hbad := rankUnitaryHaar_canonical_interval_word_image_failure_le hpm hmr hD
      (by omega : 1 ≤ s) hk1 hsk G G hG (by norm_num : (0 : ℝ) ≤ 1 / 10000) hself hself
      (hΔ J).le (hbudget J) (F J) (fun a S δ hS hδ ↦ himprove J a S δ hS hδ)
      S1 S2 hS1 hS2 hd1 hd2'
    dsimp only at hbad
    simp only [LinearEquiv.finrank_map_eq, hrankG, mul_one, add_zero] at hbad
    have hQ : Module.finrank ℂ (adjacentIntervalMerge L q J.val.1 m J.val.2 hpm hmr S1 S2) ≤
        D ^ 12 * s ^ 6 :=
      calc _ ≤ Module.finrank ℂ S1 * Module.finrank ℂ S2 :=
            finrank_adjacentIntervalMerge_le hpm hmr S1 S2
        _ ≤ count * count := Nat.mul_le_mul hd1 hd2'
        _ ≤ D ^ 12 * s ^ 6 := hcountsq
    refine (measure_mono ?_).trans
      (hbad.trans (ENNReal.ofReal_le_ofReal ((hfailure _ hQ).trans hfail64)))
    intro v hfail himage
    apply hfail
    have hsmall : Submodule.IsViable (1 / 400 : ℝ)
      (⨆ i, (canonicalIntervalRangeSample L q J.val.1 J.val.2 s
          (adjacentIntervalMerge L q J.val.1 m J.val.2 hpm hmr S1 S2) v).map
          (wordFamily (F J) k i).toLinearMap)
        (G.map (Entropy.regionTensorCoordinates q
          (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap) := by
      rw [iSup_map_wordFamily]
      exact himage.of_le (by norm_num)
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
    linarith only [hstep]
  have hmeas := measurableSet_canonicalWordTrimTreeGood hwidth Nfam F k s xi G (3 / 200)
  have hprob := intervalSamplingMeasure_canonicalWordTrimTreeGood_compl_le hwidth
    (by omega : 1 ≤ q) Nfam F hN hxi.le hxi1 hleaf le_rfl G (by norm_num : (0 : ℝ) ≤ 3 / 200)
    (ENNReal.ofReal beta) hnode
  exact ⟨xi, _, _, hxi, hprofile, hmeas, hprob, fun U hU ↦
    have hroot := hterminal count _ (hprofile U 0 L (Nat.zero_le L) le_rfl)
      ((isViable_fullInterval_iff_isCloseTo _ G).mp hU.1)
    ⟨hroot.2.2.1, hroot.2.2.2.1, hroot.2.2.2.2.1, hroot.2.2.2.2.2.1, hroot.2.2.2.2.2.2.1,
      hroot.2.2.2.2.2.2.2⟩⟩

end TNLean.MPS.AreaLaw.ALVV
