/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalDGSampledNode
import TNLean.MPS.AreaLaw.IntervalSamplingTree
import QICLean.Analysis.ViableTrimmingRank
import QICLean.Analysis.ViableNodeLeafCount

/-!
# An actual recursive viable tree for the full physical ground space

The Hamiltonian chooses the common reference and one improving family for
every long parent before the sampling size and child spaces. Positive
fixed-input Haar success events select literal sampled-word images and
collective trims. A balanced recursion then gives viable spaces for the
same original full ground space, with explicit recorded-generator counts
and internal-cut ranks.

**Scope restriction (block leaves, one final trim and capped gap):** The
leaf width is `4 * ell`; long nodes use one final collective trim after the
word images. Independent scalar tail/filter conditions and `min gamma 1`
remain explicit, as documented in
`docs/paper-gaps/alvv16_approximation_parameters.tex`. This is a recursive
witness theorem, not the unrestricted printed algorithm or its runtime.
No measurable dependence on earlier choices, joint adaptive success bound,
low-density construction or final spectral extraction is asserted.
-/

open Matrix
open scoped BigOperators TensorProduct ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- Construct actual recursively selected interval spaces from the original
nearest-neighbour Hamiltonian. Every long parent uses one fixed family
chosen before all sampling sizes and child spaces. The recorded vectors
have the displayed count and weighted rank bounds for every positive
radius below the common reference bound; these are not assigned to every
vector in their span. Supporting ALVV, arXiv:1602.08828v2, `t:alg1`,
lines 1777–1817. The stated block-leaf and scalar scope is explicit. -/
theorem exists_physical_dg_recursive_interval_spaces_of_le_radius :
    ∃ K : ℝ, 0 < K ∧ ∀ (L q : ℕ),
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
    let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
    let epsilonRef : ℝ := 1 / 10000
    let b := 16 + Real.log (1 / g) +
      Real.log (32 * (rG : ℝ) * ((L : ℝ) + 1) / epsilonRef)
    ∃ B : ℕ, 1 ≤ B ∧
    Real.log (B : ℝ) ≤
      K * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) * u) *
        (1 + Real.log b) ∧
    let Dref := rG ^ 2 * B
    let xiMax := 1 / (1000 * (Dref : ℝ) * Real.sqrt ((L : ℝ) + 1))
    ∀ (m ell : ℕ) (t Delta : ℝ), q ≤ m → 50 ≤ m → ∀ (_hell : 1 ≤ ell), 21 ≤ t →
    (288 * Real.exp (11 / 8)) * Real.exp (-(t - g) / 8) ≤
      (1 / (m : ℝ)) * g / 1000000 →
    (∀ R : ℝ, 0 < R → R ≤ 3 * t + 4 * (ell : ℝ) →
      (2 * Real.exp (-2 * (ell : ℝ) ^ 2 * Real.sqrt ((4 * g / 5) / R))) ^ 2 ≤ Delta) →
    let D := (m * ell ^ 2) ^ (22 * ell)
    (D : ℝ) ^ 12 * Delta ≤ 1 / 100000 →
    let width := 4 * ell
    let hwidth : 1 ≤ width := by omega
    ∃ (N : LongIntervalIndex L width → ℕ)
      (F : ∀ J : LongIntervalIndex L width,
        Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
          EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)),
      (∀ J, N J ≤ D ^ 2) ∧
      ∀ xi : ℝ, 0 < xi → xi ≤ xiMax →
      ∀ (beta : ℝ), 0 < beta → beta < 1 →
      let A := 1 + Real.log (rG : ℝ) + Real.log (D : ℝ) + Real.log (1 / beta)
      let s := Nat.ceil (4096 * (rG : ℝ) * A)
      let count := D ^ 6 * s ^ 3
      (s : ℝ) ≤ 4097 * (rG : ℝ) * A ∧
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
          ∃ U : Matrix.unitaryGroup
            (Fin (Module.finrank ℂ (adjacentIntervalMerge L q
              J.val.1 k J.val.2 hpk hkr S1 S2))) ℂ,
            operation J.val.1 k J.val.2 hpk hkr S1 S2 =
              sampledIntervalTrim L q J.val.1 J.val.2 (F J) (Nat.clog D (D ^ 2 * s)) s xi
                (adjacentIntervalMerge L q J.val.1 k J.val.2 hpk hkr S1 S2) U) ∧
        ∀ (p r : ℕ), p ≤ r → r ≤ L →
          let S := balancedIntervalSpace operation width hwidth p r
          Submodule.IsViable (3 / 200 : ℝ) S
            (G.map (Entropy.regionTensorCoordinates q
              (interval L p r)).toLinearEquiv.toLinearMap) ∧
          Module.finrank ℂ S ≤ count ∧
          IsIntervalSpanWithRankBound L q p r count xi S := by
  classical
  obtain ⟨K, hK, hphysical⟩ := exists_physical_dg_sampled_interval_node_event_of_le_radius
  refine ⟨K, hK, ?_⟩
  intro L q h hsupp h0 h1 mu nu gamma hgamma H hH hmu hnu hmunu hgap
    G rG g u epsilonRef b
  obtain ⟨B, hB, hlogB, hNodes⟩ :=
    hphysical L q h hsupp h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
  refine ⟨B, hB, hlogB, ?_⟩
  intro Dref xiMax m ell t Delta hqm hm hell ht htail hfilter D htrade width hwidth
  have hG : G ≠ ⊥ := hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl
  have hrG : 1 ≤ rG := Submodule.one_le_finrank_iff.mpr hG
  have hq : 1 ≤ q := (by decide : 1 ≤ 2).trans
    (hH.two_le_local_dimension_of_two_spectral_values hmu hnu (ne_of_lt hmunu))
  have hDref : 1 ≤ Dref := by
    dsimp only [Dref]
    simpa only [one_mul] using Nat.mul_le_mul (Nat.one_le_pow 2 rG hrG) hB
  have hxiMax1 : xiMax ≤ 1 := by
    have hDrefR : (1 : ℝ) ≤ Dref := by exact_mod_cast hDref
    have hroot : 1 ≤ Real.sqrt ((L : ℝ) + 1) := Real.one_le_sqrt.mpr
      (by linarith only [(Nat.cast_nonneg L : (0 : ℝ) ≤ (L : ℝ))])
    have hprod := one_le_mul_of_one_le_of_one_le hDrefR hroot
    dsimp only [xiMax]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [hprod]
  have hell2 : 1 ≤ ell ^ 2 := Nat.one_le_pow 2 ell hell
  have hmBase : m ≤ m * ell ^ 2 := by
    simpa only [mul_one] using Nat.mul_le_mul_left m hell2
  have hbase : 2 ≤ m * ell ^ 2 := (by omega : 2 ≤ m).trans hmBase
  have hD : 2 ≤ D := Nat.one_lt_pow (by omega : 22 * ell ≠ 0) (by omega)
  have hfamilies := fun J : LongIntervalIndex L width ↦
    hNodes m ell t Delta hqm hm hell ht htail hfilter htrade
      J.val.1 J.val.2 J.property.1 J.property.2.1 J.property.2.2
  choose T N F hN _hdim hEvents using hfamilies
  refine ⟨N, F, hN, ?_⟩
  intro xi hxi hxiMax beta hbeta hbeta1 A s count
  have hxi1 : xi ≤ 1 := hxiMax.trans hxiMax1
  obtain ⟨hs, hscount, _htail, _hfailure⟩ :=
    Real.viable_node_uniform_sampling_size hD hrG hbeta hbeta1.le
  have hleaf : q ^ width ≤ count :=
    Nat.viable_tree_leaf_count_le hqm (by omega) hell hs
  have hselected := exists_balanced_sampled_interval_tree hwidth hq hD hrG G hxi hxi1
    N F hN hbeta hbeta1
  obtain ⟨operation, hliteral, htree⟩ := hselected hleaf (by
    intro J k hpk hkr S1 S2 hS1 hS2 hd1 hd2
    obtain ⟨Good, _hGood, hbad, _hprob, hout⟩ :=
      hEvents J xi hxi hxiMax k s hpk hkr hs S1 S2 hS1 hS2 hd1 hd2
    refine ⟨Good, hbad, ?_⟩
    intro U hU
    exact (hout U hU).2)
  refine ⟨hscount, operation, hliteral, ?_⟩
  intro p r hpr hrL S
  exact htree p r hpr hrL


/-- Construct actual recursively selected interval spaces from the original
nearest-neighbour Hamiltonian. Every long parent uses one fixed family
chosen before all sampling sizes and child spaces. The recorded vectors
have the displayed count and rank bounds; these are not assigned to every
vector in their span. Supporting ALVV, arXiv:1602.08828v2, `t:alg1`,
lines 1777–1817. The stated block-leaf and scalar scope is explicit. -/
theorem exists_physical_dg_recursive_interval_spaces :
    ∃ K : ℝ, 0 < K ∧ ∀ (L q : ℕ),
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
    let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
    let epsilonRef : ℝ := 1 / 10000
    let b := 16 + Real.log (1 / g) +
      Real.log (32 * (rG : ℝ) * ((L : ℝ) + 1) / epsilonRef)
    ∃ B : ℕ, 1 ≤ B ∧
    Real.log (B : ℝ) ≤
      K * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) * u) *
        (1 + Real.log b) ∧
    let Dref := rG ^ 2 * B
    let xi := 1 / (1000 * (Dref : ℝ) * Real.sqrt ((L : ℝ) + 1))
    ∀ (m ell : ℕ) (t Delta : ℝ), q ≤ m → 50 ≤ m → ∀ (_hell : 1 ≤ ell), 21 ≤ t →
    (288 * Real.exp (11 / 8)) * Real.exp (-(t - g) / 8) ≤
      (1 / (m : ℝ)) * g / 1000000 →
    (∀ R : ℝ, 0 < R → R ≤ 3 * t + 4 * (ell : ℝ) →
      (2 * Real.exp (-2 * (ell : ℝ) ^ 2 * Real.sqrt ((4 * g / 5) / R))) ^ 2 ≤ Delta) →
    let D := (m * ell ^ 2) ^ (22 * ell)
    (D : ℝ) ^ 12 * Delta ≤ 1 / 100000 →
    let width := 4 * ell
    let hwidth : 1 ≤ width := by omega
    ∃ (N : LongIntervalIndex L width → ℕ)
      (F : ∀ J : LongIntervalIndex L width,
        Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
          EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)),
      (∀ J, N J ≤ D ^ 2) ∧
      ∀ (beta : ℝ), 0 < beta → beta < 1 →
      let A := 1 + Real.log (rG : ℝ) + Real.log (D : ℝ) + Real.log (1 / beta)
      let s := Nat.ceil (4096 * (rG : ℝ) * A)
      let count := D ^ 6 * s ^ 3
      (s : ℝ) ≤ 4097 * (rG : ℝ) * A ∧
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
          ∃ U : Matrix.unitaryGroup
            (Fin (Module.finrank ℂ (adjacentIntervalMerge L q
              J.val.1 k J.val.2 hpk hkr S1 S2))) ℂ,
            operation J.val.1 k J.val.2 hpk hkr S1 S2 =
              sampledIntervalTrim L q J.val.1 J.val.2 (F J) (Nat.clog D (D ^ 2 * s)) s xi
                (adjacentIntervalMerge L q J.val.1 k J.val.2 hpk hkr S1 S2) U) ∧
        ∀ (p r : ℕ), p ≤ r → r ≤ L →
          let S := balancedIntervalSpace operation width hwidth p r
          Submodule.IsViable (3 / 200 : ℝ) S
            (G.map (Entropy.regionTensorCoordinates q
              (interval L p r)).toLinearEquiv.toLinearMap) ∧
          Module.finrank ℂ S ≤ count ∧
          ∃ n : ℕ, n ≤ count ∧
            ∃ u : Fin n → EuclideanSpace ℂ (interval L p r → Fin q),
              S = Submodule.span ℂ (Set.range u) ∧
              ∀ j : ℕ, j < r - p - 1 → ∀ i : Fin n,
                Matrix.schmidtRank (WithLp.ofLp
                  (Entropy.cutVector (n := fun _ : interval L p r ↦ q)
                    (intervalTrimCut L p r j) (u i))) ≤
                  1000000 * Dref ^ 2 * (L + 1) * count := by
  classical
  obtain ⟨K, hK, hphysical⟩ := exists_physical_dg_recursive_interval_spaces_of_le_radius
  refine ⟨K, hK, ?_⟩
  intro L q h hsupp h0 h1 mu nu gamma hgamma H hH hmu hnu hmunu hgap
    G rG g u epsilonRef b
  obtain ⟨B, hB, hlogB, hTree⟩ :=
    hphysical L q h hsupp h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
  refine ⟨B, hB, hlogB, ?_⟩
  intro Dref xi m ell t Delta hqm hm hell ht htail hfilter D htrade width hwidth
  have hrG : 1 ≤ rG := Submodule.one_le_finrank_iff.mpr
    (hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl)
  have hDref : 1 ≤ Dref := by dsimp only [Dref]; nlinarith only [hrG, hB]
  have hxi : 0 < xi :=
    (Real.viable_node_trimming_radius_budget (L := L) (cuts := 0) (Nat.zero_le L) hDref).1
  obtain ⟨N, F, hN, hFamilies⟩ :=
    hTree m ell t Delta hqm hm hell ht htail hfilter htrade
  refine ⟨N, F, hN, ?_⟩
  intro beta hbeta hbeta1 A s count
  obtain ⟨hscount, operation, hliteral, htree⟩ := hFamilies xi hxi le_rfl beta hbeta hbeta1
  refine ⟨hscount, operation, hliteral, ?_⟩
  intro p r hpr hrL S
  obtain ⟨hviable, hdim, n, hn, vectors, hspan, hranks⟩ := htree p r hpr hrL
  refine ⟨hviable, hdim, n, hn, vectors, hspan, ?_⟩
  intro j hj i
  exact Real.viable_node_trimming_rank_bound hDref (hranks j hj i)

end TNLean.MPS.AreaLaw
