/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.Parameter.PolynomialFilterParameters
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.LowDensity.SharpApproximationParameters
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.DegenerateGround.PhysicalDGIntervalTrimming
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTree.IntervalSamplingTree
import QICLean.Analysis.Parameter.ViableRefinementParameters
import QICLean.Analysis.Parameter.ViableNodeParameters
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTrimming.FullIntervalMPS

/-!
# Automatic parameters for the physical recursive viable tree

Universal constants are chosen before the chain and Hamiltonian. The
explicit enlarged count base is `m = max q 50`. The existing uniform
scalar theorem then chooses the degree and truncation scale and proves
all numerical tail and filter estimates required by the recursive physical
construction. No such numerical estimates are hypotheses of the result.
The actual parent families are chosen before every sampling size and child
space, and all recursive spaces remain viable for the original full ground
space.

**Scope restriction (block leaves, one final trim and capped gap):** This
is the recursive witness construction with full local spaces at leaves of
length at most `4 * ell`, one final trim at each long node, and
`g = min gamma 1`. The distinction from the printed algorithm is recorded
in `docs/paper-gaps/alvv16_approximation_parameters.tex`. No adaptive joint
probability, energy-estimation invariant, final spectral extraction or
running time is asserted. Rank bounds concern the recorded generators,
not every vector in their span.

It also contains the following results.

* `TNLean.MPS.AreaLaw.exists_physical_dg_recursive_interval_spaces_of_le_radius`,
  `TNLean.MPS.AreaLaw.exists_physical_dg_recursive_interval_spaces`: an actual recursive viable tree
  for the full physical ground space.
* `TNLean.MPS.AreaLaw.exists_physical_dg_interval_tree_mps`: native matrix product states in the
  actual recursive root space.
-/

open ManyBody (interval)
open Matrix
open scoped BigOperators TensorProduct ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

section PhysicalDGIntervalTree

/-!
## An actual recursive viable tree for the full physical ground space

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

/-- Construct actual recursively selected interval spaces from the original
nearest-neighbour Hamiltonian. Every long parent uses one fixed family
chosen before all sampling sizes and child spaces. The recorded vectors
have the displayed count and weighted rank bounds for every positive
radius below the common reference bound; these are not assigned to every
vector in their span. Supporting ALVV, arXiv:1602.08828v2, `t:alg1`,
lines 1777–1817. The stated block-leaf and scalar scope is explicit. -/
theorem exists_physical_dg_recursive_interval_spaces_of_le_radius :
    ∃ K : ℝ, 0 < K ∧ ∀ (L q : ℕ),
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
  intro L q Φ h0 h1 mu nu gamma hgamma H hH hmu hnu hmunu hgap
    G rG g u epsilonRef b
  obtain ⟨B, hB, hlogB, hNodes⟩ :=
    hphysical L q Φ h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
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
                  (ManyBody.cutVector (X := fun _ ↦ Fin q)
                    (intervalTrimCut L p r j) (u i))) ≤
                  1000000 * Dref ^ 2 * (L + 1) * count := by
  classical
  obtain ⟨K, hK, hphysical⟩ := exists_physical_dg_recursive_interval_spaces_of_le_radius
  refine ⟨K, hK, ?_⟩
  intro L q Φ h0 h1 mu nu gamma hgamma H hH hmu hnu hmunu hgap
    G rG g u epsilonRef b
  obtain ⟨B, hB, hlogB, hTree⟩ :=
    hphysical L q Φ h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
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

end PhysicalDGIntervalTree

section PhysicalDGTreeParameters

/-- The original nearest-neighbour Hamiltonian determines an actual
recursive viable tree, with all numerical tail and filter conditions
derived from the displayed degree choice. The constants precede every
physical input, and each parent family precedes the sampling size and
child spaces and every admissible smaller trimming radius. Supporting ALVV,
arXiv:1602.08828v2, `t:alg1`,
lines 1777–1817, with the explicitly stated modified-tree scope. -/
theorem exists_physical_dg_interval_tree_of_le_radius :
    ∃ C K : ℝ, 1 ≤ C ∧ 0 < K ∧ ∀ (L q : ℕ),
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
    let epsilonRef : ℝ := 1 / 10000
    let b := 16 + Real.log (1 / g) +
      Real.log (32 * (rG : ℝ) * ((L : ℝ) + 1) / epsilonRef)
    let m := max q 50
    let v := 1 + Real.log (m : ℝ) + Real.log (1 / g)
    let ell : ℕ := Nat.ceil (C * v ^ 2 / g)
    let D := (m * ell ^ 2) ^ (22 * ell)
    ∃ _hell : 21 ≤ ell,
    Real.log (D : ℝ) ≤ 22 * (C + 1) * (6 + 2 * Real.log (C + 1)) / g * v ^ 3 ∧
    ∃ B : ℕ, 1 ≤ B ∧
    Real.log (B : ℝ) ≤
      K * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) * u) *
        (1 + Real.log b) ∧
    let Dref := rG ^ 2 * B
    let xiMax := 1 / (1000 * (Dref : ℝ) * Real.sqrt ((L : ℝ) + 1))
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
  obtain ⟨C, hC, _hC21, _hCM, _hClog, hparameters⟩ :=
    Real.exists_dg_accuracy_scalar_parameters
  obtain ⟨K, hK, hconditional⟩ := exists_physical_dg_recursive_interval_spaces_of_le_radius
  refine ⟨C, K, hC, hK, ?_⟩
  intro L q Φ h0 h1 mu nu gamma hgamma H hH hmu hnu hmunu hgap
    G rG g u epsilonRef b m v ell D
  have hm2 : 2 ≤ m := (by decide : 2 ≤ 50).trans (Nat.le_max_right q 50)
  have hqm : q ≤ m := Nat.le_max_left q 50
  have hm50 : 50 ≤ m := Nat.le_max_right q 50
  have hg : 0 < g := lt_min hgamma (by norm_num)
  have hg1 : g ≤ 1 := min_le_right gamma 1
  obtain ⟨hell, _hmD, hD, _hlower, _hupper, _hscale, _hcount,
    hlogD, htrade, htail⟩ := hparameters m g hm2 hg hg1
  refine ⟨hell, hlogD, ?_⟩
  obtain ⟨B, hB, hlogB, htree⟩ :=
    hconditional L q Φ h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
  refine ⟨B, hB, hlogB, ?_⟩
  intro Dref xiMax width hwidth
  have hDR : (0 : ℝ) < D := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < (2 : ℕ)) hD)
  have hpow : 0 < (D : ℝ) ^ 12 := pow_pos hDR 12
  let Delta : ℝ := (1 / 100000) / (D : ℝ) ^ 12
  have hbudget : (D : ℝ) ^ 12 * Delta = 1 / 100000 := by
    dsimp only [Delta]
    field_simp
  have hfilter : ∀ R : ℝ, 0 < R → R ≤ 3 * (ell : ℝ) + 4 * (ell : ℝ) →
      (2 * Real.exp (-2 * (ell : ℝ) ^ 2 * Real.sqrt ((4 * g / 5) / R))) ^ 2 ≤ Delta := by
    intro R hR hRbudget
    rw [Real.squared_chebyshev_error_eq]
    apply (le_div_iff₀ hpow).2
    have hR8 : R ≤ 8 * (ell : ℝ) := by
      linarith only [hRbudget, (Nat.cast_nonneg ell : (0 : ℝ) ≤ (ell : ℝ))]
    have hsmall : (D : ℝ) ^ 12 *
        (4 * Real.exp (-4 * (ell : ℝ) ^ 2 * Real.sqrt ((4 * g / 5) / R))) ≤
          1 / 100000 := by
      simpa only [neg_mul] using htrade R hR hR8
    nlinarith only [hsmall]
  have htail' : (288 * Real.exp (11 / 8)) *
      Real.exp (-((ell : ℝ) - g) / 8) ≤ (1 / (m : ℝ)) * g / 1000000 := by
    rw [div_mul_eq_mul_div, one_mul, div_div, mul_comm (m : ℝ) 1000000]
    exact htail
  exact htree m ell (ell : ℝ) Delta hqm hm50 (by omega) (by exact_mod_cast hell)
    htail' hfilter hbudget.le


/-- The original nearest-neighbour Hamiltonian determines an actual
recursive viable tree, with all numerical tail and filter conditions
derived from the displayed degree choice. The constants precede every
physical input, and each parent family precedes the sampling size and
child spaces. Supporting ALVV, arXiv:1602.08828v2, `t:alg1`,
lines 1777–1817, with the explicitly stated modified-tree scope. -/
theorem exists_physical_dg_interval_tree :
    ∃ C K : ℝ, 1 ≤ C ∧ 0 < K ∧ ∀ (L q : ℕ),
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
    let epsilonRef : ℝ := 1 / 10000
    let b := 16 + Real.log (1 / g) +
      Real.log (32 * (rG : ℝ) * ((L : ℝ) + 1) / epsilonRef)
    let m := max q 50
    let v := 1 + Real.log (m : ℝ) + Real.log (1 / g)
    let ell : ℕ := Nat.ceil (C * v ^ 2 / g)
    let D := (m * ell ^ 2) ^ (22 * ell)
    ∃ _hell : 21 ≤ ell,
    Real.log (D : ℝ) ≤ 22 * (C + 1) * (6 + 2 * Real.log (C + 1)) / g * v ^ 3 ∧
    ∃ B : ℕ, 1 ≤ B ∧
    Real.log (B : ℝ) ≤
      K * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) * u) *
        (1 + Real.log b) ∧
    let Dref := rG ^ 2 * B
    let xi := 1 / (1000 * (Dref : ℝ) * Real.sqrt ((L : ℝ) + 1))
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
                  (ManyBody.cutVector (X := fun _ ↦ Fin q)
                    (intervalTrimCut L p r j) (u i))) ≤
                  1000000 * Dref ^ 2 * (L + 1) * count := by
  classical
  obtain ⟨C, K, hC, hK, hphysical⟩ := exists_physical_dg_interval_tree_of_le_radius
  refine ⟨C, K, hC, hK, ?_⟩
  intro L q Φ h0 h1 mu nu gamma hgamma H hH hmu hnu hmunu hgap
    G rG g u epsilonRef b m v ell D
  obtain ⟨hell, hlogD, B, hB, hlogB, hTree⟩ :=
    hphysical L q Φ h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
  refine ⟨hell, hlogD, B, hB, hlogB, ?_⟩
  intro Dref xi width hwidth
  have hDref : 1 ≤ Dref := by
    dsimp only [Dref]
    simpa only [one_mul] using Nat.mul_le_mul
      (Nat.one_le_pow 2 rG (Submodule.one_le_finrank_iff.mpr
        (hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl))) hB
  have hxi : 0 < xi :=
    (Real.viable_node_trimming_radius_budget (L := L) (cuts := 0) (Nat.zero_le L) hDref).1
  obtain ⟨N, F, hN, hFamilies⟩ := hTree
  refine ⟨N, F, hN, ?_⟩
  intro beta hbeta hbeta1 A s count
  obtain ⟨hscount, operation, hliteral, htree⟩ := hFamilies xi hxi le_rfl beta hbeta hbeta1
  refine ⟨hscount, operation, hliteral, ?_⟩
  intro p r hpr hrL S
  obtain ⟨hviable, hdim, n, hn, vectors, hspan, hranks⟩ := htree p r hpr hrL
  refine ⟨hviable, hdim, n, hn, vectors, hspan, ?_⟩
  intro j hj i
  exact Real.viable_node_trimming_rank_bound hDref (hranks j hj i)

end PhysicalDGTreeParameters

section PhysicalDGTreeMPS

/-!
## Native matrix product states in the actual recursive root space

The original Hamiltonian determines the recursively selected viable tree.
At the full-chain root, its recorded generators have native matrix product
representations after identifying the full interval with the chain. Every
vector in their span then has bond dimension at most the recorded count
times the generator bound. The actual recursive space and its viability
are retained; no independent area-law approximation is substituted.

**Scope restriction (the recursive witness, not final spectral extraction):**
The capped gap, block leaves and one final trim are those of the automatic
parameter theorem, documented in
`docs/paper-gaps/alvv16_approximation_parameters.tex`. The bound for the
entire root space has the extra count factor. No adaptive joint success
probability, final spectral extraction or running time is asserted.
-/

/-- Every vector in the actual recursively selected root space, read in
native chain coordinates, has the displayed matrix product bond bound.
The same literal families, operations, intermediate spaces and original
full-ground-space viability are retained. Supporting ALVV,
arXiv:1602.08828v2, `t:alg1`, lines 1777–1817, and LVV13,
arXiv:1307.5143v1, Claim `c:2`, lines 520–527. -/
theorem exists_physical_dg_interval_tree_mps :
    ∃ C K : ℝ, 1 ≤ C ∧ 0 < K ∧ ∀ (L q : ℕ),
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
    let epsilonRef : ℝ := 1 / 10000
    let b := 16 + Real.log (1 / g) +
      Real.log (32 * (rG : ℝ) * ((L : ℝ) + 1) / epsilonRef)
    let m := max q 50
    let v := 1 + Real.log (m : ℝ) + Real.log (1 / g)
    let ell : ℕ := Nat.ceil (C * v ^ 2 / g)
    let D := (m * ell ^ 2) ^ (22 * ell)
    ∃ _hell : 21 ≤ ell,
    Real.log (D : ℝ) ≤ 22 * (C + 1) * (6 + 2 * Real.log (C + 1)) / g * v ^ 3 ∧
    ∃ B : ℕ, 1 ≤ B ∧
    Real.log (B : ℝ) ≤
      K * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) * u) *
        (1 + Real.log b) ∧
    let Dref := rG ^ 2 * B
    let xi := 1 / (1000 * (Dref : ℝ) * Real.sqrt ((L : ℝ) + 1))
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
        (∀ (p r : ℕ), p ≤ r → r ≤ L →
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
                  (ManyBody.cutVector (X := fun _ ↦ Fin q)
                    (intervalTrimCut L p r j) (u i))) ≤
                  1000000 * Dref ^ 2 * (L + 1) * count) ∧
        ∀ v : EuclideanSpace ℂ (interval L 0 L → Fin q),
          v ∈ balancedIntervalSpace operation width hwidth 0 L →
          IsOpenMPS L q (1000000 * Dref ^ 2 * (L + 1) * count ^ 2)
            (fullIntervalRead L q v) := by
  classical
  obtain ⟨C, K, hC, hK, hphysical⟩ := exists_physical_dg_interval_tree
  refine ⟨C, K, hC, hK, ?_⟩
  intro L q Φ h0 h1 mu nu gamma hgamma H hH hmu hnu hmunu hgap
    G rG g u epsilonRef b m v ell D
  obtain ⟨hell, hlogD, B, hB, hlogB, hfamilies⟩ :=
    hphysical L q Φ h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
  refine ⟨hell, hlogD, B, hB, hlogB, ?_⟩
  intro Dref xi width hwidth
  obtain ⟨N, F, hN, hparents⟩ := hfamilies
  refine ⟨N, F, hN, ?_⟩
  intro beta hbeta hbeta1 A s count
  obtain ⟨hscount, operation, hliteral, htree⟩ := hparents beta hbeta hbeta1
  refine ⟨hscount, operation, hliteral, htree, ?_⟩
  intro vector hvector
  obtain ⟨_hviable, _hdim, n, hn, generators, hspan, hranks⟩ :=
    htree 0 L (Nat.zero_le L) le_rfl
  let R := 1000000 * Dref ^ 2 * (L + 1) * count
  have hgenerators : ∀ (i : Fin n) (j : ℕ), j < L - 1 →
      Matrix.schmidtRank (WithLp.ofLp
        (ManyBody.cutVector (intervalTrimCut L 0 L j) (generators i))) ≤ R := by
    intro i j hj
    exact hranks j (by simpa only [Nat.sub_zero] using hj) i
  rw [hspan] at hvector
  have hmps := isOpenMPS_fullIntervalRead_of_mem_span generators hgenerators hvector
  apply hmps.mono
  calc
    n * R ≤ count * R := Nat.mul_le_mul_right R hn
    _ = 1000000 * Dref ^ 2 * (L + 1) * count ^ 2 := by dsimp only [R]; ring

end PhysicalDGTreeMPS

end TNLean.MPS.AreaLaw
