/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.DegenerateGround.DGCanonicalNodeParent
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.DegenerateGround.DGConstantNodeTree
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTree.CanonicalWordTrimTree

/-!
# Success probability of the degenerate-gap tree of constant node dimension

ALVV, arXiv:1602.08828v2, Theorem `t:alg1`, lines 1777–1818, runs the merge tree with a fresh
random sample at every merge. This file proves that the randomly sampled tree of node dimension
`count = D^{2k} s ≤ D² s²` succeeds on a measurable event: with one independent rank-independent
Haar coordinate for every interval, the root and all internal nodes are `3/200`-viable for the
original ground space except on a set of measure at most `(L - 1) β`, for the sampling size
`s = ⌈4096 r (1 + log r + log D + log (1/β))⌉`. Every node has dimension at most `count` for
every coordinate, including failures.

The composition is a union bound over the `L - 1` internal nodes of the per-node failure of
Lemma `l:rs`, which is at most `β` for this sampling size.

**Local fix (sampling parametrization):** in the maintainer's reading of the arXiv v2 text, §6.2,
Theorem 6.1 (`t:alg1`) and its proof state overall success probability at least `1 - 1/n`, derived
by a union bound from a per-merge failure probability at most `1/n²`. The bound `(L - 1) β` is that
union bound for an arbitrary per-merge failure `β`; the parameter `β` and the sampling envelope
`s = ⌈4096 r (1 + log r + log D + log (1/β))⌉` are a sufficient parametrization chosen by the
formalization, not the source's formula. For `L ≥ 2`, the choice `β = 1/L²` is the source's
per-merge bound and gives overall failure `(L - 1)/L² < 1/L`; for `L ≤ 1` the tree is a single short
leaf and the bound is `0`. The identification of this tree with the source's algorithm, its output
and its running time is not proved. See `docs/paper-gaps/alvv16_approximation_parameters.tex`.

**Local fix (rounding of the number of rounds):** `k = ⌈⌈log_D s⌉ / 2⌉`, as in
`DGConstantNodeTree`; see `docs/paper-gaps/alvv16_approximation_parameters.tex`.

**Scope restriction (block leaves, one final trim and capped gap):** leaves are full blocks of
length at most `4 ℓ`; each long node applies one collective trim after its `k` rounds; the
parameters use `g = min γ 1`; and only the root and its internal nodes are asserted viable. See
`docs/paper-gaps/alvv16_approximation_parameters.tex`.
-/

open ManyBody (interval)

open Matrix
open scoped BigOperators TensorProduct ComplexOrder MatrixOrder Matrix.Norms.L2Operator ENNReal
open MeasureTheory

namespace TNLean.MPS.AreaLaw.ALVV

open TNLean.MPS.AreaLaw TNLean.Lattice

/-- **Success probability of the degenerate-gap tree of constant node dimension.** For a
nearest-neighbour chain with `0 ≤ hᵢ ≤ 1` satisfying Assumption (DG), with ground space `G` of
dimension `r` and gap `γ`, the improving families of Theorem 4.7 (`t:ais`, from Corollary 4.6
`c:goodagsphardtrunc`) on every long interval are fixed before the trimming radius, the failure
parameter and every coordinate. For every trimming radius `ξ` below the reference bound and every
`0 < β < 1`, put `s = ⌈4096 r (1 + log r + log D + log (1/β))⌉`, `k = ⌈⌈log_D s⌉ / 2⌉` and
`count = D^{2k} s ≤ D² s²`. With one independent rank-independent Haar coordinate per interval, the
canonical tree with `k` rounds and one collective trim at every long node has every node of
dimension at most `count`, and its root and internal nodes are all `3/200`-viable for `G` outside a
measurable set of measure at most `(L - 1) β`.

ALVV, arXiv:1602.08828v2, Theorem `t:alg1`, lines 1777–1818, in its probabilistic form, under the
markers of this module. -/
theorem exists_physical_dg_canonical_constant_node_tree_failure_le :
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
      let k := (Nat.clog D s + 1) / 2
      let count := D ^ (2 * k) * s
      (s : ℝ) ≤ 4097 * (rG : ℝ) * A ∧ count ≤ D ^ 2 * s ^ 2 ∧
      (∀ (U : IntervalSamplingChoices L q) (p r : ℕ), p ≤ r → r ≤ L →
        Module.finrank ℂ (balancedIntervalSpace (canonicalWordTrimOperation N F k s xi U)
          width hwidth p r) ≤ count) ∧
      MeasurableSet (canonicalWordTrimTreeGood hwidth N F k s xi G (3 / 200)) ∧
      intervalSamplingMeasure L q (canonicalWordTrimTreeGood hwidth N F k s xi G (3 / 200))ᶜ ≤
        ((L - 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal beta := by
  classical
  obtain ⟨C, hC, _hC21, _hCM, _hClog, hparameters⟩ :=
    Real.exists_dg_accuracy_scalar_parameters
  obtain ⟨K, hK, hphysical⟩ := exists_physical_dg_canonical_interval_node_failure_of_power
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
  obtain ⟨B, hB, hlogB, hNodes⟩ :=
    hphysical L q Φ h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
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
  have hfamilies := fun J : LongIntervalIndex L width ↦
    hNodes m ell (ell : ℝ) Delta hqm hm50 (by omega) (by exact_mod_cast hell) htail' hfilter
      hbudget.le J.val.1 J.val.2 J.property.1 J.property.2.1 J.property.2.2
  choose N F hN hEvents using hfamilies
  refine ⟨N, F, hN, ?_⟩
  intro xi hxi hxiMax beta hbeta hbeta1 A s k count
  have hxi1 : xi ≤ 1 := hxiMax.trans hxiMax1
  obtain ⟨hs, hscount, hfail64, hfailure⟩ :=
    Real.viable_node_uniform_sampling_size hD hrG hbeta hbeta1.le
  have hs2 : 2 ≤ s := by
    have hlogr : 0 ≤ Real.log (rG : ℝ) := Real.log_nonneg (by exact_mod_cast hrG)
    have hlogD : 0 ≤ Real.log (D : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (le_trans (by norm_num) hD : 1 ≤ D))
    have hlogb : 0 ≤ Real.log (1 / beta) :=
      Real.log_nonneg (by rw [le_div_iff₀ hbeta]; linarith)
    have hrGR : (1 : ℝ) ≤ rG := by exact_mod_cast hrG
    have hA : 1 ≤ A := by dsimp only [A]; linarith
    have hceil := Nat.le_ceil (4096 * (rG : ℝ) * A)
    have : (2 : ℝ) ≤ s := le_trans (by nlinarith) hceil
    exact_mod_cast this
  obtain ⟨hk1, hsk, hkD⟩ := merge_rounds_bounds hD hs2
  have hcount2 : count ≤ D ^ 2 * s ^ 2 := by
    calc count = D ^ (2 * k) * s := rfl
      _ ≤ (D ^ 2 * s) * s := Nat.mul_le_mul_right s hkD
      _ = D ^ 2 * s ^ 2 := by ring
  have hcountsq : count * count ≤ D ^ 12 * s ^ 6 := by
    calc count * count ≤ (D ^ 2 * s ^ 2) * (D ^ 2 * s ^ 2) := Nat.mul_le_mul hcount2 hcount2
      _ = D ^ 4 * s ^ 4 := by ring
      _ ≤ D ^ 12 * s ^ 6 := Nat.mul_le_mul
          (Nat.pow_le_pow_right (le_trans (by norm_num) hD) (by norm_num))
          (Nat.pow_le_pow_right (le_trans (by norm_num) hs2) (by norm_num))
  have hleaf : q ^ width ≤ count := by
    have hell2 : 1 ≤ ell ^ 2 := Nat.one_le_pow 2 ell (by omega)
    have hqD : q ^ width ≤ D :=
      calc q ^ width = q ^ (4 * ell) := rfl
        _ ≤ q ^ (22 * ell) := Nat.pow_le_pow_right hq (by omega)
        _ ≤ (m * ell ^ 2) ^ (22 * ell) := Nat.pow_le_pow_left
          (hqm.trans (by simpa only [mul_one] using Nat.mul_le_mul_left m hell2)) _
    calc q ^ width ≤ D := hqD
      _ ≤ D ^ (2 * k) :=
          Nat.le_self_pow (Nat.mul_ne_zero two_ne_zero (Nat.pos_iff_ne_zero.mp hk1)) D
      _ ≤ D ^ (2 * k) * s := Nat.le_mul_of_pos_right _ (lt_of_lt_of_le (by norm_num) hs2)
  refine ⟨hscount, hcount2,
    finrank_balancedIntervalSpace_canonicalWordTrimOperation_le hwidth hq N F hN hxi.le hxi1
      hleaf le_rfl,
    measurableSet_canonicalWordTrimTreeGood hwidth N F k s xi G _, ?_⟩
  apply intervalSamplingMeasure_canonicalWordTrimTreeGood_compl_le hwidth hq N F hN hxi.le hxi1
    hleaf le_rfl G (by norm_num)
  intro J j hpj hjr S1 S2 hS1 hS2 hd1 hd2
  refine (hEvents J xi hxi hxiMax k s hk1 hs hsk j hpj hjr S1 S2 hS1 hS2 hd1 hd2).trans
    (ENNReal.ofReal_le_ofReal ((hfailure _ ?_).trans hfail64))
  calc Module.finrank ℂ (adjacentIntervalMerge L q J.val.1 j J.val.2 hpj hjr S1 S2)
      ≤ Module.finrank ℂ S1 * Module.finrank ℂ S2 :=
        finrank_adjacentIntervalMerge_le hpj hjr S1 S2
    _ ≤ count * count := Nat.mul_le_mul hd1 hd2
    _ ≤ D ^ 12 * s ^ 6 := hcountsq

end TNLean.MPS.AreaLaw.ALVV
