/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.DyadicLongIntervalLowDensityFamily
import TNLean.MPS.AreaLaw.IntervalSamplingTree
import TNLean.MPS.AreaLaw.IntervalCollectiveTrimming
import TNLean.MPS.AreaLaw.LowEnergyMPSBasis
import TNLean.MPS.AreaLaw.FullIntervalViability
import TNLean.MPS.AreaLaw.FullIntervalMPS
import QICLean.Analysis.ViableTrimmingRadius
import QICLean.Analysis.ViableTrimmingRank
import QICLean.Analysis.ViableNodeLeafCount
import QICLean.Analysis.ViableSubspaceDimension
import TNLean.MPS.AreaLaw.PhysicalLDTreeNode

/-!
# A sampled merge tree for a low-density spectrum

The original nearest-neighbour Hamiltonian determines one low-density
filter family on every long interval, before the tree, the window and the
sampling size. A long node tensors its two children, samples the merged
space, applies all words of length `clog_D (D^2 s)` of its family, and trims
the image collectively. The family carries the upper window `G(η)` to the
lower window `G(η - 3w)` with suppression `Δ^k` on words of length `k`, so
the window shrinks by the buffer `3w` at each level. The level of `[p, r)`
is `clog₂ (r - p)`, and every node is `3/200`-viable for the window
`etaLD - 3w · clog₂ (r - p)`. The node dimension is at most `D^6 s^3`,
where `s = ⌈4096 r (1 + log r + log D + log (1/β))⌉` is linear, up to a logarithmic
factor, in the dimension `r` of the window `G(etaLD)`.
The root is close to the window shortened by `3w · clog₂ L`, and it consists
of matrix product states.

This is the existence content of ALVV, arXiv:1602.08828v2, Theorem `t:alg2`,
lines 1869–1878, run as Theorem `t:alg1`, lines 1777–1817, with the
families of Theorem `t:aisgapless`, lines 1027–1041, under Assumption (LD),
lines 281–284. The source buffer `w = μ / (3 log n)` and condition
`η₁ ≥ 2μ / log n` correspond to the hypothesis `3w (clog₂ L + 1) ≤ etaLD`.

**Scope restriction (modified tree and fixed bandwidth):** As in the
gapped tree, the leaves are full blocks of length at most `4 * ell`, each
long node has one final collective trim, and the theorem asserts the
existence of successful samples rather than a success probability or a
running time. The trimming threshold and the bond bound of the root
depend on an existential reference bond `Dref`, and the hidden constant
depends on the fixed bandwidth `etaLD`; the local dimension satisfies
`q ≥ 2`. No final refinement of the root is asserted. See
`docs/paper-gaps/alvv16_low_energy_family_scope.tex` and
`docs/paper-gaps/alvv16_approximation_parameters.tex`.
-/

open ManyBody (interval)

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory

namespace TNLean.MPS.AreaLaw

open Matrix

/-- The original nearest-neighbour Hamiltonian determines, on every long
interval, one low-density family of at most `D ^ 2` operators, chosen before
the tree, the window and the sampling size. For a buffer `w` with
`3w (clog₂ L + 1) ≤ etaLD` there is one reference bond `Dref` and, for every
failure parameter `beta`, an actual balanced tree whose long nodes are
literal sampled word images followed by collective trims at the threshold
`xi`. Every node `[p, r)` is `3/200`-viable for the original window
`etaLD - 3w · clog₂ (r - p)`, has dimension at most `count = D^6 s^3`, and is
spanned by at most `count` recorded vectors of controlled Schmidt rank.
The root is `3/200`-close to the window `etaLD - 3w · clog₂ L`, and each of
its vectors is a matrix product state of bond dimension
`10^6 Dref^2 (L + 1) count^2`. ALVV, arXiv:1602.08828v2, Theorem `t:alg2`,
lines 1869–1878, with Theorem `t:alg1`, lines 1777–1817, and the families
of Theorem `t:aisgapless`, lines 1027–1041. The conclusion at the root is
recorded as any consequence `Q` of its closeness, dimension and matrix
product bounds, so that its instances need not repeat the construction. -/
theorem exists_physical_ld_sampled_interval_tree_of_clause (etaLD : ℝ) (hLD : 0 < etaLD)
    (Q : ∀ (L q _m : ℕ) (_w : ℝ) (_hq : 2 ≤ q)
      (Φ : ManyBody.BondInteraction L q) (_h0 : ∀ i, 0 ≤ Φ.term i)
      (_count _Dref : ℕ), Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q)) → Prop)
    (hQ : ∀ (L q m : ℕ) (w : ℝ) (hq : 2 ≤ q), q ≤ m → 0 < w →
      ∀ (Φ : ManyBody.BondInteraction L q),
      ∀ (h0 : ∀ i, 0 ≤ Φ.term i), (∀ i, Φ.term i ≤ 1) →
      let _ : Nonempty (Fin L → Fin q) :=
        ⟨fun _ ↦ ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩⟩
      let H := Φ.hamiltonian
      let hRaw : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      let G := fun eta : ℝ ↦ Submodule.spectralSpanLE
        hRaw.eigenvectorBasis hRaw.eigenvalues (minEigenvalue hRaw + eta)
      ∀ (count Dref : ℕ) (S0 : Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q))),
      Submodule.IsCloseTo (3 / 200 : ℝ) (nativeFullIntervalSpace L q S0)
        (G (etaLD - 3 * w * Nat.clog 2 L)) →
      Module.finrank ℂ S0 ≤ count →
      (∀ v ∈ S0, IsOpenMPS L q (1000000 * Dref ^ 2 * (L + 1) * count ^ 2)
        (fullIntervalRead L q v)) →
      Q L q m w hq Φ h0 count Dref S0) :
    ∃ C : ℝ, 100 ≤ C ∧ 19 + etaLD ≤ C ∧
      ∀ (L q m : ℕ) (w : ℝ) (hq : 2 ≤ q), q ≤ m → 0 < w →
      let mi := 4 * m
      let g := min w 1
      let u := 1 + Real.log (mi : ℝ) + Real.log (1 / g)
      let ell : ℕ := ⌈C * u ^ 2 / g⌉₊
      let D := (mi * ell ^ 2) ^ (22 * ell)
      ∀ (Φ : ManyBody.BondInteraction L q),
      ∀ (h0 : ∀ i, 0 ≤ Φ.term i), (∀ i, Φ.term i ≤ 1) →
      let _ : Nonempty (Fin L → Fin q) :=
        ⟨fun _ ↦ ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩⟩
      let H := Φ.hamiltonian
      let hRaw : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      let G := fun eta : ℝ ↦ Submodule.spectralSpanLE
        hRaw.eigenvectorBasis hRaw.eigenvalues (minEigenvalue hRaw + eta)
      let rG := Module.finrank ℂ (G etaLD)
      ∃ _hell : 21 ≤ ell,
      Real.log (D : ℝ) ≤ 22 * (C + 1) * (6 + 2 * Real.log (C + 1)) / g * u ^ 3 ∧
      let width := 4 * ell
      let hwidth : 1 ≤ width := by omega
      let target := fun p r : ℕ ↦ G (etaLD - 3 * w * Nat.clog 2 (r - p))
      ∃ (N : LongIntervalIndex L width → ℕ)
        (F : ∀ J : LongIntervalIndex L width,
          Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
            EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)),
        (∀ J, N J ≤ D ^ 2) ∧
        (3 * w * ((Nat.clog 2 L : ℝ) + 1) ≤ etaLD →
        ∃ Dref : ℕ, 1 ≤ Dref ∧
        let xi := 1 / (1000 * (Dref : ℝ) * Real.sqrt ((L : ℝ) + 1))
        ∀ beta : ℝ, 0 < beta → beta < 1 →
        let A := 1 + Real.log (rG : ℝ) + Real.log (D : ℝ) + Real.log (1 / beta)
        let s := Nat.ceil (4096 * (rG : ℝ) * A)
        let count := D ^ 6 * s ^ 3
        (s : ℝ) ≤ 4097 * (rG : ℝ) * A ∧
        ∃ operation : IntervalMergeOperation L q,
          (∀ (J : LongIntervalIndex L width) (k : ℕ) (hpk : J.val.1 ≤ k) (hkr : k ≤ J.val.2),
            k = J.val.1 + (J.val.2 - J.val.1) / 2 →
            ∀ (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 k → Fin q)))
              (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k J.val.2 → Fin q))),
            Submodule.IsViable (3 / 200 : ℝ) S1
              ((target J.val.1 k).map (Entropy.regionTensorCoordinates q
                (interval L J.val.1 k)).toLinearEquiv.toLinearMap) →
            Submodule.IsViable (3 / 200 : ℝ) S2
              ((target k J.val.2).map (Entropy.regionTensorCoordinates q
                (interval L k J.val.2)).toLinearEquiv.toLinearMap) →
            Module.finrank ℂ S1 ≤ count → Module.finrank ℂ S2 ≤ count →
            ∃ U : Matrix.unitaryGroup
              (Fin (Module.finrank ℂ (adjacentIntervalMerge L q
                J.val.1 k J.val.2 hpk hkr S1 S2))) ℂ,
              operation J.val.1 k J.val.2 hpk hkr S1 S2 =
                sampledIntervalTrim L q J.val.1 J.val.2 (F J) (Nat.clog D (D ^ 2 * s)) s xi
                  (adjacentIntervalMerge L q J.val.1 k J.val.2 hpk hkr S1 S2) U) ∧
          (∀ p r : ℕ, p ≤ r → r ≤ L →
            let S := balancedIntervalSpace operation width hwidth p r
            Submodule.IsViable (3 / 200 : ℝ) S
              ((target p r).map (Entropy.regionTensorCoordinates q
                (interval L p r)).toLinearEquiv.toLinearMap) ∧
            Module.finrank ℂ S ≤ count ∧ IsIntervalSpanWithRankBound L q p r count xi S) ∧
          let S0 := balancedIntervalSpace operation width hwidth 0 L
          Q L q m w hq Φ h0 count Dref S0) := by
  classical
  -- Eliminate existentials and project conjunctions, rather than destructuring them, so
  -- that the large goal is not re-checked at every step.
  refine (exists_fixed_bandwidth_long_interval_dyadic_low_energy_word_family etaLD hLD).elim
    fun C hlong ↦ ?_
  have hC := hlong.1
  have hCeta := hlong.2.1
  have hlong := hlong.2.2
  refine (exists_fixed_bandwidth_low_energy_orthonormal_mps_basis etaLD hLD).elim
    fun _Kref hbasis ↦ ?_
  have hbasis := hbasis.2
  refine ⟨C, hC, hCeta, ?_⟩
  intro L q m w hq hqm hw mi g u ell D Φ h0 h1 config H hRaw G rG
  let : Nonempty (Fin L → Fin q) := config
  have hm4 : m * 2 ^ 2 = mi := by dsimp only [mi]; ring
  have hfamily (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) := by
    have hfam := hlong L q m p r 2 w hq hqm hpr hrL hw Φ h0 h1
    rw [hm4, show (1 / 200 : ℝ) / 2 ^ (4 * 2) = 1 / 51200 by norm_num] at hfam
    exact hfam
  have hfamily0 := hfamily 0 0 le_rfl (Nat.zero_le L)
  have hell := hfamily0.1
  have hlogD := hfamily0.2.1
  refine ⟨hell, hlogD, ?_⟩
  intro width hwidth target
  have hell1 : 1 ≤ ell := (by decide : 1 ≤ 21).trans hell
  have hqmi : q ≤ mi := hqm.trans (by dsimp only [mi]; omega)
  have hmi2 : 2 ≤ mi := hq.trans hqmi
  have hD : 2 ≤ D := by
    have hbase : 2 ≤ mi * ell ^ 2 := hmi2.trans
      (by simpa only [mul_one] using Nat.mul_le_mul_left mi (Nat.one_le_pow 2 ell hell1))
    exact Nat.one_lt_pow (by omega : 22 * ell ≠ 0) (by omega)
  -- The low-density word families on every long interval, before every window.
  have hfamilies := fun J : LongIntervalIndex L width ↦
    ((hfamily J.val.1 J.val.2 J.property.1 J.property.2.1).2.2 J.property.2.2)
  choose N F hN hwords using hfamilies
  refine ⟨N, F, hN, ?_⟩
  intro hdepth
  -- Facts about the original windows.
  have hGmono {a b : ℝ} (hab : a ≤ b) : G a ≤ G b :=
    Submodule.spectralSpanLE_mono_cutoff hRaw.eigenvectorBasis hRaw.eigenvalues
      (by linarith only [hab])
  have hGne {eta : ℝ} (heta : 0 ≤ eta) : G eta ≠ ⊥ := by
    obtain ⟨i, hi⟩ := minEigenvalue_achieved hRaw
    apply hRaw.spectralSpanLE_ne_bot_of_mem_spectrum
    · simpa only [hi] using hRaw.eigenvalues_mem_spectrum_real i
    · linarith only [heta]
  have hrG : 1 ≤ rG := Submodule.one_le_finrank_iff.mpr (hGne hLD.le)
  -- One reference matrix product space for every level window.
  have hreference : ∀ K : ℕ, ∃ (Uref : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
      (DK : ℕ), 1 ≤ DK ∧ (1 ≤ K →
        Submodule.IsCloseTo (1 / 10000) (G (etaLD - 3 * w * K)) Uref ∧
        Submodule.IsCloseTo (1 / 10000) Uref (G (etaLD - 3 * w * K)) ∧
        ∀ v ∈ Uref, IsOpenMPS L q DK (fun x ↦ v x)) := by
    intro K
    by_cases hK : 1 ≤ K
    · have hv : 0 < 3 * w * (K : ℝ) := by
        have : (1 : ℝ) ≤ K := by exact_mod_cast hK
        positivity
      obtain ⟨B, _hB, _hlogB, _phi, _hphi, hrest⟩ :=
        hbasis L q (3 * w * K) (by omega) hv Φ h0 h1 (1 / 10000) (by norm_num) (by norm_num)
      obtain ⟨_hinj, _hdim, _hdimle, _hspan, hVG, hGV, _hGV', hMPS, _⟩ := hrest
      exact ⟨_, _ + 1, Nat.le_add_left 1 _, fun _ ↦ ⟨hGV, hVG,
        fun v hv' ↦ (hMPS v hv').mono (Nat.le_succ _)⟩⟩
    · exact ⟨⊥, 1, le_rfl, fun h1K ↦ absurd h1K hK⟩
  choose Uref DK hDK hUref using hreference
  let Dref := ∑ K ∈ Finset.range (Nat.clog 2 L + 1), DK K
  have hDK_le (K : ℕ) (hK : K ≤ Nat.clog 2 L) : DK K ≤ Dref :=
    Finset.single_le_sum (f := DK) (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hK))
  have hDref : 1 ≤ Dref := (hDK 0).trans (hDK_le 0 (Nat.zero_le _))
  refine ⟨Dref, hDref, ?_⟩
  intro xi beta hbeta hbeta1 A s count
  have hsize := Real.viable_node_uniform_sampling_size hD hrG hbeta hbeta1.le
  have hs := hsize.1
  have hscount := hsize.2.1
  have hxi : 0 < xi :=
    (Real.viable_node_trimming_radius_budget (L := L) (cuts := 0) (Nat.zero_le L) hDref).1
  have hxi1 : xi ≤ 1 := by
    have hDrefR : (1 : ℝ) ≤ Dref := by exact_mod_cast hDref
    have hroot : 1 ≤ Real.sqrt ((L : ℝ) + 1) := Real.one_le_sqrt.mpr
      (by linarith only [(Nat.cast_nonneg L : (0 : ℝ) ≤ (L : ℝ))])
    have hprod := one_le_mul_of_one_le_of_one_le hDrefR hroot
    dsimp only [xi]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [hprod]
  have hleaf : q ^ width ≤ count := Nat.viable_tree_leaf_count_le hqmi hmi2 hell1 hs
  have htreeSpec :=
    exists_balanced_sampled_interval_tree_of_targets hwidth (by omega) hD hrG target
      (fun p k r ↦ k = p + (r - p) / 2) (fun _ _ ↦ rfl) hxi hxi1 N F hN hbeta hbeta1 hleaf
      (physical_ld_tree_node G hGmono hGne le_rfl hwidth hw hdepth hD hs N F hN
        (fun J eta hbuffer hetaLD ↦ by
          -- The words of each long interval, in the original windows and coordinates.
          have hwordsJ := hwords J eta hbuffer hetaLD
          refine hwordsJ.elim fun Tlo hwordsJ ↦ hwordsJ.elim fun Thi hwordsJ ↦
            hwordsJ.elim fun Delta hwordsJ ↦
              ⟨Tlo, Thi, Delta, hwordsJ.2.1, ?_, hwordsJ.2.2.2.1, hwordsJ.2.2.2.2.1, ?_⟩
          · simpa only [G, add_sub_assoc] using hwordsJ.2.2.1
          · intro a S delta hS hdelta
            rw [Entropy.regionTensorCoordinates_eq_exteriorFirst] at hS ⊢
            exact (hwordsJ.2.2.2.2.2 a S delta hS hdelta).2)
        Uref (fun K hK hKL ↦ ⟨(hUref K hK).1, (hUref K hK).2.1,
          fun v hv ↦ ((hUref K hK).2.2 v hv).mono (hDK_le K hKL)⟩) hDref rfl)
  refine htreeSpec.elim fun operation htreeSpec ↦ ?_
  have hliteral := htreeSpec.1
  have htree := htreeSpec.2
  refine ⟨hscount, operation, fun J k hpk hkr hmid ↦ hliteral J k hpk hkr hmid, htree, ?_⟩
  intro S0
  have hspec := htree 0 L (Nat.zero_le L) le_rfl
  refine hspec.elim fun hroot hspec ↦ hspec.elim fun hdim0 hspec ↦ hspec.elim fun n hspec ↦
    hspec.elim fun hn hspec ↦ hspec.elim fun vectors hspec ↦ hspec.elim fun hspan hspec ↦ ?_
  have hranks := hspec
  refine hQ L q m w hq hqm hw Φ h0 h1 count Dref S0
    ((isViable_fullInterval_iff_isCloseTo _ _).mp hroot) hdim0 ?_
  intro v hv
  have hrank (i : Fin n) (j : ℕ) (hj : j < L - 1) :
      Matrix.schmidtRank (WithLp.ofLp
        (ManyBody.cutVector (intervalTrimCut L 0 L j) (vectors i))) ≤
        1000000 * Dref ^ 2 * (L + 1) * count :=
    Real.viable_node_trimming_rank_bound hDref (hranks j hj i)
  have hmem : v ∈ Submodule.span ℂ (Set.range vectors) := by
    rw [← hspan]
    exact hv
  apply (isOpenMPS_fullIntervalRead_of_mem_span vectors hrank hmem).mono
  calc
    n * (1000000 * Dref ^ 2 * (L + 1) * count) ≤
        count * (1000000 * Dref ^ 2 * (L + 1) * count) := Nat.mul_le_mul_right _ hn
    _ = 1000000 * Dref ^ 2 * (L + 1) * count ^ 2 := by ring

end TNLean.MPS.AreaLaw
