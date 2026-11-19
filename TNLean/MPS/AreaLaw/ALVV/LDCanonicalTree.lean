/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalLDTree
import TNLean.MPS.AreaLaw.ALVV.LDCanonicalNodeEvent
import TNLean.MPS.AreaLaw.ALVV.CanonicalWordTrimTargetTree

/-!
# Success probability of the low-density merge tree

ALVV, arXiv:1602.08828v2, Theorem `t:alg2`, lines 1869–1878, runs the merge tree of Theorem
`t:alg1`, lines 1777–1817, with the low-density families of Theorem `t:aisgapless`,
lines 1027–1041, under Assumption (LD), lines 281–284, sampling afresh at every merge. This file
proves that the randomly sampled tree succeeds on a measurable event: with one independent
rank-independent Haar coordinate for every interval, every node has dimension at most
`count = D⁶ s³` for every coordinate, and the root and all internal nodes `[p, r)` are
`3/200`-viable for their windows `etaLD - 3w · clog₂ (r - p)` outside a set of measure at most
`(L - 1) β`, for the sample size `s = ⌈4096 r (1 + log r + log D + log (1/β))⌉`.

**Local fix (sampling parametrization):** in the maintainer's reading of the arXiv v2 text, §6.2,
Theorem 6.1 (`t:alg1`) and its proof state overall success probability at least `1 - 1/n`, derived
by a union bound from a per-merge failure probability at most `1/n²`; Theorem 6.3 (`t:alg2`) states
success at least `1 - 1/n`. The bound `(L - 1) β` is that union bound for an arbitrary per-merge
failure `β`; the parameter `β` and the sampling envelope
`s = ⌈4096 r (1 + log r + log D + log (1/β))⌉` are a sufficient parametrization chosen by the
formalization, not the source's formula. For `L ≥ 2`, the choice `β = 1/L²` is the source's
per-merge bound and gives overall failure `(L - 1)/L² < 1/L`; for `L ≤ 1` the tree is a single short
leaf and the bound is `0`. The identification of this tree with the source's algorithm, its output
and its running time is not proved. See `docs/paper-gaps/alvv16_low_energy_family_scope.tex`.

**Scope restriction (modified tree and fixed bandwidth):** as in `PhysicalLDTree`, the leaves are
full blocks of length at most `4 ℓ`, each long node has one final collective trim, the trimming
threshold depends on an existential reference bond `Dref`, the hidden constant depends on the
fixed bandwidth `etaLD`, and the local dimension satisfies `q ≥ 2`; in addition no conclusion at
the root beyond its viability is asserted on the success event. See
`docs/paper-gaps/alvv16_low_energy_family_scope.tex` and
`docs/paper-gaps/alvv16_approximation_parameters.tex`.
-/

open ManyBody (interval)

open Matrix
open scoped BigOperators TensorProduct ComplexOrder MatrixOrder Matrix.Norms.L2Operator ENNReal
open MeasureTheory

namespace TNLean.MPS.AreaLaw.ALVV

open TNLean.MPS.AreaLaw TNLean.Lattice

/-- The children of a long interval split at the midpoint have level at most
one less than the parent. Supporting ALVV, arXiv:1602.08828v2, merge
geometry, lines 1662–1677. -/
private theorem clog_half_lt {n : ℕ} (hn : 2 ≤ n) :
    Nat.clog 2 (n / 2) + 1 ≤ Nat.clog 2 n ∧ Nat.clog 2 (n - n / 2) + 1 ≤ Nat.clog 2 n := by
  have hrec := Nat.clog_of_two_le (by norm_num : 1 < 2) hn
  have hceil : n - n / 2 = (n + 2 - 1) / 2 := by omega
  refine ⟨?_, ?_⟩
  · rw [hrec]
    exact Nat.add_le_add_right (Nat.clog_mono_right 2 (by omega)) 1
  · rw [hrec, hceil]

/-- The corrected sampling failure bound increases with the dimension of the
target. Supporting ALVV, arXiv:1602.08828v2, `l:rs`, lines 530–558. -/
private theorem sampling_failure_mono {Q s a b : ℕ} (hab : a ≤ b) :
    (if Q ≤ s then (0 : ℝ) else
      (1 + 2 / Real.sqrt ((1 - (1 / 4 : ℝ)) * (s : ℝ) / (8 * (Q : ℝ)))) ^ (2 * a) *
        (Q : ℝ) * Real.exp (-(s / 16 : ℝ))) ≤
    (if Q ≤ s then (0 : ℝ) else
      (1 + 2 / Real.sqrt ((1 - (1 / 4 : ℝ)) * (s : ℝ) / (8 * (Q : ℝ)))) ^ (2 * b) *
        (Q : ℝ) * Real.exp (-(s / 16 : ℝ))) := by
  split_ifs
  · exact le_rfl
  · have hbase : 1 ≤ 1 + 2 / Real.sqrt ((1 - (1 / 4 : ℝ)) * (s : ℝ) / (8 * (Q : ℝ))) := by
      have : 0 ≤ 2 / Real.sqrt ((1 - (1 / 4 : ℝ)) * (s : ℝ) / (8 * (Q : ℝ))) := by positivity
      linarith only [this]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    exact pow_le_pow_right₀ hbase (by omega)

/-- **Success probability of the low-density merge tree.** With the families, windows, reference
bond and parameters of `exists_physical_ld_sampled_interval_tree_of_clause`, and for every
`0 < β < 1`, the canonical tree with `⌈log_D (D² s)⌉` rounds and one collective trim at every long
node has every node of dimension at most `D⁶ s³` for every coordinate, and outside a measurable
set of measure at most `(L - 1) β` its root and internal nodes `[p, r)` are all `3/200`-viable for
the windows `etaLD - 3w · clog₂ (r - p)`.

ALVV, arXiv:1602.08828v2, Theorem `t:alg2`, lines 1869–1878, in its probabilistic form, under the
markers of this module; the running time and the output clause are not formalized. -/
theorem exists_physical_ld_canonical_tree_failure_le (etaLD : ℝ) (hLD : 0 < etaLD) :
    ∃ C : ℝ, 100 ≤ C ∧ 19 + etaLD ≤ C ∧
      ∀ (L q m : ℕ) (w : ℝ) (hq : 2 ≤ q), q ≤ m → 0 < w →
      let mi := 4 * m
      let g := min w 1
      let u := 1 + Real.log (mi : ℝ) + Real.log (1 / g)
      let ell : ℕ := ⌈C * u ^ 2 / g⌉₊
      let D := (mi * ell ^ 2) ^ (22 * ell)
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ),
      (∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
        (h i) (interval L i.val (i.val + 2))) →
      ∀ (h0 : ∀ i, 0 ≤ h i), (∀ i, h i ≤ 1) →
      let _ : Nonempty (Fin L → Fin q) :=
        ⟨fun _ ↦ ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩⟩
      let H := ∑ i, h i
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
        let power := Nat.clog D (D ^ 2 * s)
        (s : ℝ) ≤ 4097 * (rG : ℝ) * A ∧
        (∀ (U : IntervalSamplingChoices L q) (p r : ℕ), p ≤ r → r ≤ L →
          Module.finrank ℂ (balancedIntervalSpace (canonicalWordTrimOperation N F power s xi U)
            width hwidth p r) ≤ count) ∧
        MeasurableSet
          (canonicalWordTrimTreeGoodOfTargets hwidth N F power s xi target (3 / 200)) ∧
        intervalSamplingMeasure L q
            (canonicalWordTrimTreeGoodOfTargets hwidth N F power s xi target (3 / 200))ᶜ ≤
          ((L - 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal beta) := by
  classical
  obtain ⟨C, hC, hCeta, hlong⟩ :=
    exists_fixed_bandwidth_long_interval_dyadic_low_energy_word_family etaLD hLD
  obtain ⟨_Kref, _hKref, hbasis⟩ :=
    exists_fixed_bandwidth_low_energy_orthonormal_mps_basis etaLD hLD
  refine ⟨C, hC, hCeta, ?_⟩
  intro L q m w hq hqm hw mi g u ell D h hsupp h0 h1 config H hRaw G rG
  let : Nonempty (Fin L → Fin q) := config
  have hm4 : m * 2 ^ 2 = mi := by dsimp only [mi]; ring
  have hfamily (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) := by
    have hfam := hlong L q m p r 2 w hq hqm hpr hrL hw h hsupp h0 h1
    rw [hm4, show (1 / 200 : ℝ) / 2 ^ (4 * 2) = 1 / 51200 by norm_num] at hfam
    exact hfam
  obtain ⟨hell, hlogD, -⟩ := hfamily 0 0 le_rfl (Nat.zero_le L)
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
  have hlevel (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) :
      (Nat.clog 2 (r - p) : ℝ) ≤ Nat.clog 2 L := by
    exact_mod_cast Nat.clog_mono_right 2 (by omega)
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
        hbasis L q (3 * w * K) (by omega) hv h hsupp h0 h1 (1 / 10000) (by norm_num) (by norm_num)
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
  intro xi beta hbeta hbeta1 A s count power
  obtain ⟨hs, hscount, htail, hfailure⟩ :=
    Real.viable_node_uniform_sampling_size hD hrG hbeta hbeta1.le
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
  have hcount : D ^ (2 * power) * s ≤ count := by
    calc D ^ (2 * power) * s = (D ^ power) ^ 2 * s := by rw [Nat.mul_comm 2 power, pow_mul]
      _ ≤ D ^ 6 * s ^ 3 := (Nat.viable_node_power_bounds hD hs).2.2.2
  refine ⟨hscount,
    finrank_balancedIntervalSpace_canonicalWordTrimOperation_le hwidth (by omega) N F hN hxi.le
      hxi1 hleaf hcount,
    measurableSet_canonicalWordTrimTreeGoodOfTargets hwidth N F power s xi target _, ?_⟩
  apply intervalSamplingMeasure_canonicalWordTrimTreeGoodOfTargets_compl_le hwidth (by omega) N F
    hN hxi.le hxi1 hleaf hcount target (by norm_num)
  intro J
  obtain ⟨⟨p, r⟩, hpr, hrL, hlongJ⟩ := J
  dsimp only
  intro hpk hkr S1 S2 hS1 hS2 hd1 hd2
  -- The level of the parent and the window of its children.
  obtain ⟨hleft, hright⟩ := clog_half_lt (n := r - p) (by omega)
  obtain ⟨K, hK⟩ : ∃ K, Nat.clog 2 (r - p) = K + 1 :=
    ⟨Nat.clog 2 (r - p) - 1, by omega⟩
  have hKL : ((K : ℝ) + 1) ≤ Nat.clog 2 L := by
    have := hlevel p r hpr hrL
    rw [hK] at this
    exact_mod_cast this
  let eta := etaLD - 3 * w * K
  have hbuffer : 6 * w ≤ eta := by
    dsimp only [eta]
    nlinarith only [hdepth, hKL, hw]
  have hetaLD : eta ≤ etaLD := by
    dsimp only [eta]
    nlinarith only [hw, (Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
  have hchild (a b : ℕ) (hab : Nat.clog 2 (b - a) + 1 ≤ Nat.clog 2 (r - p)) :
      G eta ≤ target a b := by
    apply hGmono
    have : (Nat.clog 2 (b - a) : ℝ) ≤ K := by
      have h' : Nat.clog 2 (b - a) ≤ K := by omega
      exact_mod_cast h'
    dsimp only [eta]
    nlinarith only [this, hw]
  have hS1' := hS1.of_target_le (Submodule.map_mono (hchild p (p + (r - p) / 2)
    (by simpa only [Nat.add_sub_cancel_left] using hleft)))
  have hS2' := hS2.of_target_le (Submodule.map_mono (hchild (p + (r - p) / 2) r
    (by simpa only [show r - (p + (r - p) / 2) = (r - p) - (r - p) / 2 by omega]
      using hright)))
  -- The low-density words of the parent at this window.
  obtain ⟨Tlo, Thi, Delta, _hnest, hupper, hlower, hDelta, htrade, himprove⟩ :=
    hwords ⟨(p, r), hpr, hrL, hlongJ⟩ eta hbuffer hetaLD
  let RC := Entropy.regionTensorCoordinates q (interval L p r)
  have hlower' : Submodule.IsCloseTo (1 / 51200) Tlo (G (eta - 3 * w)) := by
    simpa only [G, add_sub_assoc] using hlower
  have himprove' : ∀ (a : ℕ)
      (S : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q))) (delta : ℝ),
      Submodule.IsViable delta S (Thi.map RC.toLinearEquiv.toLinearMap) → delta < 1 →
      Submodule.IsViable (Delta ^ a / (1 - delta) ^ 2)
        (⨆ v : Fin a → Fin (N ⟨(p, r), hpr, hrL, hlongJ⟩),
          S.map (List.ofFn (fun j ↦ F ⟨(p, r), hpr, hrL, hlongJ⟩ (v j))).prod.toLinearMap)
        (Tlo.map RC.toLinearEquiv.toLinearMap) := by
    intro a S delta hS hdelta
    dsimp only [RC] at hS ⊢
    rw [Entropy.regionTensorCoordinates_eq_exteriorFirst] at hS ⊢
    exact (himprove a S delta hS hdelta).2
  have hbad := rankUnitaryHaar_canonical_interval_word_image_failure_le_of_nested hpk hkr hD hs
    (G eta) (G (eta - 3 * w)) Thi Tlo (hGne (by linarith only [hbuffer, hw]))
    (by norm_num) hupper hlower' hDelta.le htrade
    (F ⟨(p, r), hpr, hrL, hlongJ⟩) himprove' S1 S2 hS1' hS2' hd1 hd2
  have hdimThi : Module.finrank ℂ (Thi.map RC.toLinearEquiv.toLinearMap) ≤ rG := by
    rw [LinearEquiv.finrank_map_eq]
    exact (hupper.finrank_le (by norm_num)).trans (Submodule.finrank_mono (hGmono hetaLD))
  have hQ : Module.finrank ℂ (adjacentIntervalMerge L q p (p + (r - p) / 2) r hpk hkr S1 S2) ≤
      D ^ 12 * s ^ 6 :=
    calc _ ≤ Module.finrank ℂ S1 * Module.finrank ℂ S2 :=
          finrank_adjacentIntervalMerge_le hpk hkr S1 S2
      _ ≤ (D ^ 6 * s ^ 3) * (D ^ 6 * s ^ 3) := Nat.mul_le_mul hd1 hd2
      _ = D ^ 12 * s ^ 6 := by ring
  refine (measure_mono ?_).trans (hbad.trans (ENNReal.ofReal_le_ofReal
    (((sampling_failure_mono hdimThi).trans (hfailure _ hQ)).trans htail)))
  intro v hfail himage
  apply hfail
  · -- Trimming against the reference space of the parent's window.
    have hsR : (1 : ℝ) ≤ (s : ℝ) := Nat.one_le_cast.mpr hs
    have hden : (1 : ℝ) ≤ (s : ℝ) ^ 2 := one_le_pow₀ hsR
    have hratio : (1024 / 9 : ℝ) * (1 / 100000) / (s : ℝ) ^ 2 ≤
        (1024 / 9 : ℝ) * (1 / 100000) := by
      apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hden)).mpr
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hden
        (by norm_num : (0 : ℝ) ≤ (1024 / 9 : ℝ) * (1 / 100000))
    have hcut : eta - 3 * w = etaLD - 3 * w * ((Nat.clog 2 (r - p) : ℕ) : ℝ) := by
      dsimp only [eta]
      rw [hK]
      push_cast
      ring
    have hKL' : K + 1 ≤ Nat.clog 2 L := by exact_mod_cast hKL
    obtain ⟨hGU, hUG, hUMPS⟩ := hUref (K + 1) (by omega)
    have hcutK : etaLD - 3 * w * ((K + 1 : ℕ) : ℝ) = eta - 3 * w := by
      dsimp only [eta]
      push_cast
      ring
    rw [hcutK] at hGU hUG
    have hsmall : Submodule.IsViable (1 / 400 : ℝ)
        (⨆ i, (canonicalIntervalRangeSample L q p r s
          (adjacentIntervalMerge L q p (p + (r - p) / 2) r hpk hkr S1 S2) v).map
            (wordFamily (F ⟨(p, r), hpr, hrL, hlongJ⟩) power i).toLinearMap)
        ((G (eta - 3 * w)).map RC.toLinearEquiv.toLinearMap) := by
      rw [iSup_map_wordFamily]
      exact Submodule.IsCloseTo.of_le himage (by linarith only [hratio])
    have hradius := Real.viable_node_trimming_radius_budget (L := L) (D := Dref)
      (show r - p - 1 ≤ L by omega) hDref
    have hT : G (eta - 3 * w) = target p r := congrArg G hcut
    have hb : 4 * xi * Real.sqrt (((r - p - 1 : ℕ) : ℝ) * (Dref : ℝ) ^ 2) ≤ 1 / 250 :=
      hradius.2
    unfold canonicalSampledIntervalWordTrim intervalFamilyTrimStep
    dsimp only
    rw [← hT]
    exact Submodule.IsCloseTo.of_le (isViable_intervalTrimSubspace_of_reference hDref
      (by norm_num : (0 : ℝ) ≤ 1 / 10000) (by norm_num : (0 : ℝ) ≤ 1 / 400) hxi hGU hUG
      (fun v hv ↦ (hUMPS v hv).mono (hDK_le (K + 1) hKL')) _ hsmall) (by linarith only [hb])

end TNLean.MPS.AreaLaw.ALVV
