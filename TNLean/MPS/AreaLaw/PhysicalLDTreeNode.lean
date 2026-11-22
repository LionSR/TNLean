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
import QICLean.Analysis.Parameter.ViableRefinementParameters
import QICLean.Analysis.Parameter.ViableNodeParameters
import QICLean.Analysis.Subspace.ViableSubspace

/-!
# The node event of the low-density merge tree

One long node of the sampled merge tree for a low-density spectrum. Its two
children are `3/200`-viable for the windows of their levels; the merged space is
sampled, the words of the parent's family are applied, and the image is trimmed
collectively against a reference matrix product space. With positive probability the
result is `3/200`-viable for the parent's window, one buffer `3w` shorter.

The windows form any monotone family `G` of nonzero spaces, and the word families
and references are hypotheses, so that the tree in
`TNLean.MPS.AreaLaw.PhysicalLDTree` supplies them from the original Hamiltonian.
This is the merge step of ALVV, arXiv:1602.08828v2, Theorem `t:alg1`,
lines 1777–1817, as used by Theorem `t:alg2`, lines 1869–1878.

**Scope restriction (one final trim):** The node applies one collective trim after its
sampled word image, as in the gapped tree; see
`docs/paper-gaps/alvv16_approximation_parameters.tex`.
-/

open ManyBody (interval)

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory

namespace TNLean.MPS.AreaLaw

open Matrix

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

/-- One long node of the low-density merge tree. For a monotone family `G` of nonzero
windows, word families improving `G(η)` to `G(η - 3w)` on every long interval, and
reference matrix product spaces of bond `Dref` close to the windows of every level, the
sampled and trimmed merge of two children viable for their levels is, on an event whose
complement has the corrected sampling failure probability, `3/200`-viable for the window
`etaLD - 3w · clog₂ (r - p)` of the parent. ALVV, arXiv:1602.08828v2, Theorem `t:alg1`,
lines 1777–1817, with the families of Theorem `t:aisgapless`, lines 1027–1041. -/
theorem physical_ld_tree_node {L q width D rG s Dref : ℕ} {etaLD w xi : ℝ}
    (G : ℝ → Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (hGmono : ∀ {a b : ℝ}, a ≤ b → G a ≤ G b)
    (hGne : ∀ {eta : ℝ}, 0 ≤ eta → G eta ≠ ⊥)
    (hrG : Module.finrank ℂ (G etaLD) ≤ rG)
    (hwidth : 1 ≤ width) (hw : 0 < w) (hdepth : 3 * w * ((Nat.clog 2 L : ℝ) + 1) ≤ etaLD)
    (hD : 2 ≤ D) (hs : 1 ≤ s)
    (N : LongIntervalIndex L width → ℕ)
    (F : ∀ J : LongIntervalIndex L width,
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (hN : ∀ J, N J ≤ D ^ 2)
    (hwords : ∀ (J : LongIntervalIndex L width) (eta : ℝ), 6 * w ≤ eta → eta ≤ etaLD →
      ∃ (Tlo Thi : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) (Delta : ℝ),
        Submodule.IsCloseTo (1 / 51200) (G eta) Thi ∧
        Submodule.IsCloseTo (1 / 51200) Tlo (G (eta - 3 * w)) ∧
        0 < Delta ∧ (D : ℝ) ^ 12 * Delta ≤ 1 / 100000 ∧
        ∀ (a : ℕ) (S : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)))
          (delta : ℝ),
          Submodule.IsViable delta S (Thi.map (Entropy.regionTensorCoordinates q
            (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap) → delta < 1 →
          Submodule.IsViable (Delta ^ a / (1 - delta) ^ 2)
            (⨆ v : Fin a → Fin (N J), S.map (List.ofFn (fun j ↦ F J (v j))).prod.toLinearMap)
            (Tlo.map (Entropy.regionTensorCoordinates q
              (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap))
    (Uref : ℕ → Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (hUref : ∀ K : ℕ, 1 ≤ K → K ≤ Nat.clog 2 L →
      Submodule.IsCloseTo (1 / 10000) (G (etaLD - 3 * w * K)) (Uref K) ∧
      Submodule.IsCloseTo (1 / 10000) (Uref K) (G (etaLD - 3 * w * K)) ∧
      ∀ v ∈ Uref K, IsOpenMPS L q Dref (fun x ↦ v x))
    (hDref : 1 ≤ Dref) (hxi : xi = 1 / (1000 * (Dref : ℝ) * Real.sqrt ((L : ℝ) + 1))) :
    let target := fun p r : ℕ ↦ G (etaLD - 3 * w * Nat.clog 2 (r - p))
    let failure : ℕ → ℝ := fun Q ↦ if Q ≤ s then 0 else
      (1 + 2 / Real.sqrt ((1 - (1 / 4 : ℝ)) * (s : ℝ) / (8 * Q))) ^ (2 * rG) * Q *
        Real.exp (-(s / 16 : ℝ))
    ∀ (J : LongIntervalIndex L width) (k : ℕ) (hpk : J.val.1 ≤ k) (hkr : k ≤ J.val.2)
      (_hcutk : k = J.val.1 + (J.val.2 - J.val.1) / 2)
      (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 k → Fin q)))
      (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k J.val.2 → Fin q))),
      Submodule.IsViable (3 / 200 : ℝ) S1
        ((target J.val.1 k).map (Entropy.regionTensorCoordinates q
          (interval L J.val.1 k)).toLinearEquiv.toLinearMap) →
      Submodule.IsViable (3 / 200 : ℝ) S2
        ((target k J.val.2).map (Entropy.regionTensorCoordinates q
          (interval L k J.val.2)).toLinearEquiv.toLinearMap) →
      Module.finrank ℂ S1 ≤ D ^ 6 * s ^ 3 → Module.finrank ℂ S2 ≤ D ^ 6 * s ^ 3 →
      let W := adjacentIntervalMerge L q J.val.1 k J.val.2 hpk hkr S1 S2
      ∃ Good : Set (Matrix.unitaryGroup (Fin (Module.finrank ℂ W)) ℂ),
        Matrix.unitaryHaar (Fin (Module.finrank ℂ W)) Goodᶜ ≤
          ENNReal.ofReal (failure (Module.finrank ℂ W)) ∧
        ∀ U ∈ Good, Submodule.IsViable (3 / 200 : ℝ)
          (sampledIntervalTrim L q J.val.1 J.val.2 (F J)
            (Nat.clog D (D ^ 2 * s)) s xi W U)
          ((target J.val.1 J.val.2).map (Entropy.regionTensorCoordinates q
            (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap) := by
  intro target failure
  have hxi0 : 0 < xi := by
    rw [hxi]
    exact (Real.viable_node_trimming_radius_budget (L := L) (cuts := 0) (Nat.zero_le L) hDref).1
  intro J k hpk hkr hmid S1 S2 hS1 hS2 hd1 hd2 W
  obtain ⟨⟨p, r⟩, hpr, hrL, hlongJ⟩ := J
  dsimp only at hpk hkr hmid S1 S2 hS1 hS2 hd1 hd2 W ⊢
  subst hmid
  -- The level of the parent and the window of its children.
  -- Projections and local definitions avoid re-checking the large node goal.
  have hhalf := clog_half_lt (n := r - p) (by omega)
  have hleft := hhalf.1
  have hright := hhalf.2
  let K := Nat.clog 2 (r - p) - 1
  have hK : Nat.clog 2 (r - p) = K + 1 := by omega
  have hKL : ((K : ℝ) + 1) ≤ Nat.clog 2 L := by
    have hlev : Nat.clog 2 (r - p) ≤ Nat.clog 2 L := Nat.clog_mono_right 2 (by omega)
    rw [hK] at hlev
    exact_mod_cast hlev
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
  have hwordsJ := hwords ⟨(p, r), hpr, hrL, hlongJ⟩ eta hbuffer hetaLD
  refine hwordsJ.elim fun Tlo hwordsJ ↦ hwordsJ.elim fun Thi hwordsJ ↦
    hwordsJ.elim fun Delta hwordsJ ↦ ?_
  have hupper := hwordsJ.1
  have hlower' := hwordsJ.2.1
  have hDelta := hwordsJ.2.2.1
  have htrade := hwordsJ.2.2.2.1
  have himprove' := hwordsJ.2.2.2.2
  let RC := Entropy.regionTensorCoordinates q (interval L p r)
  have hevent := exists_measurable_interval_word_image_event_of_nested hpk hkr hD hs
      (G eta) (G (eta - 3 * w)) Thi Tlo (hGne (by linarith only [hbuffer, hw]))
      (by norm_num) (by norm_num) hupper hlower' hDelta.le htrade
      (F ⟨(p, r), hpr, hrL, hlongJ⟩) (hN _) himprove' S1 S2 hS1' hS2' hd1 hd2
  refine hevent.elim fun Good hGood ↦ ?_
  have hbad := hGood.2.1
  have himages := hGood.2.2.2
  dsimp only [W]
  refine ⟨Good, ?_, ?_⟩
  · -- The event's failure bound with the dimension of the upper target.
    have hdimThi : Module.finrank ℂ (Thi.map RC.toLinearEquiv.toLinearMap) ≤ rG := by
      rw [LinearEquiv.finrank_map_eq]
      exact ((hupper.finrank_le (by norm_num)).trans
        (Submodule.finrank_mono (hGmono hetaLD))).trans hrG
    exact hbad.trans (ENNReal.ofReal_le_ofReal (sampling_failure_mono hdimThi))
  · -- Trimming against the reference space of the parent's window.
    intro U hU
    have hV := (himages U hU).2
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
    have hUrefK := hUref (K + 1) (by omega) hKL'
    have hGU := hUrefK.1
    have hUG := hUrefK.2.1
    have hUMPS := hUrefK.2.2
    have hcutK : etaLD - 3 * w * ((K + 1 : ℕ) : ℝ) = eta - 3 * w := by
      dsimp only [eta]
      push_cast
      ring
    rw [hcutK] at hGU hUG
    have hsmall : Submodule.IsViable (1 / 400 : ℝ)
        (Submodule.sampledWordImage (F ⟨(p, r), hpr, hrL, hlongJ⟩)
          (Nat.clog D (D ^ 2 * s)) s
          (adjacentIntervalMerge L q p (p + (r - p) / 2) r hpk hkr S1 S2) U)
        ((G (eta - 3 * w)).map RC.toLinearEquiv.toLinearMap) :=
      Submodule.IsCloseTo.of_le hV (by linarith only [hratio])
    have htrim := isViable_intervalTrimSubspace_of_reference hDref
      (by norm_num : (0 : ℝ) ≤ 1 / 10000) (by norm_num : (0 : ℝ) ≤ 1 / 400) hxi0 hGU hUG hUMPS
      (stdOrthonormalBasis ℂ _) hsmall
    have hradius := Real.viable_node_trimming_radius_budget (L := L) (D := Dref)
      (show r - p - 1 ≤ L by omega) hDref
    have hT : G (eta - 3 * w) = target p r := congrArg G hcut
    rw [hT] at htrim
    have hb : 4 * xi * Real.sqrt (((r - p - 1 : ℕ) : ℝ) * (Dref : ℝ) ^ 2) ≤ 1 / 250 := by
      rw [hxi]
      exact hradius.2
    unfold sampledIntervalTrim
    exact Submodule.IsCloseTo.of_le htrim (by linarith only [hb])

end TNLean.MPS.AreaLaw
