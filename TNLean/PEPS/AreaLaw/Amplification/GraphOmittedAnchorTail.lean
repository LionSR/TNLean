/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.ExponentialDistanceProfile
import QICLean.Analysis.StretchedExponentialSummability
import TNLean.PEPS.AreaLaw.Amplification.GraphChannelWeightedRow
import TNLean.PEPS.AreaLaw.GraphExtendedMetric

/-!
# Exponential tails for omitted graph anchors

Quadratic graph-ball growth and bounded anchor multiplicity control the sum of
finite shell weights against a distance profile. If every omitted anchor is
farther than `r` from the finite target set, the sum decays exponentially in
`r ^ α`. The constants precede the graph, all finite types, the omitted labels,
the support and the shell cutoff. Empty sets and disconnected components are
retained, using extended graph distance before taking real values.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`09-amplification.tex`, lines 203–215, at revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean text is reused.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open QuantumCircuit
open scoped BigOperators ENNReal

namespace TNLean.PEPS.AreaLaw

private theorem profile_finset_le_sum_singleton {ι : Type*} [PseudoEMetricSpace ι]
    (S : Finset ι) (c α : ℝ) (z : ι) :
    Metric.exponentialDistanceProfile (S : Set ι) c α z ≤
      ∑ s ∈ S, Metric.exponentialDistanceProfile {s} c α z := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  obtain ⟨s, hs, hdist⟩ := S.finite_toSet.isCompact.exists_infEDist_eq_edist
    (by simpa using hS) z
  have heq : Metric.exponentialDistanceProfile (S : Set ι) c α z =
      Metric.exponentialDistanceProfile {s} c α z := by
    simp only [Metric.exponentialDistanceProfile, Metric.infEDist_singleton, hdist]
  rw [heq]
  exact Finset.single_le_sum (fun x _ => Metric.exponentialDistanceProfile_nonneg {x} c α z) hs

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- A singleton distance profile has a volume-independent total mass under
quadratic graph-ball growth. The moment is the existing QICLean summable
second moment. Source: area law, `09-amplification.tex`, lines 203–212. -/
theorem sum_graph_singleton_exponentialDistanceProfile_le
    (G : SimpleGraph ι) {K c α : ℝ} (hK : 0 ≤ K) (hc : 0 < c) (hα : 0 < α)
    (hball : ∀ x l, ((graphBall G x l).card : ℝ) ≤ K * ((l : ℝ) + 1) ^ 2)
    (s : ι) :
    letI := graphPseudoEMetricSpace G
    (∑ z, Metric.exponentialDistanceProfile {s} c α z) ≤
      K * ∑' n : ℕ, (1 + (n : ℝ)) ^ 2 * Real.exp (-c * (n : ℝ) ^ α) := by
  classical
  let := graphPseudoEMetricSpace G
  let T := Finset.univ.filter fun z => G.Reachable s z
  let D := T.image (G.dist s)
  have hprofile (z : ι) : Metric.exponentialDistanceProfile {s} c α z =
      if G.Reachable s z then Real.exp (-c * (G.dist s z : ℝ) ^ α) else 0 := by
    by_cases hz : G.Reachable s z
    · have hz' : edist z s ≠ ⊤ :=
        (graphPseudoEMetricSpace_edist_ne_top G z s).mpr hz.symm
      rw [Metric.exponentialDistanceProfile, Metric.infEDist_singleton, ite_eq_right hz',
        graphPseudoEMetricSpace_edist_toReal, G.dist_comm, ite_eq_left hz]
    · have hz' : edist z s = ⊤ :=
        (graphPseudoEMetricSpace_edist_eq_top G z s).mpr (fun h => hz h.symm)
      rw [Metric.exponentialDistanceProfile, Metric.infEDist_singleton,
        ite_eq_left hz', ite_eq_right hz]
  have hfiber (n : ℕ) : ((T.filter fun z => G.dist s z = n).card : ℝ) ≤
      K * ((n : ℝ) + 1) ^ 2 := by
    apply le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_)) (hball s n)
    intro z hz
    obtain ⟨hzT, hzn⟩ := Finset.mem_filter.mp hz
    have hreach : G.Reachable s z := (Finset.mem_filter.mp hzT).2
    apply mem_graphBall.mpr
    rw [← hreach.coe_dist_eq_edist, hzn]
  calc
    _ = ∑ z ∈ T, Real.exp (-c * (G.dist s z : ℝ) ^ α) := by
      simp only [hprofile, T, Finset.sum_filter]
    _ = ∑ n ∈ D, ((T.filter fun z => G.dist s z = n).card : ℝ) *
        Real.exp (-c * (n : ℝ) ^ α) := by
      have h := Finset.sum_fiberwise_of_maps_to' (s := T) (t := D) (g := G.dist s)
        (fun z hz => Finset.mem_image_of_mem (G.dist s) hz)
        (fun n : ℕ => Real.exp (-c * (n : ℝ) ^ α))
      simpa only [Finset.sum_const, nsmul_eq_mul] using h.symm
    _ ≤ ∑ n ∈ D, (K * ((n : ℝ) + 1) ^ 2) * Real.exp (-c * (n : ℝ) ^ α) := by
      exact Finset.sum_le_sum fun n _ =>
        mul_le_mul_of_nonneg_right (hfiber n) (Real.exp_pos _).le
    _ = K * ∑ n ∈ D, (1 + (n : ℝ)) ^ 2 * Real.exp (-c * (n : ℝ) ^ α) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((Real.summable_nat_pow_mul_exp_neg_mul_rpow 2 hc hα).sum_le_tsum D
        (fun _ _ => by positivity)) hK

/-- The total profile mass is at most the singleton mass times the support
cardinality, including zero mass for the empty support. Source: area law,
`09-amplification.tex`, lines 203–212. -/
theorem sum_graph_exponentialDistanceProfile_le
    (G : SimpleGraph ι) {K c α : ℝ} (hK : 0 ≤ K) (hc : 0 < c) (hα : 0 < α)
    (hball : ∀ x l, ((graphBall G x l).card : ℝ) ≤ K * ((l : ℝ) + 1) ^ 2)
    (S : Finset ι) :
    letI := graphPseudoEMetricSpace G
    (∑ z, Metric.exponentialDistanceProfile (S : Set ι) c α z) ≤
      (S.card : ℝ) * K * ∑' n : ℕ, (1 + (n : ℝ)) ^ 2 *
        Real.exp (-c * (n : ℝ) ^ α) := by
  classical
  let := graphPseudoEMetricSpace G
  calc
    _ ≤ ∑ z, ∑ s ∈ S, Metric.exponentialDistanceProfile {s} c α z :=
      Finset.sum_le_sum fun z _ => profile_finset_le_sum_singleton S c α z
    _ = ∑ s ∈ S, ∑ z, Metric.exponentialDistanceProfile {s} c α z := Finset.sum_comm
    _ ≤ ∑ _s ∈ S, K * ∑' n : ℕ, (1 + (n : ℝ)) ^ 2 *
        Real.exp (-c * (n : ℝ) ^ α) :=
      Finset.sum_le_sum fun s _ =>
        sum_graph_singleton_exponentialDistanceProfile_le G hK hc hα hball s
    _ = _ := by simp [mul_assoc]

/-- A shell meeting a profile based beyond radius `r` spends half its decay
rate on `r`, leaving both half-rate factors available for summation. Infinite
distance to the support gives a literal zero on both sides. Source: area law,
`09-amplification.tex`, lines 203–212. -/
theorem exp_mul_graph_exponentialDistanceProfile_le_of_anchor_far
    (G : SimpleGraph ι) (S : Finset ι) {b β α r : ℝ}
    (hb : 0 < b) (hβ : 0 < β) (hα : 0 < α) (hα₁ : α ≤ 1) (hr : 0 ≤ r)
    {x z : ι} {l : ℕ} (hz : z ∈ graphBall G x l)
    (hfar : ∀ s ∈ S, ENNReal.ofReal r < (G.edist x s : ℝ≥0∞)) :
    letI := graphPseudoEMetricSpace G
    Real.exp (-b * (l : ℝ) ^ α) * Metric.exponentialDistanceProfile (S : Set ι) β α z ≤
      Real.exp (-((min b β) / 2) * r ^ α) *
        (Real.exp (-(b / 2) * (l : ℝ) ^ α) *
          Metric.exponentialDistanceProfile (S : Set ι) (β / 2) α z) := by
  classical
  let := graphPseudoEMetricSpace G
  by_cases hzS : Metric.infEDist z (S : Set ι) = ⊤
  · simp [Metric.exponentialDistanceProfile, hzS]
  have hxz' : G.edist x z ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (mem_graphBall.mp hz)
  have hxz : edist x z ≠ ⊤ := by
    simpa only [graphPseudoEMetricSpace_edist, ENat.toENNReal_ne_top] using hxz'
  have hdist : (edist x z).toReal ≤ (l : ℝ) := by
    rw [graphPseudoEMetricSpace_edist_toReal]
    exact_mod_cast G.natCast_dist_le_edist.trans (mem_graphBall.mp hz)
  have htriangle : Metric.infEDist x (S : Set ι) ≤
      edist x z + Metric.infEDist z (S : Set ι) := Metric.infEDist_le_edist_add_infEDist
  have hxS : Metric.infEDist x (S : Set ι) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hxz, hzS⟩) htriangle
  have hsep : ENNReal.ofReal r ≤ Metric.infEDist x (S : Set ι) := by
    apply Metric.le_infEDist.mpr
    intro s hs
    exact (hfar s hs).le
  have hrx := (ENNReal.ofReal_le_iff_le_toReal hxS).mp hsep
  have htri := ENNReal.toReal_le_add htriangle hxz hzS
  have hpow : r ^ α ≤ (l : ℝ) ^ α + (Metric.infEDist z (S : Set ι)).toReal ^ α :=
    (Real.rpow_le_rpow hr (by linarith) hα.le).trans
      (Real.rpow_add_le_add_rpow (by positivity) ENNReal.toReal_nonneg hα.le hα₁)
  have hrate : (min b β) / 2 * r ^ α ≤ b / 2 * (l : ℝ) ^ α +
      β / 2 * (Metric.infEDist z (S : Set ι)).toReal ^ α := by
    calc
      _ ≤ (min b β) / 2 * ((l : ℝ) ^ α +
          (Metric.infEDist z (S : Set ι)).toReal ^ α) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ _ := by
        rw [mul_add]
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_right (min_le_left b β) (by norm_num)) (by positivity)
        · exact mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_right (min_le_right b β) (by norm_num)) (by positivity)
  rw [Metric.exponentialDistanceProfile_of_ne_top _ _ _ _ hzS,
    Metric.exponentialDistanceProfile_of_ne_top _ _ _ _ hzS,
    ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

variable [DecidableEq ι]

/-- Bounded anchor fibers reduce the unweighted incidence sum of a
nonnegative site function to its total mass times a quadratic ball bound.
The counting step reuses `card_graphBall_anchors_le`. Source: area law,
`09-amplification.tex`, lines 203–212. -/
theorem sum_graphBall_site_function_le (G : SimpleGraph ι) (a : κ → ι)
    {K μ : ℝ} (hμ : 0 ≤ μ)
    (hball : ∀ x l, ((graphBall G x l).card : ℝ) ≤ K * ((l : ℝ) + 1) ^ 2)
    (hfiber : ∀ x, ((Finset.univ.filter fun i : κ => a i = x).card : ℝ) ≤ μ)
    (f : ι → ℝ) (hf : ∀ z, 0 ≤ f z) (l : ℕ) :
    (∑ i, ∑ z ∈ graphBall G (a i) l, f z) ≤
      μ * K * ((l : ℝ) + 1) ^ 2 * ∑ z, f z := by
  classical
  have hcount (z : ι) :
      ((Finset.univ.filter fun i : κ => z ∈ graphBall G (a i) l).card : ℝ) ≤
        μ * K * ((l : ℝ) + 1) ^ 2 := by
    calc
      _ ≤ μ * (graphBall G z l).card := card_graphBall_anchors_le G a hfiber z l
      _ ≤ μ * (K * ((l : ℝ) + 1) ^ 2) := mul_le_mul_of_nonneg_left (hball z l) hμ
      _ = _ := by ring
  calc
    _ = ∑ z, ((Finset.univ.filter fun i : κ =>
        z ∈ graphBall G (a i) l).card : ℝ) * f z := by
      calc
        _ = ∑ i, ∑ z, if z ∈ graphBall G (a i) l then f z else 0 := by simp
        _ = ∑ z, ∑ i, if z ∈ graphBall G (a i) l then f z else 0 := Finset.sum_comm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro z _
          rw [Finset.natCast_card_filter, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          split_ifs <;> simp
    _ ≤ ∑ z, (μ * K * ((l : ℝ) + 1) ^ 2) * f z :=
      Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_right (hcount z) (hf z)
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- The unrestricted finite anchor-shell sum is controlled by the product of
two summable second moments. No bound depends on the site count or cutoff.
Source: area law, `09-amplification.tex`, lines 203–212. -/
theorem sum_graphBall_exponentialDistanceProfile_le
    (G : SimpleGraph ι) (a : κ → ι) {K μ b β α : ℝ}
    (hK : 0 ≤ K) (hμ : 0 ≤ μ) (hb : 0 < b) (hβ : 0 < β) (hα : 0 < α)
    (hball : ∀ x l, ((graphBall G x l).card : ℝ) ≤ K * ((l : ℝ) + 1) ^ 2)
    (hfiber : ∀ x, ((Finset.univ.filter fun i : κ => a i = x).card : ℝ) ≤ μ)
    (S : Finset ι) (N : ℕ) :
    letI := graphPseudoEMetricSpace G
    (∑ i, ∑ l ∈ Finset.range (N + 1), Real.exp (-b * (l : ℝ) ^ α) *
      ∑ z ∈ graphBall G (a i) l, Metric.exponentialDistanceProfile (S : Set ι) β α z) ≤
      μ * K ^ 2 *
        (∑' n : ℕ, (1 + (n : ℝ)) ^ 2 * Real.exp (-b * (n : ℝ) ^ α)) *
        (∑' n : ℕ, (1 + (n : ℝ)) ^ 2 * Real.exp (-β * (n : ℝ) ^ α)) * S.card := by
  classical
  let := graphPseudoEMetricSpace G
  let M (c : ℝ) := ∑' n : ℕ, (1 + (n : ℝ)) ^ 2 * Real.exp (-c * (n : ℝ) ^ α)
  have hM (c : ℝ) : 0 ≤ M c := tsum_nonneg fun _ => by positivity
  have hsite := sum_graph_exponentialDistanceProfile_le G hK hβ hα hball S
  have hshell (l : ℕ) :
      (∑ i, ∑ z ∈ graphBall G (a i) l, Metric.exponentialDistanceProfile (S : Set ι) β α z) ≤
        μ * K ^ 2 * M β * S.card * (1 + (l : ℝ)) ^ 2 := by
    calc
      _ ≤ μ * K * ((l : ℝ) + 1) ^ 2 *
          ∑ z, Metric.exponentialDistanceProfile (S : Set ι) β α z :=
        sum_graphBall_site_function_le G a hμ hball hfiber _
          (Metric.exponentialDistanceProfile_nonneg _ _ _) l
      _ ≤ μ * K * ((l : ℝ) + 1) ^ 2 * ((S.card : ℝ) * K * M β) :=
        mul_le_mul_of_nonneg_left hsite (by positivity)
      _ = _ := by ring
  calc
    _ = ∑ l ∈ Finset.range (N + 1), Real.exp (-b * (l : ℝ) ^ α) *
        ∑ i, ∑ z ∈ graphBall G (a i) l,
          Metric.exponentialDistanceProfile (S : Set ι) β α z := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ l ∈ Finset.range (N + 1), Real.exp (-b * (l : ℝ) ^ α) *
        (μ * K ^ 2 * M β * S.card * (1 + (l : ℝ)) ^ 2) :=
      Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hshell l) (Real.exp_pos _).le
    _ = (μ * K ^ 2 * M β * S.card) * ∑ l ∈ Finset.range (N + 1),
        (1 + (l : ℝ)) ^ 2 * Real.exp (-b * (l : ℝ) ^ α) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ ≤ (μ * K ^ 2 * M β * S.card) * M b :=
      mul_le_mul_of_nonneg_left
        ((Real.summable_nat_pow_mul_exp_neg_mul_rpow 2 hb hα).sum_le_tsum _
          (fun _ _ => by positivity)) (by positivity)
    _ = _ := by dsimp [M]; ring

/-- Omitted anchor-shell weights have a uniform stretched-exponential tail.
The witnesses depend only on `K, μ, b, β, α`, and precede the graph, finite
site and event types, omitted labels, target support, cutoff and radius.
The exponent is `(min b β) / 2`; empty supports, empty omitted sets and
arbitrary disconnected graphs require no special hypotheses.
Source: area law, `09-amplification.tex`, lines 203–215. -/
theorem exists_sum_omitted_graphBall_exponentialDistanceProfile_le
    {K μ b β α : ℝ} (hK : 0 ≤ K) (hμ : 0 ≤ μ)
    (hb : 0 < b) (hβ : 0 < β) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ C γ : ℝ, 0 ≤ C ∧ 0 < γ ∧ γ = (min b β) / 2 ∧
      ∀ (ι κ : Type*) [Fintype ι] [DecidableEq ι] [Fintype κ]
        (G : SimpleGraph ι) (a : κ → ι),
        (∀ x l, ((graphBall G x l).card : ℝ) ≤ K * ((l : ℝ) + 1) ^ 2) →
        (∀ x, ((Finset.univ.filter fun i : κ => a i = x).card : ℝ) ≤ μ) →
        ∀ (E : Finset κ) (S : Finset ι) (N : ℕ) (r : ℝ), 0 ≤ r →
          (∀ i ∈ E, ∀ s ∈ S, ENNReal.ofReal r < (G.edist (a i) s : ℝ≥0∞)) →
          letI := graphPseudoEMetricSpace G
          (∑ i ∈ E, ∑ l ∈ Finset.range (N + 1), Real.exp (-b * (l : ℝ) ^ α) *
            ∑ z ∈ graphBall G (a i) l,
              Metric.exponentialDistanceProfile (S : Set ι) β α z) ≤
            C * S.card * Real.exp (-γ * r ^ α) := by
  let M (c : ℝ) := ∑' n : ℕ, (1 + (n : ℝ)) ^ 2 * Real.exp (-c * (n : ℝ) ^ α)
  have hM (c : ℝ) : 0 ≤ M c := tsum_nonneg fun _ => by positivity
  refine ⟨μ * K ^ 2 * M (b / 2) * M (β / 2), (min b β) / 2,
    by positivity, by positivity, rfl, ?_⟩
  intro ι κ _ _ _ G a hball hfiber E S N r hr hfar
  classical
  let := graphPseudoEMetricSpace G
  let F (c d : ℝ) (i : κ) := ∑ l ∈ Finset.range (N + 1),
    Real.exp (-c * (l : ℝ) ^ α) *
      ∑ z ∈ graphBall G (a i) l, Metric.exponentialDistanceProfile (S : Set ι) d α z
  have hF (c d : ℝ) (i : κ) : 0 ≤ F c d i := by
    apply Finset.sum_nonneg
    intro l _
    exact mul_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun z _ =>
      Metric.exponentialDistanceProfile_nonneg _ _ _ _)
  have hterm (i : κ) (hi : i ∈ E) : F b β i ≤
      Real.exp (-((min b β) / 2) * r ^ α) * F (b / 2) (β / 2) i := by
    dsimp [F]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l _
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun z hz =>
      exp_mul_graph_exponentialDistanceProfile_le_of_anchor_far G S
        hb hβ hα hα₁ hr hz (hfar i hi)
  have hfull := sum_graphBall_exponentialDistanceProfile_le G a hK hμ
    (half_pos hb) (half_pos hβ) hα hball hfiber S N
  calc
    _ = ∑ i ∈ E, F b β i := rfl
    _ ≤ ∑ i ∈ E, Real.exp (-((min b β) / 2) * r ^ α) * F (b / 2) (β / 2) i :=
      Finset.sum_le_sum hterm
    _ = Real.exp (-((min b β) / 2) * r ^ α) * ∑ i ∈ E, F (b / 2) (β / 2) i :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ Real.exp (-((min b β) / 2) * r ^ α) * ∑ i, F (b / 2) (β / 2) i :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E)
          (fun i _ _ => hF _ _ i)) (Real.exp_pos _).le
    _ ≤ Real.exp (-((min b β) / 2) * r ^ α) *
        (μ * K ^ 2 * M (b / 2) * M (β / 2) * S.card) :=
      mul_le_mul_of_nonneg_left hfull (Real.exp_pos _).le
    _ = _ := by ring

end TNLean.PEPS.AreaLaw
