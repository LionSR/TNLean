/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.LatticeConstraints
import TNLean.PEPS.AreaLaw.LatticeCounts
import QICLean.Analysis.ContractionWordDecay
import QICLean.Probability.PoissonWordPartition
import QICLean.Probability.PoissonWordRealOccupation

/-!
# Truncating the retained constraint product

Let `D_ret` be the chronological product of the roots `G_i = (I - k_i)^{1/2}`
over the events of a Poisson word whose anchors lie within `r` of a set `S`,
and let `L` be the same product with each `G_i` replaced by
`G_{i,r} = (I - E_{i,r} k_i)^{1/2}`, where `E_{i,r}` is the conditional
expectation onto the ball `N_r(a_i)`. Telescoping the two products gives
`‖D_ret - L‖ ≤ n ε` for a word with `n` retained events when each factor
changes by at most `ε`. Under the Poisson word law the expected number of
retained events is the number of retained labels times `t`.

On a finite induced lattice domain the number of labels anchored within `r`
of `S` is at most a constant times `|S| (1 + r)²`, by the ball count and
the anchor multiplicity bound. Together with the root tail this gives the
truncation estimate `eq:amplification-product-truncation`,
`E‖D_ret - L‖ ≤ C t |S| (1 + r)² e^{-c r^α}`, on the same realization of
the full word as the untruncated product, with constants chosen before the
domain. Each truncated product is a contraction supported on `N_{2r}(S)`.

The factors are written `CFC.sqrt (1 - k_i)`. For `0 ≤ k_i ≤ I`, the case of the
source and of the lattice constraints, this is the positive root of `I - k_i`. The
generic lemmas assume only `0 ≤ k_i`; then `CFC.sqrt (1 - k_i)` is still a positive
contraction, which is all their proofs use.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Lemma 10.1 (`lem:amplification-local-products`),
  `09-amplification.tex`, lines 42–63 (statement) and 228–234 (proof of
  `eq:amplification-product-truncation`), at revision
  `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The root tail is
  Lemma 4.4, `03-quasilocal.tex`, lines 336–389; the lattice counts are
  `01-preliminaries.tex`, lines 82–103. Independently formalized from the
  manuscript; no upstream Lean text is reused.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open QuantumCircuit SpectralFilter Matrix MeasureTheory
open scoped BigOperators NNReal Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw

section Generic

variable {n ι : Type*} [Fintype n] [DecidableEq n]

private theorem norm_sqrt_one_sub_le_one {k : Matrix n n ℂ} (hk₀ : 0 ≤ k) :
    ‖CFC.sqrt (1 - k)‖ ≤ 1 :=
  norm_le_one_of_nonneg_of_le_one (CFC.sqrt_nonneg _) (sqrt_le_one (sub_le_self 1 hk₀))

/-- A chronological product of the roots `(I - k_i)^{1/2}` of positive constraints
is a contraction. Source: area law, `09-amplification.tex`, line 63. -/
theorem norm_contractionWord_le_one (k : ι → Matrix n n ℂ) (hk₀ : ∀ i, 0 ≤ k i) :
    ∀ (m : ℕ) (w : Fin m → ι), ‖contractionWord k m w‖ ≤ 1
  | 0, w => by
    rw [contractionWord_zero]
    exact norm_le_one_of_nonneg_of_le_one zero_le_one le_rfl
  | m + 1, w => by
    rw [contractionWord]
    exact (norm_mul_le _ _).trans ((mul_le_mul (norm_sqrt_one_sub_le_one (hk₀ _))
      (norm_contractionWord_le_one k hk₀ m _) (norm_nonneg _) zero_le_one).trans_eq
        (one_mul 1))

/-- Replacing each root by one within `ε` changes a chronological product of
`m` roots by at most `m ε`. This is the telescoping step in area law,
`09-amplification.tex`, lines 230–232. -/
theorem norm_contractionWord_sub_le (k k' : ι → Matrix n n ℂ)
    (hk₀ : ∀ i, 0 ≤ k i) (hk'₀ : ∀ i, 0 ≤ k' i) {ε : ℝ}
    (hε : ∀ i, ‖CFC.sqrt (1 - k i) - CFC.sqrt (1 - k' i)‖ ≤ ε) :
    ∀ (m : ℕ) (w : Fin m → ι),
      ‖contractionWord k m w - contractionWord k' m w‖ ≤ m * ε
  | 0, w => by simp
  | m + 1, w => by
    rw [contractionWord, contractionWord]
    set G := CFC.sqrt (1 - k (w (Fin.last m)))
    set G' := CFC.sqrt (1 - k' (w (Fin.last m)))
    set X := contractionWord k m fun j => w j.castSucc
    set X' := contractionWord k' m fun j => w j.castSucc
    have hsplit : G * X - G' * X' = G * (X - X') + (G - G') * X' := by
      rw [Matrix.mul_sub, Matrix.sub_mul]; abel
    have hG : ‖G‖ ≤ 1 := norm_sqrt_one_sub_le_one (hk₀ _)
    have hX' : ‖X'‖ ≤ 1 := norm_contractionWord_le_one k' hk'₀ m _
    have hXX : ‖X - X'‖ ≤ m * ε := norm_contractionWord_sub_le k k' hk₀ hk'₀ hε m _
    have hGG : ‖G - G'‖ ≤ ε := hε _
    have hε0 : 0 ≤ ε := (norm_nonneg _).trans hGG
    rw [hsplit]
    calc ‖G * (X - X') + (G - G') * X'‖
        ≤ ‖G‖ * ‖X - X'‖ + ‖G - G'‖ * ‖X'‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ 1 * (m * ε) + ε * 1 :=
          add_le_add (mul_le_mul hG hXX (norm_nonneg _) zero_le_one)
            (mul_le_mul hGG hX' (norm_nonneg _) hε0)
      _ = ((m + 1 : ℕ) : ℝ) * ε := by push_cast; ring

variable [Fintype ι]

/-- Under the Poisson word law on a finite alphabet, the expected norm of the
difference of two chronological root products whose factors differ by at most
`ε` is at most `ε |ι| t`. Source: area law, `09-amplification.tex`,
lines 228–232. -/
theorem integrable_and_integral_norm_contractionWord_sub_le (k k' : ι → Matrix n n ℂ)
    (hk₀ : ∀ i, 0 ≤ k i) (hk'₀ : ∀ i, 0 ≤ k' i) {ε : ℝ}
    (hε : ∀ i, ‖CFC.sqrt (1 - k i) - CFC.sqrt (1 - k' i)‖ ≤ ε) (t : ℝ≥0) :
    Integrable (fun u : PoissonWord.Word ι =>
        ‖contractionWord k u.1 u.2 - contractionWord k' u.1 u.2‖)
      (PoissonWord.measure ι t) ∧
      (∫ u, ‖contractionWord k u.1 u.2 - contractionWord k' u.1 u.2‖
        ∂PoissonWord.measure ι t) ≤ ε * Fintype.card ι * t := by
  have hint : Integrable (fun u : PoissonWord.Word ι =>
      ‖contractionWord k u.1 u.2 - contractionWord k' u.1 u.2‖)
      (PoissonWord.measure ι t) :=
    PoissonWord.integrable_of_nonneg_le_const t _ (fun _ => norm_nonneg _) (C := 1 + 1)
      fun u => (norm_sub_le _ _).trans (add_le_add
        (norm_contractionWord_le_one k hk₀ _ _) (norm_contractionWord_le_one k' hk'₀ _ _))
  refine ⟨hint, ?_⟩
  calc (∫ u, ‖contractionWord k u.1 u.2 - contractionWord k' u.1 u.2‖
        ∂PoissonWord.measure ι t)
      ≤ ∫ u : PoissonWord.Word ι, ε * (u.1 : ℝ) ∂PoissonWord.measure ι t :=
        integral_mono hint ((PoissonWord.integrable_length t).const_mul ε)
          fun u => (norm_contractionWord_sub_le k k' hk₀ hk'₀ hε u.1 u.2).trans_eq
            (mul_comm _ _)
    _ = ε * Fintype.card ι * t := by
        rw [integral_const_mul, PoissonWord.integral_length, mul_assoc]

/-- The same estimate on the coupled realization: both products are evaluated on
the retained part of one full word, and the bound counts only retained labels.
Source: area law, `09-amplification.tex`, lines 70 and 228–232. -/
theorem integrable_and_integral_norm_contractionWord_retained_sub_le
    (P : ι → Prop) [DecidablePred P] (k k' : {i // P i} → Matrix n n ℂ)
    (hk₀ : ∀ i, 0 ≤ k i) (hk'₀ : ∀ i, 0 ≤ k' i) {ε : ℝ}
    (hε : ∀ i, ‖CFC.sqrt (1 - k i) - CFC.sqrt (1 - k' i)‖ ≤ ε) (t : ℝ≥0) :
    Integrable (fun w : PoissonWord.Word ι =>
        ‖contractionWord k (PoissonWord.partitionWords P w).1.1
            (PoissonWord.partitionWords P w).1.2 -
          contractionWord k' (PoissonWord.partitionWords P w).1.1
            (PoissonWord.partitionWords P w).1.2‖)
      (PoissonWord.measure ι t) ∧
      (∫ w, ‖contractionWord k (PoissonWord.partitionWords P w).1.1
            (PoissonWord.partitionWords P w).1.2 -
          contractionWord k' (PoissonWord.partitionWords P w).1.1
            (PoissonWord.partitionWords P w).1.2‖ ∂PoissonWord.measure ι t) ≤
        ε * Fintype.card {i // P i} * t := by
  set g : PoissonWord.Word ι → PoissonWord.Word {i // P i} :=
    fun w => (PoissonWord.partitionWords P w).1
  set f : PoissonWord.Word {i // P i} → ℝ :=
    fun u => ‖contractionWord k u.1 u.2 - contractionWord k' u.1 u.2‖
  obtain ⟨hint, hle⟩ := integrable_and_integral_norm_contractionWord_sub_le k k' hk₀ hk'₀ hε t
  have hmap : Measure.map g (PoissonWord.measure ι t) = PoissonWord.measure {i // P i} t :=
    PoissonWord.map_partitionWords_fst P t
  have hgm : AEMeasurable g (PoissonWord.measure ι t) := Measurable.of_discrete.aemeasurable
  have hfm : AEStronglyMeasurable f (Measure.map g (PoissonWord.measure ι t)) :=
    AEStronglyMeasurable.of_discrete
  have hint' : Integrable f (Measure.map g (PoissonWord.measure ι t)) := by
    rw [hmap]; exact hint
  refine ⟨(integrable_map_measure hfm hgm).mp hint', ?_⟩
  have h := integral_map (f := f) hgm hfm
  rw [hmap] at h
  change (∫ w, f (g w) ∂PoissonWord.measure ι t) ≤ _
  rw [← h]
  exact hle

end Generic

section Lattice

variable {Λ : Finset (ℤ × ℤ)}

private theorem mem_graphNeighborhood_iff {R : ℕ} {X : Finset (Site Λ)} {y : Site Λ} :
    y ∈ graphNeighborhood Λ R X ↔ ∃ x ∈ X, (domainGraph Λ).edist x y ≤ R := by
  classical
  constructor
  · intro h
    obtain ⟨-, x, hx, hw⟩ := Finset.mem_filter.mp h
    exact ⟨x, hx, (exists_walk_length_le_iff_edist_le Λ R x y).mp hw⟩
  · rintro ⟨x, hx, hd⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ y, x, hx, (exists_walk_length_le_iff_edist_le Λ R x y).mpr hd⟩

/-- A ball of radius `r` about a site within `r` of `S` lies in `N_{2r}(S)`.
Source: area law, `09-amplification.tex`, lines 232–234. -/
theorem graphBall_subset_graphNeighborhood_two_mul {S : Finset (Site Λ)} {r : ℕ}
    {x : Site Λ} (hx : x ∈ graphNeighborhood Λ r S) :
    graphBall (domainGraph Λ) x r ⊆ graphNeighborhood Λ (2 * r) S := by
  intro y hy
  obtain ⟨s, hs, hd⟩ := mem_graphNeighborhood_iff.mp hx
  refine mem_graphNeighborhood_iff.mpr ⟨s, hs, ?_⟩
  calc (domainGraph Λ).edist s y ≤ (domainGraph Λ).edist s x + (domainGraph Λ).edist x y :=
        SimpleGraph.edist_triangle
    _ ≤ r + r := add_le_add hd (mem_graphBall.mp hy)
    _ = ((2 * r : ℕ) : ℕ∞) := by push_cast; ring

/-- With at most `μ` labels anchored at each site, at most `2 μ |S| (1 + r)²` labels have
anchors in `N_r(S)`. Source: area law, `09-amplification.tex`, line 228, with the ball
count of `01-preliminaries.tex`, lines 82–103. -/
theorem card_filter_anchor_mem_graphNeighborhood_le {κ : Type*} [Fintype κ]
    (a : κ → Site Λ) {μ : ℝ} (hμ : 0 ≤ μ)
    (hfiber : ∀ x, ((Finset.univ.filter fun i => a i = x).card : ℝ) ≤ μ)
    (S : Finset (Site Λ)) (r : ℕ) :
    ((Finset.univ.filter fun i => a i ∈ graphNeighborhood Λ r S).card : ℝ) ≤
      2 * μ * S.card * (1 + (r : ℝ)) ^ 2 := by
  classical
  have hsub : (Finset.univ.filter fun i => a i ∈ graphNeighborhood Λ r S) ⊆
      S.biUnion fun s => (graphBall (domainGraph Λ) s r).biUnion
        fun x => Finset.univ.filter fun i => a i = x := by
    intro i hi
    obtain ⟨s, hs, hd⟩ := mem_graphNeighborhood_iff.mp (Finset.mem_filter.mp hi).2
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨s, hs, a i, mem_graphBall.mpr hd, rfl⟩
  have hcard := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hball (s : Site Λ) : (((graphBall (domainGraph Λ) s r).biUnion
      fun x => Finset.univ.filter fun i => a i = x).card : ℝ) ≤
        μ * (2 * ((r : ℝ) + 1) ^ 2) := by
    calc _ ≤ ((∑ x ∈ graphBall (domainGraph Λ) s r,
          (Finset.univ.filter fun i => a i = x).card : ℕ) : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ graphBall (domainGraph Λ) s r, μ := by
          push_cast; exact Finset.sum_le_sum fun x _ => hfiber x
      _ = μ * (graphBall (domainGraph Λ) s r).card := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ μ * (2 * ((r : ℝ) + 1) ^ 2) :=
          mul_le_mul_of_nonneg_left (card_graphBall_domainGraph_le s r) hμ
  calc ((Finset.univ.filter fun i => a i ∈ graphNeighborhood Λ r S).card : ℝ)
      ≤ ((∑ s ∈ S, ((graphBall (domainGraph Λ) s r).biUnion
          fun x => Finset.univ.filter fun i => a i = x).card : ℕ) : ℝ) := by
        exact_mod_cast hcard
    _ ≤ ∑ _s ∈ S, μ * (2 * ((r : ℝ) + 1) ^ 2) := by
        push_cast; exact Finset.sum_le_sum fun s _ => hball s
    _ = 2 * μ * S.card * (1 + (r : ℝ)) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- At most `2 μ_R |S| (1 + r)²` labels have anchors in `N_r(S)`, where `μ_R` is the
anchor multiplicity. Source: area law, `09-amplification.tex`, line 228, with the
counts of `01-preliminaries.tex`, lines 82–103. -/
theorem card_anchor_graphNeighborhood_le {R : ℕ} (a : AdmissibleSupport Λ R → Site Λ)
    (ha : ∀ X, a X ∈ X.1) (S : Finset (Site Λ)) (r : ℕ) :
    ((Finset.univ.filter fun i => a i ∈ graphNeighborhood Λ r S).card : ℝ) ≤
      2 * (2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) * S.card * (1 + (r : ℝ)) ^ 2 :=
  card_filter_anchor_mem_graphNeighborhood_le a (Nat.cast_nonneg _)
    (fun x => by exact_mod_cast card_anchor_fiber_le a ha x) S r

/-- Every product of the radius-`r` local roots `(I - E_{N_r(a_i)} k_i)^{1/2}` over labels
anchored in `N_r(S)` is supported on `N_{2r}(S)`.
Source: area law, `09-amplification.tex`, lines 232–234. -/
theorem contractionWord_siteExpectation_mem_supportedOperators {q : ℕ} [NeZero q]
    {κ : Type*} (a : κ → Site Λ) {S : Finset (Site Λ)} {r : ℕ}
    (k : {i // a i ∈ graphNeighborhood Λ r S} →
      Matrix (Configuration Λ q) (Configuration Λ q) ℂ) (hk₁ : ∀ i, k i ≤ 1) :
    ∀ (m : ℕ) (u : Fin m → {i // a i ∈ graphNeighborhood Λ r S}),
      contractionWord (fun i : {i // a i ∈ graphNeighborhood Λ r S} =>
          siteExpectation q (graphBall (domainGraph Λ) (a i) r) (k i))
        m u ∈ supportedOperators q (graphNeighborhood Λ (2 * r) S : Set (Site Λ)) := by
  have hmem (i : {i // a i ∈ graphNeighborhood Λ r S}) :
      CFC.sqrt (1 - siteExpectation q (graphBall (domainGraph Λ) (a i) r) (k i)) ∈
        supportedOperators q (graphNeighborhood Λ (2 * r) S : Set (Site Λ)) := by
    set K := graphBall (domainGraph Λ) (a i) r
    have hK : CFC.sqrt (1 - siteExpectation q K (k i)) ∈
        supportedOperators q (K : Set (Site Λ)) :=
      sqrt_mem_supportedOperators K (sub_nonneg.mpr (siteExpectation_le_one _ (hk₁ i)))
        ((supportedOperators q (K : Set (Site Λ))).sub_mem (one_mem_supportedOperators _)
          (siteExpectation_mem_supportedOperators K (k i)))
    exact supportedOperators_mono
      (by exact_mod_cast graphBall_subset_graphNeighborhood_two_mul i.2) hK
  intro m
  induction m with
  | zero => intro u; rw [contractionWord_zero]; exact one_mem_supportedOperators _
  | succ m ih =>
    intro u
    rw [contractionWord]
    exact mul_mem_supportedOperators (hmem _) (ih _)

/-- The prefactor `2 μ √C` of the truncation of the retained constraint product, for
localization tails `C e^{-c l^α}` and at most `μ` labels per site. Source: area law,
`09-amplification.tex`, lines 228–234. -/
noncomputable def constraintWordTruncationPrefactor (μ C : ℝ) : ℝ :=
  2 * μ * Real.sqrt C

theorem constraintWordTruncationPrefactor_nonneg {μ : ℝ} (hμ : 0 ≤ μ) (C : ℝ) :
    0 ≤ constraintWordTruncationPrefactor μ C := by
  unfold constraintWordTruncationPrefactor; positivity

/-- **Truncation of the retained constraint product for general constraints, with explicit
constants** (Lemma 10.1, `eq:amplification-product-truncation`, `09-amplification.tex`,
lines 42–63 and 228–234). The bound of `exists_domainConstraintWord_truncation` holds with
`A = constraintWordTruncationPrefactor μ C = 2 μ √C` and `γ = c / 2`. -/
theorem domainConstraintWord_truncation {C μ c α : ℝ} (hC : 0 ≤ C) (hμ : 0 ≤ μ) :
    ∀ {q : ℕ} [NeZero q] (Λ : Finset (ℤ × ℤ)) (κ : Type*) [Fintype κ]
      (a : κ → Site Λ) (k : κ → Matrix (Configuration Λ q) (Configuration Λ q) ℂ),
      (∀ i, 0 ≤ k i) → (∀ i, k i ≤ 1) →
      (∀ x, ((Finset.univ.filter fun i : κ => a i = x).card : ℝ) ≤ μ) →
      (∀ i (l : ℕ), ‖k i - siteExpectation q (graphBall (domainGraph Λ) (a i) l) (k i)‖ ≤
        C * Real.exp (-(c * (l : ℝ) ^ α))) →
      ∀ (S : Finset (Site Λ)) (r : ℕ) (t : ℝ≥0),
      let P := fun i : κ => a i ∈ graphNeighborhood Λ r S
      let kr := fun i : {i // P i} =>
        siteExpectation q (graphBall (domainGraph Λ) (a i) r) (k i)
      let D := fun w : PoissonWord.Word κ =>
        contractionWord (fun i : {i // P i} => k i) (PoissonWord.partitionWords P w).1.1
          (PoissonWord.partitionWords P w).1.2
      let L := fun w : PoissonWord.Word κ =>
        contractionWord kr (PoissonWord.partitionWords P w).1.1
          (PoissonWord.partitionWords P w).1.2
      Integrable (fun w => ‖D w - L w‖) (PoissonWord.measure κ t) ∧
      (∫ w, ‖D w - L w‖ ∂PoissonWord.measure κ t) ≤
        constraintWordTruncationPrefactor μ C * t * S.card * (1 + (r : ℝ)) ^ 2 *
          Real.exp (-(c / 2 * (r : ℝ) ^ α)) ∧
      ∀ w, ‖L w‖ ≤ 1 ∧
        L w ∈ supportedOperators q (graphNeighborhood Λ (2 * r) S : Set (Site Λ)) := by
  unfold constraintWordTruncationPrefactor
  intro q _ Λ κ _ a k hk₀ hk₁ hfiber htail S r t P kr D L
  have hkr₀ (i : {i // P i}) : 0 ≤ kr i := siteExpectation_nonneg _ (hk₀ i)
  have hkr₁ (i : {i // P i}) : kr i ≤ 1 := siteExpectation_le_one _ (hk₁ i)
  set ε := Real.sqrt C * Real.exp (-(c / 2 * (r : ℝ) ^ α)) with hε_def
  have hε (i : {i // P i}) : ‖CFC.sqrt (1 - k i) - CFC.sqrt (1 - kr i)‖ ≤ ε := by
    refine (norm_sqrt_one_sub_sub_le (hk₁ i) (hkr₁ i)).trans ?_
    calc Real.sqrt ‖k i - kr i‖ ≤ Real.sqrt (C * Real.exp (-(c * (r : ℝ) ^ α))) :=
          Real.sqrt_le_sqrt (htail i r)
      _ = ε := by
          rw [Real.sqrt_mul hC, ← Real.exp_half, hε_def]
          ring_nf
  obtain ⟨hint, hle⟩ := integrable_and_integral_norm_contractionWord_retained_sub_le P
    (fun i : {i // P i} => k i) kr (fun i => hk₀ i) hkr₀ hε t
  refine ⟨hint, hle.trans ?_, fun w => ⟨norm_contractionWord_le_one kr hkr₀ _ _,
    contractionWord_siteExpectation_mem_supportedOperators a _ (fun i => hk₁ i) _ _⟩⟩
  have hcardP : (Fintype.card {i // P i} : ℝ) ≤ 2 * μ * S.card * (1 + (r : ℝ)) ^ 2 := by
    rw [Fintype.card_subtype]; exact card_filter_anchor_mem_graphNeighborhood_le a hμ hfiber S r
  have hε0 : 0 ≤ ε := by positivity
  calc ε * Fintype.card {i // P i} * t ≤ ε * (2 * μ * S.card * (1 + (r : ℝ)) ^ 2) * t :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcardP hε0) t.2
    _ = _ := by rw [hε_def]; ring

/-- **Truncation of the retained constraint product for general constraints**
(Lemma 10.1, `lem:amplification-local-products`, `eq:amplification-product-truncation`,
`09-amplification.tex`, lines 42–63, proof at lines 228–234).
For tail constants `C ≥ 0`, `c > 0` and a multiplicity bound `μ ≥ 0` there are `A ≥ 0`
and `γ > 0` with the following property. Let `k_i` be positive contractions on a finite
domain `Λ`, anchored at `a_i` with at most `μ` labels per site, with
`‖k_i - E_{N_l(a_i)} k_i‖ ≤ C e^{-c l^α}` for all `l`. Retain the labels with
`d_Λ(a_i, S) ≤ r`. On each realization `w` of the full Poisson word, let `D_ret(w)` be
the chronological product of the roots `(I - k_i)^{1/2}` over the retained events and
`L(w)` the same product of `(I - E_{N_r(a_i)} k_i)^{1/2}`. Then `‖D_ret - L‖` is
integrable, `E‖D_ret - L‖ ≤ A t |S| (1 + r)² e^{-γ r^α}`, and every `L(w)` is a
contraction supported on `N_{2r}(S)`. The constants precede the local dimension,
domain, labels, anchors, constraints, `S`, `r` and `t`. The source assumes `S`
nonempty and `r ≥ 1`; neither is needed here. -/
theorem exists_domainConstraintWord_truncation {C μ c α : ℝ} (hC : 0 ≤ C) (hμ : 0 ≤ μ)
    (hc : 0 < c) :
    ∃ A γ : ℝ, 0 ≤ A ∧ 0 < γ ∧
      ∀ {q : ℕ} [NeZero q] (Λ : Finset (ℤ × ℤ)) (κ : Type*) [Fintype κ]
        (a : κ → Site Λ) (k : κ → Matrix (Configuration Λ q) (Configuration Λ q) ℂ),
        (∀ i, 0 ≤ k i) → (∀ i, k i ≤ 1) →
        (∀ x, ((Finset.univ.filter fun i : κ => a i = x).card : ℝ) ≤ μ) →
        (∀ i (l : ℕ), ‖k i - siteExpectation q (graphBall (domainGraph Λ) (a i) l) (k i)‖ ≤
          C * Real.exp (-(c * (l : ℝ) ^ α))) →
        ∀ (S : Finset (Site Λ)) (r : ℕ) (t : ℝ≥0),
        let P := fun i : κ => a i ∈ graphNeighborhood Λ r S
        let kr := fun i : {i // P i} =>
          siteExpectation q (graphBall (domainGraph Λ) (a i) r) (k i)
        let D := fun w : PoissonWord.Word κ =>
          contractionWord (fun i : {i // P i} => k i) (PoissonWord.partitionWords P w).1.1
            (PoissonWord.partitionWords P w).1.2
        let L := fun w : PoissonWord.Word κ =>
          contractionWord kr (PoissonWord.partitionWords P w).1.1
            (PoissonWord.partitionWords P w).1.2
        Integrable (fun w => ‖D w - L w‖) (PoissonWord.measure κ t) ∧
        (∫ w, ‖D w - L w‖ ∂PoissonWord.measure κ t) ≤
          A * t * S.card * (1 + (r : ℝ)) ^ 2 * Real.exp (-(γ * (r : ℝ) ^ α)) ∧
        ∀ w, ‖L w‖ ≤ 1 ∧
          L w ∈ supportedOperators q (graphNeighborhood Λ (2 * r) S : Set (Site Λ)) :=
  ⟨_, _, constraintWordTruncationPrefactor_nonneg hμ C, half_pos hc,
    domainConstraintWord_truncation hC hμ⟩

/-- **Truncation of the retained constraint product for the exact positive constraints, with
explicit constants** (Lemma 10.1, `eq:amplification-product-truncation`;
`09-amplification.tex`, lines 42–63 and 228–234). Let `C ≥ 0` be a localization prefactor of
the positive constraints, in the form of Proposition 4.3, with rate `c`. Then the bound of
`exists_latticeConstraintWord_truncation` holds with
`C_t = constraintWordTruncationPrefactor μ_R C = 2 μ_R √C`, `μ_R = 2^{2R(R+1)}`, and
`c_t = c / 2`. -/
theorem latticeConstraintWord_truncation_of_positiveConstraints {p : ℕ} (R : ℕ) {J Δ C c : ℝ}
    (hC : 0 ≤ C)
    (hpos : ∀ {q : ℕ} [NeZero q] (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J)
        (a : AdmissibleSupport Λ R → Site Λ), (∀ X, a X ∈ X.1) →
        ∀ (E₀ : ℝ) (Ω : StateSpace Λ q), IsGappedGroundState Λ q h.operator E₀ Ω Δ →
        let cs := positiveNormalization p (Δ / 2) J
        let k := fun i => positiveConstraint cs (centeredFilter p (Δ / 2) h.operator Ω (h.term i))
        0 < cs ∧
        (∀ i, 0 ≤ k i ∧ k i ≤ 1 ∧ k i *ᵥ WithLp.ofLp Ω = 0) ∧
        cs⁻¹ • (h.operator - (E₀ : ℂ) • 1) ≤ ∑ i, k i ∧
        ((Δ / cs : ℝ) : ℂ) • (1 - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤
          cs⁻¹ • (h.operator - (E₀ : ℂ) • 1) ∧
        ((Δ / cs : ℝ) : ℂ) • (1 - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤
          ∑ i, k i ∧
        (∀ i (l : ℕ), 0 ≤ siteExpectation q (graphBall (domainGraph Λ) (a i) l) (k i) ∧
          siteExpectation q (graphBall (domainGraph Λ) (a i) l) (k i) ≤ 1 ∧
          ‖k i - siteExpectation q (graphBall (domainGraph Λ) (a i) l) (k i)‖ ≤
            C * Real.exp (-(c * (l : ℝ) ^ kernelExponent p))) ∧
        (∀ i, k i ∈ supportedOperators q {x | (domainGraph Λ).Reachable (a i) x})) :
    ∀ {q : ℕ} [NeZero q] (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J)
      (a : AdmissibleSupport Λ R → Site Λ), (∀ X, a X ∈ X.1) →
      ∀ (E₀ : ℝ) (Ω : StateSpace Λ q), IsGappedGroundState Λ q h.operator E₀ Ω Δ →
      ∀ (S : Finset (Site Λ)) (r : ℕ) (t : ℝ≥0),
      let P := fun i : AdmissibleSupport Λ R => a i ∈ graphNeighborhood Λ r S
      let k := fun i : {i // P i} => positiveConstraint (positiveNormalization p (Δ / 2) J)
        (centeredFilter p (Δ / 2) h.operator Ω (h.term i))
      let kr := fun i : {i // P i} =>
        siteExpectation q (graphBall (domainGraph Λ) (a i) r) (k i)
      let D := fun w : PoissonWord.Word (AdmissibleSupport Λ R) =>
        contractionWord k (PoissonWord.partitionWords P w).1.1
          (PoissonWord.partitionWords P w).1.2
      let L := fun w : PoissonWord.Word (AdmissibleSupport Λ R) =>
        contractionWord kr (PoissonWord.partitionWords P w).1.1
          (PoissonWord.partitionWords P w).1.2
      Integrable (fun w => ‖D w - L w‖) (PoissonWord.measure (AdmissibleSupport Λ R) t) ∧
      (∫ w, ‖D w - L w‖ ∂PoissonWord.measure (AdmissibleSupport Λ R) t) ≤
        constraintWordTruncationPrefactor ((2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) : ℝ) C * t *
          S.card * (1 + (r : ℝ)) ^ 2 * Real.exp (-(c / 2 * (r : ℝ) ^ kernelExponent p)) ∧
      ∀ w, ‖L w‖ ≤ 1 ∧
        L w ∈ supportedOperators q (graphNeighborhood Λ (2 * r) S : Set (Site Λ)) := by
  intro q _ Λ h a ha E₀ Ω hgs S r t
  obtain ⟨-, hk, -, -, -, htail, -⟩ := hpos Λ h a ha E₀ Ω hgs
  exact domainConstraintWord_truncation hC (Nat.cast_nonneg _) Λ (AdmissibleSupport Λ R) a _
    (fun i => (hk i).1) (fun i => (hk i).2.1)
    (fun x => by exact_mod_cast card_anchor_fiber_le a ha x) (fun i l => (htail i l).2.2) S r t

/-- **Truncation of the retained constraint product** (Lemma 10.1,
`lem:amplification-local-products`, `eq:amplification-product-truncation`,
`09-amplification.tex`, lines 42–63, proof at lines 228–234).
For `p ≥ 1`, `R`, `J ≥ 0` and `Δ > 0` there are `C ≥ 0` and `c > 0` such that the
following holds for the exact positive constraints `k_i` of every gapped lattice
Hamiltonian, every anchoring `a_i ∈ X_i`, every set `S`, radius `r` and time `t`.
Retain the labels with `d_Λ(a_i, S) ≤ r`. On each realization `w` of the full
Poisson word, let `D_ret(w)` be the chronological product of the roots
`(I - k_i)^{1/2}` over the retained events and `L(w)` the same product of
`(I - E_{N_r(a_i)} k_i)^{1/2}`. Then `‖D_ret - L‖` is integrable,
`E‖D_ret - L‖ ≤ C t |S| (1 + r)² e^{-c r^α}` with `α = p / (p + 1)`, and every
`L(w)` is a contraction supported on `N_{2r}(S)`. The constants precede the local
dimension, domain, Hamiltonian, anchors, ground state, `S`, `r` and `t`.
The source assumes `S` nonempty and `r ≥ 1`; neither is needed here. -/
theorem exists_latticeConstraintWord_truncation {p : ℕ} (hp : 1 ≤ p) (R : ℕ) {J Δ : ℝ}
    (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧
      ∀ {q : ℕ} [NeZero q] (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J)
        (a : AdmissibleSupport Λ R → Site Λ), (∀ X, a X ∈ X.1) →
        ∀ (E₀ : ℝ) (Ω : StateSpace Λ q), IsGappedGroundState Λ q h.operator E₀ Ω Δ →
        ∀ (S : Finset (Site Λ)) (r : ℕ) (t : ℝ≥0),
        let P := fun i : AdmissibleSupport Λ R => a i ∈ graphNeighborhood Λ r S
        let k := fun i : {i // P i} => positiveConstraint (positiveNormalization p (Δ / 2) J)
          (centeredFilter p (Δ / 2) h.operator Ω (h.term i))
        let kr := fun i : {i // P i} =>
          siteExpectation q (graphBall (domainGraph Λ) (a i) r) (k i)
        let D := fun w : PoissonWord.Word (AdmissibleSupport Λ R) =>
          contractionWord k (PoissonWord.partitionWords P w).1.1
            (PoissonWord.partitionWords P w).1.2
        let L := fun w : PoissonWord.Word (AdmissibleSupport Λ R) =>
          contractionWord kr (PoissonWord.partitionWords P w).1.1
            (PoissonWord.partitionWords P w).1.2
        Integrable (fun w => ‖D w - L w‖) (PoissonWord.measure (AdmissibleSupport Λ R) t) ∧
        (∫ w, ‖D w - L w‖ ∂PoissonWord.measure (AdmissibleSupport Λ R) t) ≤
          C * t * S.card * (1 + (r : ℝ)) ^ 2 *
            Real.exp (-(c * (r : ℝ) ^ kernelExponent p)) ∧
        ∀ w, ‖L w‖ ≤ 1 ∧
          L w ∈ supportedOperators q (graphNeighborhood Λ (2 * r) S : Set (Site Λ)) := by
  obtain ⟨C, c, hC, hc, hpos⟩ := exists_latticePositiveConstraints hp R hJ hΔ
  exact ⟨_, _, constraintWordTruncationPrefactor_nonneg (Nat.cast_nonneg _) C, half_pos hc,
    latticeConstraintWord_truncation_of_positiveConstraints R hC hpos⟩

end Lattice

end TNLean.PEPS.AreaLaw
