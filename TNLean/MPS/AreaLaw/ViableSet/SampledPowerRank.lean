/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Basic
import TNLean.MPS.AreaLaw.OpenMPS
import QICLean.Entropy.SupportedOperatorSchmidtWords
import QICLean.Algebra.WordMultiplicity
import QICLean.Probability.PhysicalPowerSampling

/-!
# Spatial rank of the normalized nearest-neighbour power sampler

An identity-padded word in adjacent-pair operators has operator Schmidt rank
at most `q^(2c)` across an interior cut, where `c` is the actual number of
occurrences of the unique crossing letter. The proof specializes QICLean's
ordered-support product estimate. One-sided letters and identity padding cost
no rank. A sum of `ℓ` sampled words with all letter counts at most `u` therefore
has rank at most `ℓ * q^(2u)` simultaneously across every cut, including endpoints.

The final theorem composes this deterministic estimate with QICLean's actual
normalized-power sample. One word family satisfies both operator-norm
approximations, every letter-count bound, and every spatial rank bound. Its
explicit positive sample count retains `exp (2 * E0 * log Q / Δ)`. In particular,
this does not remove the ground-energy dependence of the published sampler.

**Local fix (paired matrix indices):** the local matrix-unit decomposition uses
one common pair of indices on its two tensor factors. The correction to LVV's
printed decomposition is recorded in QICLean:
https://sirui-lu.com/QICLean/docs/paper-gaps/lvv13_paired_matrix_decomposition.html.

Source: Landau, Vazirani and Vidick, arXiv:1307.5143v1, Section 2.3.1,
equation `e:decomp`, lines 584--588, and the published Methods, Proposition 1,
p. 6, https://people.eecs.berkeley.edu/~vazirani/pubs/1dalg.pdf,
DOI 10.1038/nphys3345. The distinction between the source versions is recorded
in `docs/paper-gaps/lvv13_sampling_ground_energy.tex`.
-/

open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

open Matrix
namespace TNLean.MPS.AreaLaw

private theorem adjacent_interval_side {L k : ℕ} (i : Fin (L - 1))
    (hne : i.val + 1 ≠ k) :
    interval L i.val (i.val + 2) ⊆ leftBlock L k ∨
      Disjoint (interval L i.val (i.val + 2)) (leftBlock L k) := by
  by_cases hi : i.val + 1 < k
  · left
    intro x hx
    simp only [mem_interval] at hx
    simp only [mem_leftBlock]
    omega
  · right
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [mem_interval] at hx
    simp only [mem_leftBlock] at hy
    omega

private theorem adjacent_interval_inter_crossing {L k : ℕ}
    (hk : 0 < k) (hkL : k < L) :
    interval L (k - 1) (k - 1 + 2) ∩ leftBlock L k =
      {⟨k - 1, by omega⟩} := by
  ext x
  simp only [Finset.mem_inter, mem_interval, mem_leftBlock, Finset.mem_singleton,
    Fin.ext_iff]
  omega

private def paddedNNWordSupport {L : ℕ} (a : Option (Fin (L - 1))) : Finset (Fin L) :=
  a.elim ∅ (fun i ↦ interval L i.val (i.val + 2))

private theorem crossingWeight_eq_count {L k : ℕ} (hk : 0 < k) (hkL : k < L)
    (w : List (Option (Fin (L - 1)))) :
    ((w.filter (fun a ↦ ¬ (paddedNNWordSupport a ⊆ leftBlock L k ∨
      Disjoint (paddedNNWordSupport a) (leftBlock L k)))).map
      (fun a ↦ (paddedNNWordSupport a ∩ leftBlock L k).card)).sum =
        w.count (some ⟨k - 1, by omega⟩) := by
  classical
  have hcross : ¬ (interval L (k - 1) (k - 1 + 2) ⊆ leftBlock L k ∨
      Disjoint (interval L (k - 1) (k - 1 + 2)) (leftBlock L k)) := by
    rintro (hs | hd)
    · have hx := hs (mem_interval.mpr (show k - 1 ≤ k ∧ k < k - 1 + 2 by omega) :
          (⟨k, hkL⟩ : Fin L) ∈ interval L (k - 1) (k - 1 + 2))
      exact Nat.lt_irrefl k (by simpa only [mem_leftBlock] using hx)
    · have hx : (⟨k - 1, by omega⟩ : Fin L) ∈ interval L (k - 1) (k - 1 + 2) :=
        mem_interval.mpr (by change k - 1 ≤ k - 1 ∧ k - 1 < k - 1 + 2; omega)
      have hy : (⟨k - 1, by omega⟩ : Fin L) ∈ leftBlock L k :=
        mem_leftBlock.mpr (by change k - 1 < k; omega)
      exact Finset.disjoint_left.mp hd hx hy
  induction w with
  | nil => simp
  | cons a w ih =>
    cases a with
    | none =>
      have hs : paddedNNWordSupport (none : Option (Fin (L - 1))) ⊆ leftBlock L k ∨
          Disjoint (paddedNNWordSupport none) (leftBlock L k) :=
        Or.inl (Finset.empty_subset _)
      simpa only [List.filter_cons, decide_eq_true_eq, hs, not_true_eq_false,
        ↓reduceIte, List.count_cons, beq_iff_eq, reduceCtorEq, ite_false, Nat.add_zero] using ih
    | some i =>
      by_cases hi : i = ⟨k - 1, by omega⟩
      · subst i
        have hc : ¬ (paddedNNWordSupport (some (⟨k - 1, by omega⟩ : Fin (L - 1))) ⊆
            leftBlock L k ∨ Disjoint (paddedNNWordSupport (some ⟨k - 1, by omega⟩))
              (leftBlock L k)) := hcross
        have hcard : (paddedNNWordSupport (some (⟨k - 1, by omega⟩ : Fin (L - 1))) ∩
            leftBlock L k).card = 1 := by
          simp only [paddedNNWordSupport, Option.elim_some,
            adjacent_interval_inter_crossing hk hkL, Finset.card_singleton]
        simp only [List.filter_cons, decide_eq_true_eq, hc, not_false_eq_true,
          ↓reduceIte, List.map_cons, List.sum_cons, hcard, List.count_cons_self]
        omega
      · have hne : i.val + 1 ≠ k := by
          intro h
          apply hi
          apply Fin.ext
          change i.val = k - 1
          omega
        have hs : paddedNNWordSupport (some i) ⊆ leftBlock L k ∨
            Disjoint (paddedNNWordSupport (some i)) (leftBlock L k) := adjacent_interval_side i hne
        simpa only [List.filter_cons, decide_eq_true_eq, hs, not_true_eq_false,
          ↓reduceIte, List.count_cons, Option.some.injEq, beq_iff_eq, hi, ite_false,
          Nat.add_zero] using ih

private theorem isSupportedOn_paddedNNWordSupport {L q : ℕ}
    (P : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hP : ∀ i, Entropy.IsSupportedOn (P i) (interval L i.val (i.val + 2)))
    (a : Option (Fin (L - 1))) :
    Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (a.elim 1 P) (paddedNNWordSupport a) := by
  cases a with
  | none => exact Entropy.isSupportedOn_one _
  | some i => exact hP i

/-- Across an interior cut, each occurrence of the unique crossing letter costs at
most the square of the local dimension. LVV13, equation e:decomp, lines 584--588. -/
theorem operatorSchmidtRank_padded_nn_word_le
    {L q k : ℕ} (hk : 0 < k) (hkL : k < L)
    (P : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hP : ∀ i, Entropy.IsSupportedOn (P i) (interval L i.val (i.val + 2)))
    (w : List (Option (Fin (L - 1)))) :
    operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L k)
      ((w.map (fun a ↦ a.elim 1 P)).prod)) ≤
      q ^ (2 * w.count (some ⟨k - 1, by omega⟩)) := by
  classical
  simpa only [crossingWeight_eq_count hk hkL] using
    Entropy.operatorSchmidtRank_cutOperator_list_prod_le (leftBlock L k)
      paddedNNWordSupport (fun a ↦ a.elim 1 P) (isSupportedOn_paddedNNWordSupport P hP) w

private theorem count_ofFn_eq_countsFinsupp {α : Type*} [BEq α] [LawfulBEq α] {m : ℕ}
    (w : Fin m → α) (a : α) : (List.ofFn w).count a = WordMultiplicity.countsFinsupp w a := by
  classical
  induction m with
  | zero => simp [WordMultiplicity.countsFinsupp]
  | succ m ih =>
    simp only [List.ofFn_succ, List.count_cons, WordMultiplicity.countsFinsupp,
      Fin.sum_univ_succ, Finsupp.add_apply]
    rw [← WordMultiplicity.countsFinsupp, ← ih]
    by_cases h : w 0 = a
    · subst a
      simp [Nat.add_comm]
    · simp [h, Ne.symm h]

private theorem rank_padded_nn_word_endpoint {L q k : ℕ}
    (hk : k = 0 ∨ L ≤ k)
    (P : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hP : ∀ i, Entropy.IsSupportedOn (P i) (interval L i.val (i.val + 2)))
    (w : List (Option (Fin (L - 1)))) :
    operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L k)
      ((w.map (fun a ↦ a.elim 1 P)).prod)) ≤ 1 := by
  classical
  have hfilter : w.filter (fun a ↦ ¬ (paddedNNWordSupport a ⊆ leftBlock L k ∨
      Disjoint (paddedNNWordSupport a) (leftBlock L k))) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro a _
    cases a with
    | none => simp [paddedNNWordSupport]
    | some i =>
      have hne : i.val + 1 ≠ k := by rcases hk with hk | hk <;> omega
      simp [paddedNNWordSupport, adjacent_interval_side i hne]
  simpa only [hfilter, List.map_nil, List.sum_nil, Nat.mul_zero, pow_zero] using
    Entropy.operatorSchmidtRank_cutOperator_list_prod_le (leftBlock L k)
      paddedNNWordSupport (fun a ↦ a.elim 1 P) (isSupportedOn_paddedNNWordSupport P hP) w

/-- Uniform letter-count control bounds the actual padded word across every chain cut,
including both endpoints. LVV13, equation e:decomp, lines 584--588. -/
theorem operatorSchmidtRank_padded_nn_word_le_of_counts
    {L q m u : ℕ} (hq : 1 ≤ q)
    (P : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hP : ∀ i, Entropy.IsSupportedOn (P i) (interval L i.val (i.val + 2)))
    (w : Fin m → Option (Fin (L - 1)))
    (hcounts : ∀ a, WordMultiplicity.countsFinsupp w a ≤ u) (k : ℕ) :
    operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L k)
      ((List.ofFn fun j ↦ (w j).elim 1 P).prod)) ≤ q ^ (2 * u) := by
  classical
  have hmap : (List.ofFn w).map (fun a ↦ a.elim 1 P) =
      List.ofFn (fun j ↦ (w j).elim 1 P) := List.map_ofFn
  by_cases hk : 0 < k ∧ k < L
  · rw [← hmap]
    refine (operatorSchmidtRank_padded_nn_word_le hk.1 hk.2 P hP (List.ofFn w)).trans ?_
    rw [count_ofFn_eq_countsFinsupp]
    exact Nat.pow_le_pow_right hq (Nat.mul_le_mul_left _ (hcounts _))
  · rw [← hmap]
    exact (rank_padded_nn_word_endpoint (by omega) P hP (List.ofFn w)).trans (one_le_pow₀ hq)

/-- Summing the same sampled words costs only the sample cardinality in operator
Schmidt rank. No independence or concentration is assumed for this deterministic
consequence. LVV13, Section 2.3.1, following equation e:decomp. -/
theorem operatorSchmidtRank_padded_nn_sample_sum_le
    {L q m u : ℕ} {β : Type*} [Fintype β] (hq : 1 ≤ q)
    (P : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hP : ∀ i, Entropy.IsSupportedOn (P i) (interval L i.val (i.val + 2)))
    (σ : β → Fin m → Option (Fin (L - 1)))
    (hcounts : ∀ b a, WordMultiplicity.countsFinsupp (σ b) a ≤ u)
    (weight : β → ℂ) (k : ℕ) :
    operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L k)
      (∑ b, weight b • (List.ofFn fun j ↦ (σ b j).elim 1 P).prod)) ≤
      Fintype.card β * q ^ (2 * u) := by
  classical
  let φ := Matrix.reindexAlgEquiv ℂ ℂ (Entropy.cutEquiv (fun _ : Fin L ↦ q) (leftBlock L k))
  change operatorSchmidtRank (φ (∑ b, weight b • _)) ≤ _
  rw [map_sum]
  refine (operatorSchmidtRank_sum_le Finset.univ _).trans ?_
  calc
    _ ≤ ∑ _b : β, q ^ (2 * u) := Finset.sum_le_sum fun b _ ↦ by
      rw [map_smul]
      exact (operatorSchmidtRank_smul_le _ _).trans
        (operatorSchmidtRank_padded_nn_word_le_of_counts hq P hP (σ b) (hcounts b) k)
    _ = _ := by simp

private theorem isSupportedOn_complement {L q : ℕ}
    {X : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ} {S : Finset (Fin L)}
    (hX : Entropy.IsSupportedOn X S) : Entropy.IsSupportedOn (1 - X) S := by
  have h1 := Entropy.isSupportedOn_one (n := fun _ : Fin L ↦ q) S
  constructor
  · intro σ τ h
    simp only [Matrix.sub_apply, h1.1 σ τ h, hX.1 σ τ h, sub_self]
  · intro σ τ σ' τ' hσ hτ hστ hστ'
    simp only [Matrix.sub_apply, h1.2 σ τ σ' τ' hσ hτ hστ hστ',
      hX.2 σ τ σ' τ' hσ hτ hστ hστ']

/-- The normalized sampled complement sum has the same spatial rank bound as its
actual word family. Scalar normalization does not increase operator Schmidt rank.
LVV13, Section 2.3.1, equation e:decomp and Corollary 2.14. -/
theorem operatorSchmidtRank_sampled_nn_complements_le
    {L q m u : ℕ} {β : Type*} [Fintype β] (hq : 1 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (h i) (interval L i.val (i.val + 2)))
    (σ : β → Fin m → Option (Fin (L - 1)))
    (hcounts : ∀ b a, WordMultiplicity.countsFinsupp (σ b) a ≤ u)
    (c d : ℂ) (k : ℕ) :
    operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L k)
      (d • ∑ b, c • (List.ofFn fun j ↦ 1 - (σ b j).elim 0 h).prod)) ≤
      Fintype.card β * q ^ (2 * u) := by
  classical
  let P := fun i ↦ 1 - h i
  have hP i : Entropy.IsSupportedOn (P i) (interval L i.val (i.val + 2)) :=
    isSupportedOn_complement (hs i)
  have hletter (a : Option (Fin (L - 1))) : 1 - a.elim 0 h = a.elim 1 P := by
    cases a <;> simp [P]
  let φ := Matrix.reindexAlgEquiv ℂ ℂ (Entropy.cutEquiv (fun _ : Fin L ↦ q) (leftBlock L k))
  change operatorSchmidtRank (φ (d • _)) ≤ _
  rw [map_smul]
  refine (operatorSchmidtRank_smul_le _ _).trans ?_
  simpa only [hletter, φ, Matrix.coe_reindexAlgEquiv, Entropy.cutOperator] using
    operatorSchmidtRank_padded_nn_sample_sum_le hq P hP σ hcounts (fun _ ↦ c) k

/-- The published energy-dependent normalized-power sampler admits a simultaneous
operator Schmidt-rank bound at every chain cut. The exact sampled operator, word
counts and projection approximation are constructed together. LVV, published
Methods, Proposition 1, p. 6; arXiv:1307.5143v1, equation e:decomp. -/
theorem exists_sampled_nn_power_approximation_with_rank
    {L q : ℕ} (hq : 1 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (h i) (interval L i.val (i.val + 2)))
    (hpos : ∀ i, (h i).PosSemidef) (hu : ∀ i, h i ≤ 1)
    {E0 Δ : ℝ} {Ω : EuclideanSpace ℂ (Fin L → Fin q)} (hΩ : ‖Ω‖ = 1)
    (hHΩ : (∑ i, h i) *ᵥ WithLp.ofLp Ω = (E0 : ℂ) • WithLp.ofLp Ω)
    (hgap : ((∑ i, h i) - (E0 : ℂ) • 1 - (Δ : ℂ) •
      (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
    (hΔ : 0 < Δ) {Q η : ℝ} (hQ : 1 ≤ Q) (hη : 0 < η)
    {p : ℕ} (hp : 0 < p) (hpD : 2 * (q : ℝ) ^ L < (4 : ℝ) ^ p) :
    let N := Fintype.card (Fin (L - 1)) + 1
    let m := ⌈((N : ℝ) - E0) / Δ * Real.log Q⌉₊
    let C := (1 - E0 / N)⁻¹
    let ℓ := ⌈16 * (p : ℝ) ^ 2 * (N : ℝ) ^ 2 *
      Real.exp (2 * E0 * Real.log Q / Δ) / η ^ 2⌉₊ + 1
    let u := ⌈((m : ℝ) / N + Real.log (2 * (N : ℝ) * ℓ)) / Real.log 2⌉₊
    0 < ℓ ∧ ∃ σ : Fin ℓ → Fin m → Option (Fin (L - 1)),
      let K := (ℓ : ℂ)⁻¹ • ∑ b,
        (C : ℂ) ^ m • (List.ofFn fun j ↦ 1 - (σ b j).elim 0 h).prod
      ‖K - ((C : ℂ) • (1 - (Fintype.card (Fin (L - 1)) + 1 : ℂ)⁻¹ • ∑ i, h i)) ^ m‖ < η ∧
      ‖K - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))‖ < η + 1 / Q ∧
      (∀ b a, WordMultiplicity.countsFinsupp (σ b) a < u) ∧
      ∀ k : ℕ, operatorSchmidtRank
        (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L k) K) ≤
          ℓ * q ^ (2 * u) := by
  classical
  intro N m C ℓ u
  have hres := Matrix.exists_sampled_power_approximation_with_explicit_count
    h hpos hu hΩ hHΩ hgap hΔ hQ hη hp (by
      simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using hpD)
  obtain ⟨hℓ, σ, hA, hProj, hcounts⟩ := hres
  refine ⟨hℓ, σ, hA, hProj, hcounts, fun k ↦ ?_⟩
  have hrank := operatorSchmidtRank_sampled_nn_complements_le
    (m := m) (u := u) (β := Fin ℓ) hq h hs σ
    (fun b a ↦ (hcounts b a).le) ((C : ℂ) ^ m) (ℓ : ℂ)⁻¹ k
  simpa only [Fintype.card_fin] using hrank

end TNLean.MPS.AreaLaw
