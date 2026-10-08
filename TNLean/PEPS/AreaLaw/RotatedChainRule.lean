/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.RegionalEntropyBridge
import TNLean.PEPS.AreaLaw.RegionalStates

/-!
# The entropy chain rule averaged over rotated color orders

Let `X_i` be pairwise disjoint regions indexed by a finite set, and order the indices by a
key. The entropy chain rule writes `S(⋃ X_i)` as the sum of the conditional entropies
`S(X_i | X_{<i})`. Each term is at most `S(X_i)`. If the indices carry `N` colors and the
buffer `T_i` of a region lies in the union of the regions of other colors, then in the order
that puts the color of `i` last the term of `i` is at most `S(X_i | T_i)`. Averaging the chain
rule over the `N` cyclic rotations of the colors gives
`S(⋃ X_i) ≤ ∑ S(X_i) - (1/N) ∑_{i good} (S(X_i) - S(X_i | T_i))`.

This replaces the uniformly random child order in the proof of Proposition 3.3 of the
area-law manuscript by an average over `N` deterministic orders; each good child is last
among its neighbors in at least one of them, so the event of the source has frequency at
least `1/N`.

## Main results

* `sum_sub_filter_key_eq`: telescoping along an injective key.
* `regionalEntropy_biUnion_le_rotations`: the averaged chain rule.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  proof of Proposition 3.3 (`prop:initial-box`), `02-initial.tex`, lines 625–646.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw

/-- **Telescoping along an injective key.** For an injective key `κ` into a linear order,
`∑_{i ∈ s} (G {j ∈ s | κ j ≤ κ i} - G {j ∈ s | κ j < κ i}) = G s - G ∅`. -/
theorem sum_sub_filter_key_eq {ι β : Type*} [LinearOrder β] (κ : ι → β)
    (hκ : Function.Injective κ) (G : Finset ι → ℝ) (s : Finset ι) :
    ∑ i ∈ s, (G (s.filter fun j ↦ κ j ≤ κ i) - G (s.filter fun j ↦ κ j < κ i)) =
      G s - G ∅ := by
  classical
  induction s using Finset.induction_on_max_value κ with
  | empty => simp
  | insert a s ha hmax ih =>
    have hlt : ∀ x ∈ s, κ x < κ a := fun x hx ↦
      lt_of_le_of_ne (hmax x hx) fun h ↦ ha (hκ h ▸ hx)
    have h1 : (insert a s).filter (fun j ↦ κ j ≤ κ a) = insert a s :=
      Finset.filter_true_of_mem fun x hx ↦ by
        rcases Finset.mem_insert.mp hx with rfl | hx
        exacts [le_rfl, (hlt x hx).le]
    have h2 : (insert a s).filter (fun j ↦ κ j < κ a) = s := by
      rw [Finset.filter_insert, ite_eq_right (lt_irrefl _)]
      exact Finset.filter_true_of_mem hlt
    have h3 : ∀ i ∈ s, (insert a s).filter (fun j ↦ κ j ≤ κ i) =
        s.filter (fun j ↦ κ j ≤ κ i) := fun i hi ↦ by
      rw [Finset.filter_insert, ite_eq_right (not_le.mpr (hlt i hi))]
    have h4 : ∀ i ∈ s, (insert a s).filter (fun j ↦ κ j < κ i) =
        s.filter (fun j ↦ κ j < κ i) := fun i hi ↦ by
      rw [Finset.filter_insert, ite_eq_right (not_lt.mpr (hlt i hi).le)]
    rw [Finset.sum_insert ha, h1, h2,
      Finset.sum_congr rfl fun i hi ↦ by rw [h3 i hi, h4 i hi], ih]
    ring

variable {Λ : Finset (ℤ × ℤ)} {q : ℕ}

/-- Conditioning reduces entropy, read with the regional entropies of the finite-domain
model: `S(X | T) ≤ S(X | T')` for `T' ⊆ T` disjoint from `X`. -/
theorem regionalEntropy_cond_anti (Ω : StateSpace Λ q) {X T' T : Finset (Site Λ)}
    (hXT : Disjoint X T) (hT' : T' ⊆ T) :
    regionalEntropy Λ q Ω (X ∪ T) - regionalEntropy Λ q Ω T ≤
      regionalEntropy Λ q Ω (X ∪ T') - regionalEntropy Λ q Ω T' := by
  simp only [regionalEntropy_eq_regionEntropy]
  exact Entropy.regionEntropy_cond_anti (n := fun _ ↦ q) hXT hT' Ω

/-- **The chain rule averaged over rotated color orders.** Let `Ω` be a unit vector, `X_i`
pairwise disjoint regions, and `col i < N` colors. Suppose every `i ∈ good` has a buffer `T_i`
contained in the union of the regions of the other colors, with
`S(X_i | T_i) ≤ S(X_i)/2 + β`. Then
`S(⋃ X_i) ≤ ∑_i S(X_i) - (1/(2N)) ∑_{i ∈ good} S(X_i) + |good| β / N`.
Source: `02-initial.tex`, lines 625–646, the expected entropy chain rule. -/
theorem regionalEntropy_biUnion_le_rotations (Ω : StateSpace Λ q) (hΩ : ‖Ω‖ = 1) {ι : Type*}
    [Fintype ι] (Xs : ι → Finset (Site Λ))
    (hdisj : Pairwise fun i j ↦ Disjoint (Xs i) (Xs j)) {N : ℕ} (col : ι → ℕ)
    (hcol : ∀ i, col i < N) (good : Finset ι) (T : ι → Finset (Site Λ)) (β : ℝ)
    (hT : ∀ i ∈ good, T i ⊆ (Finset.univ.filter fun j ↦ col j ≠ col i).biUnion Xs)
    (hbuf : ∀ i ∈ good, regionalEntropy Λ q Ω (Xs i ∪ T i) - regionalEntropy Λ q Ω (T i) ≤
      regionalEntropy Λ q Ω (Xs i) / 2 + β) :
    regionalEntropy Λ q Ω (Finset.univ.biUnion Xs) ≤
      ∑ i, regionalEntropy Λ q Ω (Xs i) -
        (∑ i ∈ good, regionalEntropy Λ q Ω (Xs i)) / (2 * N) + good.card * β / N := by
  classical
  -- `N > 0` unless the index set is empty
  rcases isEmpty_or_nonempty ι with hι | hι
  · obtain rfl : good = ∅ := Finset.eq_empty_of_isEmpty good
    simp [Finset.univ_eq_empty, regionalEntropy_empty Λ q Ω hΩ]
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) (hcol (Classical.arbitrary ι))
  set S : Finset (Site Λ) → ℝ := regionalEntropy Λ q Ω
  -- the key of the `k`-th rotation
  set e := Fintype.equivFin ι
  set κ : ℕ → ι → Lex (ℕ × ℕ) := fun k i ↦ toLex ((col i + k) % N, (e i : ℕ))
  have hκ : ∀ k, Function.Injective (κ k) := fun k i j h ↦ by
    have := congrArg (fun p : Lex (ℕ × ℕ) ↦ (ofLex p).2) h
    simp only [κ, ofLex_toLex] at this
    exact e.injective (Fin.ext this)
  set pre : ℕ → ι → Finset (Site Λ) := fun k i ↦
    (Finset.univ.filter fun j ↦ κ k j < κ k i).biUnion Xs
  set term : ℕ → ι → ℝ := fun k i ↦ S (Xs i ∪ pre k i) - S (pre k i)
  -- the chain rule for each rotation
  have hchain : ∀ k, S (Finset.univ.biUnion Xs) = ∑ i, term k i := by
    intro k
    have h := sum_sub_filter_key_eq (κ k) (hκ k) (fun s ↦ S (s.biUnion Xs)) Finset.univ
    simp only [Finset.biUnion_empty] at h
    rw [show S ∅ = 0 from regionalEntropy_empty Λ q Ω hΩ, sub_zero] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hins : (Finset.univ.filter fun j ↦ κ k j ≤ κ k i) =
        insert i (Finset.univ.filter fun j ↦ κ k j < κ k i) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro hj
        rcases hj.lt_or_eq with hj | hj
        · exact Or.inr hj
        · exact Or.inl (hκ k hj)
      · rintro (rfl | hj)
        exacts [le_rfl, hj.le]
    simp only [term, pre]
    rw [hins, Finset.biUnion_insert]
  -- disjointness from the predecessors
  have hpre : ∀ k i, Disjoint (Xs i) (pre k i) := fun k i ↦ by
    refine (Finset.disjoint_biUnion_right _ _ _).mpr fun j hj ↦ hdisj ?_
    rintro rfl
    simp at hj
  have hterm : ∀ k i, term k i ≤ S (Xs i) := fun k i ↦ by
    have := regionalEntropy_cond_anti Ω (hpre k i) (Finset.empty_subset (pre k i))
    simpa [term, S, regionalEntropy_empty Λ q Ω hΩ] using this
  -- the good rotation of a good index
  have hgood : ∀ i ∈ good, term (N - 1 - col i) i ≤ S (Xs i) / 2 + β := by
    intro i hi
    set k := N - 1 - col i
    have hci := hcol i
    have hki : (col i + k) % N = N - 1 := by
      rw [show col i + k = N - 1 by omega]; exact Nat.mod_eq_of_lt (by omega)
    have hsub : T i ⊆ pre k i := by
      refine (hT i hi).trans (Finset.biUnion_subset_biUnion_of_subset_left _ ?_)
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      have hcj := hcol j
      have hne : (col j + k) % N ≠ N - 1 := by
        intro h
        have h1 : (col j + k) % N = (col i + k) % N := by rw [h, hki]
        have := Nat.ModEq.add_right_cancel' k h1
        exact hj (by rwa [Nat.ModEq, Nat.mod_eq_of_lt hcj, Nat.mod_eq_of_lt hci] at this)
      have hlt : (col j + k) % N < N - 1 := by
        have := Nat.mod_lt (col j + k) hN; omega
      simp only [κ]
      exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl (by rw [hki]; exact hlt))
    have hdisjT : Disjoint (Xs i) (pre k i) := hpre k i
    have := regionalEntropy_cond_anti Ω hdisjT hsub
    exact this.trans (hbuf i hi)
  -- sum over the rotations
  have hsumk : (N : ℝ) * S (Finset.univ.biUnion Xs) =
      ∑ i, ∑ k ∈ Finset.range N, term k i := by
    calc (N : ℝ) * S (Finset.univ.biUnion Xs) =
          ∑ k ∈ Finset.range N, S (Finset.univ.biUnion Xs) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = ∑ k ∈ Finset.range N, ∑ i, term k i := Finset.sum_congr rfl fun k _ ↦ hchain k
      _ = _ := Finset.sum_comm
  have hbound : ∀ i, ∑ k ∈ Finset.range N, term k i ≤
      N * S (Xs i) - (if i ∈ good then S (Xs i) / 2 - β else 0) := by
    intro i
    by_cases hi : i ∈ good
    · rw [ite_eq_left hi]
      have hk : N - 1 - col i ∈ Finset.range N := Finset.mem_range.mpr (by omega)
      rw [← Finset.add_sum_erase _ _ hk]
      have hrest : ∑ k ∈ (Finset.range N).erase (N - 1 - col i), term k i ≤
          ((N : ℝ) - 1) * S (Xs i) := by
        refine (Finset.sum_le_sum fun k _ ↦ hterm k i).trans ?_
        rw [Finset.sum_const, Finset.card_erase_of_mem hk, Finset.card_range, nsmul_eq_mul,
          Nat.cast_sub (by omega), Nat.cast_one]
      have := hgood i hi
      linarith
    · rw [ite_eq_right hi, sub_zero]
      refine (Finset.sum_le_sum fun k _ ↦ hterm k i).trans ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have htot := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ hbound i
  rw [← hsumk, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_mem,
    Finset.univ_inter, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    ← Finset.sum_div] at htot
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have key : S (Finset.univ.biUnion Xs) ≤ (N * ∑ i, S (Xs i) -
      (∑ i ∈ good, S (Xs i)) / 2 + good.card * β) / N := by
    rw [le_div_iff₀ hNpos]; linarith
  refine key.trans (le_of_eq ?_)
  field_simp

end TNLean.PEPS.AreaLaw
