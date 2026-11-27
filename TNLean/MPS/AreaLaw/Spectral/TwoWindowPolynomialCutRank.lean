/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Spectral.TwoWindowPolynomialRank

/-!
# Rank of a polynomial of the two-window family at one cut

A cut inside one bulk region meets only the bulk operator of that region and the two terms of
the family that cross the cut. Across such a cut the sum of the family has operator Schmidt rank
at most `B + 2`, where `B` bounds the rank of the bulk operator, so every polynomial of degree at
most `k` has rank at most `(B + 2) ^ (k + 1)`. This gives Theorem 4.2, item 4, of ALVV at cuts in
the middle, left and right regions of the two-window family.

## References

ALVV, arXiv:1602.08828v2, `thm:Cheby-AGSP`, item 4, lines 825–826 and 848, and
`eq:H-mid-cut`, lines 813–821.
-/

open ManyBody (interval interval_mono mem_interval)

open Matrix
open scoped BigOperators Kronecker

/-! ### Cuts inside one bulk region -/

namespace Matrix

/-- Operator Schmidt rank is submultiplicative along powers, including the zeroth power.
Supporting algebra for ALVV, arXiv:1602.08828v2, Theorem `thm:Cheby-AGSP`, item 4,
lines 825–826 and 848. -/
private theorem operatorSchmidtRank_pow_le
    {l n : Type*} [Fintype l] [Fintype n] [DecidableEq l] [DecidableEq n]
    (M : Matrix (l × n) (l × n) ℂ) (r : ℕ) :
    operatorSchmidtRank (M ^ r) ≤ operatorSchmidtRank M ^ r := by
  induction r with
  | zero => simpa only [pow_zero] using operatorSchmidtRank_one_le
  | succ r ih =>
    rw [pow_succ, pow_succ]
    exact (operatorSchmidtRank_mul_le _ _).trans (Nat.mul_le_mul_right _ ih)

end Matrix

noncomputable section
namespace TNLean.MPS.AreaLaw


/-- **Rank of a polynomial at a cut inside one bulk region.** Let `H = ∑ β, F β` be a finite
sum of operators on `ι → Fin q`, and let `S` be a set of sites. Suppose that every term other
than `F β₀` acts on `S` or on its complement, and that `F β₀` has operator Schmidt rank at most
`B` across `(S, Sᶜ)`. Then every polynomial `P(H)` of degree at most `k` has operator Schmidt
rank at most `(B + 2) ^ (k + 1)` across `(S, Sᶜ)`.

This is the argument of ALVV, arXiv:1602.08828v2, Theorem `thm:Cheby-AGSP`, item 4,
lines 825–826, with proof at line 848: across the cut, `H` has rank at most `B + 2`, and `P(H)`
is a combination of the powers `H ^ j` with `j ≤ k`. -/
theorem operatorSchmidtRank_aeval_sum_le_pow_of_bulk
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] {q : ℕ} [DecidableEq (ι → Fin q)]
    (S : Finset ι)
    (F : α → Matrix (ι → Fin q) (ι → Fin q) ℂ) (β₀ : α)
    (hside : ∀ β, β ≠ β₀ → F β ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) S ∨
      F β ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) (Sᶜ : Finset ι))
    {B : ℕ} (hB : operatorSchmidtRank
        ((F β₀).reindex (ManyBody.cutEquiv (fun _ ↦ Fin q) S) (ManyBody.cutEquiv (fun _ ↦ Fin q) S))
        ≤ B)
    (k : ℕ) (P : Polynomial ℂ) (hdeg : P.natDegree ≤ k) :
    operatorSchmidtRank ((Polynomial.aeval (∑ β, F β) P).reindex
        (ManyBody.cutEquiv (fun _ ↦ Fin q) S) (ManyBody.cutEquiv (fun _ ↦ Fin q) S)) ≤ (B + 2) ^
            (k + 1) := by
  classical
  let g := ManyBody.cutEquiv (fun _ ↦ Fin q) S
  let M := ∑ β, F β
  have htransport : (Polynomial.aeval M P).reindex g g =
      Polynomial.aeval (M.reindex g g) P := by
    simpa only [Matrix.coe_reindexAlgEquiv] using
      (Polynomial.aeval_algHom_apply (Matrix.reindexAlgEquiv ℂ ℂ g) M P).symm
  -- The terms acting on `S` and those acting on `Sᶜ`.
  let s := (Finset.univ.erase β₀).filter fun β ↦ F β ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) S
  let t := (Finset.univ.erase β₀).filter fun β ↦ F β ∉ ManyBody.supportedOperators (fun _ ↦ Fin q) S
  have hM : M = F β₀ + ((∑ β ∈ s, F β) + ∑ β ∈ t, F β) := by
    rw [Finset.sum_filter_add_sum_filter_not, Finset.add_sum_erase _ _ (Finset.mem_univ β₀)]
  have hleft : (∑ β ∈ s, F β) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) S :=
    sum_mem fun β hβ ↦ (Finset.mem_filter.mp hβ).2
  have hright : (∑ β ∈ t, F β) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) (Sᶜ : Finset ι) := by
    refine sum_mem fun β hβ ↦ ?_
    obtain ⟨hβ, hnot⟩ := Finset.mem_filter.mp hβ
    exact (hside β (Finset.ne_of_mem_erase hβ)).resolve_left hnot
  obtain ⟨X, hX⟩ : ∃ X : Matrix (S → Fin q) (S → Fin q) ℂ,
      (∑ β ∈ s, F β).submatrix g.symm g.symm = X ⊗ₖ 1 := by
    obtain ⟨K, hK⟩ := ManyBody.exists_eq_place_of_mem_supportedOperators hleft
    exact ⟨K, by rw [hK]; exact ManyBody.cutOperator_place K⟩
  obtain ⟨Y, hY⟩ : ∃ Y : Matrix ({v // v ∉ S} → Fin q) ({v // v ∉ S} → Fin q) ℂ,
      (∑ β ∈ t, F β).submatrix g.symm g.symm = 1 ⊗ₖ Y := by
    obtain ⟨K, hK⟩ := ManyBody.exists_eq_one_kronecker_of_mem_supportedOperators
      (disjoint_compl_left : Disjoint Sᶜ S) hright
    exact ⟨K, by
      rw [hK, Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id]⟩
  have hrankM : operatorSchmidtRank (M.reindex g g) ≤ B + 2 := by
    rw [hM, Matrix.reindex_apply, Matrix.submatrix_add, Matrix.submatrix_add]
    refine (operatorSchmidtRank_add_le _ _).trans ?_
    refine (Nat.add_le_add hB (operatorSchmidtRank_add_le _ _)).trans ?_
    have h1 : operatorSchmidtRank ((∑ β ∈ s, F β).submatrix g.symm g.symm) ≤ 1 := by
      rw [hX]
      exact operatorSchmidtRank_kronecker_le_one _ _
    have h2 : operatorSchmidtRank ((∑ β ∈ t, F β).submatrix g.symm g.symm) ≤ 1 := by
      rw [hY]
      exact operatorSchmidtRank_kronecker_le_one _ _
    omega
  rw [htransport]
  refine (Matrix.operatorSchmidtRank_aeval_le_sum (M.reindex g g) P k hdeg).trans ?_
  calc ∑ r ∈ Finset.range (k + 1), operatorSchmidtRank ((M.reindex g g) ^ r)
      ≤ ∑ r ∈ Finset.range (k + 1), (B + 2) ^ r :=
        Finset.sum_le_sum fun r _ ↦ (Matrix.operatorSchmidtRank_pow_le _ r).trans
          (Nat.pow_le_pow_left hrankM r)
    _ ≤ (B + 2) ^ (k + 1) :=
        (Nat.geomSum_lt (by omega) fun r hr ↦ Finset.mem_range.mp hr).le

/-- Sites of `[x, y)` with `c ≤ x` lie to the right of the cut `[0, c)`. -/
private theorem coe_interval_subset_compl {L c x y : ℕ} (hcx : c ≤ x) :
    (interval L x y : Set (Fin L)) ⊆ ((interval L 0 c)ᶜ : Finset (Fin L)) := by
  intro i hi
  simp only [Finset.coe_compl, Set.mem_compl_iff, Finset.mem_coe, mem_interval] at hi ⊢
  omega

/-- Sites of `[x, y)` with `y ≤ c` lie to the left of the cut `[0, c)`. -/
private theorem coe_interval_subset_left {L c x y : ℕ} (hyc : y ≤ c) :
    (interval L x y : Set (Fin L)) ⊆ (interval L 0 c : Finset (Fin L)) :=
  Finset.coe_subset.mpr (interval_mono (Nat.zero_le x) hyc)

attribute [local instance] configurationDecidableEq alphabetDecidableEq

open Classical in
/-- **Theorem 4.2, item 4, at a cut inside `J_M`** (ALVV, arXiv:1602.08828v2,
`thm:Cheby-AGSP`, lines 825–826 and 848). In the two-window family of `eq:H-mid-cut`,
lines 813–821, consider the cut between sites `c - 1` and `c` with `a + 2ℓ + 1 ≤ c ≤ b`, both
in the middle region `J_M = [a + 2ℓ, b]`. If the middle bulk operator has operator Schmidt rank
at most `B` at this cut, then every polynomial of degree at most `k` in `∑ α, F α` has operator
Schmidt rank at most `(B + 2) ^ (k + 1)` there.

For `B ≥ 2` this is at most `B ^ (2k + 2)`, the printed bound `B ^ O(k)`. The two boundary terms
cannot be absorbed when `B ≤ 1`; see
https://sirui-lu.com/QICLean/paper-gaps/alvv16_chebyshev_near_ground_slope.pdf. -/
theorem operatorSchmidtRank_aeval_two_window_middle_cut_le
    {L q ℓ a b c : ℕ}
    (F : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) →
      Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hleft : ∀ r, F (Sum.inl (Sum.inl r)) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
      (interval L (a + r.val) (a + r.val + 2) : Finset (Fin L)))
    (hright : ∀ r, F (Sum.inl (Sum.inr r)) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
      (interval L (b + r.val) (b + r.val + 2) : Finset (Fin L)))
    (hL : F (Sum.inr 0) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
      (interval L 0 (a + 1) : Finset (Fin L)))
    (hR : F (Sum.inr 2) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
      (interval L (b + 2 * ℓ) L : Finset (Fin L)))
    (hac : a + 2 * ℓ + 1 ≤ c) (hcb : c ≤ b) {B : ℕ}
    (hB : operatorSchmidtRank ((F (Sum.inr 1)).reindex
      (ManyBody.cutEquiv (fun _ ↦ Fin q) (interval L 0 c))
          (ManyBody.cutEquiv (fun _ ↦ Fin q) (interval L 0 c))) ≤ B)
    (k : ℕ) (P : Polynomial ℂ) (hdeg : P.natDegree ≤ k) :
    operatorSchmidtRank ((Polynomial.aeval (∑ α, F α) P).reindex
        (ManyBody.cutEquiv (fun _ ↦ Fin q) (interval L 0 c))
            (ManyBody.cutEquiv (fun _ ↦ Fin q) (interval L 0 c))) ≤
      (B + 2) ^ (k + 1) := by
  refine operatorSchmidtRank_aeval_sum_le_pow_of_bulk _ F (Sum.inr 1) ?_ hB k P hdeg
  rintro ((r | r) | i) hi
  · exact Or.inl (ManyBody.supportedOperators_mono
      (coe_interval_subset_left (by have := r.isLt; omega)) (hleft r))
  · exact Or.inr (ManyBody.supportedOperators_mono
      (coe_interval_subset_compl (by have := r.isLt; omega)) (hright r))
  · fin_cases i
    · exact Or.inl (ManyBody.supportedOperators_mono (coe_interval_subset_left (by omega)) hL)
    · exact (hi rfl).elim
    · exact Or.inr (ManyBody.supportedOperators_mono (coe_interval_subset_compl (by omega)) hR)

open Classical in
/-- **Theorem 4.2, item 4, at a cut inside `J_L`** (ALVV, arXiv:1602.08828v2,
`thm:Cheby-AGSP`, lines 825–826 and 848). For the cut between sites `c - 1` and `c` with
`c ≤ a`, inside the left region `J_L = [0, a]`, the left bulk operator controls the rank: if it
has operator Schmidt rank at most `B` at this cut, then every polynomial of degree at most `k`
in `∑ α, F α` has operator Schmidt rank at most `(B + 2) ^ (k + 1)` there. -/
theorem operatorSchmidtRank_aeval_two_window_left_cut_le
    {L q ℓ a b c : ℕ}
    (F : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) →
      Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hleft : ∀ r, F (Sum.inl (Sum.inl r)) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
      (interval L (a + r.val) (a + r.val + 2) : Finset (Fin L)))
    (hright : ∀ r, F (Sum.inl (Sum.inr r)) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
      (interval L (b + r.val) (b + r.val + 2) : Finset (Fin L)))
    (hM : F (Sum.inr 1) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
      (interval L (a + 2 * ℓ) (b + 1) : Finset (Fin L)))
    (hR : F (Sum.inr 2) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
      (interval L (b + 2 * ℓ) L : Finset (Fin L)))
    (hab : a ≤ b) (hca : c ≤ a) {B : ℕ}
    (hB : operatorSchmidtRank ((F (Sum.inr 0)).reindex
      (ManyBody.cutEquiv (fun _ ↦ Fin q) (interval L 0 c))
          (ManyBody.cutEquiv (fun _ ↦ Fin q) (interval L 0 c))) ≤ B)
    (k : ℕ) (P : Polynomial ℂ) (hdeg : P.natDegree ≤ k) :
    operatorSchmidtRank ((Polynomial.aeval (∑ α, F α) P).reindex
        (ManyBody.cutEquiv (fun _ ↦ Fin q) (interval L 0 c))
            (ManyBody.cutEquiv (fun _ ↦ Fin q) (interval L 0 c))) ≤
      (B + 2) ^ (k + 1) := by
  refine operatorSchmidtRank_aeval_sum_le_pow_of_bulk _ F (Sum.inr 0) ?_ hB k P hdeg
  rintro ((r | r) | i) hi
  · exact Or.inr (ManyBody.supportedOperators_mono
      (coe_interval_subset_compl (by have := r.isLt; omega)) (hleft r))
  · exact Or.inr (ManyBody.supportedOperators_mono
      (coe_interval_subset_compl (by have := r.isLt; omega)) (hright r))
  · fin_cases i
    · exact (hi rfl).elim
    · exact Or.inr (ManyBody.supportedOperators_mono (coe_interval_subset_compl (by omega)) hM)
    · exact Or.inr (ManyBody.supportedOperators_mono (coe_interval_subset_compl (by omega)) hR)

open Classical in
/-- **Theorem 4.2, item 4, at a cut inside `J_R`** (ALVV, arXiv:1602.08828v2,
`thm:Cheby-AGSP`, lines 825–826 and 848). For the cut between sites `c - 1` and `c` with
`b + 2ℓ + 1 ≤ c`, inside the right region `J_R = [b + 2ℓ, L)`, the right bulk operator controls
the rank: if it has operator Schmidt rank at most `B` at this cut, then every polynomial of degree
at most `k` in `∑ α, F α` has operator Schmidt rank at most `(B + 2) ^ (k + 1)` there. -/
theorem operatorSchmidtRank_aeval_two_window_right_cut_le
    {L q ℓ a b c : ℕ}
    (F : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) →
      Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hleft : ∀ r, F (Sum.inl (Sum.inl r)) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
      (interval L (a + r.val) (a + r.val + 2) : Finset (Fin L)))
    (hright : ∀ r, F (Sum.inl (Sum.inr r)) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
      (interval L (b + r.val) (b + r.val + 2) : Finset (Fin L)))
    (hL : F (Sum.inr 0) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
      (interval L 0 (a + 1) : Finset (Fin L)))
    (hM : F (Sum.inr 1) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
      (interval L (a + 2 * ℓ) (b + 1) : Finset (Fin L)))
    (hab : a ≤ b) (hbc : b + 2 * ℓ + 1 ≤ c) {B : ℕ}
    (hB : operatorSchmidtRank ((F (Sum.inr 2)).reindex
      (ManyBody.cutEquiv (fun _ ↦ Fin q) (interval L 0 c))
          (ManyBody.cutEquiv (fun _ ↦ Fin q) (interval L 0 c))) ≤ B)
    (k : ℕ) (P : Polynomial ℂ) (hdeg : P.natDegree ≤ k) :
    operatorSchmidtRank ((Polynomial.aeval (∑ α, F α) P).reindex
        (ManyBody.cutEquiv (fun _ ↦ Fin q) (interval L 0 c))
            (ManyBody.cutEquiv (fun _ ↦ Fin q) (interval L 0 c))) ≤
      (B + 2) ^ (k + 1) := by
  refine operatorSchmidtRank_aeval_sum_le_pow_of_bulk _ F (Sum.inr 2) ?_ hB k P hdeg
  rintro ((r | r) | i) hi
  · exact Or.inl (ManyBody.supportedOperators_mono
      (coe_interval_subset_left (by have := r.isLt; omega)) (hleft r))
  · exact Or.inl (ManyBody.supportedOperators_mono
      (coe_interval_subset_left (by have := r.isLt; omega)) (hright r))
  · fin_cases i
    · exact Or.inl (ManyBody.supportedOperators_mono (coe_interval_subset_left (by omega)) hL)
    · exact Or.inl (ManyBody.supportedOperators_mono (coe_interval_subset_left (by omega)) hM)
    · exact (hi rfl).elim

end TNLean.MPS.AreaLaw
end
