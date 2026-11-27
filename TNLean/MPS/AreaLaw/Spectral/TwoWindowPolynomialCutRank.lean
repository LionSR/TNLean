/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Spectral.TwoWindowPolynomialRank
import QICLean.ManyBody.Sites.PlacedConfiguration
import QICLean.Algebra.OperatorSchmidt.Basic
import QICLean.ManyBody.Entropy.SupportedMarginalTails
import QICLean.Entropy.Surprisal.FilterMoment
import QICLean.ManyBody.Sites.RegionState
import QICLean.ManyBody.Sites.Placement.Basic

/-!
# Rank of a polynomial of the two-window family at one cut

A cut inside one bulk region meets only the bulk operator of that region and the two terms of
the family that cross the cut. Across such a cut the sum of the family has operator Schmidt rank
at most `B + 2`, where `B` bounds the rank of the bulk operator, so every polynomial of degree at
most `k` has rank at most `(B + 2) ^ (k + 1)`. This gives Theorem 4.2, item 4, of ALVV at cuts in
the middle, left and right regions of the two-window family. Padding a single window with
zero-interaction spectators gives the single-window bound at one cut used for AKLV, Lemma 4.2.

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

/-! ### A single cut through zero-interaction spectators

Zero-interaction spectator sites allow the two-window polynomial estimate to control a single
cut. Fixing the spectator configurations cannot increase operator Schmidt rank. Supporting AKLV,
arXiv:1301.1162v1, Lemma 4.2; the ordered-gap count includes the correction recorded at
https://sirui-lu.com/QICLean/paper-gaps/aklv13_interpolation_and_word_count.pdf. The explicit
bound is proportional to `w + k/(2*w)` in the exponent; the further optimization over the window
width is separate. -/

open ManyBody (interval mem_interval)

open Matrix QuantumCircuit
open TNLean.MPS.AreaLaw
open scoped BigOperators

noncomputable section

namespace TNLean.MPS.AreaLaw.AKLV

private local instance configurationDecidableEq {V : Type*} (q : ℕ) :
    DecidableEq (V → Fin q) := Classical.decEq _

/-- Restricting spectator sites to fixed configurations recovers the
original cut operator without increasing its operator Schmidt rank. -/
theorem operatorSchmidtRank_le_placeAlong
    {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {q : ℕ} (e : V ↪ W) (A : Finset V) (B : Finset W)
    (hAB : ∀ v, e v ∈ B ↔ v ∈ A) (τ : W → Fin q)
    (K : Matrix (V → Fin q) (V → Fin q) ℂ) :
    operatorSchmidtRank (K.reindex (ManyBody.cutEquiv (fun _ ↦ Fin q) A)
        (ManyBody.cutEquiv (fun _ ↦ Fin q) A)) ≤
      operatorSchmidtRank ((ManyBody.placeAlong (X := fun _ ↦ Fin q) e K).reindex
        (ManyBody.cutEquiv (fun _ ↦ Fin q) B) (ManyBody.cutEquiv (fun _ ↦ Fin q) B)) := by
  classical
  let eA : A → B := fun i ↦ ⟨e i, (hAB i).mpr i.property⟩
  let eC : {v // v ∉ A} → {v // v ∉ B} := fun i ↦ ⟨e i, fun h ↦ i.property ((hAB i).mp h)⟩
  have heA : Function.Injective eA := fun i j hij ↦
    Subtype.ext (e.injective (congrArg Subtype.val hij))
  have heC : Function.Injective eC := fun i j hij ↦
    Subtype.ext (e.injective (congrArg Subtype.val hij))
  let f : (A → Fin q) → (B → Fin q) := fun x ↦
    Function.extend eA x (fun j ↦ τ j)
  let g : ({v // v ∉ A} → Fin q) → ({v // v ∉ B} → Fin q) := fun x ↦
    Function.extend eC x (fun j ↦ τ j)
  have hread (x : A → Fin q) (y : {v // v ∉ A} → Fin q) :
      (ManyBody.cutEquiv (fun _ ↦ Fin q) B).symm (f x, g y) ∘ e =
          (ManyBody.cutEquiv (fun _ ↦ Fin q) A).symm (x, y) := by
    funext i
    by_cases hi : i ∈ A
    · have hei : e i ∈ B := (hAB i).mpr hi
      simp only [Function.comp_apply,
        ManyBody.cutEquiv_symm_apply_mem _ _ hei,
        ManyBody.cutEquiv_symm_apply_mem _ _ hi]
      exact heA.extend_apply x (fun j ↦ τ j) ⟨i, hi⟩
    · have hei : e i ∉ B := fun h ↦ hi ((hAB i).mp h)
      simp only [Function.comp_apply,
        ManyBody.cutEquiv_symm_apply_not_mem _ _ hei,
        ManyBody.cutEquiv_symm_apply_not_mem _ _ hi]
      exact heC.extend_apply y (fun j ↦ τ j) ⟨i, hi⟩
  have hout (x : A → Fin q) (y : {v // v ∉ A} → Fin q) (j : W)
      (hj : ∀ i, e i ≠ j) : (ManyBody.cutEquiv (fun _ ↦ Fin q) B).symm (f x, g y) j = τ j := by
    by_cases hB : j ∈ B
    · rw [ManyBody.cutEquiv_symm_apply_mem _ _ hB]
      exact Function.extend_apply' (f := eA) x (fun j ↦ τ j) ⟨j, hB⟩ (by
        rintro ⟨i, hi⟩
        exact hj i (congrArg Subtype.val hi))
    · rw [ManyBody.cutEquiv_symm_apply_not_mem _ _ hB]
      exact Function.extend_apply' (f := eC) y (fun j ↦ τ j) ⟨j, hB⟩ (by
        rintro ⟨i, hi⟩
        exact hj i (congrArg Subtype.val hi))
  have hmatrix : K.reindex (ManyBody.cutEquiv (fun _ ↦ Fin q) A)
      (ManyBody.cutEquiv (fun _ ↦ Fin q) A) =
      ((ManyBody.placeAlong (X := fun _ ↦ Fin q) e K).reindex
        (ManyBody.cutEquiv (fun _ ↦ Fin q) B) (ManyBody.cutEquiv (fun _ ↦ Fin q) B)).submatrix
            (Prod.map f g) (Prod.map f g) := by
    ext ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
    simp only [reindex_apply, submatrix_apply, ManyBody.placeAlong_apply, Prod.map]
    rw [ite_eq_left (show ∀ j, (∀ i, e i ≠ j) → (ManyBody.cutEquiv (fun _ ↦ Fin q) B).symm
        (f x₁, g x₂) j =
        (ManyBody.cutEquiv (fun _ ↦ Fin q) B).symm (f y₁, g y₂) j from
        fun j hj ↦ (hout x₁ x₂ j hj).trans (hout y₁ y₂ j hj).symm)]
    exact congrArg₂ K (hread x₁ x₂).symm (hread y₁ y₂).symm
  rw [hmatrix]
  exact operatorSchmidtRank_submatrix_prod_le _ f f g g

/-- A polynomial in a single physical window and its two exterior
operators has the rank bound inherited from the two-window estimate.
The auxiliary window consists of zero interactions on spectator sites.
Supporting AKLV, arXiv:1301.1162v1, Lemma 4.2, with the corrected
ordered-gap count retained in the two-window estimate. -/
theorem operatorSchmidtRank_aeval_single_window_le_pow
    {L q w c : ℕ} [instConfig : DecidableEq (Fin L → Fin q)]
    (W : Fin (2 * w) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (PL PR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hW : ∀ r, W r ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
      (interval L (c + r.val) (c + r.val + 2) : Finset (Fin L)))
    (hPL : PL ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) (interval L 0 (c + 1) : Finset (Fin L)))
    (hPR : PR ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
        (interval L (c + 2 * w) L : Finset (Fin L)))
    (hw : 1 ≤ w) (hc : c + 2 * w ≤ L - 1) (τ : Fin q)
    (k : ℕ) (hk : 1 ≤ k) (P : Polynomial ℂ) (hdeg : P.natDegree ≤ k) :
    let A := interval L 0 (c + w + 1)
    operatorSchmidtRank ((Polynomial.aeval ((∑ r, W r) + PL + PR) P).reindex
      (ManyBody.cutEquiv (fun _ ↦ Fin q) A) (ManyBody.cutEquiv (fun _ ↦ Fin q) A)) ≤ (q * k) ^
          (17 * (w + k / (2 * w))) := by
  have hd : instConfig = Classical.decEq (Fin L → Fin q) := Subsingleton.elim _ _
  cases hd
  intro A
  classical
  let N := 2 * w + 1
  let T := L + N
  let e : Fin L ↪ Fin T :=
    ⟨fun i ↦ ⟨N + i.val, by dsimp [T]; omega⟩, by
      intro i j hij
      apply Fin.ext
      have := congrArg Fin.val hij
      dsimp at this
      omega⟩
  let E := (ManyBody.placeAlongHom (X := fun _ ↦ Fin q) e).toAlgHom
  let b := N + c
  let F : ((Fin (2 * w) ⊕ Fin (2 * w)) ⊕ Fin 3) →
      Matrix (Fin T → Fin q) (Fin T → Fin q) ℂ :=
    Sum.elim (Sum.elim (fun _ ↦ 0) (fun r ↦ E (W r))) ![0, E PL, E PR]
  have hmove {S : Finset (Fin L)} {R : Finset (Fin T)}
      {X : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
      (hX : X ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) S)
      (hSR : ∀ i ∈ S, e i ∈ R) : E X ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) R := by
    apply ManyBody.supportedOperators_mono ?_
      (ManyBody.placeAlong_mem_supportedOperators_map (X := fun _ ↦ Fin q) e hX)
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
    exact hSR i hi
  have hleft : ∀ r, F (Sum.inl (Sum.inl r)) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
      (interval T r.val (r.val + 2) : Finset (Fin T)) := fun _ ↦ zero_mem _
  have hright : ∀ r, F (Sum.inl (Sum.inr r)) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
      (interval T (b + r.val) (b + r.val + 2) : Finset (Fin T)) := by
    intro r
    apply hmove (hW r)
    intro i hi
    simp only [mem_interval] at hi ⊢
    change b + r.val ≤ N + i.val ∧ N + i.val < b + r.val + 2
    dsimp [b]
    omega
  have hleftbulk : F (Sum.inr 0) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
      (interval T 0 1 : Finset (Fin T)) := zero_mem _
  have hmidbulk : F (Sum.inr 1) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
      (interval T (2 * w) (b + 1) : Finset (Fin T)) := by
    apply hmove hPL
    intro i hi
    simp only [mem_interval] at hi ⊢
    change 2 * w ≤ N + i.val ∧ N + i.val < b + 1
    dsimp [b, N]
    omega
  have hrightbulk : F (Sum.inr 2) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
      (interval T (b + 2 * w) T : Finset (Fin T)) := by
    apply hmove hPR
    intro i hi
    simp only [mem_interval] at hi ⊢
    change b + 2 * w ≤ N + i.val ∧ N + i.val < T
    dsimp [b, T]
    omega
  have hab : 0 + 2 * w ≤ b := by dsimp [b, N]; omega
  have hb : b + 2 * w ≤ T - 1 := by dsimp [b, N, T]; omega
  have hrank := operatorSchmidtRank_aeval_two_window_le_pow
    (L := T) (q := q) (ℓ := w) (a := 0) (b := b) F
    (by simpa only [Nat.zero_add] using hleft) hright
    hleftbulk (by simpa only [Nat.zero_add] using hmidbulk) hrightbulk hab hb hw k hk P hdeg
    (0 : Fin 2)
  let B := interval T (0 + w + (0 : Fin 2).val) (b + w + 1)
  have hsum : (∑ i, F i) = E ((∑ r, W r) + PL + PR) := by
    simp [F, Fintype.sum_sum_type, Fin.sum_univ_succ, map_add, map_sum, add_assoc]
  have hpoly : Polynomial.aeval (∑ i, F i) P =
      E (Polynomial.aeval ((∑ r, W r) + PL + PR) P) := by
    rw [hsum]
    exact Polynomial.aeval_algHom_apply E _ P
  have hAB : ∀ i, e i ∈ B ↔ i ∈ A := by
    intro i
    simp only [B, A, mem_interval]
    change (0 + w + (0 : Fin 2).val ≤ N + i.val ∧ N + i.val < b + w + 1) ↔
      (0 ≤ i.val ∧ i.val < c + w + 1)
    dsimp [b, N]
    omega
  have hrestrict := operatorSchmidtRank_le_placeAlong e A B hAB (fun _ ↦ τ)
    (Polynomial.aeval ((∑ r, W r) + PL + PR) P)
  apply hrestrict.trans
  dsimp only at hrank
  rw [hpoly] at hrank
  exact hrank

end TNLean.MPS.AreaLaw.AKLV
