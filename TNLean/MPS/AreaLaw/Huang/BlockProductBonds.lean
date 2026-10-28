/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Basic
import TNLean.MPS.AreaLaw.OpenMPS
import QICLean.Entropy.SupportedOperatorSchmidtWords

/-!
# Simultaneous bond bounds for two layers of interval operators

In one layer of disjoint interval-supported operators, at most one block crosses any fixed
cut. A block of width at most `w` contributes operator-Schmidt rank at most `q^(2w)`.
Thus one product of two such layers, of widths `w₀,w₁`, has rank at most
`q^(2(w₀+w₁))` simultaneously at every cut. A finite weighted sum multiplies this bound
by at most the number of summands.

The same full-chain operator occurs at every cut. No cut-dependent approximate operators
or comparison of Hilbert--Schmidt and operator norms is involved. The algebra does not
require unitarity; it therefore applies to the block unitaries of Osborne,
arXiv:quant-ph/0508031v2, Figure 2 and the decomposition preceding equation (1), and to
the finite propagator sum of Huang, arXiv:1406.6355v6, Section 5.4, Lemma 19, equation (22).
The analytic approximation of time evolution by such a product is a separate theorem.
-/

open Matrix
open scoped BigOperators

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ}

/-- An interval crossing a cut contains the first site to the right of the cut.
This is the interval geometry behind the disjoint layers of Osborne,
arXiv:quant-ph/0508031v2, Figure 2. -/
theorem boundary_mem_interval_of_not_oneSided (a b k : ℕ)
    (hcross : ¬ (interval L a b ⊆ leftBlock L k ∨ Disjoint (interval L a b) (leftBlock L k))) :
    ∃ hk : k < L, (⟨k, hk⟩ : Fin L) ∈ interval L a b := by
  have hleft : ¬ interval L a b ⊆ leftBlock L k := fun h ↦ hcross (Or.inl h)
  have hright : ¬ Disjoint (interval L a b) (leftBlock L k) := fun h ↦ hcross (Or.inr h)
  obtain ⟨x, hx, hxcut⟩ := Finset.not_disjoint_iff.mp hright
  obtain ⟨y, hy, hycut⟩ := Finset.not_subset.mp hleft
  have hxk : x.val < k := mem_leftBlock.mp hxcut
  have hky : k ≤ y.val := Nat.le_of_not_gt fun h ↦ hycut (mem_leftBlock.mpr h)
  refine ⟨lt_of_le_of_lt hky y.isLt, ?_⟩
  rw [mem_interval] at hx hy ⊢
  exact ⟨hx.1.trans (Nat.le_of_lt hxk), lt_of_le_of_lt hky hy.2⟩

private theorem crossing_interval_sum_le {ι : Type*} (a b : ι → ℕ) (w : List ι)
    (hdisj : w.Pairwise fun j k ↦ Disjoint (interval L (a j) (b j)) (interval L (a k) (b k)))
    (width : ℕ) (hwidth : ∀ j ∈ w, b j - a j ≤ width) (cut : ℕ) :
    (((w.filter fun j ↦ ¬ (interval L (a j) (b j) ⊆ leftBlock L cut ∨
      Disjoint (interval L (a j) (b j)) (leftBlock L cut))).map
        fun j ↦ (interval L (a j) (b j) ∩ leftBlock L cut).card).sum) ≤ width := by
  classical
  let cross := fun j ↦ ¬ (interval L (a j) (b j) ⊆ leftBlock L cut ∨
    Disjoint (interval L (a j) (b j)) (leftBlock L cut))
  change (((w.filter cross).map
    fun j ↦ (interval L (a j) (b j) ∩ leftBlock L cut).card).sum) ≤ width
  have hpair := hdisj.filter cross
  have hmem (j : ι) (hj : j ∈ w.filter cross) : j ∈ w ∧ cross j := by
    simpa only [List.mem_filter, decide_eq_true_eq] using hj
  cases hfilter : w.filter cross with
  | nil => simp
  | cons j tail =>
    have hj : j ∈ w ∧ cross j := hmem j (by rw [hfilter]; simp)
    have htail : tail = [] := by
      cases tail with
      | nil => rfl
      | cons k rest =>
        have hk : k ∈ w ∧ cross k := hmem k (by rw [hfilter]; simp)
        rw [hfilter] at hpair
        have hdisjoint := (List.pairwise_cons.mp hpair).1 k (by simp)
        obtain ⟨hcut, hjmem⟩ := boundary_mem_interval_of_not_oneSided (a j) (b j) cut hj.2
        obtain ⟨_, hkmem⟩ := boundary_mem_interval_of_not_oneSided (a k) (b k) cut hk.2
        exact (Finset.disjoint_left.mp hdisjoint hjmem hkmem).elim
    rw [htail]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    exact (Finset.card_le_card Finset.inter_subset_left).trans
      ((card_interval_le (a j) (b j)).trans (hwidth j hj.1))

/-- One fixed ordered layer of disjoint interval operators has the asserted rank bound
at every cut. Unitarity is unnecessary. Osborne, arXiv:quant-ph/0508031v2, Figure 2,
and Huang, arXiv:1406.6355v6, Section 5.4, Lemma 19. -/
theorem operatorSchmidtRank_disjoint_interval_prod_le {ι : Type*}
    (hq : 1 ≤ q) (a b : ι → ℕ) (P : ι → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hP : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (P j) (interval L (a j) (b j)))
    (w : List ι)
    (hdisj : w.Pairwise fun j k ↦ Disjoint (interval L (a j) (b j)) (interval L (a k) (b k)))
    (width : ℕ) (hwidth : ∀ j ∈ w, b j - a j ≤ width) (cut : ℕ) :
    operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q)
      (leftBlock L cut) ((w.map P).prod)) ≤ q ^ (2 * width) := by
  classical
  exact (Entropy.operatorSchmidtRank_cutOperator_list_prod_le
    (leftBlock L cut) (fun j ↦ interval L (a j) (b j)) P hP w).trans
      (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left 2
        (crossing_interval_sum_le a b w hdisj width hwidth cut)))

/-- The same two-layer full-chain product has uniformly bounded operator-Schmidt rank
at every cut. Osborne, arXiv:quant-ph/0508031v2, Figure 2; Huang,
arXiv:1406.6355v6, Section 5.4, Lemma 19. -/
theorem operatorSchmidtRank_two_interval_layers_le {ι κ : Type*}
    (hq : 1 ≤ q) (a b : ι → ℕ) (c d : κ → ℕ)
    (P : ι → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (Q : κ → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hP : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (P j) (interval L (a j) (b j)))
    (hQ : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (Q j) (interval L (c j) (d j)))
    (u : List ι) (v : List κ)
    (hu : u.Pairwise fun j k ↦ Disjoint (interval L (a j) (b j)) (interval L (a k) (b k)))
    (hv : v.Pairwise fun j k ↦ Disjoint (interval L (c j) (d j)) (interval L (c k) (d k)))
    (width₀ width₁ : ℕ)
    (hwidth₀ : ∀ j ∈ u, b j - a j ≤ width₀) (hwidth₁ : ∀ j ∈ v, d j - c j ≤ width₁) :
    ∀ cut : ℕ, operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q)
      (leftBlock L cut) ((u.map P).prod * (v.map Q).prod)) ≤ q ^ (2 * (width₀ + width₁)) := by
  intro cut
  rw [Entropy.cutOperator_mul]
  have h₀ := operatorSchmidtRank_disjoint_interval_prod_le hq a b P hP u hu
    width₀ hwidth₀ cut
  have h₁ := operatorSchmidtRank_disjoint_interval_prod_le hq c d Q hQ v hv
    width₁ hwidth₁ cut
  exact (operatorSchmidtRank_mul_le _ _).trans
    ((Nat.mul_le_mul h₀ h₁).trans_eq (by rw [← pow_add, ← Nat.mul_add]))

/-- A scalar-weighted sum of fixed full-chain operators has simultaneous cut-rank bound
equal to the sum of their bounds. Huang, arXiv:1406.6355v6, Section 5.4, equation (22).
The coefficients may be complex and need not be positive or normalized. -/
theorem operatorSchmidtRank_weighted_chain_sum_le {σ : Type*}
    (J : Finset σ) (c : σ → ℂ)
    (K : σ → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (D : ℕ)
    (hK : ∀ j ∈ J, ∀ cut : ℕ, operatorSchmidtRank
      (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L cut) (K j)) ≤ D) :
    ∀ cut : ℕ, operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q)
      (leftBlock L cut) (∑ j ∈ J, c j • K j)) ≤ J.card * D := by
  classical
  intro cut
  have heq : Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L cut)
      (∑ j ∈ J, c j • K j) =
      ∑ j ∈ J, c j • Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L cut) (K j) := by
    ext x y
    simp only [Entropy.cutOperator, Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.sum_apply, Matrix.smul_apply]
  rw [heq]
  calc
    _ ≤ ∑ j ∈ J, operatorSchmidtRank
        (c j • Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L cut) (K j)) :=
      operatorSchmidtRank_sum_le J _
    _ ≤ ∑ _j ∈ J, D := Finset.sum_le_sum fun j hj ↦
      (operatorSchmidtRank_smul_le _ _).trans (hK j hj cut)
    _ = J.card * D := by simp

/-- A finite weighted sum of the same two interval layers has the asserted bond bound
simultaneously at all cuts. The operators in the layers may vary with the sample, while
their supports and order remain fixed. Osborne, arXiv:quant-ph/0508031v2, Figure 2;
Huang, arXiv:1406.6355v6, Section 5.4, Lemma 19 and equation (22). -/
theorem operatorSchmidtRank_weighted_two_interval_layers_le {σ ι κ : Type*}
    (hq : 1 ≤ q) (J : Finset σ) (coeff : σ → ℂ) (a b : ι → ℕ) (c d : κ → ℕ)
    (P : σ → ι → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (Q : σ → κ → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hP : ∀ t ∈ J, ∀ j,
      Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (P t j) (interval L (a j) (b j)))
    (hQ : ∀ t ∈ J, ∀ j,
      Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (Q t j) (interval L (c j) (d j)))
    (u : List ι) (v : List κ)
    (hu : u.Pairwise fun j k ↦ Disjoint (interval L (a j) (b j)) (interval L (a k) (b k)))
    (hv : v.Pairwise fun j k ↦ Disjoint (interval L (c j) (d j)) (interval L (c k) (d k)))
    (width₀ width₁ : ℕ)
    (hwidth₀ : ∀ j ∈ u, b j - a j ≤ width₀) (hwidth₁ : ∀ j ∈ v, d j - c j ≤ width₁) :
    ∀ cut : ℕ, operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q)
      (leftBlock L cut) (∑ t ∈ J, coeff t • ((u.map (P t)).prod * (v.map (Q t)).prod))) ≤
        J.card * q ^ (2 * (width₀ + width₁)) := by
  apply operatorSchmidtRank_weighted_chain_sum_le
  intro t ht
  exact operatorSchmidtRank_two_interval_layers_le hq a b c d (P t) (Q t)
    (hP t ht) (hQ t ht) u v hu hv width₀ width₁ hwidth₀ hwidth₁

end TNLean.MPS.AreaLaw
