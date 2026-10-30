/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ALVV.FrustrationFree
import TNLean.MPS.AreaLaw.Hastings.PartCommutators
import QICLean.Entropy.SupportedOperatorSchmidtWords

/-!
# Rank of the regional frustration-free replacement

We use zero-based site and bond indices. The region of sites `[a,b+1)` replaces
exactly the bonds in `[a,b)`, retaining its boundary bonds. This is the coherent
reading of the explicit sum in ALVV, arXiv:1602.08828v2, Definition 5.10.

**Local fix (regional rank):** Theorem 5.14(2) needs the bound `d² + 3` for an
interior region. A prefix or suffix retains the bound `d² + 2`.
See `docs/paper-gaps/alvv16_ff_rank.tex` for the endpoint convention and examples.
-/

open Matrix
open scoped Kronecker

namespace TNLean.MPS.AreaLaw.ALVV

variable {L q : ℕ}

/-- Matrix coordinates for the regional parity product, in the same order as
`regionalProjection`. ALVV, Definition 5.10. -/
noncomputable def regionalProjectionMatrix
    (h : ℕ → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (s : Finset ℕ) :
    ℕ → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ
  | 0 => 1
  | m + 1 => (if m ∈ s then 1 - h m else 1) * regionalProjectionMatrix h s m

/-- The matrix product is exactly the continuous-map regional product. -/
theorem toEuclideanCLM_regionalProjectionMatrix
    (h : ℕ → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (s : Finset ℕ) (m : ℕ) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)) (regionalProjectionMatrix h s m) =
      regionalProjection
        (fun i ↦ (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)) (h i)) s m := by
  classical
  induction m with
  | zero => simp [regionalProjectionMatrix, regionalProjection]
  | succ m ih =>
    rw [regionalProjectionMatrix, map_mul, ih]
    change _ = (1 - restrictedTerm _ s m) * _
    congr 1
    by_cases hm : m ∈ s <;> simp [restrictedTerm, hm]

/-- Matrix coordinates for the regional replacement, including every exterior term.
ALVV, Definition 5.10. -/
noncomputable def regionalReplacementMatrix
    (h : ℕ → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (s t : Finset ℕ) (m : ℕ) : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
  (∑ i ∈ Finset.range m, if i ∈ s ∪ t then 0 else h i) +
    (1 - regionalProjectionMatrix h s m) + (1 - regionalProjectionMatrix h t m)

/-- The matrix replacement is the operator replacement under the canonical star algebra
identification, not an independent rank model. -/
theorem toEuclideanCLM_regionalReplacementMatrix
    (h : ℕ → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (s t : Finset ℕ) (m : ℕ) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)) (regionalReplacementMatrix h s t m) =
      regionalReplacement
        (fun i ↦ (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)) (h i)) s t m := by
  classical
  simp only [regionalReplacementMatrix, regionalReplacement, map_add, map_sub, map_one,
    map_sum, toEuclideanCLM_regionalProjectionMatrix]
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hs : i ∈ s ∪ t <;>
    simp [restrictedTerm, hs, Finset.mem_range.mp hi]

private theorem edge_subset_left {i k : ℕ} (hi : i + 1 < k) :
    interval L i (i + 2) ⊆ interval L 0 k := by
  intro x hx
  simp only [mem_interval] at hx ⊢
  omega

private theorem edge_disjoint_left {i k : ℕ} (hi : k ≤ i) :
    Disjoint (interval L i (i + 2)) (interval L 0 k) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  simp only [mem_interval] at hx hy
  omega

private theorem edge_oneSided {i k : ℕ} (hi : i + 1 ≠ k) :
    interval L i (i + 2) ⊆ interval L 0 k ∨
      Disjoint (interval L i (i + 2)) (interval L 0 k) := by
  by_cases h : i + 1 < k
  · exact Or.inl (edge_subset_left h)
  · exact Or.inr (edge_disjoint_left (by omega))

private theorem rank_one_le (k : ℕ) :
    operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q)
      (interval L 0 k) 1) ≤ 1 :=
  (Entropy.isSupportedOn_one (∅ : Finset (Fin L))).operatorSchmidtRank_cutOperator_le_one
    (Or.inl (Finset.empty_subset _))

private theorem edge_rank_le_sq {i k : ℕ}
    {H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ} (hq : 1 ≤ q)
    (hH : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) H (interval L i (i + 2))) :
    operatorSchmidtRank (Entropy.cutOperator (interval L 0 k) H) ≤ q ^ 2 := by
  by_cases hi : i + 1 = k
  · have hcard : ((interval L i (i + 2)) ∩ interval L 0 k).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro x hx y hy
      simp only [Finset.mem_inter, mem_interval] at hx hy
      apply Fin.ext
      omega
    exact hH.operatorSchmidtRank_cutOperator_le.trans (by
      simp only [Finset.prod_const, ← pow_mul]
      exact Nat.pow_le_pow_right hq (by omega))
  · exact (hH.operatorSchmidtRank_cutOperator_le_one (edge_oneSided hi)).trans
      (Nat.one_le_pow 2 q hq)

/-- A regional product is supported wherever all its selected bonds are supported.
ALVV, Definition 5.10. -/
theorem regionalProjectionMatrix_supported
    {h : ℕ → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ} (hq : 1 ≤ q)
    (hh : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i (i + 2))) (s : Finset ℕ) (m : ℕ) (D : Finset (Fin L))
    (hD : ∀ i < m, i ∈ s → interval L i (i + 2) ⊆ D) :
    Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (regionalProjectionMatrix h s m) D := by
  classical
  induction m with
  | zero => exact Entropy.isSupportedOn_one D
  | succ m ih =>
    rw [regionalProjectionMatrix]
    have hprefix := ih (fun i hi hs ↦ hD i (by omega) hs)
    by_cases hm : m ∈ s
    · simp only [hm, ↓reduceIte]
      exact ((Entropy.isSupportedOn_one D).sub ((hh m).mono (hD m (by omega) hm))).mul
        hprefix (fun _ : Fin L ↦ (⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hq⟩ : Fin q))
    · simpa [hm] using hprefix

/-- A parity product with no selected bond crossing the cut has rank at most one.
The bound follows from supported-factor decompositions. -/
theorem rank_regionalProjectionMatrix_le_one
    {h : ℕ → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
    (hh : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i (i + 2))) (s : Finset ℕ) (m k : ℕ)
    (hcross : ∀ i < m, i ∈ s → i + 1 ≠ k) :
    operatorSchmidtRank (Entropy.cutOperator (interval L 0 k)
      (regionalProjectionMatrix h s m)) ≤ 1 := by
  classical
  induction m with
  | zero => exact rank_one_le k
  | succ m ih =>
    have hprefix := ih (fun i hi hs ↦ hcross i (by omega) hs)
    rw [regionalProjectionMatrix]
    by_cases hm : m ∈ s
    · simp only [hm, ↓reduceIte, Entropy.cutOperator_mul]
      have hfactor :=
        ((Entropy.isSupportedOn_one _).sub (hh m)).operatorSchmidtRank_cutOperator_le_one
         (edge_oneSided (hcross m (by omega) hm))
      exact (operatorSchmidtRank_mul_le _ _).trans (by simpa using Nat.mul_le_mul hfactor hprefix)
    · simpa [hm] using hprefix

/-- A product using each nearest-neighbor bond at most once has rank at most `q²`
at any cut. This supplies the crossing-parity contribution in ALVV, Theorem 5.14. -/
theorem rank_regionalProjectionMatrix_le_sq
    {h : ℕ → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ} (hq : 1 ≤ q)
    (hh : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i (i + 2))) (s : Finset ℕ) (m k : ℕ) :
    operatorSchmidtRank (Entropy.cutOperator (interval L 0 k)
      (regionalProjectionMatrix h s m)) ≤ q ^ 2 := by
  classical
  induction m with
  | zero => exact (rank_one_le k).trans (Nat.one_le_pow 2 q hq)
  | succ m ih =>
    rw [regionalProjectionMatrix]
    by_cases hm : m ∈ s
    · simp only [hm, ↓reduceIte, Entropy.cutOperator_mul]
      by_cases hk : m + 1 = k
      · have hprefix := rank_regionalProjectionMatrix_le_one hh s m k
          (fun i hi _ ↦ by omega)
        have hfactor := edge_rank_le_sq (k := k) hq ((Entropy.isSupportedOn_one _).sub (hh m))
        exact (operatorSchmidtRank_mul_le _ _).trans
          (by simpa using Nat.mul_le_mul hfactor hprefix)
      · have hfactor :=
          ((Entropy.isSupportedOn_one _).sub (hh m)).operatorSchmidtRank_cutOperator_le_one
           (edge_oneSided hk)
        exact (operatorSchmidtRank_mul_le _ _).trans
          (by simpa using Nat.mul_le_mul hfactor ih)
    · simpa [hm] using ih

private noncomputable def cutRank
    (H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (k : ℕ) : ℕ :=
  operatorSchmidtRank (Entropy.cutOperator (interval L 0 k) H)

private theorem cutRank_add_le
    (A B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (k : ℕ) :
    cutRank (A + B) k ≤ cutRank A k + cutRank B k :=
  operatorSchmidtRank_add_le _ _

private theorem cutRank_sub_le
    (A B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (k : ℕ) :
    cutRank (A - B) k ≤ cutRank A k + cutRank B k := by
  have hneg : cutRank (-B) k ≤ cutRank B k := by
    simpa only [cutRank, Entropy.cutOperator, reindex_apply, Matrix.submatrix_neg, Pi.neg_apply,
      neg_one_smul] using operatorSchmidtRank_smul_le (-1 : ℂ)
      (Entropy.cutOperator (interval L 0 k) B)
  exact (cutRank_add_le A (-B) k).trans (Nat.add_le_add_left hneg _)

private noncomputable def exteriorIndices (s t : Finset ℕ) (m : ℕ) : Finset ℕ :=
  (Finset.range m).filter fun i ↦ i ∉ s ∪ t

private noncomputable def leftExterior
    (h : ℕ → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (s t : Finset ℕ) (m k : ℕ) : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
  ∑ i ∈ (exteriorIndices s t m).filter (fun i ↦ i + 1 < k), h i

private noncomputable def rightExterior
    (h : ℕ → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (s t : Finset ℕ) (m k : ℕ) : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
  ∑ i ∈ (exteriorIndices s t m).filter (fun i ↦ k ≤ i), h i

private noncomputable def crossingExterior
    (h : ℕ → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (s t : Finset ℕ) (m k : ℕ) : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
  ∑ i ∈ (exteriorIndices s t m).filter (fun i ↦ i + 1 = k), h i

private theorem exterior_split
    (h : ℕ → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (s t : Finset ℕ) (m k : ℕ) :
    (∑ i ∈ Finset.range m, if i ∈ s ∪ t then 0 else h i) =
      leftExterior h s t m k + rightExterior h s t m k + crossingExterior h s t m k := by
  classical
  simp only [leftExterior, rightExterior, crossingExterior, exteriorIndices,
    Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hs : i ∈ s ∪ t
  · simp [hs]
  · simp only [hs, not_false_eq_true, ↓reduceIte]
    by_cases hl : i + 1 < k
    · simp [hl, show ¬k ≤ i by omega, show i + 1 ≠ k by omega]
    by_cases hr : k ≤ i
    · simp [hl, hr, show i + 1 ≠ k by omega]
    · simp [hr, show i + 1 = k by omega]

private theorem leftExterior_supported
    {h : ℕ → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
    (hh : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i (i + 2))) (s t : Finset ℕ) (m k : ℕ) :
    Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (leftExterior h s t m k) (interval L 0 k) :=
  TNLean.Lattice.isSupportedOn_sum _ fun i hi ↦
    (hh i).mono (edge_subset_left (Finset.mem_filter.mp hi).2)

private theorem rightExterior_supported
    {h : ℕ → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
    (hh : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i (i + 2))) (s t : Finset ℕ) (m k : ℕ) :
    Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (rightExterior h s t m k) (interval L 0 k)ᶜ := by
  apply TNLean.Lattice.isSupportedOn_sum
  intro i hi
  apply (hh i).mono
  intro x hx
  exact Finset.mem_compl.mpr fun hy ↦
    Finset.disjoint_left.mp (edge_disjoint_left (Finset.mem_filter.mp hi).2) hx hy

private theorem crossingExterior_rank_le
    {h : ℕ → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ} (hq : 1 ≤ q)
    (hh : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i (i + 2))) (s t : Finset ℕ) (m k : ℕ) :
    cutRank (crossingExterior h s t m k) k ≤ q ^ 2 := by
  classical
  let C := (exteriorIndices s t m).filter (fun i ↦ i + 1 = k)
  have hC : C.card ≤ 1 := Finset.card_le_one.mpr fun i hi j hj ↦ by
    have hi := (Finset.mem_filter.mp hi).2
    have hj := (Finset.mem_filter.mp hj).2
    omega
  change operatorSchmidtRank (Entropy.cutOperator (interval L 0 k) (∑ i ∈ C, h i)) ≤ _
  simp only [Entropy.cutOperator, reindex_apply, Matrix.submatrix_sum]
  calc
    _ ≤ ∑ i ∈ C, operatorSchmidtRank (Entropy.cutOperator (interval L 0 k) (h i)) :=
      operatorSchmidtRank_sum_le _ _
    _ ≤ ∑ _ ∈ C, q ^ 2 := Finset.sum_le_sum fun i _ ↦ edge_rank_le_sq hq (hh i)
    _ = C.card * q ^ 2 := by simp
    _ ≤ q ^ 2 := by simpa using Nat.mul_le_mul_right (q ^ 2) hC

private theorem crossingExterior_eq_zero
    (h : ℕ → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    {s t : Finset ℕ} {m a b k : ℕ} (hst : s ∪ t = Finset.Ico a b)
    (hin : a < k ∧ k ≤ b) : crossingExterior h s t m k = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i hi
  obtain ⟨hi, hik⟩ := Finset.mem_filter.mp hi
  have hn := (Finset.mem_filter.mp hi).2
  rw [hst] at hn
  simp only [Finset.mem_Ico] at hn
  omega

/-- The zero-based even bonds of the site region `[a,b+1)`: its last selected
bond is `b-1`, not `b`. ALVV, Definition 5.10's explicit regional sum. -/
def evenBonds (a b : ℕ) : Finset ℕ := (Finset.Ico a b).filter fun i ↦ i % 2 = 0

/-- The zero-based odd bonds in the same half-open bond interval. -/
def oddBonds (a b : ℕ) : Finset ℕ := (Finset.Ico a b).filter fun i ↦ i % 2 ≠ 0

private theorem union_parityBonds (a b : ℕ) : evenBonds a b ∪ oddBonds a b = Finset.Ico a b := by
  ext i
  simp only [evenBonds, oddBonds, Finset.mem_union, Finset.mem_filter, Finset.mem_Ico]
  omega

private theorem disjoint_parityBonds (a b : ℕ) : Disjoint (evenBonds a b) (oddBonds a b) := by
  rw [Finset.disjoint_left]
  intro i hi hj
  exact (Finset.mem_filter.mp hj).2 (Finset.mem_filter.mp hi).2

private theorem rank_parity_products_le
    {h : ℕ → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ} (hq : 1 ≤ q)
    (hh : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i (i + 2))) (a b m k : ℕ) :
    cutRank (regionalProjectionMatrix h (evenBonds a b) m) k +
      cutRank (regionalProjectionMatrix h (oddBonds a b) m) k ≤ q ^ 2 + 1 := by
  classical
  by_cases hs : k - 1 ∈ evenBonds a b
  · have ht := rank_regionalProjectionMatrix_le_one hh (oddBonds a b) m k (by
      intro i _ hi hik
      have : i = k - 1 := by omega
      subst i
      exact Finset.disjoint_left.mp (disjoint_parityBonds a b) hs hi)
    exact Nat.add_le_add (rank_regionalProjectionMatrix_le_sq hq hh _ m k) ht
  · have he := rank_regionalProjectionMatrix_le_one hh (evenBonds a b) m k (by
      intro i _ hi hik
      have : i = k - 1 := by omega
      exact hs (this ▸ hi))
    have ho := rank_regionalProjectionMatrix_le_sq hq hh (oddBonds a b) m k
    exact (Nat.add_le_add he ho).trans_eq (Nat.add_comm _ _)

private theorem rank_inside_le
    {h : ℕ → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ} (hq : 1 ≤ q)
    (hh : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i (i + 2))) (a b m k : ℕ) (hin : a < k ∧ k ≤ b) :
    cutRank (regionalReplacementMatrix h (evenBonds a b) (oddBonds a b) m) k ≤
      q ^ 2 + 3 := by
  classical
  let s := evenBonds a b
  let t := oddBonds a b
  let X := leftExterior h s t m k + 1
  let Y := rightExterior h s t m k + 1
  have hX := (leftExterior_supported hh s t m k).add
    (Entropy.isSupportedOn_one (interval L 0 k))
  have hY := (rightExterior_supported hh s t m k).add
    (Entropy.isSupportedOn_one (interval L 0 k)ᶜ)
  have hrX : cutRank X k ≤ 1 :=
    hX.operatorSchmidtRank_cutOperator_le_one (Or.inl (Finset.Subset.refl _))
  have hrY : cutRank Y k ≤ 1 :=
    hY.operatorSchmidtRank_cutOperator_le_one (Or.inr disjoint_compl_left)
  have hdecomp : regionalReplacementMatrix h s t m =
      X + Y - regionalProjectionMatrix h s m - regionalProjectionMatrix h t m := by
    rw [regionalReplacementMatrix, exterior_split h s t m k,
      crossingExterior_eq_zero h (union_parityBonds a b) hin]
    dsimp [X, Y]
    abel
  rw [hdecomp]
  have hsum := cutRank_add_le X Y k
  have hsub := cutRank_sub_le (X + Y) (regionalProjectionMatrix h s m) k
  have hsub' := cutRank_sub_le (X + Y - regionalProjectionMatrix h s m)
    (regionalProjectionMatrix h t m) k
  have hp := rank_parity_products_le hq hh a b m k
  change cutRank (regionalProjectionMatrix h s m) k +
    cutRank (regionalProjectionMatrix h t m) k ≤ q ^ 2 + 1 at hp
  omega

private theorem rank_outside_le
    {h : ℕ → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ} (hq : 1 ≤ q)
    (hh : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i (i + 2))) (a b m k : ℕ) (hout : k ≤ a ∨ b < k) :
    cutRank (regionalReplacementMatrix h (evenBonds a b) (oddBonds a b) m) k ≤
      q ^ 2 + 2 := by
  classical
  let s := evenBonds a b
  let t := oddBonds a b
  let Ps := regionalProjectionMatrix h s m
  let Pt := regionalProjectionMatrix h t m
  have hl := leftExterior_supported hh s t m k
  have hr := rightExterior_supported hh s t m k
  have hc := crossingExterior_rank_le hq hh s t m k
  have hregions (D : Finset (Fin L))
      (hD : ∀ i ∈ Finset.Ico a b, interval L i (i + 2) ⊆ D) :
      Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) Ps D ∧
      Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) Pt D := by
    constructor
    · exact regionalProjectionMatrix_supported hq hh s m D
        (fun i _ hi ↦ hD i (Finset.mem_filter.mp hi).1)
    · exact regionalProjectionMatrix_supported hq hh t m D
        (fun i _ hi ↦ hD i (Finset.mem_filter.mp hi).1)
  rcases hout with hleft | hright
  · obtain ⟨hPs, hPt⟩ := hregions (interval L 0 k)ᶜ (by
      intro i hi x hx
      exact Finset.mem_compl.mpr fun hy ↦
        Finset.disjoint_left.mp (edge_disjoint_left (by
          have := (Finset.mem_Ico.mp hi).1
          omega)) hx hy)
    let Y := rightExterior h s t m k + 1 + 1 - Ps - Pt
    have hY := (((hr.add (Entropy.isSupportedOn_one _)).add
      (Entropy.isSupportedOn_one _)).sub hPs).sub hPt
    have hrY : cutRank Y k ≤ 1 :=
      hY.operatorSchmidtRank_cutOperator_le_one (Or.inr disjoint_compl_left)
    have hrL : cutRank (leftExterior h s t m k) k ≤ 1 :=
      hl.operatorSchmidtRank_cutOperator_le_one (Or.inl (Finset.Subset.refl _))
    have hdecomp : regionalReplacementMatrix h s t m =
        leftExterior h s t m k + Y + crossingExterior h s t m k := by
      rw [regionalReplacementMatrix, exterior_split h s t m k]
      dsimp [Y, Ps, Pt]
      abel
    rw [hdecomp]
    have hsum := cutRank_add_le (leftExterior h s t m k) Y k
    have hsum' := cutRank_add_le (leftExterior h s t m k + Y)
      (crossingExterior h s t m k) k
    omega
  · obtain ⟨hPs, hPt⟩ := hregions (interval L 0 k) (by
      intro i hi
      exact edge_subset_left (by have := (Finset.mem_Ico.mp hi).2; omega))
    let X := leftExterior h s t m k + 1 + 1 - Ps - Pt
    have hX := (((hl.add (Entropy.isSupportedOn_one _)).add
      (Entropy.isSupportedOn_one _)).sub hPs).sub hPt
    have hrX : cutRank X k ≤ 1 :=
      hX.operatorSchmidtRank_cutOperator_le_one (Or.inl (Finset.Subset.refl _))
    have hrR : cutRank (rightExterior h s t m k) k ≤ 1 :=
      hr.operatorSchmidtRank_cutOperator_le_one (Or.inr disjoint_compl_left)
    have hdecomp : regionalReplacementMatrix h s t m =
        X + rightExterior h s t m k + crossingExterior h s t m k := by
      rw [regionalReplacementMatrix, exterior_split h s t m k]
      dsimp [X, Ps, Pt]
      abel
    rw [hdecomp]
    have hsum := cutRank_add_le X (rightExterior h s t m k) k
    have hsum' := cutRank_add_le (X + rightExterior h s t m k)
      (crossingExterior h s t m k) k
    omega

/-- The corrected all-cut rank bound for the regional replacement is `q²+3`.
ALVV, Theorem 5.14(2), with the interior-region correction documented in the module note.
Only locality and positive local dimension are needed; the terms need not be projectors. -/
private theorem rank_regionalReplacementMatrix_nat_le_sq_add_three
    {h : ℕ → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ} (hq : 1 ≤ q)
    (hh : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i (i + 2))) (a b m k : ℕ) :
    operatorSchmidtRank (Entropy.cutOperator (interval L 0 k)
      (regionalReplacementMatrix h (evenBonds a b) (oddBonds a b) m)) ≤ q ^ 2 + 3 := by
  by_cases hin : a < k ∧ k ≤ b
  · exact rank_inside_le hq hh a b m k hin
  · exact (rank_outside_le hq hh a b m k (by omega)).trans (by omega)

private theorem rank_boundary_inside_le
    {h : ℕ → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ} (hq : 1 ≤ q)
    (hh : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i (i + 2))) (a b m k : ℕ) (hin : a < k ∧ k ≤ b)
    (hboundary : a = 0 ∨ m ≤ b) :
    cutRank (regionalReplacementMatrix h (evenBonds a b) (oddBonds a b) m) k ≤
      q ^ 2 + 2 := by
  classical
  let s := evenBonds a b
  let t := oddBonds a b
  let W := leftExterior h s t m k + rightExterior h s t m k + 1 + 1
  have hW : cutRank W k ≤ 1 := by
    rcases hboundary with ha | hb
    · have hl : leftExterior h s t m k = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        obtain ⟨hi, hik⟩ := Finset.mem_filter.mp hi
        obtain ⟨him, hn⟩ := Finset.mem_filter.mp hi
        rw [show s ∪ t = Finset.Ico a b from union_parityBonds a b] at hn
        simp only [Finset.mem_Ico] at hn
        omega
      have hr := ((rightExterior_supported hh s t m k).add
        (Entropy.isSupportedOn_one (interval L 0 k)ᶜ)).add
        (Entropy.isSupportedOn_one (interval L 0 k)ᶜ)
      simpa only [cutRank, W, hl, zero_add] using hr.operatorSchmidtRank_cutOperator_le_one
        (Or.inr disjoint_compl_left)
    · have hr : rightExterior h s t m k = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        obtain ⟨hi, hik⟩ := Finset.mem_filter.mp hi
        obtain ⟨him, hn⟩ := Finset.mem_filter.mp hi
        rw [show s ∪ t = Finset.Ico a b from union_parityBonds a b] at hn
        simp only [Finset.mem_Ico, Finset.mem_range] at hn him
        omega
      have hl := ((leftExterior_supported hh s t m k).add
        (Entropy.isSupportedOn_one (interval L 0 k))).add
        (Entropy.isSupportedOn_one (interval L 0 k))
      simpa only [cutRank, W, hr, add_zero] using hl.operatorSchmidtRank_cutOperator_le_one
        (Or.inl (Finset.Subset.refl _))
  have hdecomp : regionalReplacementMatrix h s t m =
      W - regionalProjectionMatrix h s m - regionalProjectionMatrix h t m := by
    rw [regionalReplacementMatrix, exterior_split h s t m k,
      crossingExterior_eq_zero h (union_parityBonds a b) hin]
    dsimp [W]
    abel
  rw [hdecomp]
  have hsub := cutRank_sub_le W (regionalProjectionMatrix h s m) k
  have hsub' := cutRank_sub_le (W - regionalProjectionMatrix h s m)
    (regionalProjectionMatrix h t m) k
  have hp := rank_parity_products_le hq hh a b m k
  change cutRank (regionalProjectionMatrix h s m) k +
    cutRank (regionalProjectionMatrix h t m) k ≤ q ^ 2 + 1 at hp
  omega

/-- A prefix or suffix region retains the printed `q²+2` all-cut bound.
Here `m` is the number of bonds, so a suffix is expressed by `m ≤ b`.
ALVV, Theorem 5.14(2), on the stated boundary-region scope. -/
private theorem rank_regionalReplacementMatrix_nat_le_sq_add_two_of_boundary
    {h : ℕ → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ} (hq : 1 ≤ q)
    (hh : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i (i + 2))) (a b m k : ℕ) (hboundary : a = 0 ∨ m ≤ b) :
    operatorSchmidtRank (Entropy.cutOperator (interval L 0 k)
      (regionalReplacementMatrix h (evenBonds a b) (oddBonds a b) m)) ≤ q ^ 2 + 2 := by
  by_cases hin : a < k ∧ k ≤ b
  · exact rank_boundary_inside_le hq hh a b m k hin hboundary
  · exact rank_outside_le hq hh a b m k (by omega)

/-- Extend the finite list of chain bonds by zero. This makes support assumptions
refer only to the original terms, including when the chain has no bonds. -/
noncomputable def bondTermExtension {m : ℕ}
    (h : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (i : ℕ) :
    Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := if hi : i < m then h ⟨i, hi⟩ else 0

/-- Extending by zero preserves the nearest-neighbor supports. -/
theorem bondTermExtension_supported {m : ℕ}
    {h : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
    (hh : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i (i + 2))) (i : ℕ) :
    Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (bondTermExtension h i)
      (interval L i (i + 2)) := by
  classical
  unfold bondTermExtension
  split
  · exact hh _
  · exact ⟨fun _ _ _ ↦ rfl, fun _ _ _ _ _ _ _ _ ↦ rfl⟩

/-- The corrected all-cut bound `q²+3` for a finite family of nearest-neighbor
terms. No hypothesis is imposed on nonexistent bonds or on a supplied decomposition.
ALVV, Theorem 5.14(2), corrected for interior intervals. -/
theorem rank_regionalReplacementMatrix_le_sq_add_three {m : ℕ}
    (h : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (hq : 1 ≤ q)
    (hh : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i (i + 2))) (a b k : ℕ) :
    operatorSchmidtRank (Entropy.cutOperator (interval L 0 k)
      (regionalReplacementMatrix (bondTermExtension h) (evenBonds a b) (oddBonds a b) m)) ≤
      q ^ 2 + 3 :=
  rank_regionalReplacementMatrix_nat_le_sq_add_three hq (bondTermExtension_supported hh)
    a b m k

/-- The source bound `q²+2` holds for every cut of the prefix/suffix replacement.
ALVV, Theorem 5.14(2), with the boundary-region scope stated explicitly. -/
theorem rank_regionalReplacementMatrix_le_sq_add_two_of_boundary {m : ℕ}
    (h : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (hq : 1 ≤ q)
    (hh : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i (i + 2))) (a b k : ℕ) (hboundary : a = 0 ∨ m ≤ b) :
    operatorSchmidtRank (Entropy.cutOperator (interval L 0 k)
      (regionalReplacementMatrix (bondTermExtension h) (evenBonds a b) (oddBonds a b) m)) ≤
      q ^ 2 + 2 :=
  rank_regionalReplacementMatrix_nat_le_sq_add_two_of_boundary hq
    (bondTermExtension_supported hh) a b m k hboundary

end TNLean.MPS.AreaLaw.ALVV
