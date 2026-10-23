/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ProductForm.Supported
import TNLean.Lattice.TrotterActiveIndices

/-!
# Product forms with indices only on factor supports

Source: Hastings, arXiv:cond-mat/0508554v3, lines 1057–1077.
-/

open Matrix
open scoped BigOperators

namespace TNLean.Lattice.Locality

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Site-dependent indices before the grouping in Hastings,
arXiv:cond-mat/0508554v3, lines 1069–1077. -/
private structure ActiveExpansion (U : ι → Set ι) (d : ι → ℕ)
    (A : Matrix ((j : ι) → Fin (d j)) ((j : ι) → Fin (d j)) ℂ) (c : ι → ℕ) where
  Index : ι → Type
  [fintype : ∀ j, Fintype (Index j)]
  [nonempty : ∀ j, Nonempty (Index j)]
  siteOp : (j : ι) → Index j → Matrix (Fin (d j)) (Fin (d j)) ℂ
  coeff : ι → ((j : ι) → Index j) → ℂ
  coeff_local : ∀ i, DependsOn (coeff i) (U i)
  eq_sum : A = ∑ α : (j : ι) → Index j, (∏ i, coeff i α) •
    Matrix.of (fun x y ↦ ∏ j, siteOp j (α j) (x j) (y j))
  card_eq : ∀ j, Fintype.card (Index j) = (d j * d j) ^ c j

attribute [instance] ActiveExpansion.fintype ActiveExpansion.nonempty

private noncomputable def ActiveExpansion.one (U : ι → Set ι) (d : ι → ℕ) :
    ActiveExpansion U d 1 (fun _ ↦ 0) := by
  refine { Index := fun _ ↦ Unit
           siteOp := fun _ _ ↦ 1
           coeff := fun _ _ ↦ 1
           coeff_local := fun _ _ _ _ ↦ rfl
           eq_sum := ?_
           card_eq := fun _ ↦ by simp }
  ext x y
  simp only [Matrix.sum_apply, Matrix.smul_apply, Finset.prod_const_one, smul_eq_mul,
    one_mul, Matrix.of_apply, Fintype.sum_unique]
  by_cases hxy : x = y
  · subst y
    simp
  · rw [Matrix.one_apply_ne hxy]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hxy
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact Matrix.one_apply_ne hj

private noncomputable def ActiveExpansion.mul {U : ι → Set ι} {d c e : ι → ℕ}
    {A B : Matrix ((j : ι) → Fin (d j)) ((j : ι) → Fin (d j)) ℂ}
    (P : ActiveExpansion U d A c) (Q : ActiveExpansion U d B e) :
    ActiveExpansion U d (A * B) (fun j ↦ c j + e j) := by
  classical
  refine { Index := fun j ↦ P.Index j × Q.Index j
           siteOp := fun j a ↦ P.siteOp j a.1 * Q.siteOp j a.2
           coeff := fun i α ↦ P.coeff i (fun j ↦ (α j).1) *
             Q.coeff i (fun j ↦ (α j).2)
           coeff_local := ?_
           eq_sum := ?_
           card_eq := ?_ }
  · intro i α β h
    dsimp only
    rw [P.coeff_local i (fun j hj ↦ congrArg Prod.fst (h j hj)),
      Q.coeff_local i (fun j hj ↦ congrArg Prod.snd (h j hj))]
  · refine (congrArg₂ (· * ·) P.eq_sum Q.eq_sum).trans ?_
    rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
    refine Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow _ _ _).symm _ _ fun x ↦ ?_
    dsimp only [Equiv.arrowProdEquivProdArrow]
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, productEntries_mul,
      Finset.prod_mul_distrib]
    rfl
  · intro j
    simp only [Fintype.card_prod, P.card_eq, Q.card_eq, pow_add]

private noncomputable def ActiveExpansion.listProd {U : ι → Set ι} {d : ι → ℕ}
    {A : ι → Matrix ((j : ι) → Fin (d j)) ((j : ι) → Fin (d j)) ℂ}
    (X : ι → Finset ι)
    (P : ∀ i, ActiveExpansion U d (A i) (fun j ↦ if j ∈ X i then 1 else 0))
    (L : List ι) :
    ActiveExpansion U d (L.map A).prod (fun j ↦ L.countP (fun i ↦ j ∈ X i)) := by
  induction L with
  | nil => simpa using ActiveExpansion.one U d
  | cons i L ih =>
    simpa [List.countP_cons, Nat.add_comm] using (P i).mul ih

private noncomputable def ActiveExpansion.pow {U : ι → Set ι} {d c : ι → ℕ}
    {A : Matrix ((j : ι) → Fin (d j)) ((j : ι) → Fin (d j)) ℂ}
    (P : ActiveExpansion U d A c) (n : ℕ) :
    ActiveExpansion U d (A ^ n) (fun j ↦ n * c j) := by
  induction n with
  | zero => simpa using ActiveExpansion.one U d
  | succ n ih => simpa [pow_succ, Nat.succ_mul] using ih.mul P

private noncomputable def ActiveExpansion.ofSupported (U : ι → Set ι) (d : ι → ℕ)
    (X : Finset ι) (i₀ : ι) (hX : ∀ j ∈ X, j ∈ U i₀)
    (z : (j : ι) → Fin (d j))
    {A : Matrix ((j : ι) → Fin (d j)) ((j : ι) → Fin (d j)) ℂ}
    (hA : Entropy.IsSupportedOn A X) :
    ActiveExpansion U d A (fun j ↦ if j ∈ X then 1 else 0) := by
  classical
  let I (j : ι) := (j ∈ X) → Fin (d j) × Fin (d j)
  letI : ∀ j, Nonempty (I j) := fun j ↦ ⟨fun _ ↦ (z j, z j)⟩
  let row (α : (j : ι) → I j) (j : ι) := if h : j ∈ X then (α j h).1 else z j
  let col (α : (j : ι) → I j) (j : ι) := if h : j ∈ X then (α j h).2 else z j
  refine { Index := I
           siteOp := fun j a ↦ if h : j ∈ X then single (a h).1 (a h).2 1 else 1
           coeff := fun i α ↦ if i = i₀ then A (row α) (col α) else 1
           coeff_local := ?_
           eq_sum := ?_
           card_eq := ?_ }
  · intro i α β h
    dsimp only
    by_cases hi : i = i₀
    · subst i
      simp only [↓reduceIte]
      congr 1
      · funext j
        dsimp only [row]
        split_ifs with hj
        · exact congrArg Prod.fst (congrFun (h j (hX j hj)) hj)
        · rfl
      · funext j
        dsimp only [col]
        split_ifs with hj
        · exact congrArg Prod.snd (congrFun (h j (hX j hj)) hj)
        · rfl
    · simp only [ite_eq_right hi]
  · ext u v
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul,
      Finset.prod_ite_eq', Finset.mem_univ, ↓reduceIte]
    by_cases hoff : ∀ j ∉ X, u j = v j
    · rw [Finset.sum_eq_single (fun j (_ : j ∈ X) ↦ (u j, v j))]
      · rw [Finset.prod_eq_one (fun j _ ↦ ?_), mul_one]
        · exact hA.2 u v _ _ (fun j hj ↦ by simp [row, hj])
            (fun j hj ↦ by simp [col, hj]) hoff (fun j hj ↦ by simp [row, col, hj])
        · by_cases hj : j ∈ X
          · simp [hj]
          · simp [hj, Matrix.one_apply, hoff j hj]
      · intro α _ hα
        obtain ⟨j, hj⟩ := Function.ne_iff.mp hα
        obtain ⟨hj, hpair⟩ := Function.ne_iff.mp hj
        refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ j) ?_)
        rw [dite_eq_left hj, single_apply]
        split_ifs with h
        · exact absurd (Prod.ext h.1 h.2) hpair
        · rfl
      · simp
    · push Not at hoff
      obtain ⟨j, hj, huv⟩ := hoff
      rw [hA.1 u v ⟨j, hj, huv⟩]
      symm
      apply Finset.sum_eq_zero
      intro α _
      refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ j) ?_)
      simp [hj, huv]
  · intro j
    by_cases hj : j ∈ X
    · simp only [I, hj, ↓reduceIte, pow_one]
      rw [Fintype.card_congr (Equiv.trueArrowEquiv _)]
      simp
    · simp [I, hj]

private noncomputable def productFormOfEmptyConfigurations (U : ι → Set ι) (d : ι → ℕ)
    [IsEmpty ((j : ι) → Fin (d j))]
    (A : Matrix ((j : ι) → Fin (d j)) ((j : ι) → Fin (d j)) ℂ) (K : ℕ) :
    {P : ProductForm U d A // P.Index = Fin K} :=
  ⟨{ Index := Fin K
     siteOp := fun _ _ ↦ 0
     coeff := fun _ _ ↦ 0
     coeff_local := fun _ _ _ _ ↦ rfl
     eq_sum := Subsingleton.elim _ _ }, rfl⟩

/-- A finite ordered product admits indices counted only where its factors act.
The integer `K` is an auxiliary bound on the number of index values, rather than
an assumed representation. Source: Hastings, arXiv:cond-mat/0508554v3,
lines 1057–1077. No positivity assumption on local dimensions is required. -/
theorem exists_productForm_list_pow_of_isSupportedOn (U : ι → Set ι) (d : ι → ℕ)
    (hU : ∀ i, i ∈ U i) (X : ι → Finset ι) (hX : ∀ i j, j ∈ X i → j ∈ U i)
    (A : ι → Matrix ((j : ι) → Fin (d j)) ((j : ι) → Fin (d j)) ℂ)
    (hA : ∀ i, Entropy.IsSupportedOn (A i) (X i)) (L : List ι) (n K : ℕ)
    (hK : ∀ j, (d j * d j) ^ (n * L.countP (fun i ↦ j ∈ X i)) ≤ K) :
    ∃ P : ProductForm U d ((L.map A).prod ^ n), Fintype.card P.Index = K := by
  classical
  by_cases hcfg : Nonempty ((j : ι) → Fin (d j))
  · let Q := (ActiveExpansion.listProd X
      (fun i ↦ ActiveExpansion.ofSupported U d (X i) i (hX i)
        (Classical.choice hcfg) (hA i)) L).pow n
    let P := productFormOfSiteIndices U d hU Q.Index Q.siteOp Q.coeff Q.coeff_local
      Q.eq_sum K (fun j ↦ (Q.card_eq j).trans_le (hK j))
    refine ⟨P.val, ?_⟩
    simpa using Fintype.card_congr (Equiv.cast P.property)
  · let : IsEmpty ((j : ι) → Fin (d j)) := not_nonempty_iff.mp hcfg
    let P := productFormOfEmptyConfigurations U d ((L.map A).prod ^ n) K
    refine ⟨P.val, ?_⟩
    simpa using Fintype.card_congr (Equiv.cast P.property)

open scoped Classical in
/-- A sweep uses each centre exactly once. The common index bound is derived
from the largest local dimension and the largest number of coefficient
neighbourhoods containing a site. Source: Hastings, arXiv:cond-mat/0508554v3,
lines 1069–1077. -/
theorem exists_productForm_trotter_card_bound (U : ι → Set ι) (d : ι → ℕ)
    (hU : ∀ i, i ∈ U i) (X : ι → Finset ι) (hX : ∀ i j, j ∈ X i → j ∈ U i)
    (A : ι → Matrix ((j : ι) → Fin (d j)) ((j : ι) → Fin (d j)) ℂ)
    (hA : ∀ i, Entropy.IsSupportedOn (A i) (X i))
    (L : List ι) (hL : L.Perm Finset.univ.toList) (n : ℕ) :
    ∃ P : ProductForm U d ((L.map A).prod ^ n),
      Fintype.card P.Index =
        (max 1 (Finset.univ.sup d) * max 1 (Finset.univ.sup d)) ^
          (n * Finset.univ.sup (fun j ↦ (Finset.univ.filter fun i ↦ j ∈ U i).card)) := by
  classical
  apply exists_productForm_list_pow_of_isSupportedOn U d hU X hX A hA L n
  intro j
  have hcount : L.countP (fun i ↦ j ∈ X i) =
      (Finset.univ.filter fun i ↦ j ∈ X i).card := by
    rw [hL.countP_eq]
    simpa using (Finset.nodup_toList (Finset.univ : Finset ι)).card_eq_countP
      (P := fun i ↦ j ∈ X i) |>.symm
  rw [hcount]
  have hd : d j ≤ max 1 (Finset.univ.sup d) :=
    (Finset.le_sup (Finset.mem_univ j)).trans (le_max_right _ _)
  refine (pow_le_pow_left' (Nat.mul_le_mul hd hd) _).trans ?_
  apply pow_le_pow_right'
  · simp
  · apply Nat.mul_le_mul_left
    apply Finset.le_sup_of_le (Finset.mem_univ j)
    apply Finset.card_le_card
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hX i j (Finset.mem_filter.mp hi).2⟩

open scoped Classical in
/-- The finite Trotter product on a metric site set has a product form with at
most `n * S` components per site, padded to a common alphabet of `D * D`
values per component. Here `D` and `S` are chosen from the finite site set;
no index budget or product representation is assumed. Source: Hastings,
arXiv:cond-mat/0508554v3, lines 1051–1077. This is an exact finite-product
statement, not an estimate for the limiting Gibbs operator. -/
theorem exists_productForm_metric_trotter_card_bound [PseudoMetricSpace ι]
    (d : ι → ℕ) {R : ℝ} (hR : 0 ≤ R)
    (H : ι → Matrix ((j : ι) → Fin (d j)) ((j : ι) → Fin (d j)) ℂ)
    (X : ι → Finset ι) (hX : ∀ i j, j ∈ X i → dist i j ≤ R)
    (hH : ∀ i, Entropy.IsSupportedOn (H i) (X i))
    (L : List ι) (hL : L.Perm Finset.univ.toList) (β : ℝ) (n : ℕ) :
    ∃ P : ProductForm (fun i ↦ {j | dist i j ≤ R}) d
        ((L.map fun i ↦ NormedSpace.exp ((-((β : ℂ) / n)) • H i)).prod ^ n),
      Fintype.card P.Index =
        (max 1 (Finset.univ.sup d) * max 1 (Finset.univ.sup d)) ^
          (n * Finset.univ.sup (fun j : ι ↦ (Finset.univ.filter fun i ↦ dist j i ≤ R).card)) := by
  classical
  simpa only [Set.mem_ofPred_eq, dist_comm] using exists_productForm_trotter_card_bound
    (fun i ↦ {j | dist i j ≤ R}) d (fun i ↦ by simpa using hR) X hX
    (fun i ↦ NormedSpace.exp ((-((β : ℂ) / n)) • H i))
    (fun i ↦ isSupportedOn_exp_smul d (X i) (hH i) _) L hL n

end TNLean.Lattice.Locality
