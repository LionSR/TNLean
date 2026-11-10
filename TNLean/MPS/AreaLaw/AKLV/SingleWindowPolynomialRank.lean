/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.TwoWindowPolynomialRank
import TNLean.Circuit.SiteEmbedding
import QICLean.Algebra.OperatorSchmidtSubmatrix
import QICLean.Entropy.LocalLift

/-!
# Polynomial rank at one cut

Zero-interaction spectator sites allow the two-window polynomial estimate
to control a single cut. Fixing the spectator configurations cannot increase
operator Schmidt rank. The polynomial combinatorics are those of the existing
two-window theorem; no spectral claim is made on the enlarged chain.
Supporting AKLV, arXiv:1301.1162v1, Lemma 4.2.
The ordered-gap count includes the correction recorded at
https://sirui-lu.com/QICLean/paper-gaps/aklv13_interpolation_and_word_count.pdf.
The explicit bound is proportional to `w + k/(2*w)` in the exponent;
the further optimization over the window width is separate.
-/

open Matrix QuantumCircuit
open TNLean.Lattice
open TNLean.MPS.AreaLaw
open scoped BigOperators

noncomputable section

namespace TNLean.MPS.AreaLaw.AKLV

private local instance configurationDecidableEq {V : Type*} (q : ℕ) :
    DecidableEq (V → Fin q) := Classical.decEq _

/-- The regional split with the finite-set complement and the entropy
cut coordinates have the same operator Schmidt rank. -/
theorem operatorSchmidtRank_sheetSplit_eq_cutOperator
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ} (A : Finset V)
    (K : Matrix (V → Fin q) (V → Fin q) ℂ) :
    operatorSchmidtRank (K.reindex (sheetSplit q A) (sheetSplit q A)) =
      operatorSchmidtRank (Entropy.cutOperator (n := fun _ ↦ q) A K) := by
  exact operatorSchmidtRank_reindex_prodCongr (Entropy.cutOperator A K)
    (Equiv.refl _) (FiniteProduct.complementEquiv (fun _ ↦ Fin q) A)

private theorem one_eq_classical {n : Type*} (d : DecidableEq n) :
    @OfNat.ofNat (Matrix n n ℂ) 1 (@One.toOfNat1 _ (@Matrix.one n ℂ d _ _)) =
      @OfNat.ofNat (Matrix n n ℂ) 1
        (@One.toOfNat1 _ (@Matrix.one n ℂ (Classical.decEq n) _ _)) := by
  exact congrArg (fun e : DecidableEq n ↦
    @OfNat.ofNat (Matrix n n ℂ) 1 (@One.toOfNat1 _ (@Matrix.one n ℂ e _ _)))
    (Subsingleton.elim d (Classical.decEq n))

/-- Restricting spectator sites to fixed configurations recovers the
original cut operator without increasing its operator Schmidt rank. -/
theorem operatorSchmidtRank_le_embedOp
    {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {q : ℕ} (e : V ↪ W) (A : Finset V) (B : Finset W)
    (hAB : ∀ v, e v ∈ B ↔ v ∈ A) (τ : W → Fin q)
    (K : Matrix (V → Fin q) (V → Fin q) ℂ) :
    operatorSchmidtRank (K.reindex (sheetSplit q A) (sheetSplit q A)) ≤
      operatorSchmidtRank ((embedOp e K).reindex (sheetSplit q B) (sheetSplit q B)) := by
  classical
  let eA : A → B := fun i ↦ ⟨e i, (hAB i).mpr i.property⟩
  let eC : ↥Aᶜ → ↥Bᶜ := fun i ↦ ⟨e i, by
    simpa only [Finset.mem_compl, hAB] using i.property⟩
  have heA : Function.Injective eA := fun i j hij ↦
    Subtype.ext (e.injective (congrArg Subtype.val hij))
  have heC : Function.Injective eC := fun i j hij ↦
    Subtype.ext (e.injective (congrArg Subtype.val hij))
  let f : (A → Fin q) → (B → Fin q) := fun x ↦
    Function.extend eA x (fun j ↦ τ j)
  let g : (↥Aᶜ → Fin q) → (↥Bᶜ → Fin q) := fun x ↦
    Function.extend eC x (fun j ↦ τ j)
  have hread (x : A → Fin q) (y : ↥Aᶜ → Fin q) :
      (sheetSplit q B).symm (f x, g y) ∘ e = (sheetSplit q A).symm (x, y) := by
    funext i
    by_cases hi : i ∈ A
    · have hei : e i ∈ B := (hAB i).mpr hi
      simp only [Function.comp_apply, sheetSplit,
        FiniteProduct.splitEquiv_symm_apply_of_mem _ _ _ _ _ hei,
        FiniteProduct.splitEquiv_symm_apply_of_mem _ _ _ _ _ hi]
      exact heA.extend_apply x (fun j ↦ τ j) ⟨i, hi⟩
    · have hei : e i ∉ B := fun h ↦ hi ((hAB i).mp h)
      simp only [Function.comp_apply, sheetSplit,
        FiniteProduct.splitEquiv_symm_apply_of_notMem _ _ _ _ _ hei,
        FiniteProduct.splitEquiv_symm_apply_of_notMem _ _ _ _ _ hi]
      exact heC.extend_apply y (fun j ↦ τ j) ⟨i, Finset.mem_compl.mpr hi⟩
  have hout (x : A → Fin q) (y : ↥Aᶜ → Fin q) (j : W)
      (hj : ∀ i, e i ≠ j) : (sheetSplit q B).symm (f x, g y) j = τ j := by
    by_cases hB : j ∈ B
    · rw [sheetSplit, FiniteProduct.splitEquiv_symm_apply_of_mem _ _ _ _ _ hB]
      exact Function.extend_apply' (f := eA) x (fun j ↦ τ j) ⟨j, hB⟩ (by
        rintro ⟨i, hi⟩
        exact hj i (congrArg Subtype.val hi))
    · rw [sheetSplit, FiniteProduct.splitEquiv_symm_apply_of_notMem _ _ _ _ _ hB]
      exact Function.extend_apply' (f := eC) y (fun j ↦ τ j) ⟨j, Finset.mem_compl.mpr hB⟩ (by
        rintro ⟨i, hi⟩
        exact hj i (congrArg Subtype.val hi))
  have hmatrix : K.reindex (sheetSplit q A) (sheetSplit q A) =
      ((embedOp e K).reindex (sheetSplit q B) (sheetSplit q B)).submatrix
        (Prod.map f g) (Prod.map f g) := by
    ext ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
    simp only [reindex_apply, submatrix_apply, embedOp_apply, Prod.map]
    rw [ite_eq_left (show AgreeOff e ((sheetSplit q B).symm (f x₁, g x₂))
      ((sheetSplit q B).symm (f y₁, g y₂)) from
        fun j hj ↦ (hout x₁ x₂ j hj).trans (hout y₁ y₂ j hj).symm),
      hread, hread]
  rw [hmatrix]
  exact operatorSchmidtRank_submatrix_prod_le _ f f g g

/-- The supported extension is a unital algebra homomorphism. -/
private def embedOpAlgHom {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] {q : ℕ} (e : V ↪ W) :
    Matrix (V → Fin q) (V → Fin q) ℂ →ₐ[ℂ] Matrix (W → Fin q) (W → Fin q) ℂ where
  toFun := embedOp e
  map_one' := by simpa only [one_eq_classical] using (embedOp_one (d := q) e)
  map_mul' X Y := (embedOp_mul e.injective X Y).symm
  map_zero' := embedOp_zero e
  map_add' := embedOp_add e
  commutes' z := by
    simp only [Algebra.algebraMap_eq_smul_one, embedOp_smul]
    congr 1
    simpa only [one_eq_classical] using (embedOp_one (d := q) e)

/-- A polynomial in a single physical window and its two exterior
operators has the rank bound inherited from the two-window estimate.
The auxiliary window consists of zero interactions on spectator sites.
Supporting AKLV, arXiv:1301.1162v1, Lemma 4.2, with the corrected
ordered-gap count retained in the two-window estimate. -/
theorem operatorSchmidtRank_aeval_single_window_le_pow
    {L q w c : ℕ} [instConfig : DecidableEq (Fin L → Fin q)]
    (W : Fin (2 * w) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (PL PR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hW : ∀ r, W r ∈ supportedOperators q
      (interval L (c + r.val) (c + r.val + 2) : Set (Fin L)))
    (hPL : PL ∈ supportedOperators q (interval L 0 (c + 1) : Set (Fin L)))
    (hPR : PR ∈ supportedOperators q (interval L (c + 2 * w) L : Set (Fin L)))
    (hw : 1 ≤ w) (hc : c + 2 * w ≤ L - 1) (τ : Fin q)
    (k : ℕ) (hk : 1 ≤ k) (P : Polynomial ℂ) (hdeg : P.natDegree ≤ k) :
    let A := interval L 0 (c + w + 1)
    operatorSchmidtRank ((Polynomial.aeval ((∑ r, W r) + PL + PR) P).reindex
      (sheetSplit q A) (sheetSplit q A)) ≤ (q * k) ^ (17 * (w + k / (2 * w))) := by
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
  let E := embedOpAlgHom (q := q) e
  let b := N + c
  let F : ((Fin (2 * w) ⊕ Fin (2 * w)) ⊕ Fin 3) →
      Matrix (Fin T → Fin q) (Fin T → Fin q) ℂ :=
    Sum.elim (Sum.elim (fun _ ↦ 0) (fun r ↦ E (W r))) ![0, E PL, E PR]
  have hmove {S : Finset (Fin L)} {R : Finset (Fin T)}
      {X : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
      (hX : X ∈ supportedOperators q (S : Set (Fin L)))
      (hSR : ∀ i ∈ S, e i ∈ R) : E X ∈ supportedOperators q (R : Set (Fin T)) := by
    apply supportedOperators_mono ?_ (embedOp_mem_supportedOperators_image e.injective hX)
    rintro j ⟨i, hi, rfl⟩
    exact hSR i hi
  have hleft : ∀ r, F (Sum.inl (Sum.inl r)) ∈ supportedOperators q
      (interval T r.val (r.val + 2) : Set (Fin T)) := fun _ ↦ Submodule.zero_mem _
  have hright : ∀ r, F (Sum.inl (Sum.inr r)) ∈ supportedOperators q
      (interval T (b + r.val) (b + r.val + 2) : Set (Fin T)) := by
    intro r
    apply hmove (hW r)
    intro i hi
    simp only [mem_interval] at hi ⊢
    change b + r.val ≤ N + i.val ∧ N + i.val < b + r.val + 2
    dsimp [b]
    omega
  have hleftbulk : F (Sum.inr 0) ∈ supportedOperators q
      (interval T 0 1 : Set (Fin T)) := Submodule.zero_mem _
  have hmidbulk : F (Sum.inr 1) ∈ supportedOperators q
      (interval T (2 * w) (b + 1) : Set (Fin T)) := by
    apply hmove hPL
    intro i hi
    simp only [mem_interval] at hi ⊢
    change 2 * w ≤ N + i.val ∧ N + i.val < b + 1
    dsimp [b, N]
    omega
  have hrightbulk : F (Sum.inr 2) ∈ supportedOperators q
      (interval T (b + 2 * w) T : Set (Fin T)) := by
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
  have hrestrict := operatorSchmidtRank_le_embedOp e A B hAB (fun _ ↦ τ)
    (Polynomial.aeval ((∑ r, W r) + PL + PR) P)
  apply hrestrict.trans
  dsimp only at hrank
  rw [hpoly] at hrank
  exact hrank

end TNLean.MPS.AreaLaw.AKLV
