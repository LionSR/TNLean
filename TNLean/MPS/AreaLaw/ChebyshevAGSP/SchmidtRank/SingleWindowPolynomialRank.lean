/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Spectral.TwoWindowPolynomialRank
import QICLean.ManyBody.Sites.PlacedConfiguration
import QICLean.Algebra.OperatorSchmidt.Submatrix
import QICLean.ManyBody.Entropy.SupportedMarginalTails
import QICLean.Entropy.Surprisal.FilterMoment
import QICLean.ManyBody.Sites.RegionState
import QICLean.ManyBody.Sites.Placement

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

open ManyBody (interval mem_interval)

open Matrix QuantumCircuit
open TNLean.Lattice
open TNLean.MPS.AreaLaw
open scoped BigOperators

noncomputable section

namespace TNLean.MPS.AreaLaw.AKLV

private local instance configurationDecidableEq {V : Type*} (q : ℕ) :
    DecidableEq (V → Fin q) := Classical.decEq _

private theorem one_eq_classical {n : Type*} (d : DecidableEq n) :
    @OfNat.ofNat (Matrix n n ℂ) 1 (@One.toOfNat1 _ (@Matrix.one n ℂ d _ _)) =
      @OfNat.ofNat (Matrix n n ℂ) 1
        (@One.toOfNat1 _ (@Matrix.one n ℂ (Classical.decEq n) _ _)) := by
  exact congrArg (fun e : DecidableEq n ↦
    @OfNat.ofNat (Matrix n n ℂ) 1 (@One.toOfNat1 _ (@Matrix.one n ℂ e _ _)))
    (Subsingleton.elim d (Classical.decEq n))

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

/-- The placement along an embedding, as a unital algebra homomorphism for the
classical decidable equality of configurations fixed in this file. -/
private def placeAlongAlgHom {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] {q : ℕ} (e : V ↪ W) :
    Matrix (V → Fin q) (V → Fin q) ℂ →ₐ[ℂ] Matrix (W → Fin q) (W → Fin q) ℂ where
  toFun := ManyBody.placeAlong (X := fun _ ↦ Fin q) e
  map_one' := by
    simpa only [one_eq_classical] using ManyBody.placeAlong_one (X := fun _ ↦ Fin q) e
  map_mul' K K' := ManyBody.placeAlong_mul (X := fun _ ↦ Fin q) e K K'
  map_zero' := ManyBody.placeAlong_zero (X := fun _ ↦ Fin q) e
  map_add' := ManyBody.placeAlong_add (X := fun _ ↦ Fin q) e
  commutes' z := by
    simp only [Algebra.algebraMap_eq_smul_one, ManyBody.placeAlong_smul]
    congr 1
    simpa only [one_eq_classical] using ManyBody.placeAlong_one (X := fun _ ↦ Fin q) e

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
  let E := placeAlongAlgHom (q := q) e
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
