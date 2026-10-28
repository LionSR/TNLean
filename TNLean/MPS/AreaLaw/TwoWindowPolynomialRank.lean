/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.OperatorSchmidtCut
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Basic
import QICLean.Channel.FiniteProduct
import QICLean.Channel.FiniteProductOperatorSchmidt
import TNLean.Lattice.Sheet.Splitting
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Data.List.OfFn
import Mathlib.Basic.Complex.Basic
import TNLean.MPS.AreaLaw.TwoWindowOperatorForms
import QICLean.Algebra.WeightedFrequencySchmidtRank
import TNLean.Algebra.FrequencyCounts
import TNLean.MPS.AreaLaw.IntervalSymmDiff
import QICLean.Algebra.LowFrequencyWordPartition
import QICLean.Algebra.OperatorSchmidtBounds
import Mathlib.Algebra.Polynomial.AlgebraMap
import QICLean.Algebra.OperatorSchmidt
import TNLean.Algebra.TwoWindowRankBounds
import TNLean.Algebra.TwoWindowPolynomialRecovery

/-!
# Regional rank bounds for polynomials in a two-window family

A finite chain has two windows of `2 * ℓ` nearest-neighbour terms and three
independently supplied bulk operators. The original `4 * ℓ + 3` labels are retained.
For a polynomial `P` of degree at most `k`, the operator Schmidt rank of
`P (∑ α, F α)` at `Jδ = [a + ℓ + δ, b + ℓ + 1)` is at most
`(q * k) ^ (17 * (ℓ + k / (2 * ℓ)))`, for `k ≥ 1` and `ℓ ≥ 1`.
Here `δ` is zero or one, and local dimensions zero and one are included.

The proof uses simultaneous regional factors, weighted full-frequency slices,
changes of cut, and a single pair of frequency selectors fixed before the
operator family and the degrees. Every degree from zero through `k` is included.
The conclusion concerns regional rank; MPO bond dimensions and computational
complexity are additional assertions in the cited source.

**Local fix (word count):** The ordered-gap counts retain the additional `+1`
documented in the QICLean paper-gap note:
https://sirui-lu.com/QICLean/paper-gaps/aklv13_interpolation_and_word_count.pdf.

## References

ALVV, arXiv:1602.08828v2, `eq:H-mid-cut`, lines 810–821, and
Proposition 5.7 (`prop:Cheby-AGSP-eff`), lines 1324–1333.
-/

open TNLean.Lattice.Sheet

noncomputable section

/-- The middle-versus-exterior coordinates agree with the direct regional split,
up to a change of coordinates on the exterior factor.
ALVV, arXiv:1602.08828v2, `eq:H-mid-cut`, lines 810–831. -/
private theorem threeSplit_middle_rotation_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ℕ)
    (T E : Finset ι) (hTE : Disjoint T E) :
    let c :=
      (FiniteProduct.complementUnionEquiv (fun _ : ι ↦ Fin q) E T hTE.symm).trans
        ((Equiv.refl (T → Fin q)).prodCongr
          (FiniteProduct.configurationCongr (fun _ : ι ↦ Fin q)
            (show (E ∪ T)ᶜ = (T ∪ E)ᶜ by rw [Finset.union_comm E T])))
    let a := Equiv.prodAssoc (T → Fin q) (E → Fin q) (↥(T ∪ E)ᶜ → Fin q)
    let e := a.trans
      ((Equiv.prodComm (T → Fin q) ((E → Fin q) × (↥(T ∪ E)ᶜ → Fin q))).trans
        ((Equiv.prodAssoc (E → Fin q) (↥(T ∪ E)ᶜ → Fin q) (T → Fin q)).trans
          (Equiv.prodCongr (Equiv.refl (E → Fin q))
            (Equiv.prodComm (↥(T ∪ E)ᶜ → Fin q) (T → Fin q)))))
    (TNLean.Lattice.Sheet.threeSplit q T E hTE).trans e =
      (TNLean.Lattice.sheetSplit q E).trans ((Equiv.refl (E → Fin q)).prodCongr c) := by
  intro c a e
  apply Equiv.ext
  intro x
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · funext y
      exact (FiniteProduct.configurationCongr_apply (fun _ : ι ↦ Fin q)
        (show (E ∪ T)ᶜ = (T ∪ E)ᶜ by rw [Finset.union_comm E T])
        ((FiniteProduct.complementUnionEquiv (fun _ : ι ↦ Fin q) E T hTE.symm)
          ((TNLean.Lattice.sheetSplit q E) x).2).2 y).symm
open Matrix
open TNLean.Lattice.Sheet

/-- Middle-versus-exterior rank in three-region coordinates equals rank at the middle region.
The exterior change of coordinates is local to the right factor.
ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1331–1333. -/
private theorem middle_threeSplit_rank_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ℕ)
    (T E : Finset ι) (hTE : Disjoint T E)
    (M : Matrix (ι → Fin q) (ι → Fin q) ℂ) :
    let g := threeSplit q T E hTE
    let a := Equiv.prodAssoc (T → Fin q) (E → Fin q) (↥(T ∪ E)ᶜ → Fin q)
    let e := a.trans
      ((Equiv.prodComm (T → Fin q) ((E → Fin q) × (↥(T ∪ E)ᶜ → Fin q))).trans
        ((Equiv.prodAssoc (E → Fin q) (↥(T ∪ E)ᶜ → Fin q) (T → Fin q)).trans
          (Equiv.prodCongr (Equiv.refl (E → Fin q))
            (Equiv.prodComm (↥(T ∪ E)ᶜ → Fin q) (T → Fin q)))))
    operatorSchmidtRank ((M.reindex g g).reindex e e) =
      operatorSchmidtRank (M.reindex (TNLean.Lattice.sheetSplit q E)
        (TNLean.Lattice.sheetSplit q E)) := by
  intro g a e
  let c :=
    (FiniteProduct.complementUnionEquiv (fun _ : ι ↦ Fin q) E T hTE.symm).trans
      ((Equiv.refl (T → Fin q)).prodCongr
        (FiniteProduct.configurationCongr (fun _ : ι ↦ Fin q)
          (show (E ∪ T)ᶜ = (T ∪ E)ᶜ by rw [Finset.union_comm E T])))
  have he : g.trans e = (TNLean.Lattice.sheetSplit q E).trans
      ((Equiv.refl (E → Fin q)).prodCongr c) :=
    threeSplit_middle_rotation_eq q T E hTE
  have hm : (M.reindex g g).reindex e e =
      (M.reindex (TNLean.Lattice.sheetSplit q E) (TNLean.Lattice.sheetSplit q E)).reindex
        ((Equiv.refl (E → Fin q)).prodCongr c)
        ((Equiv.refl (E → Fin q)).prodCongr c) := by
    change M.reindex (g.trans e) (g.trans e) = _
    rw [he]
    rfl
  rw [hm]
  exact Matrix.operatorSchmidtRank_reindex_prodCongr _ (Equiv.refl (E → Fin q)) c
end



open scoped BigOperators

/-- Ordered word sums commute with a change of configuration coordinates.
This transports the original coefficients in ALVV, arXiv:1602.08828v2,
`eq:H-mid-cut`, lines 810–821, and Proposition 5.7, lines 1324–1333. -/
private theorem reindex_sum_word_products
    {I m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (F : I → Matrix m m ℂ) (e : m ≃ n) (r : ℕ) (W : Finset (Fin r → I)) :
    (∑ w ∈ W, (List.ofFn (fun t ↦ F (w t))).prod).reindex e e =
      ∑ w ∈ W, (List.ofFn (fun t ↦ (F (w t)).reindex e e)).prod := by
  change (Matrix.reindexAlgEquiv ℂ ℂ e)
    (∑ w ∈ W, (List.ofFn (fun t ↦ F (w t))).prod) = _
  simp only [map_sum, map_list_prod, List.map_ofFn, Matrix.coe_reindexAlgEquiv,
    Function.comp_def]


open Matrix QuantumCircuit
open scoped BigOperators Kronecker
open TNLean.Lattice.Sheet

noncomputable section
namespace TNLean.MPS.AreaLaw

/-- Identity matrices are independent of the chosen decision of equality.
This is used in the coordinate calculation for ALVV, arXiv:1602.08828v2,
`eq:H-mid-cut`, lines 810–821. -/
private theorem one_eq_classical {n : Type*} (d : DecidableEq n) :
    @OfNat.ofNat (Matrix n n ℂ) 1 (@One.toOfNat1 _ (@Matrix.one n ℂ d _ _)) =
      @OfNat.ofNat (Matrix n n ℂ) 1
        (@One.toOfNat1 _ (@Matrix.one n ℂ (Classical.decEq n) _ _)) := by
  exact congrArg (fun e : DecidableEq n ↦
    @OfNat.ofNat (Matrix n n ℂ) 1 (@One.toOfNat1 _ (@Matrix.one n ℂ e _ _)))
    (Subsingleton.elim d (Classical.decEq n))

/-- Equality of configurations in the coordinate calculation for ALVV,
arXiv:1602.08828v2, `eq:H-mid-cut`, lines 810–821. -/
private local instance configurationDecidableEq {ι : Type*} (q : ℕ) :
    DecidableEq (ι → Fin q) := Classical.decEq _

/-- Equality of the original window and bulk labels in ALVV,
arXiv:1602.08828v2, `eq:H-mid-cut`, lines 810–821. -/
private local instance alphabetDecidableEq (ℓ : ℕ) :
    DecidableEq ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) := Classical.decEq _

open Classical in
/-- A weighted full-frequency slice in the selected three-region coordinates has
one full-frequency cardinality factor and both ordered-gap factors.
ALVV, arXiv:1602.08828v2, `eq:H-mid-cut`, lines 810–821,
and Proposition 5.7, lines 1324–1333. -/
private theorem operatorSchmidtRank_two_window_full_counts_le
    {L q ℓ a b : ℕ}
    (F : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) →
      Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hleft : ∀ r, F (Sum.inl (Sum.inl r)) ∈ supportedOperators q
      (interval L (a + r.val) (a + r.val + 2) : Set (Fin L)))
    (hright : ∀ r, F (Sum.inl (Sum.inr r)) ∈ supportedOperators q
      (interval L (b + r.val) (b + r.val + 2) : Set (Fin L)))
    (hL : F (Sum.inr 0) ∈ supportedOperators q
      (interval L 0 (a + 1) : Set (Fin L)))
    (hM : F (Sum.inr 1) ∈ supportedOperators q
      (interval L (a + 2 * ℓ) (b + 1) : Set (Fin L)))
    (hR : F (Sum.inr 2) ∈ supportedOperators q
      (interval L (b + 2 * ℓ) L : Set (Fin L)))
    (hab : a + 2 * ℓ ≤ b) (hb : b + 2 * ℓ ≤ L - 1)
    (p s : Fin (2 * ℓ)) (r i j : ℕ)
    (weight : (((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) → ℕ) → ℂ) :
    let T := interval L 0 ((a + p.val) + 1)
    let E := interval L ((a + p.val) + 1) ((b + s.val) + 1)
    let hTE : Disjoint T E := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [T, E, mem_interval] at hx hx'
      omega
    let g := threeSplit q T E hTE
    let H := fun α ↦ (F α).submatrix g.symm g.symm
    let u : (Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3 := Sum.inl (Sum.inl p)
    let v : (Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3 := Sum.inl (Sum.inr s)
    let A := T → Fin q
    let B := E → Fin q
    let C := ↥(T ∪ E)ᶜ → Fin q
    let assoc := Equiv.prodAssoc A B C
    let e := assoc.trans ((Equiv.prodComm A (B × C)).trans
      ((Equiv.prodAssoc B C A).trans
        (Equiv.prodCongr (Equiv.refl B) (Equiv.prodComm C A))))
    let S := (Finset.piAntidiag
      (Finset.univ : Finset ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3)) r).filter
      (fun α ↦ α u = i ∧ α v = j)
    let coefficient := fun α ↦
      ∑ w ∈ (Finset.univ : Finset (Fin r → ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3))).filter
          (fun w ↦ (WordMultiplicity.countsFinsupp w : _ → ℕ) = α),
        (List.ofFn (fun t ↦ H (w t))).prod
    operatorSchmidtRank ((∑ α ∈ S, weight α • coefficient α).reindex e e) ≤
      (r + 1) ^ (4 * ℓ) * ((r + i + 1).choose (2 * i + 1) *
        (r + j + 1).choose (2 * j + 1) * (q ^ 2) ^ i * (q ^ 2) ^ j) := by
  classical
  intro T E hTE g H u v A B C assoc e S coefficient
  obtain ⟨HL, HM, HR, U, V, hlocal, hu, hv, hU, hV⟩ :=
    exists_threeSplit_two_window_factors F hleft hright hL hM hR hab hb p s
  have hqic := operatorSchmidtRank_middle_sum_smul_full_counts_le
    H HL HM HR u v (by simp [u, v]) U V (rU := q ^ 2) (rV := q ^ 2)
  simp only [one_eq_classical] at hqic hlocal hu hv
  have hraw := hqic hlocal hu hv hU hV r i j weight
  have hSiff (α : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) → ℕ) :
      α ∈ S ↔ (∑ a, α a) = r ∧ α u = i ∧ α v = j := by
    simp [S, Finset.mem_piAntidiag]
  have hScard : S.card = Nat.card
      {α : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) → ℕ //
        (∑ a, α a) = r ∧ α u = i ∧ α v = j} :=
    (Nat.card_eq_finsetCard S).symm.trans
      (Nat.card_congr (Equiv.subtypeEquivRight hSiff))
  have hI : Fintype.card ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) = 4 * ℓ + 3 := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hS : S.card ≤ (r + 1) ^ (4 * ℓ) := by
    rw [hScard]
    exact Nat.card_fun_sum_eq_and_two_eq_le hI u v (by simp [u, v]) r i j
  exact hraw.trans (Nat.mul_le_mul_right _ hS)

end TNLean.MPS.AreaLaw

namespace TNLean.MPS.AreaLaw

attribute [local instance] configurationDecidableEq alphabetDecidableEq

open Classical in
/-- The weighted full-frequency slice at the selected middle region has frequency
factor `(r + 1) ^ (4 * ℓ)`. All original `4 * ℓ + 3` labels are retained.
ALVV, arXiv:1602.08828v2, `eq:H-mid-cut`, lines 810–821,
and Proposition 5.7, lines 1324–1333. -/
private theorem operatorSchmidtRank_two_window_regional_full_counts_le
    {L q ℓ a b : ℕ}
    (F : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) →
      Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hleft : ∀ r, F (Sum.inl (Sum.inl r)) ∈ supportedOperators q
      (interval L (a + r.val) (a + r.val + 2) : Set (Fin L)))
    (hright : ∀ r, F (Sum.inl (Sum.inr r)) ∈ supportedOperators q
      (interval L (b + r.val) (b + r.val + 2) : Set (Fin L)))
    (hL : F (Sum.inr 0) ∈ supportedOperators q
      (interval L 0 (a + 1) : Set (Fin L)))
    (hM : F (Sum.inr 1) ∈ supportedOperators q
      (interval L (a + 2 * ℓ) (b + 1) : Set (Fin L)))
    (hR : F (Sum.inr 2) ∈ supportedOperators q
      (interval L (b + 2 * ℓ) L : Set (Fin L)))
    (hab : a + 2 * ℓ ≤ b) (hb : b + 2 * ℓ ≤ L - 1)
    (p s : Fin (2 * ℓ)) (r i j : ℕ)
    (weight : (((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) → ℕ) → ℂ) :
    let E := interval L (a + p.val + 1) (b + s.val + 1)
    let u : (Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3 := Sum.inl (Sum.inl p)
    let v : (Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3 := Sum.inl (Sum.inr s)
    let S := (Finset.piAntidiag
      (Finset.univ : Finset ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3)) r).filter
      (fun α ↦ α u = i ∧ α v = j)
    let coefficient := fun α ↦
      ∑ w ∈ (Finset.univ : Finset (Fin r → ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3))).filter
          (fun w ↦ (WordMultiplicity.countsFinsupp w : _ → ℕ) = α),
        (List.ofFn (fun t ↦ F (w t))).prod
    operatorSchmidtRank ((∑ α ∈ S, weight α • coefficient α).reindex
        (TNLean.Lattice.sheetSplit q E) (TNLean.Lattice.sheetSplit q E)) ≤
      (r + 1) ^ (4 * ℓ) * ((r + i + 1).choose (2 * i + 1) *
        (r + j + 1).choose (2 * j + 1) * (q ^ 2) ^ i * (q ^ 2) ^ j) := by
  classical
  intro E u v S coefficient
  let T := interval L 0 (a + p.val + 1)
  have hTE : Disjoint T E := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [T, E, mem_interval] at hx hx'
    omega
  let g := threeSplit q T E hTE
  let H := fun α ↦ (F α).submatrix g.symm g.symm
  let assoc := Equiv.prodAssoc (T → Fin q) (E → Fin q) (↥(T ∪ E)ᶜ → Fin q)
  let e := assoc.trans
    ((Equiv.prodComm (T → Fin q) ((E → Fin q) × (↥(T ∪ E)ᶜ → Fin q))).trans
      ((Equiv.prodAssoc (E → Fin q) (↥(T ∪ E)ᶜ → Fin q) (T → Fin q)).trans
        (Equiv.prodCongr (Equiv.refl (E → Fin q))
          (Equiv.prodComm (↥(T ∪ E)ᶜ → Fin q) (T → Fin q)))))
  let coefficientH := fun α ↦
    ∑ w ∈ (Finset.univ : Finset (Fin r → ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3))).filter
        (fun w ↦ (WordMultiplicity.countsFinsupp w : _ → ℕ) = α),
      (List.ofFn (fun t ↦ H (w t))).prod
  have hcoeff (α) : coefficientH α = (coefficient α).reindex g g :=
    (reindex_sum_word_products F g r _).symm
  have hsum : (∑ α ∈ S, weight α • coefficientH α) =
      (∑ α ∈ S, weight α • coefficient α).reindex g g := by
    simp_rw [hcoeff]
    ext x y
    simp only [Matrix.reindex_apply, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.submatrix_apply]
  have hbase : operatorSchmidtRank
      ((∑ α ∈ S, weight α • coefficientH α).reindex e e) ≤
      (r + 1) ^ (4 * ℓ) * ((r + i + 1).choose (2 * i + 1) *
        (r + j + 1).choose (2 * j + 1) * (q ^ 2) ^ i * (q ^ 2) ^ j) :=
    operatorSchmidtRank_two_window_full_counts_le
      F hleft hright hL hM hR hab hb p s r i j weight
  rw [hsum] at hbase
  have hrank := middle_threeSplit_rank_eq q T E hTE
    (∑ α ∈ S, weight α • coefficient α)
  exact hrank ▸ hbase


open scoped symmDiff

open Classical in
/-- Moving a weighted slice to a prescribed region costs the squared configuration
dimension of the symmetric difference with the selected middle region.
ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1331–1333. -/
private theorem operatorSchmidtRank_two_window_target_full_counts_le
    {L q ℓ a b : ℕ}
    (F : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) →
      Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hleft : ∀ r, F (Sum.inl (Sum.inl r)) ∈ supportedOperators q
      (interval L (a + r.val) (a + r.val + 2) : Set (Fin L)))
    (hright : ∀ r, F (Sum.inl (Sum.inr r)) ∈ supportedOperators q
      (interval L (b + r.val) (b + r.val + 2) : Set (Fin L)))
    (hL : F (Sum.inr 0) ∈ supportedOperators q
      (interval L 0 (a + 1) : Set (Fin L)))
    (hM : F (Sum.inr 1) ∈ supportedOperators q
      (interval L (a + 2 * ℓ) (b + 1) : Set (Fin L)))
    (hR : F (Sum.inr 2) ∈ supportedOperators q
      (interval L (b + 2 * ℓ) L : Set (Fin L)))
    (hab : a + 2 * ℓ ≤ b) (hb : b + 2 * ℓ ≤ L - 1)
    (p s : Fin (2 * ℓ)) (r i j : ℕ)
    (weight : (((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) → ℕ) → ℂ)
    (J : Finset (Fin L)) :
    let E := interval L (a + p.val + 1) (b + s.val + 1)
    let u : (Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3 := Sum.inl (Sum.inl p)
    let v : (Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3 := Sum.inl (Sum.inr s)
    let S := (Finset.piAntidiag
      (Finset.univ : Finset ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3)) r).filter
      (fun α ↦ α u = i ∧ α v = j)
    let coefficient := fun α ↦
      ∑ w ∈ (Finset.univ : Finset (Fin r → ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3))).filter
          (fun w ↦ (WordMultiplicity.countsFinsupp w : _ → ℕ) = α),
        (List.ofFn (fun t ↦ F (w t))).prod
    operatorSchmidtRank ((∑ α ∈ S, weight α • coefficient α).reindex
        (TNLean.Lattice.sheetSplit q J) (TNLean.Lattice.sheetSplit q J)) ≤
      q ^ (2 * (E ∆ J).card) * ((r + 1) ^ (4 * ℓ) *
        ((r + i + 1).choose (2 * i + 1) * (r + j + 1).choose (2 * j + 1) *
          (q ^ 2) ^ i * (q ^ 2) ^ j)) := by
  classical
  intro E u v S coefficient
  have hregional := operatorSchmidtRank_two_window_regional_full_counts_le
    F hleft hright hL hM hR hab hb p s r i j weight
  have hmove := FiniteProduct.operatorSchmidtRank_splitEquiv_le q E J
    (∑ α ∈ S, weight α • coefficient α)
  exact hmove.trans (Nat.mul_le_mul_left _ hregional)


open Classical in
/-- The weighted slice at the source region `Jδ` has the additional factor `q ^ (4 * ℓ)`.
The choice `δ = 0` gives the block of ALVV Proposition 5.7; `δ = 1` gives
its region between the two named cuts. Local dimensions zero and one are included.
ALVV, arXiv:1602.08828v2, `eq:H-mid-cut`, lines 810–821,
and Proposition 5.7, lines 1324–1333. -/
private theorem operatorSchmidtRank_two_window_source_full_counts_le
    {L q ℓ a b : ℕ}
    (F : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) →
      Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hleft : ∀ r, F (Sum.inl (Sum.inl r)) ∈ supportedOperators q
      (interval L (a + r.val) (a + r.val + 2) : Set (Fin L)))
    (hright : ∀ r, F (Sum.inl (Sum.inr r)) ∈ supportedOperators q
      (interval L (b + r.val) (b + r.val + 2) : Set (Fin L)))
    (hL : F (Sum.inr 0) ∈ supportedOperators q
      (interval L 0 (a + 1) : Set (Fin L)))
    (hM : F (Sum.inr 1) ∈ supportedOperators q
      (interval L (a + 2 * ℓ) (b + 1) : Set (Fin L)))
    (hR : F (Sum.inr 2) ∈ supportedOperators q
      (interval L (b + 2 * ℓ) L : Set (Fin L)))
    (hab : a + 2 * ℓ ≤ b) (hb : b + 2 * ℓ ≤ L - 1)
    (p s : Fin (2 * ℓ)) (r i j : ℕ)
    (weight : (((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) → ℕ) → ℂ)
    (δ : Fin 2) :
    let J := interval L (a + ℓ + δ.val) (b + ℓ + 1)
    let u : (Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3 := Sum.inl (Sum.inl p)
    let v : (Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3 := Sum.inl (Sum.inr s)
    let S := (Finset.piAntidiag
      (Finset.univ : Finset ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3)) r).filter
      (fun α ↦ α u = i ∧ α v = j)
    let coefficient := fun α ↦
      ∑ w ∈ (Finset.univ : Finset (Fin r → ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3))).filter
          (fun w ↦ (WordMultiplicity.countsFinsupp w : _ → ℕ) = α),
        (List.ofFn (fun t ↦ F (w t))).prod
    operatorSchmidtRank ((∑ α ∈ S, weight α • coefficient α).reindex
        (TNLean.Lattice.sheetSplit q J) (TNLean.Lattice.sheetSplit q J)) ≤
      (r + 1) ^ (4 * ℓ) * ((r + i + 1).choose (2 * i + 1) *
        (r + j + 1).choose (2 * j + 1) * q ^ (2 * (i + j) + 4 * ℓ)) := by
  classical
  intro J u v S coefficient
  by_cases hq : q = 0
  · subst q
    have hLpos : 0 < L := by
      have := p.isLt
      omega
    let : IsEmpty (Fin L → Fin 0) := ⟨fun f ↦ Fin.elim0 (f ⟨0, hLpos⟩)⟩
    have hM : (∑ α ∈ S, weight α • coefficient α) = 0 := Subsingleton.elim _ _
    have hzrank : operatorSchmidtRank ((∑ α ∈ S, weight α • coefficient α).reindex
        (TNLean.Lattice.sheetSplit 0 J) (TNLean.Lattice.sheetSplit 0 J)) ≤ 0 := by
      apply operatorSchmidtRank_le_of_hasOperatorSchmidtDecomposition
      refine ⟨Fin.elim0, Fin.elim0, ?_⟩
      rw [hM]
      ext x y
      simp [Matrix.reindex_apply]
    exact hzrank.trans (Nat.zero_le _)
  · have hraw := operatorSchmidtRank_two_window_target_full_counts_le
      F hleft hright hL hM hR hab hb p s r i j weight J
    have hgeometry :
        ((interval L (a + p.val + 1) (b + s.val + 1)) ∆ J).card ≤ 2 * ℓ :=
      card_two_window_middle_symmDiff_le (L := L) (a := a) (b := b) p s δ
    have hcost : q ^ (2 * ((interval L (a + p.val + 1) (b + s.val + 1)) ∆ J).card) ≤
        q ^ (4 * ℓ) := Nat.pow_le_pow_right (by omega) (by omega)
    refine (hraw.trans (Nat.mul_le_mul_right _ hcost)).trans_eq ?_
    simp only [pow_add, pow_mul, Nat.mul_add]
    ac_rfl

end TNLean.MPS.AreaLaw
end

/-! ## A common frequency cutoff for all degrees -/

noncomputable section
namespace TNLean.MPS.AreaLaw

attribute [local instance] configurationDecidableEq alphabetDecidableEq

open Classical in
/-- The rank of a power of degree `r ≤ k` is bounded by the two-window frequency sum
with the common cutoff `k / (2 * ℓ)`. The selected regions are transported to `Jδ`
before their ranks are added.
ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem operatorSchmidtRank_two_window_pow_le_sum
    {L q ℓ a b : ℕ}
    (F : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) →
      Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hleft : ∀ r, F (Sum.inl (Sum.inl r)) ∈ supportedOperators q
      (interval L (a + r.val) (a + r.val + 2) : Set (Fin L)))
    (hright : ∀ r, F (Sum.inl (Sum.inr r)) ∈ supportedOperators q
      (interval L (b + r.val) (b + r.val + 2) : Set (Fin L)))
    (hL : F (Sum.inr 0) ∈ supportedOperators q
      (interval L 0 (a + 1) : Set (Fin L)))
    (hM : F (Sum.inr 1) ∈ supportedOperators q
      (interval L (a + 2 * ℓ) (b + 1) : Set (Fin L)))
    (hR : F (Sum.inr 2) ∈ supportedOperators q
      (interval L (b + 2 * ℓ) L : Set (Fin L)))
    (hab : a + 2 * ℓ ≤ b) (hb : b + 2 * ℓ ≤ L - 1)
    (hℓ : 1 ≤ ℓ) (k r : ℕ) (hr : r ≤ k) (δ : Fin 2) :
    let J := interval L (a + ℓ + δ.val) (b + ℓ + 1)
    let bnd := k / (2 * ℓ)
    operatorSchmidtRank (((∑ α, F α) ^ r).reindex
        (TNLean.Lattice.sheetSplit q J) (TNLean.Lattice.sheetSplit q J)) ≤
      (2 * ℓ) ^ 2 * (∑ i ∈ Finset.range (bnd + 1), ∑ j ∈ Finset.range (bnd + 1),
        (r + 1) ^ (4 * ℓ) * ((r + i + 1).choose (2 * i + 1) *
          (r + j + 1).choose (2 * j + 1) * q ^ (2 * (i + j) + 4 * ℓ))) := by
  classical
  intro J bnd
  let eL : Fin (2 * ℓ) ↪ ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) :=
    ⟨fun p ↦ Sum.inl (Sum.inl p), fun _ _ h ↦ Sum.inl.inj (Sum.inl.inj h)⟩
  let eR : Fin (2 * ℓ) ↪ ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) :=
    ⟨fun s ↦ Sum.inl (Sum.inr s), fun _ _ h ↦ Sum.inr.inj (Sum.inl.inj h)⟩
  let Lwin := (Finset.univ : Finset (Fin (2 * ℓ))).map eL
  let Rwin := (Finset.univ : Finset (Fin (2 * ℓ))).map eR
  have hLcard : Lwin.card = 2 * ℓ := by
    simp only [Lwin, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have hRcard : Rwin.card = 2 * ℓ := by
    simp only [Rwin, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  let p0 : Fin (2 * ℓ) := ⟨0, by omega⟩
  have hLn : Lwin.Nonempty :=
    ⟨eL p0, Finset.mem_map.mpr ⟨p0, Finset.mem_univ _, rfl⟩⟩
  have hRn : Rwin.Nonempty :=
    ⟨eR p0, Finset.mem_map.mpr ⟨p0, Finset.mem_univ _, rfl⟩⟩
  obtain ⟨pickL, pickR, _hpick, hpart⟩ :=
    Fintype.exists_two_window_word_coefficient_partition_of_le
      (𝓡 := Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) Lwin Rwin hLn hRn
  let A := Finset.piAntidiag
    (Finset.univ : Finset ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3)) r
  let B := (Lwin.product (Finset.range (bnd + 1))).product
    (Rwin.product (Finset.range (bnd + 1)))
  let left : (((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) → ℕ) → Lwin :=
    fun α ↦ pickL (fun u : Lwin ↦ α u)
  let right : (((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) → ℕ) → Rwin :=
    fun α ↦ pickR (fun v : Rwin ↦ α v)
  let label := fun (α : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) → ℕ) ↦
    (((left α : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3)), α (left α)),
      ((right α : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3)), α (right α)))
  let coefficient := fun α ↦
    ∑ w ∈ (Finset.univ : Finset (Fin r → ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3))).filter
        (fun w ↦ (WordMultiplicity.countsFinsupp w : _ → ℕ) = α),
      (List.ofFn (fun t ↦ F (w t))).prod
  let C := fun i j ↦ (r + 1) ^ (4 * ℓ) *
    ((r + i + 1).choose (2 * i + 1) * (r + j + 1).choose (2 * j + 1) *
      q ^ (2 * (i + j) + 4 * ℓ))
  have hpartition : (∑ α, F α) ^ r =
      ∑ t ∈ B, ∑ α ∈ A with label α = t, coefficient α := by
    simpa only [hLcard, hRcard] using hpart F k r hr
  have hbin : ∀ t ∈ B, operatorSchmidtRank
      ((∑ α ∈ A with label α = t, coefficient α).reindex
        (TNLean.Lattice.sheetSplit q J) (TNLean.Lattice.sheetSplit q J)) ≤ C t.1.2 t.2.2 := by
    rintro ⟨⟨u, i⟩, ⟨v, j⟩⟩ ht
    have hu := (Finset.mem_product.mp (Finset.mem_product.mp ht).1).1
    have hv := (Finset.mem_product.mp (Finset.mem_product.mp ht).2).1
    obtain ⟨p, _hp, hup⟩ := Finset.mem_map.mp hu
    obtain ⟨s, _hs, hvs⟩ := Finset.mem_map.mp hv
    change eL p = u at hup
    change eR s = v at hvs
    subst u
    subst v
    have hw := frequency_bin_eq_weighted_slice A
      (fun α ↦ (left α : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3)))
      (fun α ↦ (right α : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3)))
      (eL p) (eR s) i j coefficient
    rw [hw]
    exact operatorSchmidtRank_two_window_source_full_counts_le
      F hleft hright hL hM hR hab hb p s r i j
      (fun α ↦ if (left α : _) = eL p ∧ (right α : _) = eR s then 1 else 0) δ
  have hbinsum (C : ℕ → ℕ → ℕ) :
      (∑ t ∈ B, C t.1.2 t.2.2) =
        (2 * ℓ) ^ 2 * ∑ i ∈ Finset.range (bnd + 1),
          ∑ j ∈ Finset.range (bnd + 1), C i j := by
    simp only [B, Finset.product_eq_sprod, Finset.sum_product, Finset.sum_const, Nat.nsmul_eq_mul,
      ← Finset.mul_sum, hLcard, hRcard, pow_two, mul_assoc]
  have hcut : ((∑ α, F α) ^ r).reindex
      (TNLean.Lattice.sheetSplit q J) (TNLean.Lattice.sheetSplit q J) =
      ∑ t ∈ B, (∑ α ∈ A with label α = t, coefficient α).reindex
        (TNLean.Lattice.sheetSplit q J) (TNLean.Lattice.sheetSplit q J) := by
    rw [hpartition]
    ext x y
    simp only [Matrix.reindex_apply, Matrix.sum_apply, Matrix.submatrix_apply]
  rw [hcut]
  exact (operatorSchmidtRank_sum_le B _).trans
    ((Finset.sum_le_sum hbin).trans_eq (hbinsum C))

end TNLean.MPS.AreaLaw
end


open scoped BigOperators

namespace Matrix

/-- Summing the operator Schmidt ranks of every power through a polynomial degree bound.
Supporting algebra for ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem operatorSchmidtRank_aeval_le_sum
    {l n : Type*} [Fintype l] [Fintype n] [DecidableEq l] [DecidableEq n]
    (M : Matrix (l × n) (l × n) ℂ) (P : Polynomial ℂ) (k : ℕ)
    (hdeg : P.natDegree ≤ k) :
    operatorSchmidtRank (Polynomial.aeval M P) ≤
      ∑ r ∈ Finset.range (k + 1), operatorSchmidtRank (M ^ r) := by
  rw [Polynomial.aeval_eq_sum_range' (Nat.lt_succ_of_le hdeg) M]
  exact (operatorSchmidtRank_sum_le _ _).trans
    (Finset.sum_le_sum fun r _ ↦ operatorSchmidtRank_smul_le (P.coeff r) (M ^ r))

end Matrix


/-- A one-dimensional left configuration space gives operator Schmidt rank at most one.
This supplies the local-dimension-one case of the regional estimate in ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem operatorSchmidtRank_le_one_of_unique_left
    {m n : Type*} [Fintype m] [Unique m] [Finite n]
    (M : Matrix (m × n) (m × n) ℂ) : Matrix.operatorSchmidtRank M ≤ 1 := by
  simpa only [Fintype.card_fin] using
    Matrix.operatorSchmidtRank_le_card_of_blocks_mem_span M
      (fun _ : Fin 1 ↦ Matrix.operatorBlock M default default)
      (by
        intro x y
        apply Submodule.subset_span
        refine ⟨0, ?_⟩
        exact congrArg₂ (Matrix.operatorBlock M)
          (Subsingleton.elim _ _) (Subsingleton.elim _ _))

noncomputable section
namespace TNLean.MPS.AreaLaw

attribute [local instance] configurationDecidableEq alphabetDecidableEq

open Classical in
/-- Every degree from zero through `k` contributes to the regional rank estimate
for a polynomial of degree at most `k`. The frequency cutoff is the same for all degrees.
ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem operatorSchmidtRank_two_window_aeval_le_sum
    {L q ℓ a b : ℕ}
    (F : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) →
      Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hleft : ∀ r, F (Sum.inl (Sum.inl r)) ∈ supportedOperators q
      (interval L (a + r.val) (a + r.val + 2) : Set (Fin L)))
    (hright : ∀ r, F (Sum.inl (Sum.inr r)) ∈ supportedOperators q
      (interval L (b + r.val) (b + r.val + 2) : Set (Fin L)))
    (hL : F (Sum.inr 0) ∈ supportedOperators q
      (interval L 0 (a + 1) : Set (Fin L)))
    (hM : F (Sum.inr 1) ∈ supportedOperators q
      (interval L (a + 2 * ℓ) (b + 1) : Set (Fin L)))
    (hR : F (Sum.inr 2) ∈ supportedOperators q
      (interval L (b + 2 * ℓ) L : Set (Fin L)))
    (hab : a + 2 * ℓ ≤ b) (hb : b + 2 * ℓ ≤ L - 1)
    (hℓ : 1 ≤ ℓ) (k : ℕ) (P : Polynomial ℂ) (hdeg : P.natDegree ≤ k) (δ : Fin 2) :
    let J := interval L (a + ℓ + δ.val) (b + ℓ + 1)
    let bnd := k / (2 * ℓ)
    operatorSchmidtRank ((Polynomial.aeval (∑ α, F α) P).reindex
        (TNLean.Lattice.sheetSplit q J) (TNLean.Lattice.sheetSplit q J)) ≤
      (2 * ℓ) ^ 2 * (∑ r ∈ Finset.range (k + 1),
        ∑ i ∈ Finset.range (bnd + 1), ∑ j ∈ Finset.range (bnd + 1),
          (r + 1) ^ (4 * ℓ) * ((r + i + 1).choose (2 * i + 1) *
            (r + j + 1).choose (2 * j + 1) * q ^ (2 * (i + j) + 4 * ℓ))) := by
  classical
  intro J bnd
  let g := TNLean.Lattice.sheetSplit q J
  let M := ∑ α, F α
  have htransport : (Polynomial.aeval M P).reindex g g =
      Polynomial.aeval (M.reindex g g) P := by
    simpa only [Matrix.coe_reindexAlgEquiv] using
      (Polynomial.aeval_algHom_apply (Matrix.reindexAlgEquiv ℂ ℂ g) M P).symm
  rw [htransport]
  have hdegree := Matrix.operatorSchmidtRank_aeval_le_sum (M.reindex g g) P k hdeg
  have hpowers : ∀ r ∈ Finset.range (k + 1), operatorSchmidtRank ((M.reindex g g) ^ r) ≤
      (2 * ℓ) ^ 2 * (∑ i ∈ Finset.range (bnd + 1), ∑ j ∈ Finset.range (bnd + 1),
        (r + 1) ^ (4 * ℓ) * ((r + i + 1).choose (2 * i + 1) *
          (r + j + 1).choose (2 * j + 1) * q ^ (2 * (i + j) + 4 * ℓ))) := by
    intro r hr
    have hpowmap : (M.reindex g g) ^ r = (M ^ r).reindex g g := by
      simpa only [Matrix.coe_reindexAlgEquiv] using
        (map_pow (Matrix.reindexAlgEquiv ℂ ℂ g) M r).symm
    rw [hpowmap]
    exact operatorSchmidtRank_two_window_pow_le_sum F hleft hright hL hM hR hab hb
      hℓ k r (Nat.le_of_lt_succ (Finset.mem_range.mp hr)) δ
  have hsum := hdegree.trans (Finset.sum_le_sum hpowers)
  simpa only [← Finset.mul_sum] using hsum


open Classical in
/-- An explicit regional operator Schmidt rank bound for a polynomial in a two-window family.
The three bulk operators have the independent supports in ALVV,
arXiv:1602.08828v2, `eq:H-mid-cut`, lines 810–821. The rank estimate supports
Proposition 5.7 (`prop:Cheby-AGSP-eff`), lines 1324–1333.

The region is `Jδ = [a + ℓ + δ, b + ℓ + 1)`. The choice `δ = 0` gives the
literal block in Proposition 5.7; `δ = 1` gives the region between its two named cuts.
Local dimensions zero and one are included. This statement is a regional rank estimate;
the MPO bond-dimension and computation-time assertions of Proposition 5.7 are separate. -/
theorem operatorSchmidtRank_aeval_two_window_le_pow
    {L q ℓ a b : ℕ}
    (F : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) →
      Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hleft : ∀ r, F (Sum.inl (Sum.inl r)) ∈ supportedOperators q
      (interval L (a + r.val) (a + r.val + 2) : Set (Fin L)))
    (hright : ∀ r, F (Sum.inl (Sum.inr r)) ∈ supportedOperators q
      (interval L (b + r.val) (b + r.val + 2) : Set (Fin L)))
    (hL : F (Sum.inr 0) ∈ supportedOperators q
      (interval L 0 (a + 1) : Set (Fin L)))
    (hM : F (Sum.inr 1) ∈ supportedOperators q
      (interval L (a + 2 * ℓ) (b + 1) : Set (Fin L)))
    (hR : F (Sum.inr 2) ∈ supportedOperators q
      (interval L (b + 2 * ℓ) L : Set (Fin L)))
    (hab : a + 2 * ℓ ≤ b) (hb : b + 2 * ℓ ≤ L - 1)
    (hℓ : 1 ≤ ℓ) (k : ℕ) (hk : 1 ≤ k) (P : Polynomial ℂ) (hdeg : P.natDegree ≤ k) (δ : Fin 2) :
    let J := interval L (a + ℓ + δ.val) (b + ℓ + 1)
    let bnd := k / (2 * ℓ)
    operatorSchmidtRank ((Polynomial.aeval (∑ α, F α) P).reindex
        (TNLean.Lattice.sheetSplit q J) (TNLean.Lattice.sheetSplit q J)) ≤
      (q * k) ^ (17 * (ℓ + bnd)) := by
  classical
  intro J bnd
  by_cases hq0 : q = 0
  · subst q
    have hLpos : 0 < L := by omega
    let : IsEmpty (Fin L → Fin 0) := ⟨fun f ↦ Fin.elim0 (f ⟨0, hLpos⟩)⟩
    have hM : Polynomial.aeval (∑ α, F α) P = 0 := Subsingleton.elim _ _
    have hzrank : operatorSchmidtRank ((Polynomial.aeval (∑ α, F α) P).reindex
        (TNLean.Lattice.sheetSplit 0 J) (TNLean.Lattice.sheetSplit 0 J)) ≤ 0 := by
      apply operatorSchmidtRank_le_of_hasOperatorSchmidtDecomposition
      refine ⟨Fin.elim0, Fin.elim0, ?_⟩
      rw [hM]
      ext x y
      simp [Matrix.reindex_apply]
    exact hzrank.trans (Nat.zero_le _)
  · by_cases hq1 : q = 1
    · subst q
      have hrank : operatorSchmidtRank ((Polynomial.aeval (∑ α, F α) P).reindex
          (TNLean.Lattice.sheetSplit 1 J) (TNLean.Lattice.sheetSplit 1 J)) ≤ 1 :=
        operatorSchmidtRank_le_one_of_unique_left _
      exact hrank.trans (by
        simpa only [one_mul] using (one_le_pow₀ hk : 1 ≤ k ^ (17 * (ℓ + bnd))))
    · have hq2 : 2 ≤ q := by omega
      exact (operatorSchmidtRank_two_window_aeval_le_sum
        F hleft hright hL hM hR hab hb hℓ k P hdeg δ).trans
        ((Nat.two_window_rank_sum_le_factor k q ℓ bnd (by omega) (Nat.div_le_self _ _)).trans
          (Nat.two_window_rank_factor_le_pow k q ℓ bnd hk hq2 hℓ (Nat.div_le_self _ _)))

end TNLean.MPS.AreaLaw
end
