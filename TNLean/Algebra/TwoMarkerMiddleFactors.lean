/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.OperatorBlock
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Prescribed middle factors of two-marker coefficients

Two crossing families and an ordinary middle operator determine a finite
family of ordered products. The exterior partial matrix elements of each
two-marker coefficient lie in the span of these products. A common degree
bound therefore gives the same middle family for every scalar linear
combination of the coefficients through that degree.

The construction retains zero degrees, zero crossing frequencies, empty
crossing families and empty matrix index types. No commutativity assumption
is placed on the matrix factors.

Every scalar linear combination through a fixed degree admits a Kronecker
decomposition with these prescribed middle factors. When the two crossing
families have the same square cardinality, their number has an explicit bound.

## References

Supporting algebra for ALVV, arXiv:1602.08828v2, Proposition 5.7,
lines 1316–1333. The matrix product presentations and computational
assertions of that proposition are separate from the statements here.
-/

open scoped BigOperators Matrix Kronecker
open Matrix

noncomputable section

namespace Matrix

/-- A prescribed finite family spanning every right operator block can be
retained as the right factors. Supporting algebra for ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1316–1333. -/
theorem exists_left_factors_of_operatorBlock_mem_span
    {m n ι : Type*} [Fintype ι]
    (M : Matrix (m × n) (m × n) ℂ) (C : ι → Matrix n n ℂ)
    (hC : ∀ i j, operatorBlock M i j ∈ Submodule.span ℂ (Set.range C)) :
    ∃ A : ι → Matrix m m ℂ, M = ∑ t, A t ⊗ₖ C t := by
  classical
  have hcoeff (ij : m × m) : ∃ c : ι → ℂ,
      ∑ t, c t • C t = operatorBlock M ij.1 ij.2 :=
    (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hC ij.1 ij.2)
  choose c hc using hcoeff
  refine ⟨fun t i j ↦ c (i, j) t, ?_⟩
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [Matrix.sum_apply]
  change M (i, k) (j, l) = ∑ t, c (i, j) t * C t k l
  have hentry := congrFun (congrFun (hc (i, j)) k) l
  simpa only [operatorBlock, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using hentry.symm

/-- A prescribed finite family spanning the exterior partial matrix elements
can be retained as the left factors. No finiteness assumption on either local
configuration type is needed. This is the orientation of the middle factors
in ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1316–1333. -/
theorem exists_right_factors_of_left_blocks_mem_span
    {m n ι : Type*} [Fintype ι]
    (M : Matrix (m × n) (m × n) ℂ) (C : ι → Matrix m m ℂ)
    (hC : ∀ i j : n, (fun k l : m ↦ M (k, i) (l, j)) ∈
      Submodule.span ℂ (Set.range C)) :
    ∃ B : ι → Matrix n n ℂ, M = ∑ t, C t ⊗ₖ B t := by
  classical
  have hcoeff (ij : n × n) : ∃ c : ι → ℂ,
      ∑ t, c t • C t = (fun k l : m ↦ M (k, ij.1) (l, ij.2)) :=
    (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hC ij.1 ij.2)
  choose c hc using hcoeff
  refine ⟨fun t i j ↦ c (i, j) t, ?_⟩
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [Matrix.sum_apply]
  change M (i, k) (j, l) = ∑ t, C t i j * c (k, l) t
  have hentry := congrFun (congrFun (hc (k, l)) i) j
  simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_comm] using hentry.symm

end Matrix

namespace TNLean.MPS.AreaLaw

/-- A decorated crossing word with its ordinary middle run lengths.
The sum constraint retains the degree bound in ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1324–1333. The two crossing frequencies are fixed. -/
abbrev TwoMarkerMiddleIndex (r i j rU rV : ℕ) :=
  {p : (Fin (i + j) → Fin rU ⊕ Fin rV) ×
      (Fin (i + j + 1) → Fin (r + 1)) //
    (Finset.univ.filter (fun h ↦ (p.1 h).isLeft)).card = i ∧
    (Finset.univ.filter (fun h ↦ (p.1 h).isRight)).card = j ∧
    (∑ h, (p.2 h).val) + i + j ≤ r}

/-- The ordered middle factor indexed by its crossing letters and ordinary runs.
ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333.
The ordinary middle operator is supplied explicitly; it has not been
identified with the independently given physical bulk operator. -/
def twoMarkerMiddleFactor {R : Type*} [Monoid R]
    {r i j rU rV : ℕ} (A : R) (U : Fin rU → R) (V : Fin rV → R)
    (p : TwoMarkerMiddleIndex r i j rU rV) : R :=
  (List.ofFn (fun h : Fin (i + j) ↦
    A ^ (p.1.2 h.castSucc).val * Sum.elim U V (p.1.1 h))).prod *
      A ^ (p.1.2 (Fin.last (i + j))).val

/-- Increasing the degree budget retains each middle word.
ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private def twoMarkerMiddleIndex_castSucc {r i j rU rV : ℕ}
    (p : TwoMarkerMiddleIndex r i j rU rV) : TwoMarkerMiddleIndex (r + 1) i j rU rV :=
  ⟨(p.1.1, fun h ↦ (p.1.2 h).castSucc), p.2.1, p.2.2.1,
    p.2.2.2.trans (Nat.le_succ r)⟩

/-- The degree-budget inclusion leaves the actual middle operator unchanged.
ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem twoMarkerMiddleFactor_castSucc {R : Type*} [Monoid R]
    {r i j rU rV : ℕ} (A : R) (U : Fin rU → R) (V : Fin rV → R)
    (p : TwoMarkerMiddleIndex r i j rU rV) :
    twoMarkerMiddleFactor A U V (twoMarkerMiddleIndex_castSucc p) =
      twoMarkerMiddleFactor A U V p := rfl

/-- Appending one ordinary middle letter increases only the final run.
ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private def twoMarkerMiddleIndex_appendOrdinary {r i j rU rV : ℕ}
    (p : TwoMarkerMiddleIndex r i j rU rV) : TwoMarkerMiddleIndex (r + 1) i j rU rV := by
  let e : Fin (i + j + 1) → Fin (r + 1 + 1) :=
    Fin.snoc (fun h : Fin (i + j) ↦ (p.1.2 h.castSucc).castSucc)
    ((p.1.2 (Fin.last (i + j))).succ)
  refine ⟨(p.1.1, e), p.2.1, p.2.2.1, ?_⟩
  have he : (∑ h, (e h).val) = (∑ h, (p.1.2 h).val) + 1 := by
    simp only [e, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
      Fin.val_castSucc, Fin.val_succ, Nat.add_assoc]
  rw [he]
  have hp := p.2.2.2
  omega

/-- Appending the ordinary letter has the expected noncommutative product order.
ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem twoMarkerMiddleFactor_appendOrdinary {R : Type*} [Monoid R]
    {r i j rU rV : ℕ} (A : R) (U : Fin rU → R) (V : Fin rV → R)
    (p : TwoMarkerMiddleIndex r i j rU rV) :
    twoMarkerMiddleFactor A U V (twoMarkerMiddleIndex_appendOrdinary p) =
      twoMarkerMiddleFactor A U V p * A := by
  simp only [twoMarkerMiddleFactor, twoMarkerMiddleIndex_appendOrdinary,
    Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_succ,
    pow_succ, mul_assoc]

/-- Appending a letter adds its indicator to the corresponding predicate count.
Supporting algebra for ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem card_filter_snoc {α : Type*} {n : ℕ}
    (w : Fin n → α) (x : α) (P : α → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun h ↦ P ((Fin.snoc w x : Fin (n + 1) → α) h))).card =
      (Finset.univ.filter (fun h ↦ P (w h))).card + (if P x then 1 else 0) := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_castSucc,
    Fin.snoc_castSucc, Fin.snoc_last]

/-- Transport along an equality of lengths preserves finite predicate counts.
Supporting algebra for ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem card_filter_comp_cast {α : Type*} {m n : ℕ} (h : m = n)
    (w : Fin n → α) (P : α → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun k : Fin m ↦ P (w (Fin.cast h k)))).card =
      (Finset.univ.filter (fun k : Fin n ↦ P (w k))).card := by
  subst m
  rfl

/-- Transport along an equality of lengths preserves the sum of the run lengths.
Supporting algebra for ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem sum_comp_cast {m n : ℕ} (h : m = n) (f : Fin n → ℕ) :
    (∑ k : Fin m, f (Fin.cast h k)) = ∑ k : Fin n, f k := by
  subst m
  rfl

/-- An ordered crossing product with an ordinary power in each intervening run.
Supporting algebra for ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private def middleWordProduct {R : Type*} [Monoid R] {n : ℕ}
    (A : R) (w : Fin n → R) (d : Fin (n + 1) → ℕ) : R :=
  (List.ofFn (fun h : Fin n ↦ A ^ d h.castSucc * w h)).prod * A ^ d (Fin.last n)

/-- An order-preserving transport of tuple coordinates leaves the product unchanged.
Supporting algebra for ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem middleWordProduct_cast {R : Type*} [Monoid R] {m n : ℕ}
    (h : m = n) (A : R) (w : Fin n → R) (d : Fin (n + 1) → ℕ) :
    middleWordProduct A (fun k : Fin m ↦ w (Fin.cast h k))
        (fun k : Fin (m + 1) ↦ d (Fin.cast (congrArg (fun v : ℕ ↦ v + 1) h) k)) =
      middleWordProduct A w d := by
  subst m
  rfl

/-- Appending a crossing after the final ordinary run multiplies the product on the right.
Supporting algebra for ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem middleWordProduct_snoc {R : Type*} [Monoid R] {n : ℕ}
    (A : R) (w : Fin n → R) (d : Fin (n + 1) → ℕ) (x : R) :
    middleWordProduct A (Fin.snoc w x) (Fin.snoc d 0) =
      middleWordProduct A w d * x := by
  simp only [middleWordProduct, Fin.snoc_castSucc, Fin.snoc_last, pow_zero, mul_one]
  rw [List.ofFn_succ', List.prod_concat]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, mul_assoc]

/-- Append a right crossing, preserving the left frequency and increasing the degree by one.
Supporting algebra for ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private def twoMarkerMiddleIndex_appendRight {r i j rU rV : ℕ}
    (p : TwoMarkerMiddleIndex r i j rU rV) (t : Fin rV) :
    TwoMarkerMiddleIndex (r + 1) i (j + 1) rU rV := by
  let e : Fin (i + j + 1 + 1) → Fin (r + 1 + 1) :=
    Fin.snoc (fun h : Fin (i + j + 1) ↦ (p.1.2 h).castSucc) 0
  refine ⟨(Fin.snoc p.1.1 (Sum.inr t), e), ?_, ?_, ?_⟩
  · exact (card_filter_snoc p.1.1 (Sum.inr t) (fun x ↦ x.isLeft)).trans p.2.1
  · exact (card_filter_snoc p.1.1 (Sum.inr t) (fun x ↦ x.isRight)).trans
      (congrArg (fun n : ℕ ↦ n + 1) p.2.2.1)
  · change (∑ h, (e h).val) + i + (j + 1) ≤ r + 1
    have he : (∑ h, (e h).val) = ∑ h, (p.1.2 h).val := by
      simp only [e, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
        Fin.val_castSucc, Fin.val_zero, Nat.add_zero]
    rw [he]
    exact Nat.succ_le_succ p.2.2.2

/-- The right-crossing step multiplies the retained middle factor on the right by its letter.
Supporting algebra for ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem twoMarkerMiddleFactor_appendRight {R : Type*} [Monoid R]
    {r i j rU rV : ℕ} (A : R) (U : Fin rU → R) (V : Fin rV → R)
    (p : TwoMarkerMiddleIndex r i j rU rV) (t : Fin rV) :
    twoMarkerMiddleFactor A U V (twoMarkerMiddleIndex_appendRight p t) =
      twoMarkerMiddleFactor A U V p * V t := by
  let w₀ : Fin (i + j + 1) → Fin rU ⊕ Fin rV := Fin.snoc p.1.1 (Sum.inr t)
  let e₀ : Fin (i + j + 1 + 1) → Fin (r + 1 + 1) :=
    Fin.snoc (fun h : Fin (i + j + 1) ↦ (p.1.2 h).castSucc) 0
  change middleWordProduct A (Sum.elim U V ∘ w₀) (Fin.val ∘ e₀) =
    twoMarkerMiddleFactor A U V p * V t
  dsimp only [w₀, e₀]
  rw [Fin.comp_snoc, Fin.comp_snoc]
  exact middleWordProduct_snoc A (fun h ↦ Sum.elim U V (p.1.1 h))
    (fun h ↦ (p.1.2 h).val) (V t)

/-- Append a left crossing, preserving the right frequency and increasing the degree by one.
Supporting algebra for ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private def twoMarkerMiddleIndex_appendLeft {r i j rU rV : ℕ}
    (p : TwoMarkerMiddleIndex r i j rU rV) (s : Fin rU) :
    TwoMarkerMiddleIndex (r + 1) (i + 1) j rU rV := by
  let hn : i + 1 + j = i + j + 1 := Nat.add_right_comm i 1 j
  let hne := congrArg (fun v : ℕ ↦ v + 1) hn
  let w₀ : Fin (i + j + 1) → Fin rU ⊕ Fin rV := Fin.snoc p.1.1 (Sum.inl s)
  let e₀ : Fin (i + j + 1 + 1) → Fin (r + 1 + 1) :=
    Fin.snoc (fun h : Fin (i + j + 1) ↦ (p.1.2 h).castSucc) 0
  let w : Fin (i + 1 + j) → Fin rU ⊕ Fin rV := fun h ↦ w₀ (Fin.cast hn h)
  let e : Fin (i + 1 + j + 1) → Fin (r + 1 + 1) := fun h ↦ e₀ (Fin.cast hne h)
  refine ⟨(w, e), ?_, ?_, ?_⟩
  · exact (card_filter_comp_cast hn w₀ (fun x ↦ x.isLeft)).trans
      ((card_filter_snoc p.1.1 (Sum.inl s) (fun x ↦ x.isLeft)).trans
        (congrArg (fun n : ℕ ↦ n + 1) p.2.1))
  · exact (card_filter_comp_cast hn w₀ (fun x ↦ x.isRight)).trans
      ((card_filter_snoc p.1.1 (Sum.inl s) (fun x ↦ x.isRight)).trans p.2.2.1)
  · have he : (∑ h, (e h).val) = ∑ h, (p.1.2 h).val := by
      refine (sum_comp_cast hne (fun h ↦ (e₀ h).val)).trans ?_
      simp only [e₀, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
        Fin.val_castSucc, Fin.val_zero, Nat.add_zero]
    change (∑ h, (e h).val) + (i + 1) + j ≤ r + 1
    rw [he]
    have hp := p.2.2.2
    omega

/-- The left-crossing step multiplies the retained middle factor on the right by its letter.
Supporting algebra for ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem twoMarkerMiddleFactor_appendLeft {R : Type*} [Monoid R]
    {r i j rU rV : ℕ} (A : R) (U : Fin rU → R) (V : Fin rV → R)
    (p : TwoMarkerMiddleIndex r i j rU rV) (s : Fin rU) :
    twoMarkerMiddleFactor A U V (twoMarkerMiddleIndex_appendLeft p s) =
      twoMarkerMiddleFactor A U V p * U s := by
  let hn : i + 1 + j = i + j + 1 := Nat.add_right_comm i 1 j
  let hne := congrArg (fun v : ℕ ↦ v + 1) hn
  let w₀ : Fin (i + j + 1) → Fin rU ⊕ Fin rV := Fin.snoc p.1.1 (Sum.inl s)
  let e₀ : Fin (i + j + 1 + 1) → Fin (r + 1 + 1) :=
    Fin.snoc (fun h : Fin (i + j + 1) ↦ (p.1.2 h).castSucc) 0
  change middleWordProduct A
      (fun h : Fin (i + 1 + j) ↦ Sum.elim U V (w₀ (Fin.cast hn h)))
      (fun h : Fin (i + 1 + j + 1) ↦ (e₀ (Fin.cast hne h)).val) =
    twoMarkerMiddleFactor A U V p * U s
  have hc := middleWordProduct_cast hn A (fun h ↦ Sum.elim U V (w₀ h))
    (fun h ↦ (e₀ h).val)
  refine hc.trans ?_
  change middleWordProduct A (Sum.elim U V ∘ w₀) (Fin.val ∘ e₀) = _
  dsimp only [w₀, e₀]
  rw [Fin.comp_snoc, Fin.comp_snoc]
  exact middleWordProduct_snoc A (fun h ↦ Sum.elim U V (p.1.1 h))
    (fun h ↦ (p.1.2 h).val) (U s)

end TNLean.MPS.AreaLaw

namespace Polynomial

/-- The coefficient recurrence for right multiplication by a polynomial of degree one.
Supporting algebra for ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem coeff_mul_linear_succ {R : Type*} [Semiring R]
    (P : Polynomial R) (D T : R) (n : ℕ) :
    (P * (C D + C T * X)).coeff (n + 1) =
      P.coeff (n + 1) * D + P.coeff n * T := by
  rw [mul_add, coeff_add, coeff_mul_C, ← mul_assoc, coeff_mul_X, coeff_mul_C]

end Polynomial

namespace TNLean.MPS.AreaLaw

/-- The ordered coefficient with i occurrences of U and j occurrences of V.
The outer variable marks U; the inner variable marks V.
Supporting algebra for ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
noncomputable def twoMarkerCoefficient {R : Type*} [Semiring R]
    (D U V : R) (r i j : ℕ) : R :=
  let F : Polynomial (Polynomial R) :=
    Polynomial.C (Polynomial.C D + Polynomial.C V * Polynomial.X) +
      Polynomial.C (Polynomial.C U) * Polynomial.X
  ((F ^ r).coeff i).coeff j

/-- The two positive marker frequencies at a successor degree.
Every final letter is multiplied on the right; no operators are commuted.
Supporting algebra for ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem twoMarkerCoefficient_succ_succ_succ {R : Type*} [Semiring R]
    (D U V : R) (r i j : ℕ) :
    twoMarkerCoefficient D U V (r + 1) (i + 1) (j + 1) =
      twoMarkerCoefficient D U V r (i + 1) (j + 1) * D +
        twoMarkerCoefficient D U V r (i + 1) j * V +
        twoMarkerCoefficient D U V r i (j + 1) * U := by
  simp only [twoMarkerCoefficient, pow_succ, Polynomial.coeff_mul_linear_succ,
    Polynomial.coeff_add, Polynomial.coeff_mul_C]

/-- The successor-degree recurrence when both crossing frequencies vanish.
Supporting algebra for ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem twoMarkerCoefficient_succ_zero_zero {R : Type*} [Semiring R]
    (D U V : R) (r : ℕ) :
    twoMarkerCoefficient D U V (r + 1) 0 0 = twoMarkerCoefficient D U V r 0 0 * D := by
  simp only [twoMarkerCoefficient, pow_succ, Polynomial.mul_coeff_zero,
    Polynomial.coeff_add, Polynomial.coeff_C_zero, Polynomial.coeff_X_zero, mul_zero, add_zero]

/-- The successor-degree recurrence when the left frequency vanishes.
Supporting algebra for ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem twoMarkerCoefficient_succ_zero_succ {R : Type*} [Semiring R]
    (D U V : R) (r j : ℕ) :
    twoMarkerCoefficient D U V (r + 1) 0 (j + 1) =
      twoMarkerCoefficient D U V r 0 (j + 1) * D +
        twoMarkerCoefficient D U V r 0 j * V := by
  simp only [twoMarkerCoefficient, pow_succ, Polynomial.mul_coeff_zero,
    Polynomial.coeff_add, Polynomial.coeff_C_zero, Polynomial.coeff_X_zero, mul_zero,
    add_zero, Polynomial.coeff_mul_linear_succ]

/-- The successor-degree recurrence when the right frequency vanishes.
Supporting algebra for ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem twoMarkerCoefficient_succ_succ_zero {R : Type*} [Semiring R]
    (D U V : R) (r i : ℕ) :
    twoMarkerCoefficient D U V (r + 1) (i + 1) 0 =
      twoMarkerCoefficient D U V r (i + 1) 0 * D +
        twoMarkerCoefficient D U V r i 0 * U := by
  simp only [twoMarkerCoefficient, pow_succ, Polynomial.coeff_mul_linear_succ,
    Polynomial.coeff_add, Polynomial.mul_coeff_zero, Polynomial.coeff_C_zero,
    Polynomial.coeff_X_zero, mul_zero, add_zero]

/-- Right multiplication by a product operator retains the prescribed right
factors: if the operator blocks of `M` lie in the span of `C`, and every
`C p * W` belongs to `G`, then the operator blocks of `M * (E ⊗ W)` belong
to `G`. Supporting algebra for ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1324–1333. -/
private theorem operatorBlocks_mul_kronecker_mem
    {m n ι : Type*} [Fintype m] [Fintype n] [Finite ι]
    (M : Matrix (m × n) (m × n) ℂ) (C : ι → Matrix n n ℂ)
    (hC : ∀ a b, Matrix.operatorBlock M a b ∈ Submodule.span ℂ (Set.range C))
    (E : Matrix m m ℂ) (W : Matrix n n ℂ)
    (G : Submodule ℂ (Matrix n n ℂ)) (hCW : ∀ p, C p * W ∈ G) :
    ∀ a b, Matrix.operatorBlock (M * (E ⊗ₖ W)) a b ∈ G := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨L, hL⟩ := Matrix.exists_left_factors_of_operatorBlock_mem_span M C hC
  have hmul : M * (E ⊗ₖ W) = ∑ p, (L p * E) ⊗ₖ (C p * W) := by
    rw [hL, Finset.sum_mul]
    exact Finset.sum_congr rfl fun p _ ↦
      (Matrix.mul_kronecker_mul (L p) E (C p) W).symm
  intro a b
  have hblock : Matrix.operatorBlock (M * (E ⊗ₖ W)) a b =
      ∑ p, (L p * E) a b • (C p * W) := by
    rw [hmul]
    ext x y
    simp only [Matrix.operatorBlock, Matrix.sum_apply, Matrix.kronecker_apply,
      Matrix.smul_apply, smul_eq_mul]
  rw [hblock]
  exact G.sum_mem fun p _ ↦ G.smul_mem _ (hCW p)

open Classical in
/-- The span of the prescribed ordered middle products for fixed degree and frequencies.
Supporting algebra for ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private noncomputable def middleFactorSpan
    {n : Type*} [Fintype n] [DecidableEq n] {rU rV : ℕ}
    (A : Matrix n n ℂ) (UM : Fin rU → Matrix n n ℂ) (VM : Fin rV → Matrix n n ℂ)
    (r i j : ℕ) : Submodule ℂ (Matrix n n ℂ) :=
  Submodule.span ℂ (Set.range (fun p : TwoMarkerMiddleIndex r i j rU rV ↦
    twoMarkerMiddleFactor A UM VM p))

open Classical in
/-- Each prescribed middle product belongs to its specified span.
Supporting algebra for ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem twoMarkerMiddleFactor_mem_middleFactorSpan
    {n : Type*} [Fintype n] [DecidableEq n] {rU rV r i j : ℕ}
    (A : Matrix n n ℂ) (UM : Fin rU → Matrix n n ℂ) (VM : Fin rV → Matrix n n ℂ)
    (p : TwoMarkerMiddleIndex r i j rU rV) :
    twoMarkerMiddleFactor A UM VM p ∈ middleFactorSpan A UM VM r i j :=
  Submodule.subset_span ⟨p, rfl⟩

/-- Taking an exterior partial matrix element commutes with a finite sum.
Supporting algebra for ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
theorem operatorBlock_sum {m n ι : Type*} [Fintype ι]
    (F : ι → Matrix (m × n) (m × n) ℂ) (a b : m) :
    Matrix.operatorBlock (∑ t, F t) a b = ∑ t, Matrix.operatorBlock (F t) a b := by
  ext x y
  simp only [Matrix.operatorBlock, Matrix.sum_apply]

/-- A common linear space containing both families of partial matrix elements
contains the partial matrix elements of their sum.
Supporting algebra for ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem operatorBlocks_add_mem {m n : Type*}
    (M N : Matrix (m × n) (m × n) ℂ) (G : Submodule ℂ (Matrix n n ℂ))
    (hM : ∀ a b, Matrix.operatorBlock M a b ∈ G)
    (hN : ∀ a b, Matrix.operatorBlock N a b ∈ G) :
    ∀ a b, Matrix.operatorBlock (M + N) a b ∈ G :=
  fun a b ↦ G.add_mem (hM a b) (hN a b)

open Classical in
/-- An ordinary exterior or middle letter raises only the degree budget of
an operator-block span. Supporting algebra for ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1324–1333. -/
private theorem operatorBlocks_mul_ordinary_mem_middleFactorSpan
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] {rU rV r i j : ℕ}
    (A : Matrix n n ℂ) (UM : Fin rU → Matrix n n ℂ) (VM : Fin rV → Matrix n n ℂ)
    (M : Matrix (m × n) (m × n) ℂ)
    (hM : ∀ a b, Matrix.operatorBlock M a b ∈ middleFactorSpan A UM VM r i j)
    (E : Matrix m m ℂ) :
    ∀ a b, Matrix.operatorBlock
      (M * (E ⊗ₖ (1 : Matrix n n ℂ) + (1 : Matrix m m ℂ) ⊗ₖ A)) a b ∈
        middleFactorSpan A UM VM (r + 1) i j := by
  classical
  rw [Matrix.mul_add]
  refine operatorBlocks_add_mem _ _ _ ?_ ?_
  · refine operatorBlocks_mul_kronecker_mem M
      (fun p : TwoMarkerMiddleIndex r i j rU rV ↦ twoMarkerMiddleFactor A UM VM p)
      hM E (1 : Matrix n n ℂ) (middleFactorSpan A UM VM (r + 1) i j) ?_
    intro p
    simpa only [twoMarkerMiddleFactor_castSucc, Matrix.mul_one] using
      twoMarkerMiddleFactor_mem_middleFactorSpan A UM VM
        (twoMarkerMiddleIndex_castSucc p)
  · refine operatorBlocks_mul_kronecker_mem M
      (fun p : TwoMarkerMiddleIndex r i j rU rV ↦ twoMarkerMiddleFactor A UM VM p)
      hM (1 : Matrix m m ℂ) A (middleFactorSpan A UM VM (r + 1) i j) ?_
    intro p
    simpa only [twoMarkerMiddleFactor_appendOrdinary] using
      twoMarkerMiddleFactor_mem_middleFactorSpan A UM VM
        (twoMarkerMiddleIndex_appendOrdinary p)

open Classical in
/-- A left crossing raises the degree budget and the left crossing frequency,
while retaining the prescribed middle factors. Supporting algebra for ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem operatorBlocks_mul_left_crossing_mem_middleFactorSpan
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    {rU rV r i j : ℕ}
    (A : Matrix n n ℂ) (UM : Fin rU → Matrix n n ℂ) (VM : Fin rV → Matrix n n ℂ)
    (M : Matrix (m × n) (m × n) ℂ)
    (hM : ∀ a b, Matrix.operatorBlock M a b ∈ middleFactorSpan A UM VM r i j)
    (EU : Fin rU → Matrix m m ℂ) :
    ∀ a b, Matrix.operatorBlock (M * (∑ s, EU s ⊗ₖ UM s)) a b ∈
      middleFactorSpan A UM VM (r + 1) (i + 1) j := by
  classical
  intro a b
  rw [Finset.mul_sum, operatorBlock_sum]
  refine (middleFactorSpan A UM VM (r + 1) (i + 1) j).sum_mem fun s _ ↦ ?_
  apply operatorBlocks_mul_kronecker_mem M
    (fun p : TwoMarkerMiddleIndex r i j rU rV ↦ twoMarkerMiddleFactor A UM VM p)
    hM (EU s) (UM s) (middleFactorSpan A UM VM (r + 1) (i + 1) j) _ a b
  intro p
  simpa only [twoMarkerMiddleFactor_appendLeft] using
    twoMarkerMiddleFactor_mem_middleFactorSpan A UM VM
      (twoMarkerMiddleIndex_appendLeft p s)

open Classical in
/-- A right crossing raises the degree budget and the right crossing frequency,
while retaining the prescribed middle factors. Supporting algebra for ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem operatorBlocks_mul_right_crossing_mem_middleFactorSpan
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    {rU rV r i j : ℕ}
    (A : Matrix n n ℂ) (UM : Fin rU → Matrix n n ℂ) (VM : Fin rV → Matrix n n ℂ)
    (M : Matrix (m × n) (m × n) ℂ)
    (hM : ∀ a b, Matrix.operatorBlock M a b ∈ middleFactorSpan A UM VM r i j)
    (EV : Fin rV → Matrix m m ℂ) :
    ∀ a b, Matrix.operatorBlock (M * (∑ t, EV t ⊗ₖ VM t)) a b ∈
      middleFactorSpan A UM VM (r + 1) i (j + 1) := by
  classical
  intro a b
  rw [Finset.mul_sum, operatorBlock_sum]
  refine (middleFactorSpan A UM VM (r + 1) i (j + 1)).sum_mem fun t _ ↦ ?_
  apply operatorBlocks_mul_kronecker_mem M
    (fun p : TwoMarkerMiddleIndex r i j rU rV ↦ twoMarkerMiddleFactor A UM VM p)
    hM (EV t) (VM t) (middleFactorSpan A UM VM (r + 1) i (j + 1)) _ a b
  intro p
  simpa only [twoMarkerMiddleFactor_appendRight] using
    twoMarkerMiddleFactor_mem_middleFactorSpan A UM VM
      (twoMarkerMiddleIndex_appendRight p t)

/-- An exterior partial matrix element of a product operator is a scalar multiple
of its middle factor.
Supporting algebra for ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
theorem operatorBlock_kronecker_eq_smul {m n : Type*}
    (E : Matrix m m ℂ) (W : Matrix n n ℂ) (a b : m) :
    Matrix.operatorBlock (E ⊗ₖ W) a b = E a b • W := by
  ext x y
  simp only [Matrix.operatorBlock, Matrix.kronecker_apply, Matrix.smul_apply, smul_eq_mul]

open Classical in
/-- At degree zero with zero crossing frequencies, the prescribed family contains
the identity operator.
Supporting algebra for ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem one_mem_middleFactorSpan
    {n : Type*} [Fintype n] [DecidableEq n] {rU rV : ℕ}
    (A : Matrix n n ℂ) (UM : Fin rU → Matrix n n ℂ) (VM : Fin rV → Matrix n n ℂ) :
    (1 : Matrix n n ℂ) ∈ middleFactorSpan A UM VM 0 0 0 := by
  let p : TwoMarkerMiddleIndex 0 0 0 rU rV :=
    ⟨(Fin.elim0, fun _ ↦ 0), by simp, by simp, by simp⟩
  simpa [twoMarkerMiddleFactor, p] using
    twoMarkerMiddleFactor_mem_middleFactorSpan A UM VM p

open Classical in
/-- At degree zero, every partial matrix element belongs to the prescribed span,
including coefficients with positive crossing frequencies.
Supporting algebra for ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem operatorBlock_twoMarkerCoefficient_zero_mem_middleFactorSpan
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] {rU rV : ℕ}
    (A : Matrix n n ℂ) (UM : Fin rU → Matrix n n ℂ) (VM : Fin rV → Matrix n n ℂ)
    (D U V : Matrix (m × n) (m × n) ℂ) :
    ∀ i j a b, Matrix.operatorBlock (twoMarkerCoefficient D U V 0 i j) a b ∈
      middleFactorSpan A UM VM 0 i j := by
  classical
  intro i j a b
  cases i with
  | zero =>
    cases j with
    | zero =>
      have hc : twoMarkerCoefficient D U V 0 0 0 = 1 := by simp [twoMarkerCoefficient]
      rw [hc, ← Matrix.one_kronecker_one, operatorBlock_kronecker_eq_smul]
      exact (middleFactorSpan A UM VM 0 0 0).smul_mem _ (one_mem_middleFactorSpan A UM VM)
    | succ j =>
      have hc : twoMarkerCoefficient D U V 0 0 (j + 1) = 0 := by
        simp [twoMarkerCoefficient, Polynomial.coeff_one]
      rw [hc]
      exact (middleFactorSpan A UM VM 0 0 (j + 1)).zero_mem
  | succ i =>
    have hc : twoMarkerCoefficient D U V 0 (i + 1) j = 0 := by
      simp [twoMarkerCoefficient, Polynomial.coeff_one]
    rw [hc]
    exact (middleFactorSpan A UM VM 0 (i + 1) j).zero_mem

open Classical in
/-- Every exterior partial matrix element of the double-marker coefficient belongs
to the span of the prescribed middle products, for all degrees and frequencies.
Supporting algebra for ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem operatorBlock_twoMarkerCoefficient_mem_middleFactorSpan
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] {rU rV : ℕ}
    (E : Matrix m m ℂ) (A : Matrix n n ℂ)
    (EU : Fin rU → Matrix m m ℂ) (UM : Fin rU → Matrix n n ℂ)
    (EV : Fin rV → Matrix m m ℂ) (VM : Fin rV → Matrix n n ℂ) (r : ℕ) :
    let D := E ⊗ₖ (1 : Matrix n n ℂ) + (1 : Matrix m m ℂ) ⊗ₖ A
    let U := ∑ s, EU s ⊗ₖ UM s
    let V := ∑ t, EV t ⊗ₖ VM t
    ∀ i j a b, Matrix.operatorBlock (twoMarkerCoefficient D U V r i j) a b ∈
      middleFactorSpan A UM VM r i j := by
  classical
  intro D U V
  induction r with
  | zero =>
    exact operatorBlock_twoMarkerCoefficient_zero_mem_middleFactorSpan A UM VM D U V
  | succ r ih =>
    have hord (i j : ℕ) := operatorBlocks_mul_ordinary_mem_middleFactorSpan A UM VM
      (twoMarkerCoefficient D U V r i j) (ih i j) E
    have hleft (i j : ℕ) := operatorBlocks_mul_left_crossing_mem_middleFactorSpan A UM VM
      (twoMarkerCoefficient D U V r i j) (ih i j) EU
    have hright (i j : ℕ) := operatorBlocks_mul_right_crossing_mem_middleFactorSpan A UM VM
      (twoMarkerCoefficient D U V r i j) (ih i j) EV
    intro i j
    cases i with
    | zero =>
      cases j with
      | zero =>
        rw [twoMarkerCoefficient_succ_zero_zero]
        exact hord 0 0
      | succ j =>
        rw [twoMarkerCoefficient_succ_zero_succ]
        exact operatorBlocks_add_mem _ _ _ (hord 0 (j + 1)) (hright 0 j)
    | succ i =>
      cases j with
      | zero =>
        rw [twoMarkerCoefficient_succ_succ_zero]
        exact operatorBlocks_add_mem _ _ _ (hord (i + 1) 0) (hleft i 0)
      | succ j =>
        rw [twoMarkerCoefficient_succ_succ_succ]
        exact operatorBlocks_add_mem _ _ _
          (operatorBlocks_add_mem _ _ _ (hord (i + 1) (j + 1)) (hright (i + 1) j))
          (hleft i (j + 1))

/-- The prescribed middle family is contained in the full finite set of
crossing decorations and bounded run lengths. Supporting count for ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem card_twoMarkerMiddleIndex_le (r i j rU rV : ℕ) :
    Fintype.card (TwoMarkerMiddleIndex r i j rU rV) ≤
      (rU + rV) ^ (i + j) * (r + 1) ^ (i + j + 1) := by
  classical
  calc
    Fintype.card (TwoMarkerMiddleIndex r i j rU rV) ≤
        Fintype.card ((Fin (i + j) → Fin rU ⊕ Fin rV) ×
          (Fin (i + j + 1) → Fin (r + 1))) :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    _ = _ := by simp

/-- A larger degree bound retains the prescribed word, including its product
order. Supporting simultaneous-degree construction for ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private def twoMarkerMiddleIndex_castLE {r k i j rU rV : ℕ} (hrk : r ≤ k)
    (p : TwoMarkerMiddleIndex r i j rU rV) : TwoMarkerMiddleIndex k i j rU rV :=
  ⟨(p.1.1, fun h ↦ (p.1.2 h).castLE (Nat.add_le_add_right hrk 1)),
    p.2.1, p.2.2.1, p.2.2.2.trans hrk⟩

/-- Increasing the degree bound changes neither the chosen middle factors
nor their ordered product. ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1324–1333. -/
private theorem twoMarkerMiddleFactor_castLE {R : Type*} [Monoid R]
    {r k i j rU rV : ℕ} (hrk : r ≤ k)
    (A : R) (U : Fin rU → R) (V : Fin rV → R)
    (p : TwoMarkerMiddleIndex r i j rU rV) :
    twoMarkerMiddleFactor A U V (twoMarkerMiddleIndex_castLE hrk p) =
      twoMarkerMiddleFactor A U V p := rfl

/-- Equal crossing ranks give the explicit local-dimension factor in ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
theorem card_twoMarkerMiddleIndex_square_le (r i j q : ℕ) :
    Fintype.card (TwoMarkerMiddleIndex r i j (q ^ 2) (q ^ 2)) ≤
      2 ^ (i + j) * q ^ (2 * (i + j)) * (r + 1) ^ (i + j + 1) := by
  convert card_twoMarkerMiddleIndex_le r i j (q ^ 2) (q ^ 2) using 1
  rw [show q ^ 2 + q ^ 2 = 2 * q ^ 2 by omega, Nat.mul_pow, ← pow_mul]

/-- All degrees up to a common bound use factors from the same prescribed
family. ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem range_twoMarkerMiddleFactor_subset {R : Type*} [Monoid R]
    {r k i j rU rV : ℕ} (hrk : r ≤ k)
    (A : R) (U : Fin rU → R) (V : Fin rV → R) :
    Set.range (twoMarkerMiddleFactor (r := r) (i := i) (j := j) A U V) ⊆
      Set.range (twoMarkerMiddleFactor (r := k) (i := i) (j := j) A U V) := by
  rintro _ ⟨p, rfl⟩
  exact ⟨twoMarkerMiddleIndex_castLE hrk p, twoMarkerMiddleFactor_castLE hrk A U V p⟩

open Classical in
/-- A common prescribed middle family suffices for all linear combinations
of the coefficients through degree k. The family is fixed before the scalar
weights are supplied. This preserves polynomial-coefficient independence in
ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1316–1333.
MPO bond bounds and computational cost remain separate assertions. -/
theorem exists_sum_twoMarkerCoefficient_decomposition
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] {rU rV : ℕ}
    (E : Matrix m m ℂ) (A : Matrix n n ℂ)
    (EU : Fin rU → Matrix m m ℂ) (UM : Fin rU → Matrix n n ℂ)
    (EV : Fin rV → Matrix m m ℂ) (VM : Fin rV → Matrix n n ℂ)
    (k i j : ℕ) (c : Fin (k + 1) → ℂ) :
    let D := E ⊗ₖ (1 : Matrix n n ℂ) + (1 : Matrix m m ℂ) ⊗ₖ A
    let U := ∑ s, EU s ⊗ₖ UM s
    let V := ∑ t, EV t ⊗ₖ VM t
    ∃ B : TwoMarkerMiddleIndex k i j rU rV → Matrix m m ℂ,
      (∑ r : Fin (k + 1), c r • twoMarkerCoefficient D U V r.val i j) =
        ∑ p, B p ⊗ₖ twoMarkerMiddleFactor A UM VM p := by
  classical
  intro D U V
  apply Matrix.exists_left_factors_of_operatorBlock_mem_span
    (∑ r : Fin (k + 1), c r • twoMarkerCoefficient D U V r.val i j)
    (fun p : TwoMarkerMiddleIndex k i j rU rV ↦ twoMarkerMiddleFactor A UM VM p)
  intro a b
  rw [operatorBlock_sum]
  apply (middleFactorSpan A UM VM k i j).sum_mem
  intro r _
  change c r • Matrix.operatorBlock (twoMarkerCoefficient D U V r.val i j) a b ∈ _
  apply (middleFactorSpan A UM VM k i j).smul_mem
  have hsub : middleFactorSpan A UM VM r.val i j ≤ middleFactorSpan A UM VM k i j :=
    Submodule.span_mono (range_twoMarkerMiddleFactor_subset (by omega) A UM VM)
  exact hsub (operatorBlock_twoMarkerCoefficient_mem_middleFactorSpan
    E A EU UM EV VM r.val i j a b)

end TNLean.MPS.AreaLaw

end
