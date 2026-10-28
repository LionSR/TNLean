/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CoreWordCoefficients
import TNLean.MPS.AreaLaw.TraceCoreSlices
import TNLean.MPS.AreaLaw.FixedConfigurationExtension
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Retained matrices and finite families of ordered cores

An affine product with retained matrix coefficients expands into retained
matrix units tensored with scalar-closed stacks. Every degree through the
number of affine steps is included, and each core uses the actual supplied
interior tensors.

Natural interval coordinates keep a single retained complement. The closing
matrix obtained by restriction is the ordered suffix times the supplied cap
times the ordered prefix. This identifies the affine product of the supplied
full-chain trace operator with its retained/interior expression.

The finite family retains its degree and retained matrix entries. Each
naturally inserted summand has the general square open-boundary bond bound
of its scalar-closed stack, including zero virtual dimension and empty
intervals. No source-sharp bond or algorithmic estimate is asserted.

## References

Supporting algebra for ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1324–1333.
-/

open Matrix
open scoped BigOperators Kronecker Matrix

noncomputable section

namespace MPOTensor

open TNLean.MPS.AreaLaw

/-- One scalar retained-matrix entry supplies the closing matrix at a fixed
core count. This matrix is defined before the interior chain is supplied.
Supporting ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private def retainedStackClosingMatrix {m : Type*} [Fintype m] [DecidableEq m] {B : ℕ}
    (R : Fin B × Fin B → Matrix m m ℂ)
    (steps : List (Matrix m m ℂ × ℂ)) (t : ℕ) (i j : m) :
    Matrix (Fin (B ^ t)) (Fin (B ^ t)) ℂ :=
  stackClosingMatrix (fun w : Fin t → Fin B × Fin B ↦
    Matrix.coreWordCoeff R steps (List.ofFn w) i j)

/-- A retained matrix unit tensored with one scalar-closed common stack.
For the later physical construction the retained index set is the finite
collar configuration space. No physical reordering or MPO predicate is
introduced here. Supporting ALVV, arXiv:1602.08828v2, Proposition 5.7,
lines 1324–1333. -/
private noncomputable def retainedStackTerm
    {m : Type*} [Fintype m] [DecidableEq m] {L q B : ℕ}
    (R : Fin B × Fin B → Matrix m m ℂ)
    (steps : List (Matrix m m ℂ × ℂ)) (A : Fin L → MPOTensor q B)
    (t : ℕ) (i j : m) :
    Matrix (m × (Fin L → Fin q)) (m × (Fin L → Fin q)) ℂ :=
  Matrix.single i j (1 : ℂ) ⊗ₖ
    (fun σ τ ↦ Matrix.trace (retainedStackClosingMatrix R steps t i j *
      (List.ofFn (fun v ↦ stackedTensor (A v) t (σ v) (τ v))).prod))

/-- Resolve the retained coefficients on matrix units, obtaining one
scalar-closed common stack for each degree and retained matrix entry.
The degree cutoff is inclusive. Arbitrary affine-step scalars, including
interpolation weights and zero, are retained exactly. Supporting ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. This applies to a
separated middle word with finite retained collars; no exterior Hamiltonian
is asserted to be a retained step, and no source bond or runtime claim is made. -/
private theorem prod_retainedCoreSteps_eq_sum_retainedStackTerm
    {m : Type*} [Fintype m] [DecidableEq m] {L q B : ℕ}
    (R : Fin B × Fin B → Matrix m m ℂ)
    (steps : List (Matrix m m ℂ × ℂ)) (A : Fin L → MPOTensor q B) :
    (steps.map (fun z ↦
      (z.1 ⊗ₖ (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)) +
        ∑ a : Fin B × Fin B, (z.2 • R a) ⊗ₖ interiorMatrixSlice A a.1 a.2)).prod =
      ∑ t ∈ Finset.range (steps.length + 1), ∑ i : m, ∑ j : m,
        retainedStackTerm R steps A t i j := by
  classical
  rw [Matrix.prod_coreStep_eq_sum R (fun a ↦ interiorMatrixSlice A a.1 a.2) steps]
  ext ⟨i, σ⟩ ⟨j, τ⟩
  simp only [Matrix.sum_apply, Matrix.kronecker_apply]
  apply Finset.sum_congr rfl
  intro t _
  rw [sum_word_slices_eq_trace_stackedTensor A t
    (fun w ↦ Matrix.coreWordCoeff R steps (List.ofFn w) i j) σ τ]
  let f : m → m → ℂ := fun a b ↦
    Matrix.trace (retainedStackClosingMatrix R steps t a b *
      (List.ofFn (fun v ↦ stackedTensor (A v) t (σ v) (τ v))).prod)
  have hentry (a b : m) : retainedStackTerm R steps A t a b (i, σ) (j, τ) =
      Matrix.single a b (f a b) i j := by
    change Matrix.single a b (1 : ℂ) i j * f a b = _
    simp only [Matrix.single_apply]
    split_ifs <;> simp
  simp_rw [hentry]
  simpa only [Matrix.sum_apply, Matrix.of_apply, f, retainedStackClosingMatrix] using
    (congrFun (congrFun (Matrix.sum_sum_single f) i) j).symm

/-- The actual scalar-closed core at a retained matrix entry.
Supporting ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
noncomputable def retainedStackCore
    {m : Type*} [Fintype m] [DecidableEq m] {L q B : ℕ}
    (R : Fin B × Fin B → Matrix m m ℂ)
    (steps : List (Matrix m m ℂ × ℂ)) (A : Fin L → MPOTensor q B)
    (t : ℕ) (i j : m) : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
  fun σ τ ↦ Matrix.trace (retainedStackClosingMatrix R steps t i j *
    (List.ofFn (fun v ↦ stackedTensor (A v) t (σ v) (τ v))).prod)

/-- A scalar-closed core with t layers has an open-boundary presentation
of bond bound (B^t)^2. This conversion does not assert ALVV's sharper B^k
bound or its running time. Supporting ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1311–1333. -/
private theorem retainedStackCore_entries_isOpenMPS
    {m : Type*} [Fintype m] [DecidableEq m] {L q B : ℕ}
    (R : Fin B × Fin B → Matrix m m ℂ)
    (steps : List (Matrix m m ℂ × ℂ)) (A : Fin L → MPOTensor q B)
    (t : ℕ) (i j : m) :
    TNLean.MPS.AreaLaw.IsOpenMPS L (q * q) ((B ^ t) ^ 2)
      (fun w ↦ retainedStackCore R steps A t i j
        (fun v ↦ (finProdFinEquiv.symm (w v)).1)
        (fun v ↦ (finProdFinEquiv.symm (w v)).2)) := by
  simpa only [retainedStackCore, Fin.prod_eq_prod_map_finRange, ← List.ofFn_eq_map] using
    TNLean.MPS.AreaLaw.isOpenMPS_trace_closed_chain
      (retainedStackClosingMatrix R steps t i j)
      (fun v z ↦ stackedTensor (A v) t (finProdFinEquiv.symm z).1
        (finProdFinEquiv.symm z).2)

/-- Resolve one ordered affine middle word into exactly
(length+1)*card(m)^2 indexed retained matrix entries and scalar-closed cores.
The layer count is at most the word length. Each actual core has the
open-boundary square bound, including empty chains and zero dimensions.
This is a finite algebraic component supporting ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1324–1333; the physical collar identification,
source B^k bound and algorithmic assertion remain separate obligations. -/
private theorem exists_finite_retained_core_family
    {m : Type*} [Fintype m] [DecidableEq m] {L q B : ℕ}
    (R : Fin B × Fin B → Matrix m m ℂ)
    (steps : List (Matrix m m ℂ × ℂ)) (A : Fin L → MPOTensor q B) :
    let n := (steps.length + 1) * Fintype.card m ^ 2
    ∃ (t : Fin n → Fin (steps.length + 1)) (i j : Fin n → m)
        (W : Fin n → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ),
      (∀ r, W r = retainedStackCore R steps A (t r).val (i r) (j r)) ∧
      (∀ r, TNLean.MPS.AreaLaw.IsOpenMPS L (q * q) ((B ^ (t r).val) ^ 2)
        (fun w ↦ W r (fun v ↦ (finProdFinEquiv.symm (w v)).1)
          (fun v ↦ (finProdFinEquiv.symm (w v)).2))) ∧
      (steps.map (fun z ↦
        (z.1 ⊗ₖ (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)) +
          ∑ a : Fin B × Fin B,
            (z.2 • R a) ⊗ₖ interiorMatrixSlice A a.1 a.2)).prod =
        ∑ r, Matrix.single (i r) (j r) (1 : ℂ) ⊗ₖ W r := by
  classical
  intro n
  let I := Fin (steps.length + 1) × (m × m)
  have hc : Fintype.card I = n := by simp [I, n, pow_two]
  let e : I ≃ Fin n := (Fintype.equivFin I).trans (finCongr hc)
  let t (r : Fin n) := (e.symm r).1
  let i (r : Fin n) := (e.symm r).2.1
  let j (r : Fin n) := (e.symm r).2.2
  let W (r : Fin n) := retainedStackCore R steps A (t r).val (i r) (j r)
  refine ⟨t, i, j, W, fun _ ↦ rfl,
    fun r ↦ retainedStackCore_entries_isOpenMPS R steps A (t r).val (i r) (j r), ?_⟩
  change _ = ∑ r, retainedStackTerm R steps A (e.symm r).1.val
    (e.symm r).2.1 (e.symm r).2.2
  rw [e.symm.sum_comp (fun x : I ↦
    retainedStackTerm R steps A x.1.val x.2.1 x.2.2)]
  rw [prod_retainedCoreSteps_eq_sum_retainedStackTerm]
  simp only [I, Fintype.sum_prod_type]
  exact (Fin.sum_univ_eq_sum_range
    (fun t ↦ ∑ i : m, ∑ j : m, retainedStackTerm R steps A t i j)
    (steps.length + 1)).symm

end MPOTensor

namespace TNLean.MPS.AreaLaw

/-- Natural coordinates on an interval and its single retained complement.
Supporting the physical cut movement in ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1332–1333. The complement contains each site once. -/
def retainedIntervalEquiv {T L : ℕ} {X : Type*}
    (a : ℕ) (ha : a + L ≤ T) :
    (({v : Fin T // ¬(a ≤ v.val ∧ v.val < a + L)} → X) × (Fin L → X)) ≃
      (Fin T → X) where
  toFun z v := if h : a ≤ v.val ∧ v.val < a + L then
    z.2 ⟨v.val - a, by omega⟩ else z.1 ⟨v, h⟩
  invFun f := (fun v ↦ f v.val, fun v ↦ f ⟨a + v.val, by omega⟩)
  left_inv z := by
    apply Prod.ext
    · funext v
      change (if h : a ≤ v.val.val ∧ v.val.val < a + L then
        z.2 ⟨v.val.val - a, by omega⟩ else z.1 ⟨v.val, h⟩) = z.1 v
      simp only [dite_eq_right v.property]
    · funext v
      change (if h : a ≤ a + v.val ∧ a + v.val < a + L then
        z.2 ⟨a + v.val - a, by omega⟩ else
        z.1 ⟨⟨a + v.val, by omega⟩, h⟩) = z.2 v
      rw [dite_eq_left (show a ≤ a + v.val ∧ a + v.val < a + L by omega)]
      apply congrArg z.2
      apply Fin.ext
      simp
  right_inv f := by
    funext v
    change (if h : a ≤ v.val ∧ v.val < a + L then
      f ⟨a + (v.val - a), by omega⟩ else f v) = f v
    split_ifs with h
    · congr 1
      apply Fin.ext
      dsimp
      omega
    · rfl

/-- The prefix in its original site order, using retained coordinates only.
Supporting ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1332–1333. -/
private def retainedIntervalPrefix {T L B : ℕ} {X : Type*}
    (G : Fin T → X → Matrix (Fin B) (Fin B) ℂ)
    (a : ℕ) (ha : a + L ≤ T)
    (η : {v : Fin T // ¬(a ≤ v.val ∧ v.val < a + L)} → X) :=
  (List.ofFn (fun v : Fin a ↦
    G ⟨v.val, by omega⟩ (η ⟨⟨v.val, by omega⟩, by dsimp; omega⟩))).prod

/-- The suffix in its original site order, using the same retained complement.
Supporting ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1332–1333. -/
private def retainedIntervalSuffix {T L B : ℕ} {X : Type*}
    (G : Fin T → X → Matrix (Fin B) (Fin B) ℂ)
    (a : ℕ) (ha : a + L ≤ T)
    (η : {v : Fin T // ¬(a ≤ v.val ∧ v.val < a + L)} → X) :=
  (List.ofFn (fun v : Fin (T - (a + L)) ↦
    G ⟨a + L + v.val, by omega⟩
      (η ⟨⟨a + L + v.val, by omega⟩, by dsimp; omega⟩))).prod

/-- The full ordered contraction splits into the retained prefix, the actual
interval tensors, and the retained suffix. Empty intervals and one-site chains
obey the same identity. Supporting ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1332–1333. -/
private theorem prod_retainedInterval_eq {T L B : ℕ} {X : Type*}
    (G : Fin T → X → Matrix (Fin B) (Fin B) ℂ)
    (a : ℕ) (ha : a + L ≤ T)
    (η : {v : Fin T // ¬(a ≤ v.val ∧ v.val < a + L)} → X)
    (x : Fin L → X) :
    (List.ofFn (fun v ↦ G v (retainedIntervalEquiv a ha (η, x) v))).prod =
      retainedIntervalPrefix G a ha η *
        (List.ofFn (fun v : Fin L ↦ G ⟨a + v.val, by omega⟩ (x v))).prod *
          retainedIntervalSuffix G a ha η := by
  let f := List.ofFn (fun v ↦ G v (retainedIntervalEquiv a ha (η, x) v))
  have hp : f.take a = List.ofFn (fun v : Fin a ↦
      G ⟨v.val, by omega⟩ (η ⟨⟨v.val, by omega⟩, by dsimp; omega⟩)) := by
    apply List.ext_getElem
    · simp only [f, List.length_take, List.length_ofFn]
      omega
    · intro i hi hi'
      have hiA : i < a := by simpa only [List.length_ofFn] using hi'
      simp only [f, List.getElem_take, List.getElem_ofFn]
      simp [retainedIntervalEquiv, show ¬(a ≤ i ∧ i < a + L) by omega]
  have hm : (f.drop a).take L = List.ofFn (fun v : Fin L ↦
      G ⟨a + v.val, by omega⟩ (x v)) := by
    apply List.ext_getElem
    · simp only [f, List.length_take, List.length_drop, List.length_ofFn]
      omega
    · intro i hi hi'
      have hiL : i < L := by simpa only [List.length_ofFn] using hi'
      simp only [f, List.getElem_take, List.getElem_drop, List.getElem_ofFn]
      simp [retainedIntervalEquiv,
        show a ≤ a + i ∧ a + i < a + L by omega]
  have hs : f.drop (a + L) = List.ofFn (fun v : Fin (T - (a + L)) ↦
      G ⟨a + L + v.val, by omega⟩
        (η ⟨⟨a + L + v.val, by omega⟩, by dsimp; omega⟩)) := by
    apply List.ext_getElem
    · simp only [f, List.length_drop, List.length_ofFn]
    · intro i hi hi'
      simp only [f, List.getElem_drop, List.getElem_ofFn]
      simp [retainedIntervalEquiv]
  change f.prod = _
  rw [orderedProduct_partition_interval f a L, hp, hm, hs]
  rfl

/-- The explicit closing matrix is suffix times the original cap times prefix.
It depends only on the single retained configuration, before any interval input.
Supporting ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1332–1333. -/
private theorem trace_retainedInterval_eq {T L B : ℕ} {X : Type*}
    (G : Fin T → X → Matrix (Fin B) (Fin B) ℂ)
    (C : Matrix (Fin B) (Fin B) ℂ) (a : ℕ) (ha : a + L ≤ T)
    (η : {v : Fin T // ¬(a ≤ v.val ∧ v.val < a + L)} → X)
    (x : Fin L → X) :
    Matrix.trace (C *
      (List.ofFn (fun v ↦ G v (retainedIntervalEquiv a ha (η, x) v))).prod) =
      Matrix.trace ((retainedIntervalSuffix G a ha η * C *
        retainedIntervalPrefix G a ha η) *
          (List.ofFn (fun v : Fin L ↦ G ⟨a + v.val, by omega⟩ (x v))).prod) := by
  rw [prod_retainedInterval_eq G a ha η x]
  simpa only [Matrix.mul_assoc] using
    Matrix.trace_mul_cycle C
      (retainedIntervalPrefix G a ha η *
        (List.ofFn (fun v : Fin L ↦ G ⟨a + v.val, by omega⟩ (x v))).prod)
      (retainedIntervalSuffix G a ha η)

end TNLean.MPS.AreaLaw

namespace MPOTensor

open TNLean.MPS.AreaLaw

/-- Expanding the trace exposes the actual interior endpoints, while retaining
the given exterior matrix entries. The closing entry has its two virtual
indices reversed by the trace pairing. Supporting contraction algebra for
ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333; no bond-count
or approximation bound is asserted. -/
private theorem trace_retained_entry_eq_sum_interiorMatrixSlice
    {m : Type*} {L q B : ℕ}
    (F : m → m → Matrix (Fin B) (Fin B) ℂ)
    (A : Fin L → MPOTensor q B) :
    (fun x y : m × (Fin L → Fin q) ↦ Matrix.trace
      (F x.1 y.1 * (List.ofFn (fun v ↦ A v (x.2 v) (y.2 v))).prod)) =
      ∑ ab : Fin B × Fin B,
        (fun i j : m ↦ F i j ab.2 ab.1) ⊗ₖ
          interiorMatrixSlice A ab.1 ab.2 := by
  ext ⟨i, σ⟩ ⟨j, τ⟩
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.sum_apply, Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- The closing matrix obtained from the supplied trace chain and one retained
complement. It contains the actual suffix, original cap and actual prefix, and
has no dependence on the interior physical coordinates.
Supporting ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1332–1333. -/
def actualRetainedIntervalClosing {T L q B : ℕ}
    (A : Fin T → MPOTensor q B) (C : Matrix (Fin B) (Fin B) ℂ)
    (a : ℕ) (ha : a + L ≤ T)
    (η θ : {v : Fin T // ¬(a ≤ v.val ∧ v.val < a + L)} → Fin q) :=
  retainedIntervalSuffix (fun v (z : Fin q × Fin q) ↦ A v z.1 z.2)
      a ha (fun v ↦ (η v, θ v)) * C *
    retainedIntervalPrefix (fun v (z : Fin q × Fin q) ↦ A v z.1 z.2)
      a ha (fun v ↦ (η v, θ v))

/-- In the canonical retained-complement and natural interval coordinates, the
supplied trace operator is the sum of its retained matrices tensored with the
actual ordered interior slices. No endpoint is duplicated for short intervals.
The retained matrices are fixed by the supplied chain, cap and interval, before
any exterior Hamiltonian or interpolation coefficient is supplied.
Supporting ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333;
no assertion about the source's sharp open-boundary bond bound is made. -/
private theorem trace_actual_retainedInterval_eq_sum {T L q B : ℕ}
    (A : Fin T → MPOTensor q B) (C : Matrix (Fin B) (Fin B) ℂ)
    (a : ℕ) (ha : a + L ≤ T) :
    (fun s t :
        ({v : Fin T // ¬(a ≤ v.val ∧ v.val < a + L)} → Fin q) × (Fin L → Fin q) ↦
      Matrix.trace (C * (List.ofFn (fun v ↦
        A v (retainedIntervalEquiv a ha s v)
          (retainedIntervalEquiv a ha t v))).prod)) =
      ∑ ab : Fin B × Fin B,
        (fun η θ ↦ actualRetainedIntervalClosing A C a ha η θ ab.2 ab.1) ⊗ₖ
          interiorMatrixSlice (fun v : Fin L ↦ A ⟨a + v.val, by omega⟩)
            ab.1 ab.2 := by
  rw [← trace_retained_entry_eq_sum_interiorMatrixSlice
    (actualRetainedIntervalClosing A C a ha)
    (fun v : Fin L ↦ A ⟨a + v.val, by omega⟩)]
  ext ⟨η, σ⟩ ⟨θ, τ⟩
  have hpair (v : Fin T) :
      (retainedIntervalEquiv a ha (η, σ) v,
        retainedIntervalEquiv a ha (θ, τ) v) =
      retainedIntervalEquiv a ha (fun v ↦ (η v, θ v), fun v ↦ (σ v, τ v)) v := by
    dsimp only [retainedIntervalEquiv, Equiv.coe_fn_mk]
    split_ifs <;> rfl
  have h := trace_retainedInterval_eq
    (fun v (z : Fin q × Fin q) ↦ A v z.1 z.2)
    C a ha (fun v ↦ (η v, θ v)) (fun v ↦ (σ v, τ v))
  have hsites (v : Fin T) :
      A v (retainedIntervalEquiv a ha (η, σ) v)
        (retainedIntervalEquiv a ha (θ, τ) v) =
      A v (retainedIntervalEquiv a ha
        (fun v ↦ (η v, θ v), fun v ↦ (σ v, τ v)) v).1
        (retainedIntervalEquiv a ha
          (fun v ↦ (η v, θ v), fun v ↦ (σ v, τ v)) v).2 := by
    rw [← hpair v]
  simpa only [actualRetainedIntervalClosing, ← hsites] using h

end MPOTensor

namespace TNLean.MPS.AreaLaw

/-- A retained matrix unit in canonical interval coordinates fixes precisely the
single complement configuration in the ket and bra. Its full-chain coefficient
is the corresponding interior coefficient, or zero. This is the matrix-unit
insertion supporting ALVV, arXiv:1602.08828v2, Proposition 5.7,
lines 1332–1333; it does not reorder the physical chain. -/
private theorem retainedSingle_kronecker_entry {T L q : ℕ}
    (a : ℕ) (ha : a + L ≤ T)
    (η θ : {v : Fin T // ¬(a ≤ v.val ∧ v.val < a + L)} → Fin q)
    (W : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (σ τ : Fin T → Fin q) :
    ((Matrix.single η θ (1 : ℂ)) ⊗ₖ W).submatrix
        (retainedIntervalEquiv a ha).symm (retainedIntervalEquiv a ha).symm σ τ =
      if (fun v : {v : Fin T // ¬(a ≤ v.val ∧ v.val < a + L)} ↦ σ v.val) = η ∧
          (fun v : {v : Fin T // ¬(a ≤ v.val ∧ v.val < a + L)} ↦ τ v.val) = θ then
        W (fun v ↦ σ ⟨a + v.val, by omega⟩)
          (fun v ↦ τ ⟨a + v.val, by omega⟩)
      else 0 := by
  classical
  change Matrix.single η θ (1 : ℂ) (fun v ↦ σ v.val) (fun v ↦ τ v.val) *
    W (fun v ↦ σ ⟨a + v.val, by omega⟩)
      (fun v ↦ τ ⟨a + v.val, by omega⟩) = _
  by_cases hη : (fun v : {v : Fin T // ¬(a ≤ v.val ∧ v.val < a + L)} ↦ σ v.val) = η
  · by_cases hθ : (fun v : {v : Fin T // ¬(a ≤ v.val ∧ v.val < a + L)} ↦ τ v.val) = θ
    · simp [hη, hθ]
    · simp [hη, hθ, Ne.symm hθ]
  · simp [hη, Ne.symm hη]

/-- Insert a retained matrix unit around an actual operator core in the original
physical order. A pair-alphabet open-boundary witness for the core gives the
full-chain bond bound `max 1 D`. The maximum accounts for cuts introduced outside
an empty or one-site core. Supporting ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1332–1333. -/
private theorem isOpenMPS_retainedSingle_kronecker {T L q D : ℕ}
    (a : ℕ) (ha : a + L ≤ T)
    (η θ : {v : Fin T // ¬(a ≤ v.val ∧ v.val < a + L)} → Fin q)
    (W : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hW : IsOpenMPS L (q * q) D (fun w ↦ W
      (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w v)).1)
      (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w v)).2))) :
    IsOpenMPS T (q * q) (max 1 D) (fun w ↦
      ((Matrix.single η θ (1 : ℂ)) ⊗ₖ W).submatrix
        (retainedIntervalEquiv a ha).symm (retainedIntervalEquiv a ha).symm
        (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w v)).1)
        (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w v)).2)) := by
  let ψ : EuclideanSpace ℂ (Fin L → Fin (q * q)) := WithLp.toLp 2 (fun w ↦ W
    (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w v)).1)
    (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w v)).2))
  have hψ : IsOpenMPS L (q * q) D (fun x ↦ ψ x) := hW
  have h := hψ.extend_interval_by_configuration a ha
    (fun v ↦ finProdFinEquiv (η v, θ v))
  convert h using 1
  funext w
  rw [retainedSingle_kronecker_entry]
  have hmatch :
      ((fun v : {v : Fin T // ¬(a ≤ v.val ∧ v.val < a + L)} ↦
          ((finProdFinEquiv (m := q) (n := q)).symm (w v.val)).1) = η ∧
        (fun v : {v : Fin T // ¬(a ≤ v.val ∧ v.val < a + L)} ↦
          ((finProdFinEquiv (m := q) (n := q)).symm (w v.val)).2) = θ) ↔
      (fun v : {v : Fin T // ¬(a ≤ v.val ∧ v.val < a + L)} ↦ w v.val) =
        (fun v ↦ finProdFinEquiv (η v, θ v)) := by
    constructor
    · rintro ⟨hη, hθ⟩
      funext v
      apply (finProdFinEquiv (m := q) (n := q)).symm.injective
      simpa only [Equiv.symm_apply_apply] using
        Prod.ext (congrFun hη v) (congrFun hθ v)
    · intro hw
      constructor
      · funext v
        simpa only [Equiv.symm_apply_apply] using
          congrArg (fun z ↦ ((finProdFinEquiv (m := q) (n := q)).symm z).1)
            (congrFun hw v)
      · funext v
        simpa only [Equiv.symm_apply_apply] using
          congrArg (fun z ↦ ((finProdFinEquiv (m := q) (n := q)).symm z).2)
            (congrFun hw v)
  simp only [hmatch]
  rfl

end TNLean.MPS.AreaLaw

namespace MPOTensor

open TNLean.MPS.AreaLaw

/-- The actual scalar-closed stack, inserted beside a retained matrix unit in
natural interval order, has the same open-boundary square bound as the core.
A zero virtual space gives the zero operator and is treated separately from the
generic insertion bound. Supporting ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1332–1333. This is the general square-bound component. -/
private theorem retainedStackCore_naturalInsertion_isOpenMPS
    {m : Type*} [Fintype m] [DecidableEq m] {T L q B : ℕ}
    (R : Fin B × Fin B → Matrix m m ℂ)
    (steps : List (Matrix m m ℂ × ℂ)) (A : Fin L → MPOTensor q B)
    (t : ℕ) (i j : m) (a : ℕ) (ha : a + L ≤ T)
    (η θ : {v : Fin T // ¬(a ≤ v.val ∧ v.val < a + L)} → Fin q) :
    IsOpenMPS T (q * q) ((B ^ t) ^ 2) (fun w ↦
      ((Matrix.single η θ (1 : ℂ)) ⊗ₖ retainedStackCore R steps A t i j).submatrix
        (retainedIntervalEquiv a ha).symm (retainedIntervalEquiv a ha).symm
        (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w v)).1)
        (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w v)).2)) := by
  classical
  by_cases hz : B ^ t = 0
  · have hzero : retainedStackCore R steps A t i j = 0 := by
      let : IsEmpty (Fin (B ^ t)) := ⟨fun v ↦ by have := v.isLt; omega⟩
      ext σ τ
      simp [retainedStackCore, Matrix.trace]
    rw [hzero, Matrix.kronecker_zero]
    change IsOpenMPS T (q * q) ((B ^ t) ^ 2)
      (fun w ↦ (0 : EuclideanSpace ℂ (Fin T → Fin (q * q))) w)
    apply isOpenMPS_of_internal_cutMatrix_rank_le
    intro k hk0 hkT
    have hcut : cutMatrix (0 : EuclideanSpace ℂ (Fin T → Fin (q * q))) k = 0 := by
      ext x y
      simp [cutMatrix_apply]
    rw [hcut, Matrix.rank_zero]
    exact Nat.zero_le _
  · have hdim : 1 ≤ (B ^ t) ^ 2 := by
      have hp : 0 < B ^ t := Nat.pos_of_ne_zero hz
      exact Nat.succ_le_of_lt (Nat.pow_pos hp)
    simpa only [max_eq_right hdim] using
      isOpenMPS_retainedSingle_kronecker a ha η θ
        (retainedStackCore R steps A t i j)
        (retainedStackCore_entries_isOpenMPS R steps A t i j)

/-- Configurations of the single retained complement of the supplied interval. -/
abbrev actualAffineRetainedConfig (T L q a : ℕ) :=
  {v : Fin T // ¬(a ≤ v.val ∧ v.val < a + L)} → Fin q

/-- The existing finite retained/core family in the original physical order.
Each summand is the natural insertion of its actual retained matrix unit and
scalar-closed stack, with the same general square bound as its core.
Supporting ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333;
no source-sharp bond bound, cardinal estimate or algorithmic bound is asserted. -/
theorem exists_finite_natural_retained_core_family {T L q B : ℕ}
    (a : ℕ) (ha : a + L ≤ T)
    (R : Fin B × Fin B → Matrix (actualAffineRetainedConfig T L q a)
      (actualAffineRetainedConfig T L q a) ℂ)
    (steps : List (Matrix (actualAffineRetainedConfig T L q a)
      (actualAffineRetainedConfig T L q a) ℂ × ℂ)) (A : Fin L → MPOTensor q B) :
    let n := (steps.length + 1) * Fintype.card (actualAffineRetainedConfig T L q a) ^ 2
    ∃ (t : Fin n → Fin (steps.length + 1))
      (i j : Fin n → actualAffineRetainedConfig T L q a)
      (V : Fin n → Matrix (Fin T → Fin q) (Fin T → Fin q) ℂ),
      (∀ r, V r =
        ((Matrix.single (i r) (j r) (1 : ℂ)) ⊗ₖ
          retainedStackCore R steps A (t r).val (i r) (j r)).submatrix
          (retainedIntervalEquiv a ha).symm (retainedIntervalEquiv a ha).symm) ∧
      (∀ r, IsOpenMPS T (q * q) ((B ^ (t r).val) ^ 2) (fun w ↦ V r
        (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w v)).1)
        (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w v)).2))) ∧
      ((steps.map (fun z : Matrix (actualAffineRetainedConfig T L q a)
          (actualAffineRetainedConfig T L q a) ℂ × ℂ ↦
        (z.1 ⊗ₖ (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)) +
          ∑ b : Fin B × Fin B,
            (z.2 • R b) ⊗ₖ interiorMatrixSlice A b.1 b.2)).prod).submatrix
          (retainedIntervalEquiv a ha).symm (retainedIntervalEquiv a ha).symm =
        ∑ r, V r := by
  intro n
  obtain ⟨t, i, j, W, hW, _, hprod⟩ := exists_finite_retained_core_family R steps A
  let V : Fin n → Matrix (Fin T → Fin q) (Fin T → Fin q) ℂ :=
    fun r ↦ ((Matrix.single (i r) (j r) (1 : ℂ)) ⊗ₖ W r).submatrix
    (retainedIntervalEquiv a ha).symm (retainedIntervalEquiv a ha).symm
  refine ⟨t, i, j, V, ?_, ?_, ?_⟩
  · intro r
    dsimp only [V]
    rw [hW r]
  · intro r
    dsimp only [V]
    rw [hW r]
    exact retainedStackCore_naturalInsertion_isOpenMPS R steps A (t r).val
      (i r) (j r) a ha (i r) (j r)
  · rw [hprod]
    ext σ τ
    simp only [Matrix.submatrix_apply, Matrix.sum_apply, V]
    rfl

/-- The ordered affine product for the supplied full-chain trace operator is
the natural transport of the affine retained/interior product. Its retained
coefficients are the actual suffix-cap-prefix entries of that supplied chain.
Supporting ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333;
this identifies only the supplied trace operator and adds no regional
Hamiltonian identification, cardinal estimate or resource bound. -/
theorem prod_actual_natural_affine_eq {T L q B : ℕ}
    (Afull : Fin T → MPOTensor q B) (C : Matrix (Fin B) (Fin B) ℂ)
    (a : ℕ) (ha : a + L ≤ T)
    (steps : List (Matrix (actualAffineRetainedConfig T L q a)
      (actualAffineRetainedConfig T L q a) ℂ × ℂ)) :
    let e : (actualAffineRetainedConfig T L q a × (Fin L → Fin q)) ≃
      (Fin T → Fin q) := retainedIntervalEquiv a ha;
    let R : Fin B × Fin B → Matrix (actualAffineRetainedConfig T L q a)
      (actualAffineRetainedConfig T L q a) ℂ := fun ab η θ ↦
      actualRetainedIntervalClosing Afull C a ha η θ ab.2 ab.1;
    let Ainterval : Fin L → MPOTensor q B := fun v ↦ Afull ⟨a + v.val, by omega⟩;
      (steps.map (fun z : Matrix (actualAffineRetainedConfig T L q a)
          (actualAffineRetainedConfig T L q a) ℂ × ℂ ↦
        (z.1 ⊗ₖ (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)).submatrix e.symm e.symm +
          z.2 • (Matrix.of fun σ τ : Fin T → Fin q ↦ Matrix.trace
            (C * (List.ofFn (fun v : Fin T ↦ Afull v (σ v) (τ v))).prod)))).prod =
        ((steps.map (fun z : Matrix (actualAffineRetainedConfig T L q a)
            (actualAffineRetainedConfig T L q a) ℂ × ℂ ↦
          (z.1 ⊗ₖ (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)) +
            ∑ ab : Fin B × Fin B,
              (z.2 • R ab) ⊗ₖ interiorMatrixSlice Ainterval ab.1 ab.2)).prod).submatrix
          e.symm e.symm := by
  intro e R Ainterval
  have hH :
      (Matrix.of fun σ τ : Fin T → Fin q ↦ Matrix.trace
        (C * (List.ofFn (fun v : Fin T ↦ Afull v (σ v) (τ v))).prod)) =
        (∑ ab : Fin B × Fin B,
          R ab ⊗ₖ interiorMatrixSlice Ainterval ab.1 ab.2).submatrix e.symm e.symm := by
    ext σ τ
    simpa only [Matrix.submatrix_apply, Matrix.of_apply, e, R, Ainterval,
      Equiv.apply_symm_apply] using
      congrFun (congrFun (trace_actual_retainedInterval_eq_sum Afull C a ha)
        (e.symm σ)) (e.symm τ)
  simp_rw [hH]
  simpa only [Matrix.smul_kronecker, ← Finset.smul_sum, List.map_map,
    Function.comp_def, Matrix.coe_reindexRingEquiv, Matrix.reindex_apply,
    Matrix.submatrix_add, Matrix.submatrix_smul, Pi.add_apply, Pi.smul_apply] using
    (map_list_prod (Matrix.reindexRingEquiv ℂ e)
      (steps.map (fun z : Matrix (actualAffineRetainedConfig T L q a)
          (actualAffineRetainedConfig T L q a) ℂ × ℂ ↦
        (z.1 ⊗ₖ (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)) +
          ∑ ab : Fin B × Fin B,
            (z.2 • R ab) ⊗ₖ interiorMatrixSlice Ainterval ab.1 ab.2))).symm

end MPOTensor

end
