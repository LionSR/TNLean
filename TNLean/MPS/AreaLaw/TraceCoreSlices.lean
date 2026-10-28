/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.OpenMPSCutRank
import TNLean.MPS.MPDO.StackedLayers
import TNLean.MPS.MPDO.SitewiseOperatorProduct
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.List.OfFn

/-!
# Trace contractions and interior slices

A trace-closed chain with virtual dimension `D` admits an open-boundary
representation with internal bond bound `D ^ 2`. Exposing the virtual endpoints
of a supplied interior chain also identifies ordered products of its slices
with the corresponding entries of the existing stacked tensors. Scalar word
coefficients are collected in a joint closing matrix chosen independently of
the interior tensors.

The site-dependent operator product identity is imported from
`TNLean.MPS.MPDO.SitewiseOperatorProduct`. No second product construction is
introduced here. Empty chains and zero physical or virtual dimensions are
included under the existing scalar-cap convention.

These identities support the contraction steps in ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. The square-derived
conversion does not assert the source's sharper bond bound or a running-time
estimate.
-/

open Matrix
open scoped BigOperators Kronecker

noncomputable section

namespace TNLean.MPS.AreaLaw

/-- Split an ordered product at a prescribed position. This is the ordered-list
identity needed for the trace-closed chain conversion supporting ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1311–1333. -/
private theorem orderedProduct_split {R : Type*} [Monoid R] {L : ℕ}
    (f : Fin L → R) (k : ℕ) (hk : k ≤ L) :
    (List.ofFn f).prod =
      (List.ofFn (fun v : Fin k ↦ f (v.castLE hk))).prod *
      (List.ofFn (fun v : Fin (L - k) ↦ f ⟨k + v.val, by omega⟩)).prod := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
  simpa only [List.prod_append, Nat.add_sub_cancel_left, Fin.val_cast, Fin.natAdd, Fin.castLE] using
    congrArg List.prod (List.ofFn_add (n := k) (m := r) (f := f))

/-- An arbitrary scalar closing matrix in a nonuniform trace-form chain gives an
open-boundary representation with internal bond bound D². Empty chains use the
existing scalar cap; zero physical or virtual dimensions are allowed.
This conditional conversion supports the boundary-convention distinction in
ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1311–1333. -/
theorem isOpenMPS_trace_closed_chain {L q D : ℕ}
    (C : Matrix (Fin D) (Fin D) ℂ)
    (A : Fin L → Fin q → Matrix (Fin D) (Fin D) ℂ) :
    IsOpenMPS L q (D ^ 2)
      (fun w ↦ Matrix.trace (C * Fin.prod (fun v ↦ A v (w v)))) := by
  classical
  let ψ := WithLp.toLp 2 (fun w : Fin L → Fin q ↦
    Matrix.trace (C * Fin.prod (fun v ↦ A v (w v))))
  apply isOpenMPS_of_internal_cutMatrix_rank_le ψ
  intro k hk0 hkL
  let P (a : {v : Fin L // v ∈ leftBlock L k} → Fin q) :
      Matrix (Fin D) (Fin D) ℂ :=
    (List.ofFn (fun v : Fin k ↦
      A (v.castLE hkL.le) (a ⟨v.castLE hkL.le, mem_leftBlock.mpr v.isLt⟩))).prod
  let Q (b : {v : Fin L // v ∉ leftBlock L k} → Fin q) :
      Matrix (Fin D) (Fin D) ℂ :=
    (List.ofFn (fun v : Fin (L - k) ↦
      A ⟨k + v.val, by omega⟩ (b ⟨⟨k + v.val, by omega⟩, by
        rw [mem_leftBlock]
        change ¬ k + v.val < k
        omega⟩))).prod
  let U : Matrix ({v : Fin L // v ∈ leftBlock L k} → Fin q)
      (Fin D × Fin D) ℂ := fun a ij ↦ (C * P a) ij.1 ij.2
  let V : Matrix (Fin D × Fin D)
      ({v : Fin L // v ∉ leftBlock L k} → Fin q) ℂ := fun ij b ↦ Q b ij.2 ij.1
  have hfactor : cutMatrix ψ k = U * V := by
    ext a b
    rw [cutMatrix_apply]
    change Matrix.trace (C * Fin.prod (fun v ↦ A v
      ((Entropy.cutEquiv (fun _ : Fin L ↦ q) (leftBlock L k)).symm (a, b) v))) = _
    rw [Fin.prod_eq_prod_map_finRange, ← List.ofFn_eq_map,
      orderedProduct_split _ k hkL.le]
    have hP : (List.ofFn (fun v : Fin k ↦ A (v.castLE hkL.le)
        ((Entropy.cutEquiv (fun _ : Fin L ↦ q) (leftBlock L k)).symm
          (a, b) (v.castLE hkL.le)))).prod = P a := by
      apply congrArg List.prod
      apply congrArg List.ofFn
      funext v
      have hv : v.castLE hkL.le ∈ leftBlock L k := mem_leftBlock.mpr v.isLt
      rw [Entropy.cutEquiv_symm_apply_mem _ _ hv]
    have hQ : (List.ofFn (fun v : Fin (L - k) ↦ A ⟨k + v.val, by omega⟩
        ((Entropy.cutEquiv (fun _ : Fin L ↦ q) (leftBlock L k)).symm
          (a, b) ⟨k + v.val, by omega⟩))).prod = Q b := by
      apply congrArg List.prod
      apply congrArg List.ofFn
      funext v
      have hv : (⟨k + v.val, by omega⟩ : Fin L) ∉ leftBlock L k := by
        rw [mem_leftBlock]
        change ¬ k + v.val < k
        omega
      rw [Entropy.cutEquiv_symm_apply_not_mem _ _ hv]
    rw [hP, hQ, ← Matrix.mul_assoc]
    change (∑ i, ∑ j, (C * P a) i j * Q b j i) =
      ∑ ij : Fin D × Fin D, (C * P a) ij.1 ij.2 * Q b ij.2 ij.1
    rw [Fintype.sum_prod_type]
  rw [hfactor]
  refine (Matrix.rank_mul_le_left U V).trans ?_
  simpa only [Fintype.card_prod, Fintype.card_fin, pow_two] using
    Matrix.rank_le_card_width U

/-- Split an ordered list product into its prefix, interval and suffix.
This is the ordered-product identity supporting the cut movement in ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1332–1333. -/
theorem orderedProduct_partition_interval {R : Type*} [Monoid R]
    (l : List R) (a L : ℕ) :
    l.prod = (l.take a).prod * ((l.drop a).take L).prod * (l.drop (a + L)).prod := by
  rw [← List.prod_take_mul_prod_drop l a,
    ← List.prod_take_mul_prod_drop (l.drop a) L]
  simp only [List.drop_drop, mul_assoc]

end TNLean.MPS.AreaLaw

namespace MPOTensor

/-- The exposed virtual entry of a site-dependent product tensor is the
physical product of its two supplied chain slices. Supporting contraction
algebra for ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333.
Both virtual spaces and the physical alphabet may be empty. -/
private theorem prod_mulTensor_entry {L q D₁ D₂ : ℕ}
    (A : Fin L → MPOTensor q D₁) (B : Fin L → MPOTensor q D₂)
    (σ τ : Fin L → Fin q) (a b : Fin D₁ × Fin D₂) :
    let e : Fin (D₁ * D₂) ≃ Fin D₁ × Fin D₂ := finProdFinEquiv.symm
    (List.ofFn (fun v ↦ mulTensor (A v) (B v) (σ v) (τ v))).prod
        (e.symm a) (e.symm b) =
      ∑ ρ : Fin L → Fin q,
        (List.ofFn (fun v ↦ A v (σ v) (ρ v))).prod a.1 b.1 *
          (List.ofFn (fun v ↦ B v (ρ v) (τ v))).prod a.2 b.2 := by
  intro e
  simpa only [Matrix.single_kronecker_single, one_mul,
    Matrix.submatrix_single_equiv, Matrix.trace_single_mul, one_smul] using
    trace_prod_mulTensor A B
      (Matrix.single b.1 a.1 (1 : ℂ)) (Matrix.single b.2 a.2 (1 : ℂ)) σ τ

/-- The virtual index of an ordered layer word, with the last layer as the
least significant digit. Supporting coordinate algebra for ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private def stackWordIndex {B p : ℕ} : (Fin p → Fin B) ≃ Fin (B ^ p) :=
  (Equiv.arrowCongr Fin.revPerm (Equiv.refl (Fin B))).trans finFunctionFinEquiv

/-- The empty word has the unique virtual index, also at zero bond dimension.
Supporting algebra for ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem stackWordIndex_zero {B : ℕ} (w : Fin 0 → Fin B) :
    stackWordIndex w = (0 : Fin 1) := by
  let : Unique (Fin (B ^ 0)) := Equiv.unique (finCongr (pow_zero B))
  exact Subsingleton.elim _ _

/-- Appending one layer gives the existing virtual product encoding.
Supporting algebra for ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem stackWordIndex_snoc {B p : ℕ} (w : Fin p → Fin B) (a : Fin B) :
    stackWordIndex (Fin.snoc w a) = finProdFinEquiv (stackWordIndex w, a) := by
  apply Fin.ext
  change (finFunctionFinEquiv (Fin.snoc w a ∘ Fin.rev) : ℕ) =
    a.val + B * (finFunctionFinEquiv (w ∘ Fin.rev) : ℕ)
  rw [Fin.snoc_comp_rev, finFunctionFinEquiv_apply, finFunctionFinEquiv_apply]
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.val_zero, Fin.val_succ, pow_zero, mul_one, pow_succ']
  apply congrArg (fun t : ℕ ↦ a.val + t)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ac_rfl

/-- Separate the last letter of a nonempty word in the actual stack coordinates.
Supporting algebra for ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem stackWordIndex_succ {B p : ℕ} (u : Fin (p + 1) → Fin B) :
    stackWordIndex u =
      finProdFinEquiv (stackWordIndex (fun j : Fin p ↦ u j.castSucc), u (Fin.last p)) := by
  have h := stackWordIndex_snoc (Fin.init u) (u (Fin.last p))
  rw [Fin.snoc_init_self] at h
  simpa only [Fin.init_def] using h

/-- The actual operator matrix with exposed virtual endpoints of a supplied
site-dependent interior chain. Supporting algebra for ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
def interiorMatrixSlice {L q B : ℕ}
    (A : Fin L → MPOTensor q B) (a b : Fin B) :
    Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
  fun σ τ ↦ (List.ofFn (fun v ↦ A v (σ v) (τ v))).prod a b

/-- An ordered product of exposed interior slices is the corresponding
entry of the existing sitewise stacked tensor. The virtual word is encoded
with its last letter least significant, so no matrix factors are reversed.
Supporting ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem prod_interiorMatrixSlice_eq_stackedTensor {L q B : ℕ}
    (A : Fin L → MPOTensor q B) (p : ℕ) (u v : Fin p → Fin B)
    (σ τ : Fin L → Fin q) :
    (List.ofFn (fun r ↦ interiorMatrixSlice A (u r) (v r))).prod σ τ =
      (List.ofFn (fun j ↦ stackedTensor (A j) p (σ j) (τ j))).prod
        (stackWordIndex u) (stackWordIndex v) := by
  induction p generalizing σ τ with
  | zero =>
    simp only [List.ofFn_zero, List.prod_nil, stackedTensor]
    rw [stackWordIndex_zero u, stackWordIndex_zero v]
    set_option backward.isDefEq.respectTransparency false in
      simpa only [mpo_apply, mpoMatrixEntry, evalWord_ofFn, Matrix.trace_fin_one] using
        (congrFun (congrFun (mpo_idTensor q L) σ) τ).symm
  | succ p ih =>
    rw [List.ofFn_succ_last, List.prod_append, List.prod_singleton, Matrix.mul_apply]
    simp_rw [ih]
    rw [stackWordIndex_succ u, stackWordIndex_succ v]
    exact (prod_mulTensor_entry (fun j ↦ stackedTensor (A j) p) A σ τ
      (stackWordIndex (fun r : Fin p ↦ u r.castSucc), u (Fin.last p))
      (stackWordIndex (fun r : Fin p ↦ v r.castSucc), v (Fin.last p))).symm

/-- Scalar word coefficients are placed in one joint closing matrix, chosen
without the interior chain or its physical space. The reversed row/column
placement is exactly the trace pairing. Supporting ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
def stackClosingMatrix {B p : ℕ}
    (c : (Fin p → Fin B × Fin B) → ℂ) : Matrix (Fin (B ^ p)) (Fin (B ^ p)) ℂ :=
  fun a b ↦ c (fun r ↦
    ((stackWordIndex (B := B) (p := p)).symm b r,
      (stackWordIndex (B := B) (p := p)).symm a r))

/-- Every scalar linear combination of ordered slice words is represented
by the actual common p-layer interior tensors with one scalar joint cap.
The closing matrix does not depend on the supplied interior tensors.
All lengths and dimensions may be zero. Supporting contraction algebra for
ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. This gives no
open-boundary bond estimate, source-convention or running-time assertion. -/
theorem sum_word_slices_eq_trace_stackedTensor {L q B : ℕ}
    (A : Fin L → MPOTensor q B) (p : ℕ)
    (c : (Fin p → Fin B × Fin B) → ℂ) (σ τ : Fin L → Fin q) :
    (∑ w : Fin p → Fin B × Fin B,
      c w * (List.ofFn (fun r ↦ interiorMatrixSlice A (w r).1 (w r).2)).prod σ τ) =
      Matrix.trace (stackClosingMatrix c *
        (List.ofFn (fun j ↦ stackedTensor (A j) p (σ j) (τ j))).prod) := by
  rw [← (Equiv.arrowProdEquivProdArrow (Fin p)
    (fun _ ↦ Fin B) (fun _ ↦ Fin B)).symm.sum_comp, Fintype.sum_prod_type]
  change (∑ u : Fin p → Fin B, ∑ v : Fin p → Fin B,
    c (fun r ↦ (u r, v r)) *
      (List.ofFn (fun r ↦ interiorMatrixSlice A (u r) (v r))).prod σ τ) = _
  simp_rw [prod_interiorMatrixSlice_eq_stackedTensor]
  change (∑ u : Fin p → Fin B, ∑ v : Fin p → Fin B,
    c (fun r ↦ (u r, v r)) *
      (List.ofFn (fun j ↦ stackedTensor (A j) p (σ j) (τ j))).prod
        (stackWordIndex u) (stackWordIndex v)) =
    (∑ a : Fin (B ^ p), ∑ b : Fin (B ^ p),
      c (fun r ↦ ((stackWordIndex (B := B) (p := p)).symm b r,
        (stackWordIndex (B := B) (p := p)).symm a r)) *
        (List.ofFn (fun j ↦ stackedTensor (A j) p (σ j) (τ j))).prod b a)
  conv_rhs => rw [Finset.sum_comm]
  rw [← (stackWordIndex (B := B) (p := p)).symm.sum_comp]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [← (stackWordIndex (B := B) (p := p)).symm.sum_comp]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  simp only [Equiv.apply_symm_apply]

end MPOTensor

end
