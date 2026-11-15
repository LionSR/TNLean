/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Sparse couplings of finite positive masses

Two nonnegative mass lists with the same positive total admit a coupling
using at most the sum of their lengths minus one weighted pairs. This is
the finite transport step in the residual-map construction for the cyclic
root-selection argument associated with arXiv:1708.00029, Theorem 4.1;
see `docs/paper-gaps/dccsp17_root_kraus_rank_thm41.tex`.

The proof applies Carathéodory's theorem to pairs of standard basis vectors.
An affine-independent family of these pairs is linearly independent and
lies in the codimension-one subspace of equal total mass.
-/

open scoped BigOperators

namespace SparseCoupling

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

private def rowTotal : ((α → ℝ) × (β → ℝ)) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, x.1 i
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum]

private def colTotal : ((α → ℝ) × (β → ℝ)) →ₗ[ℝ] ℝ where
  toFun x := ∑ j, x.2 j
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum]

private def atom (ij : α × β) :
    (α → ℝ) × (β → ℝ) := (Pi.single ij.1 1, Pi.single ij.2 1)

omit [Fintype β] in
private theorem atom_rowTotal (ij : α × β) :
    rowTotal (atom ij) = 1 := by simp [rowTotal, atom, Pi.single_apply]

omit [Fintype α] in
private theorem atom_colTotal (ij : α × β) :
    colTotal (atom ij) = 1 := by simp [colTotal, atom, Pi.single_apply]

/-- Finite probability lists admit a nonnegative coupling on at most
`card α + card β - 1` weighted pairs. The finite index allows direct use
as a Kraus index in the cyclic root-selection argument for
arXiv:1708.00029, Theorem 4.1. -/
theorem exists_probability_coupling [Nonempty α] [Nonempty β]
    (a : α → ℝ) (b : β → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (haSum : ∑ i, a i = 1) (hbSum : ∑ j, b j = 1) :
    ∃ (r : ℕ) (row : Fin r → α) (col : Fin r → β) (w : Fin r → ℝ),
      r + 1 ≤ Fintype.card α + Fintype.card β ∧
      (∀ k, 0 ≤ w k) ∧
      (∀ i, (∑ k, if row k = i then w k else 0) = a i) ∧
      (∀ j, (∑ k, if col k = j then w k else 0) = b j) := by
  classical
  let E := (α → ℝ) × (β → ℝ)
  have hWeights : ∑ ij : α × β, a ij.1 * b ij.2 = 1 := by
    simp [Fintype.sum_prod_type, ← Finset.mul_sum, haSum, hbSum]
  have hVector : ∑ ij : α × β, (a ij.1 * b ij.2) • atom ij = (a, b) := by
    apply Prod.ext
    · ext i
      simp [atom, Fintype.sum_prod_type, Prod.fst_sum, Finset.sum_apply,
        Pi.single_apply, mul_ite, ← Finset.mul_sum, hbSum]
    · ext j
      simp [atom, Fintype.sum_prod_type, Prod.snd_sum, Finset.sum_apply,
        Pi.single_apply, mul_ite, ← Finset.sum_mul, haSum]
  have hx : (a, b) ∈ convexHull ℝ (Set.range (atom (α := α) (β := β))) :=
    mem_convexHull_of_exists_fintype (fun ij : α × β => a ij.1 * b ij.2) atom
      (fun ij => mul_nonneg (ha ij.1) (hb ij.2)) hWeights
      (fun ij => Set.mem_range_self ij) hVector
  let t : Finset E := Caratheodory.minCardFinsetOfMemConvexHull hx
  have ht : (t : Set E) ⊆ Set.range atom :=
    Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx
  have hAff : AffineIndependent ℝ ((↑) : t → E) :=
    Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx
  have hConv : (a, b) ∈ convexHull ℝ (t : Set E) :=
    Caratheodory.mem_minCardFinsetOfMemConvexHull hx
  obtain ⟨w, hw, hwSum, hwVector⟩ := Finset.mem_convexHull'.mp hConv
  have hRow (x : t) : rowTotal (x : E) = 1 := by
    obtain ⟨ij, hij⟩ := ht x.property
    rw [← hij]
    exact atom_rowTotal ij
  have hCol (x : t) : colTotal (x : E) = 1 := by
    obtain ⟨ij, hij⟩ := ht x.property
    rw [← hij]
    exact atom_colTotal ij
  have hLI : LinearIndependent ℝ ((↑) : t → E) := by
    rw [linearIndependent_iff']
    intro s c hZero
    have hSum : ∑ x ∈ s, c x = 0 := by
      have h := congrArg (rowTotal (α := α) (β := β)) hZero
      simpa only [map_sum, map_smul, hRow, smul_eq_mul, mul_one, map_zero] using h
    exact hAff.eq_zero_of_sum_eq_zero hSum hZero
  let f : E →ₗ[ℝ] ℝ := rowTotal - colTotal
  have hf : Function.Surjective f := by
    intro x
    refine ⟨(Pi.single (Classical.arbitrary α) x, 0), ?_⟩
    simp [f, rowTotal, colTotal, Pi.single_apply]
  have hKer (x : t) : (x : E) ∈ f.ker := by
    change rowTotal (x : E) - colTotal (x : E) = 0
    rw [hRow, hCol, sub_self]
  let z : t → f.ker := fun x => ⟨(x : E), hKer x⟩
  have hZ : LinearIndependent ℝ z := by
    apply LinearIndependent.of_comp f.ker.subtype
    exact hLI
  have hCard := hZ.fintype_card_le_finrank
  have hDim := f.finrank_range_add_finrank_ker
  have hRange : Module.finrank ℝ f.range = 1 := by
    rw [LinearMap.range_eq_top.mpr hf]
    simp
  have hTotal : Module.finrank ℝ E = Fintype.card α + Fintype.card β := by
    simp [E, Module.finrank_prod]
  have hBound : Fintype.card t + 1 ≤ Fintype.card α + Fintype.card β := by
    rw [hRange, hTotal] at hDim
    omega
  have hAtom : ∀ x : t, ∃ ij : α × β, atom ij = (x : E) := fun x => ht x.property
  choose ij hij using hAtom
  let e : Fin (Fintype.card t) ≃ t := (Fintype.equivFin t).symm
  have hV : ∑ x : t, w x • (x : E) = (a, b) := by
    simpa only [Finset.univ_eq_attach] using
      (t.sum_attach (fun x : E => w x • x)).trans hwVector
  have hVE : ∑ k : Fin (Fintype.card t), w (e k) • atom (ij (e k)) = (a, b) := by
    calc
      _ = ∑ x : t, w x • (x : E) :=
        Fintype.sum_equiv e _ _ (fun k => by rw [hij])
      _ = (a, b) := hV
  refine ⟨Fintype.card t, fun k => (ij (e k)).1, fun k => (ij (e k)).2,
    fun k => w (e k), hBound, fun k => hw _ (e k).property, ?_, ?_⟩
  · intro i
    have h := congrArg (fun x : E => x.1 i) hVE
    simpa [atom, Prod.fst_sum, Finset.sum_apply, Pi.single_apply, mul_ite, eq_comm] using h
  · intro j
    have h := congrArg (fun x : E => x.2 j) hVE
    simpa [atom, Prod.snd_sum, Finset.sum_apply, Pi.single_apply, mul_ite, eq_comm] using h

/-- Two finite nonnegative mass lists of the same positive total admit a
coupling on at most the sum of their lengths minus one weighted pairs.
This supplies the sparse classical transport used to preserve a residual
map's trace functional and prepared-state output in the cyclic case of
arXiv:1708.00029, Theorem 4.1. -/
theorem exists_positive_mass_coupling [Nonempty α] [Nonempty β]
    (a : α → ℝ) (b : β → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hMass : ∑ i, a i = ∑ j, b j) (hPos : 0 < ∑ i, a i) :
    ∃ (r : ℕ) (row : Fin r → α) (col : Fin r → β) (w : Fin r → ℝ),
      r + 1 ≤ Fintype.card α + Fintype.card β ∧
      (∀ k, 0 ≤ w k) ∧
      (∀ i, (∑ k, if row k = i then w k else 0) = a i) ∧
      (∀ j, (∑ k, if col k = j then w k else 0) = b j) := by
  let M := ∑ i, a i
  have hM : 0 < M := hPos
  have haNorm : ∑ i, a i / M = 1 := by rw [← Finset.sum_div]; exact div_self hM.ne'
  have hbNorm : ∑ j, b j / M = 1 := by
    rw [← Finset.sum_div, ← hMass]
    exact div_self hM.ne'
  obtain ⟨r, row, col, w, hCard, hw, hRow, hCol⟩ := exists_probability_coupling
    (fun i => a i / M) (fun j => b j / M)
    (fun i => div_nonneg (ha i) hM.le) (fun j => div_nonneg (hb j) hM.le)
    haNorm hbNorm
  refine ⟨r, row, col, fun k => M * w k, hCard,
    fun k => mul_nonneg hM.le (hw k), ?_, ?_⟩
  · intro i
    calc
      _ = M * ∑ k, if row k = i then w k else 0 := by
        simp only [Finset.mul_sum, mul_ite, mul_zero]
      _ = a i := by rw [hRow]; field_simp [hM.ne']
  · intro j
    calc
      _ = M * ∑ k, if col k = j then w k else 0 := by
        simp only [Finset.mul_sum, mul_ite, mul_zero]
      _ = b j := by rw [hCol]; field_simp [hM.ne']

end SparseCoupling
