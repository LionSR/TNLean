/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.WeylMonotonicity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Data.List.GetD

/-!
# Ordered spectra and zero padding in the half-chain limit

The decreasing eigenvalues of a positive semidefinite matrix are extended by
zero to a sequence on the natural numbers. Characteristic-polynomial identities
up to powers of \(X\) identify these sequences, including multiplicities.
Weyl monotonicity also gives continuity of each ordered eigenvalue, and hence
of the zero-extended sequence in a fixed finite dimension.

These are the finite-dimensional spectral comparisons used in the half-chain
Schmidt limit of PGVWC07, arXiv:quant-ph/0608197, Theorem 6.
-/

open scoped MatrixOrder ComplexOrder Topology

namespace Matrix

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

namespace IsHermitian

variable {A : Matrix n n ℂ}

/-- An increasing scalar function acts termwise on the decreasing eigenvalues. -/
theorem eigenvalues₀_cfc_monotone (hA : A.IsHermitian) (f : ℝ → ℝ)
    (hf : Monotone f) (i : Fin (Fintype.card n)) :
    (IsSelfAdjoint.cfc (f := f) (a := A)).isHermitian.eigenvalues₀ i =
      f (hA.eigenvalues₀ i) := by
  have hroots : (cfc f A).charpoly.roots =
      Multiset.map (Complex.ofReal ∘ f ∘ hA.eigenvalues₀) Finset.univ.val := by
    have hroots' : (cfc f A).charpoly.roots =
        Multiset.map (Complex.ofReal ∘ f ∘ hA.eigenvalues) Finset.univ.val := by
      rw [hA.charpoly_cfc_eq, Polynomial.roots_prod]
      · simp
      · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
    rw [hroots']
    change Multiset.map ((Complex.ofReal ∘ f ∘ hA.eigenvalues₀) ∘
      (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).symm)
      Finset.univ.val = _
    rw [← Multiset.map_map, Multiset.map_univ_val_equiv]
  have heq : List.ofFn (IsSelfAdjoint.cfc (f := f) (a := A)).isHermitian.eigenvalues₀ =
      List.ofFn (fun j ↦ f (hA.eigenvalues₀ j)) := by
    rw [← sort_roots_charpoly_eq_eigenvalues₀, hroots]
    simp only [Fin.univ_val_map, Multiset.map_coe, List.map_ofFn,
      Function.comp_def, Multiset.coe_sort]
    apply List.mergeSort_of_pairwise
    simp only [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
    exact (hf.comp_antitone hA.eigenvalues₀_antitone).sortedGE_ofFn
  exact congrFun (List.ofFn_inj.mp heq) i

/-- Adding a scalar multiple of the identity translates every ordered eigenvalue. -/
theorem eigenvalues₀_add_algebraMap (hA : A.IsHermitian) (r : ℝ)
    (i : Fin (Fintype.card n)) :
    (hA.add ((IsSelfAdjoint.all r).algebraMap (Matrix n n ℂ)).isHermitian).eigenvalues₀ i =
      hA.eigenvalues₀ i + r := by
  have heq : cfc (fun x : ℝ ↦ x + r) A = A + algebraMap ℝ (Matrix n n ℂ) r := by
    rw [cfc_add_const r (fun x : ℝ ↦ x) A continuousOn_id hA.isSelfAdjoint,
      cfc_id' ℝ A hA.isSelfAdjoint]
  simpa only [heq] using hA.eigenvalues₀_cfc_monotone (fun x ↦ x + r)
    (fun _ _ h ↦ by dsimp; linarith) i

/-- A nonnegative scalar multiplies the ordered eigenvalues term by term. -/
theorem eigenvalues₀_smul (hA : A.IsHermitian) {r : ℝ} (hr : 0 ≤ r)
    (i : Fin (Fintype.card n)) :
    (hA.smul (IsSelfAdjoint.all r)).eigenvalues₀ i = r * hA.eigenvalues₀ i := by
  have heq : cfc (fun x : ℝ ↦ r * x) A = r • A :=
    cfc_const_mul_id r A hA.isSelfAdjoint
  simpa only [heq] using hA.eigenvalues₀_cfc_monotone (fun x ↦ r * x)
    (fun _ _ h ↦ mul_le_mul_of_nonneg_left h hr) i

open scoped Matrix.Norms.L2Operator in
/-- Weyl's perturbation bound for a fixed ordered eigenvalue, in operator norm. -/
theorem abs_eigenvalues₀_sub_le (hA : A.IsHermitian) {B : Matrix n n ℂ}
    (hB : B.IsHermitian) (i : Fin (Fintype.card n)) :
    |hA.eigenvalues₀ i - hB.eigenvalues₀ i| ≤ ‖A - B‖ := by
  have hupper : hA.eigenvalues₀ i ≤ hB.eigenvalues₀ i + ‖A - B‖ := by
    rw [← hB.eigenvalues₀_add_algebraMap]
    apply hA.eigenvalues₀_mono
    exact sub_le_iff_le_add'.mp
      (IsSelfAdjoint.le_algebraMap_norm_self (A - B) (hA.sub hB).isSelfAdjoint)
  have hlower : hB.eigenvalues₀ i ≤ hA.eigenvalues₀ i + ‖A - B‖ := by
    rw [← norm_sub_rev B A, ← hA.eigenvalues₀_add_algebraMap]
    apply hB.eigenvalues₀_mono
    exact sub_le_iff_le_add'.mp
      (IsSelfAdjoint.le_algebraMap_norm_self (B - A) (hB.sub hA).isSelfAdjoint)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

open scoped Matrix.Norms.L2Operator in
/-- Ordered eigenvalues converge when Hermitian matrices converge in fixed dimension. -/
theorem eigenvalues₀_tendsto {α : Type*} {l : Filter α}
    {M : α → Matrix n n ℂ} {B : Matrix n n ℂ}
    (hM : ∀ k, (M k).IsHermitian) (hB : B.IsHermitian)
    (h : Filter.Tendsto M l (𝓝 B)) (i : Fin (Fintype.card n)) :
    Filter.Tendsto (fun k ↦ (hM k).eigenvalues₀ i) l (𝓝 (hB.eigenvalues₀ i)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero (g := fun k ↦ ‖M k - B‖)
    (fun k ↦ norm_nonneg _) (fun k ↦ ?_) ?_
  · simpa only [Real.norm_eq_abs] using (hM k).abs_eigenvalues₀_sub_le hB i
  · simpa using (h.sub_const B).norm

/-- The decreasing eigenvalues, followed by zeros after the matrix dimension. -/
noncomputable def paddedEigenvalues (hA : A.IsHermitian) (k : ℕ) : ℝ :=
  (List.ofFn hA.eigenvalues₀).getD k 0

@[simp]
theorem paddedEigenvalues_fin (hA : A.IsHermitian) (i : Fin (Fintype.card n)) :
    hA.paddedEigenvalues i = hA.eigenvalues₀ i := by
  simp [paddedEigenvalues]

/-- Every position past the matrix dimension in the extended spectrum is zero. -/
theorem paddedEigenvalues_eq_zero (hA : A.IsHermitian) {k : ℕ}
    (hk : Fintype.card n ≤ k) : hA.paddedEigenvalues k = 0 := by
  exact List.getD_eq_default _ _ (by simpa using hk)

/-- Multiplication by a nonnegative scalar commutes with zero extension. -/
theorem paddedEigenvalues_smul (hA : A.IsHermitian) {r : ℝ} (hr : 0 ≤ r) (k : ℕ) :
    (hA.smul (IsSelfAdjoint.all r)).paddedEigenvalues k = r * hA.paddedEigenvalues k := by
  by_cases hk : k < Fintype.card n
  · simpa [paddedEigenvalues, hk] using hA.eigenvalues₀_smul hr ⟨k, hk⟩
  · simp only [paddedEigenvalues_eq_zero _ (Nat.le_of_not_lt hk), mul_zero]

/-- Fixed-dimensional convergence of the zero-extended ordered eigenvalues. -/
theorem paddedEigenvalues_tendsto {α : Type*} {l : Filter α}
    {M : α → Matrix n n ℂ} {B : Matrix n n ℂ}
    (hM : ∀ k, (M k).IsHermitian) (hB : B.IsHermitian)
    (h : Filter.Tendsto M l (𝓝 B)) (i : ℕ) :
    Filter.Tendsto (fun k ↦ (hM k).paddedEigenvalues i) l
      (𝓝 (hB.paddedEigenvalues i)) := by
  by_cases hi : i < Fintype.card n
  · simpa [paddedEigenvalues, hi] using eigenvalues₀_tendsto hM hB h ⟨i, hi⟩
  · simp only [paddedEigenvalues_eq_zero _ (Nat.le_of_not_lt hi)]
    exact tendsto_const_nhds

end IsHermitian

namespace PosSemidef

variable {A : Matrix n n ℂ} {B : Matrix m m ℂ}

/-- Positivity of the canonically indexed eigenvalues. -/
theorem eigenvalues₀_nonneg (hA : A.PosSemidef) (i : Fin (Fintype.card n)) :
    0 ≤ hA.isHermitian.eigenvalues₀ i := by
  simpa [IsHermitian.eigenvalues] using hA.eigenvalues_nonneg
    ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))) i)

private theorem sort_padded_roots (hA : A.PosSemidef) (k : ℕ) :
    (((Polynomial.X ^ k * A.charpoly).roots.map Complex.re).sort (· ≥ ·)) =
      List.ofFn hA.isHermitian.eigenvalues₀ ++ List.replicate k 0 := by
  have hroots : (Polynomial.X ^ k * A.charpoly).roots.map Complex.re =
      ((List.ofFn hA.isHermitian.eigenvalues₀ ++ List.replicate k 0 : List ℝ) :
        Multiset ℝ) := by
    rw [Polynomial.roots_mul (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
      A.charpoly_monic.ne_zero), Polynomial.roots_X_pow,
      hA.isHermitian.roots_charpoly_eq_eigenvalues₀]
    simp [Multiset.map_add, Fin.univ_val_map, Function.comp_def,
      ← Multiset.coe_add, Multiset.coe_replicate, Multiset.nsmul_singleton, add_comm]
  rw [hroots, Multiset.coe_sort]
  apply List.mergeSort_of_pairwise
  simp only [decide_eq_true_eq, ← List.sortedGE_iff_pairwise, List.sortedGE_append]
  refine ⟨hA.isHermitian.eigenvalues₀_antitone.sortedGE_ofFn, ?_, ?_⟩
  · simp [List.sortedGE_iff_pairwise]
  · intro a ha b hb
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    have : b = 0 := (List.mem_replicate.mp hb).2
    simpa [this] using hA.eigenvalues₀_nonneg i

private theorem getD_append_zeros (l : List ℝ) (k i : ℕ) :
    (l ++ List.replicate k 0).getD i 0 = l.getD i 0 := by
  by_cases hi : i < l.length
  · exact List.getD_append _ _ _ _ hi
  · rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_lt hi),
      List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]
    simp [List.getD_eq_getElem?_getD]

/-- Equality of characteristic polynomials after zero padding identifies the
actual decreasing eigenvalue sequences, with zeros beyond their dimensions. -/
theorem paddedEigenvalues_eq_of_charpoly (hA : A.PosSemidef) (hB : B.PosSemidef)
    (h : Polynomial.X ^ Fintype.card m * A.charpoly =
      Polynomial.X ^ Fintype.card n * B.charpoly) :
    hA.isHermitian.paddedEigenvalues = hB.isHermitian.paddedEigenvalues := by
  have heq : List.ofFn hA.isHermitian.eigenvalues₀ ++ List.replicate (Fintype.card m) 0 =
      List.ofFn hB.isHermitian.eigenvalues₀ ++ List.replicate (Fintype.card n) 0 := by
    rw [← hA.sort_padded_roots, ← hB.sort_padded_roots, h]
  funext k
  have := congrArg (fun l : List ℝ ↦ l.getD k 0) heq
  simpa only [getD_append_zeros, IsHermitian.paddedEigenvalues] using this

end PosSemidef

end Matrix
