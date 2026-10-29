/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.UncleBoundaryProduct
import TNLean.MPS.ParentHamiltonian.IntersectionProperty
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# The four finite-chain uncle boundary sectors

The boundary words contain diagonal all-A and all-B products, together with
exactly one R or L wall summed over its possible positions. Their trace
boundary-map range is the source space \(S_n\). These words use the explicit
single-wall coefficient product, not ordinary products of the two-site
uncle tensor.

Source: arXiv:1210.6613, equation (Sn-def), lines 1077–1095, and Appendix
intersection-closure, lines 1768–1940. Full perturbation injectivity supplies
identity coefficients, which prove full word span at every positive length.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d a b : ℕ}

/-- The full one-site letter in the source injective-perturbation condition;
arXiv:1210.6613, equation (inj-condition-tensor), lines 973–983. -/
noncomputable def uncleBoundaryLetter (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) (i : Fin d) :
    Matrix (Fin (a + b)) (Fin (a + b)) ℂ :=
  uncleBlockMatrix (A i) (R i) (L i) (B i)

/-- An ordered coefficient word with at most one wall; source equation
(Sn-def), Appendix intersection-closure, arXiv:1210.6613. -/
noncomputable def uncleBoundaryWord (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) :
    List (Fin d) → Matrix (Fin (a + b)) (Fin (a + b)) ℂ
  | [] => 1
  | i :: w => uncleBoundaryMul (uncleBoundaryLetter A B R L i)
      (uncleBoundaryWord A B R L w)

@[simp] theorem uncleBoundaryWord_nil (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) : uncleBoundaryWord A B R L [] = 1 := rfl

@[simp] theorem uncleBoundaryWord_singleton (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) (i : Fin d) :
    uncleBoundaryWord A B R L [i] = uncleBoundaryLetter A B R L i :=
  uncleBoundaryMul_one _

/-- Concatenation multiplies the source single-wall coefficients. -/
theorem uncleBoundaryWord_append (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) (u v : List (Fin d)) :
    uncleBoundaryWord A B R L (u ++ v) =
      uncleBoundaryMul (uncleBoundaryWord A B R L u) (uncleBoundaryWord A B R L v) := by
  induction u with
  | nil => simp [one_uncleBoundaryMul]
  | cons i u ih =>
      simp only [List.cons_append, uncleBoundaryWord, ih, uncleBoundaryMul_assoc]

/-- Appending a physical site is right multiplication by its source letter. -/
theorem uncleBoundaryWord_ofFn_snoc (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) {n : ℕ}
    (w : Fin n → Fin d) (i : Fin d) :
    uncleBoundaryWord A B R L (List.ofFn (Fin.snoc w i)) =
      uncleBoundaryMul (uncleBoundaryWord A B R L (List.ofFn w))
        (uncleBoundaryLetter A B R L i) := by
  rw [List.ofFn_snoc, uncleBoundaryWord_append, uncleBoundaryWord_singleton]

/-- Prepending a physical site is left multiplication by its source letter. -/
theorem uncleBoundaryWord_ofFn_cons (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) {n : ℕ}
    (i : Fin d) (w : Fin n → Fin d) :
    uncleBoundaryWord A B R L (List.ofFn (Fin.cons i w)) =
      uncleBoundaryMul (uncleBoundaryLetter A B R L i)
        (uncleBoundaryWord A B R L (List.ofFn w)) := by
  rw [List.ofFn_cons]
  rfl

/-- The explicit rectangular sum with one wall, padded by A on the left
and B on the right; source equation (Sn-def), arXiv:1210.6613. -/
noncomputable def uncleDomainWallWord (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ) :
    List (Fin d) → Matrix (Fin a) (Fin b) ℂ
  | [] => 0
  | i :: w => A i * uncleDomainWallWord A B R w + R i * Kraus.evalWord B w

/-- Every wall position occurs exactly once in the source domain-wall sum. -/
theorem uncleDomainWallWord_eq_sum (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ) (w : List (Fin d)) :
    uncleDomainWallWord A B R w =
      ∑ k : Fin w.length, Kraus.evalWord A (w.take k) * R (w.get k) *
        Kraus.evalWord B (w.drop (k + 1)) := by
  induction w with
  | nil => simp [uncleDomainWallWord]
  | cons i w ih =>
      simp [uncleDomainWallWord, ih, Fin.sum_univ_succ, Matrix.mul_sum,
        Matrix.mul_assoc, add_comm]

/-- The actual four blocks of the source coefficient word. In particular
the off-diagonal terms contain a single wall, not alternating walls. -/
theorem uncleBoundaryWord_block (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) (w : List (Fin d)) :
    uncleBoundaryWord A B R L w =
      uncleBlockMatrix (Kraus.evalWord A w) (uncleDomainWallWord A B R w)
        (uncleDomainWallWord B A L w) (Kraus.evalWord B w) := by
  induction w with
  | nil => simp [uncleDomainWallWord, Kraus.evalWord, uncleBlockMatrix_one]
  | cons i w ih =>
      simp [uncleBoundaryWord, uncleBoundaryLetter, ih, uncleBoundaryMul_block,
        uncleDomainWallWord, Kraus.evalWord, add_comm]

/-- At length two the source coefficient word is exactly the existing uncle letter. -/
theorem uncleBoundaryWord_two (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) (i j : Fin d) :
    uncleBoundaryWord A B R L [i, j] =
      uncleTensor A B R L ((decodeBlockEquiv d 2).symm ![i, j]) := by
  simp [uncleBoundaryWord, uncleBoundaryLetter, uncleBoundaryMul_block, uncleTensor,
    decodeBlock_decodeBlockEquiv_symm, uncleBoundaryMul_one]

/-- The coefficient on any original two-site configuration is the existing
uncle-tensor letter with that blocked physical index. -/
theorem uncleBoundaryWord_ofFn_two (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) (σ : Fin 2 → Fin d) :
    uncleBoundaryWord A B R L (List.ofFn σ) =
      uncleTensor A B R L ((decodeBlockEquiv d 2).symm σ) := by
  have hσ : σ = ![σ 0, σ 1] := by
    ext i
    fin_cases i <;> rfl
  rw [hσ]
  simpa [List.ofFn_succ] using uncleBoundaryWord_two A B R L (σ 0) (σ 1)

/-- The full perturbation span supplies coefficients for the identity. -/
theorem exists_uncleBoundary_identity_coefficients
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hPert : Kraus.IsInjective (uncleBoundaryLetter A B R L)) :
    ∃ c : Fin d → ℂ, ∑ i, c i • uncleBoundaryLetter A B R L i = 1 := by
  apply (Submodule.mem_span_range_iff_exists_fun ℂ).mp
  rw [hPert.span_eq_top]
  exact Submodule.mem_top

/-- Contracting the first physical site against identity coefficients
removes it without adding a wall. This is the inverse-coefficient step in
the Appendix intersection proof of arXiv:1210.6613. -/
theorem sum_smul_uncleBoundaryWord_cons
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (c : Fin d → ℂ) (hc : ∑ i, c i • uncleBoundaryLetter A B R L i = 1)
    (w : List (Fin d)) :
    (∑ i, c i • uncleBoundaryWord A B R L (i :: w)) = uncleBoundaryWord A B R L w := by
  calc
    _ = uncleBoundaryMulRight (uncleBoundaryWord A B R L w)
        (∑ i, c i • uncleBoundaryLetter A B R L i) := by
      simp [uncleBoundaryWord, map_sum, map_smul]
    _ = _ := by rw [hc]; exact one_uncleBoundaryMul _

/-- Full perturbation injectivity gives full coefficient span at every
positive word length, as required in the Appendix intersection and closure
proofs of arXiv:1210.6613, lines 1925–1940. -/
theorem uncleBoundary_span_eq_top_succ
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hPert : Kraus.IsInjective (uncleBoundaryLetter A B R L)) (n : ℕ) :
    Submodule.span ℂ (Set.range fun σ : Fin (n + 1) → Fin d ↦
      uncleBoundaryWord A B R L (List.ofFn σ)) = ⊤ := by
  classical
  obtain ⟨c, hc⟩ := exists_uncleBoundary_identity_coefficients A B R L hPert
  induction n with
  | zero =>
      apply top_unique
      rw [← hPert.span_eq_top]
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨fun _ : Fin 1 ↦ i, by simp [List.ofFn_succ]⟩
  | succ n ih =>
      apply top_unique
      rw [← ih]
      apply Submodule.span_le.mpr
      rintro _ ⟨σ, rfl⟩
      change uncleBoundaryWord A B R L (List.ofFn σ) ∈ _
      rw [← sum_smul_uncleBoundaryWord_cons A B R L c hc (List.ofFn σ)]
      refine Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ (c i) ?_
      exact Submodule.subset_span ⟨Fin.cons i σ, by
        change uncleBoundaryWord A B R L (List.ofFn (Fin.cons i σ)) = _
        rw [List.ofFn_cons]⟩

/-- The trace boundary map for the four source sectors \(S_n\). -/
noncomputable def uncleBoundaryMap (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) (n : ℕ) :
    Matrix (Fin (a + b)) (Fin (a + b)) ℂ →ₗ[ℂ] NSiteSpace d n where
  toFun X σ := Matrix.trace (uncleBoundaryWord A B R L (List.ofFn σ) * X)
  map_add' X Y := by ext σ; simp [Matrix.mul_add, Matrix.trace_add]
  map_smul' c X := by ext σ; simp [Matrix.trace_smul]

/-- The actual four-sector source boundary space, equation (Sn-def) of
arXiv:1210.6613. Its word-block formula separates \(A_n,B_n,R_n,L_n\). -/
noncomputable def uncleBoundarySpace (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) (n : ℕ) : Submodule ℂ (NSiteSpace d n) :=
  LinearMap.range (uncleBoundaryMap A B R L n)

@[simp] theorem uncleBoundaryMap_apply (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) (n : ℕ)
    (X : Matrix (Fin (a + b)) (Fin (a + b)) ℂ) (σ : Fin n → Fin d) :
    uncleBoundaryMap A B R L n X σ =
      Matrix.trace (uncleBoundaryWord A B R L (List.ofFn σ) * X) := rfl

/-- The length-two source boundary map is exactly the blocked uncle map,
written on the original pair of physical indices. -/
theorem uncleBoundaryMap_two (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (X : Matrix (Fin (a + b)) (Fin (a + b)) ℂ) (σ : Fin 2 → Fin d) :
    uncleBoundaryMap A B R L 2 X σ =
      groundSpaceMap (uncleTensor A B R L) 1 X
        (fun _ ↦ (decodeBlockEquiv d 2).symm σ) := by
  rw [uncleBoundaryMap_apply, uncleBoundaryWord_ofFn_two]
  simp only [groundSpaceMap_apply, List.ofFn_succ, List.ofFn_zero, Kraus.evalWord_cons,
    Kraus.evalWord_nil, Matrix.mul_one]

end MPSTensor
