/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.UncleBoundaryWords
import QICLean.Algebra.TraceFormDuality

/-!
# Intersection of the actual uncle boundary spaces

The source four-sector space \(S_n\) has the adjacent-overlap intersection
property for \(n\geq2\). Full perturbation injectivity supplies the
identity contraction and full span on the middle \(n-1\) sites. These recover
a single boundary matrix from the two overlapping boundary descriptions.
No intersection property is assumed.

Source: arXiv:1210.6613, Lemma intersection, lines 1077–1098, and Appendix
intersection-closure, lines 1768–1940. The Appendix starts at \(S_2\) and then
treats \(k>2\); the positive middle-word length remains explicit.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d a b : ℕ}

private noncomputable def uncleTraceRight
    (X : Matrix (Fin (a + b)) (Fin (a + b)) ℂ) :
    Matrix (Fin (a + b)) (Fin (a + b)) ℂ →ₗ[ℂ] ℂ :=
  (Matrix.traceLinearMap (Fin (a + b)) ℂ ℂ).comp (LinearMap.mulRight ℂ X)

/-- Fixing the final site preserves the source boundary-space constraint. -/
theorem restrictLast_mem_uncleBoundarySpace
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) {n : ℕ}
    {ψ : NSiteSpace d (n + 1)} (hψ : ψ ∈ uncleBoundarySpace A B R L (n + 1))
    (i : Fin d) : restrictLast ψ i ∈ uncleBoundarySpace A B R L n := by
  obtain ⟨X, rfl⟩ := hψ
  let f := (uncleTraceRight X).comp
    (uncleBoundaryMulRight (uncleBoundaryLetter A B R L i))
  let Y := ((Matrix.traceBilinForm (Fin (a + b))).toDual
    Matrix.traceBilinForm_nondegenerate).symm f
  have hY (M : Matrix (Fin (a + b)) (Fin (a + b)) ℂ) :
      f M = Matrix.trace (Y * M) := by
    rw [← Matrix.traceBilinForm_apply, LinearMap.BilinForm.apply_toDual_symm_apply]
  refine ⟨Y, ?_⟩
  ext σ
  change Matrix.trace (uncleBoundaryWord A B R L (List.ofFn σ) * Y) =
    Matrix.trace (uncleBoundaryWord A B R L (List.ofFn (Fin.snoc σ i)) * X)
  rw [uncleBoundaryWord_ofFn_snoc]
  exact (Matrix.trace_mul_comm _ _).trans (hY (uncleBoundaryWord A B R L (List.ofFn σ))).symm

/-- Fixing the initial site preserves the source boundary-space constraint. -/
theorem restrictFirst_mem_uncleBoundarySpace
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) {n : ℕ}
    {ψ : NSiteSpace d (n + 1)} (hψ : ψ ∈ uncleBoundarySpace A B R L (n + 1))
    (i : Fin d) : restrictFirst ψ i ∈ uncleBoundarySpace A B R L n := by
  obtain ⟨X, rfl⟩ := hψ
  let f := (uncleTraceRight X).comp
    (uncleBoundaryMulLeft (uncleBoundaryLetter A B R L i))
  let Y := ((Matrix.traceBilinForm (Fin (a + b))).toDual
    Matrix.traceBilinForm_nondegenerate).symm f
  have hY (M : Matrix (Fin (a + b)) (Fin (a + b)) ℂ) :
      f M = Matrix.trace (Y * M) := by
    rw [← Matrix.traceBilinForm_apply, LinearMap.BilinForm.apply_toDual_symm_apply]
  refine ⟨Y, ?_⟩
  ext σ
  change Matrix.trace (uncleBoundaryWord A B R L (List.ofFn σ) * Y) =
    Matrix.trace (uncleBoundaryWord A B R L (List.ofFn (Fin.cons i σ)) * X)
  rw [uncleBoundaryWord_ofFn_cons]
  exact (Matrix.trace_mul_comm _ _).trans (hY (uncleBoundaryWord A B R L (List.ofFn σ))).symm

/-- Two overlapping source boundary descriptions reconstruct one boundary
matrix on the larger chain. This proves the reverse intersection inclusion
from full perturbation injectivity, with no supplied reconstruction premise.
Source: arXiv:1210.6613, Appendix intersection proof, lines 1768–1940. -/
theorem mem_uncleBoundarySpace_of_overlap
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hPert : Kraus.IsInjective (uncleBoundaryLetter A B R L)) (n : ℕ)
    (ψ : NSiteSpace d (n + 3))
    (hLeft : ∀ i, restrictLast ψ i ∈ uncleBoundarySpace A B R L (n + 2))
    (hRight : ∀ i, restrictFirst ψ i ∈ uncleBoundarySpace A B R L (n + 2)) :
    ψ ∈ uncleBoundarySpace A B R L (n + 3) := by
  classical
  have hX : ∀ k, ∃ X, uncleBoundaryMap A B R L (n + 2) X = restrictLast ψ k := hLeft
  have hY : ∀ i, ∃ Y, uncleBoundaryMap A B R L (n + 2) Y = restrictFirst ψ i := hRight
  choose X hX using hX
  choose Y hY using hY
  obtain ⟨c, hc⟩ := exists_uncleBoundary_identity_coefficients A B R L hPert
  let Z := ∑ i, c i • Y i
  have hCompat (i k : Fin d) (w : Fin (n + 1) → Fin d) :
      Matrix.trace (uncleBoundaryWord A B R L (i :: List.ofFn w) * X k) =
        Matrix.trace (uncleBoundaryWord A B R L (List.ofFn w ++ [k]) * Y i) := by
    have hx := congrFun (hX k) (Fin.cons i w)
    have hy := congrFun (hY i) (Fin.snoc w k)
    simp only [uncleBoundaryMap_apply, restrictLast_apply, List.ofFn_cons] at hx
    simp only [uncleBoundaryMap_apply, restrictFirst_apply, List.ofFn_snoc] at hy
    rw [Fin.cons_snoc_eq_snoc_cons] at hy
    exact hx.trans hy.symm
  have hMiddle (k : Fin d) (w : Fin (n + 1) → Fin d) :
      Matrix.trace (uncleBoundaryWord A B R L (List.ofFn w) * X k) =
        Matrix.trace (uncleBoundaryWord A B R L (List.ofFn w ++ [k]) * Z) := by
    calc
      _ = Matrix.trace
          ((∑ i, c i • uncleBoundaryWord A B R L (i :: List.ofFn w)) * X k) := by
        rw [sum_smul_uncleBoundaryWord_cons A B R L c hc]
      _ = ∑ i, c i * Matrix.trace
          (uncleBoundaryWord A B R L (i :: List.ofFn w) * X k) := by
        simp [Matrix.sum_mul, Matrix.trace_sum, Matrix.trace_smul]
      _ = ∑ i, c i * Matrix.trace
          (uncleBoundaryWord A B R L (List.ofFn w ++ [k]) * Y i) := by
        simp_rw [hCompat]
      _ = _ := by
        simp [Z, Matrix.mul_sum, Matrix.trace_sum, Matrix.trace_smul]
  have hExtend (k : Fin d) (M : Matrix (Fin (a + b)) (Fin (a + b)) ℂ) :
      Matrix.trace (M * X k) =
        Matrix.trace (uncleBoundaryMul M (uncleBoundaryLetter A B R L k) * Z) := by
    let f := uncleTraceRight (X k)
    let g := (uncleTraceRight Z).comp
      (uncleBoundaryMulRight (uncleBoundaryLetter A B R L k))
    have hfg : f = g := by
      apply LinearMap.ext_on_range (uncleBoundary_span_eq_top_succ A B R L hPert n)
      intro w
      change Matrix.trace (uncleBoundaryWord A B R L (List.ofFn w) * X k) =
        Matrix.trace (uncleBoundaryMul (uncleBoundaryWord A B R L (List.ofFn w))
          (uncleBoundaryLetter A B R L k) * Z)
      simpa only [uncleBoundaryWord_append, uncleBoundaryWord_singleton] using hMiddle k w
    exact congrArg (fun F => F M) hfg
  refine ⟨Z, ?_⟩
  ext σ
  let w := Fin.init σ
  let k := σ (Fin.last (n + 2))
  have hσ : Fin.snoc w k = σ := Fin.snoc_init_self σ
  calc
    uncleBoundaryMap A B R L (n + 3) Z σ =
        Matrix.trace (uncleBoundaryMul (uncleBoundaryWord A B R L (List.ofFn w))
          (uncleBoundaryLetter A B R L k) * Z) := by
      rw [← hσ, uncleBoundaryMap_apply, uncleBoundaryWord_ofFn_snoc]
    _ = Matrix.trace (uncleBoundaryWord A B R L (List.ofFn w) * X k) := (hExtend k _).symm
    _ = ψ σ := by
      have hx := congrFun (hX k) w
      simpa only [uncleBoundaryMap_apply, restrictLast_apply, hσ] using hx

/-- The source intersection equality holds for window length at least two.
The Appendix starts at two, so the overlapping middle length is positive.
Source: arXiv:1210.6613, Lemma intersection and Appendix lines 1768–1940. -/
theorem uncleBoundarySpace_intersection
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hPert : Kraus.IsInjective (uncleBoundaryLetter A B R L)) (n : ℕ) :
    (⨅ i : Fin d, (uncleBoundarySpace A B R L (n + 2)).comap (restrictLastₗ i)) ⊓
        (⨅ i : Fin d, (uncleBoundarySpace A B R L (n + 2)).comap (restrictFirstₗ i)) =
      uncleBoundarySpace A B R L (n + 3) := by
  ext ψ
  simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]
  constructor
  · rintro ⟨hLeft, hRight⟩
    exact mem_uncleBoundarySpace_of_overlap A B R L hPert n ψ hLeft hRight
  · intro hψ
    exact ⟨restrictLast_mem_uncleBoundarySpace A B R L hψ,
      restrictFirst_mem_uncleBoundarySpace A B R L hψ⟩

end MPSTensor
