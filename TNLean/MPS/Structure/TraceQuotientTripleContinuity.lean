/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Structure.TraceQuotientAlgebraRecovery

/-!
# Continuous multiplication on finite-ring trace quotients

For a continuous raw tensor family, the two-site trace form and the contracted
three-site columns are continuous. Pointwise injective realizations identify
its trace quotient with the minimal bond matrix algebra. On a neighborhood
where that dimension is constant, a fixed physical coefficient section yields
continuous associative multiplication coordinates and pointwise normalized
multiplicative linear equivalences with the matrix algebra.

**Scope restriction (constant minimal dimension):** The family theorem assumes
that the square of the pointwise minimal bond dimension has a fixed value.
Neither the minimal tensors nor their scalar normalizations are required to
be continuous. This is a finite-data reconstruction consequence relevant to
arXiv:1010.3732, Section II.F.2, lines 953–993, rather than the varying-dimension
phase converse. Continuous unital realization through changes of rank remains
separate; see `docs/paper-gaps/spc11_spt_interpolation_upper_range.tex`.

The raw trace form is complex bilinear. Its positive Hermitian coordinate
Gram matrix is used only to invert the chosen section.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open scoped Matrix BigOperators
namespace Matrix

/-- Contracting a continuous raw tensor family against a fixed physical
section gives continuous three-site trace columns. Auxiliary context:
arXiv:1010.3732, Section II.F.2, lines 953–993. -/
theorem continuous_traceQuotientTripleColumns
    {T : Type*} [TopologicalSpace T] {d r D : ℕ}
    (B : T → MPSTensor d D) (hB : Continuous B)
    (F : Matrix (Fin d) (Fin r) ℂ) :
    Continuous fun t => traceQuotientTripleColumns (B t) F := by
  have hLC : ∀ x : Fin d → ℂ,
      Continuous fun t => Fintype.linearCombination ℂ (B t) x := by
    intro x
    simpa only [Fintype.linearCombination_apply, Pi.smul_apply, Function.comp_apply] using
      continuous_finsetSum Finset.univ fun i _ =>
        ((continuous_apply i).comp hB).const_smul (x i)
  apply continuous_matrix
  intro j ab
  exact ((hLC (F *ᵥ Pi.single ab.1 1)).matrix_mul
    (hLC (F *ᵥ Pi.single ab.2 1))).matrix_mul
      ((continuous_apply j).comp hB) |>.matrix_trace


private theorem rank_traceGram_of_pair {d D : ℕ} (A : MPSTensor d D)
    (hA : Kraus.IsInjective A) (G : Matrix (Fin d) (Fin d) ℂ)
    (α₂ : ℂ) (hα₂ : α₂ ≠ 0)
    (hG : ∀ j i, G j i = α₂ * Matrix.trace (A i * A j)) :
    G.rank = D * D := by
  have hMap : G.mulVecLin =
      α₂ • (MPSTensor.traceMulRightPi A).comp (Fintype.linearCombination ℂ A) := by
    exact LinearMap.ext fun x => by
      simpa only [Matrix.mul_one, Matrix.one_mulVec, Matrix.coe_mulVecLin, LinearMap.comp_apply,
        LinearMap.smul_apply] using traceQuotientSection_pair A G
        (1 : Matrix (Fin d) (Fin d) ℂ) α₂ hG x
  rw [Matrix.rank, hMap, LinearMap.range_smul _ α₂ hα₂,
    LinearMap.range_comp_of_range_eq_top _
      ((Fintype.range_linearCombination ℂ A).trans hA),
    LinearMap.finrank_range_of_inj
      (LinearMap.ker_eq_bot.mp (MPSTensor.traceMulRightPi_ker_eq_bot hA))]
  simp [Module.finrank_matrix]

/-- A continuous raw tensor family with injective pointwise realizations of
constant minimal dimension admits locally continuous associative quotient
multiplication. The normalized matrix-algebra identifications are pointwise;
no continuity of the realizations or their normalization scalars is assumed.
Auxiliary context: arXiv:1010.3732, Section II.F.2, lines 953–993. -/
theorem exists_local_continuous_traceQuotientAlgebra
    {T : Type*} [TopologicalSpace T] {d r K : ℕ}
    (B : T → MPSTensor d K) (hB : Continuous B)
    (G : T → Matrix (Fin d) (Fin d) ℂ)
    (hG : ∀ t j i, G t j i = Matrix.trace (B t i * B t j))
    (D : T → ℕ) (hD : ∀ t, D t * D t = r)
    (A : ∀ t, MPSTensor d (D t)) (hA : ∀ t, Kraus.IsInjective (A t))
    (α₂ α₃ : T → ℂ) (hα₂ : ∀ t, α₂ t ≠ 0) (hα₃ : ∀ t, α₃ t ≠ 0)
    (hPair : ∀ t i j, Matrix.trace (B t i * B t j) =
      α₂ t * Matrix.trace (A t i * A t j))
    (hTriple : ∀ t i k j, Matrix.trace (B t i * B t k * B t j) =
      α₃ t * Matrix.trace (A t i * A t k * A t j)) (t₀ : T) :
    ∃ (F : Matrix (Fin d) (Fin r) ℂ) (S : Set T), IsOpen S ∧ t₀ ∈ S ∧
      ContinuousOn (fun t => traceQuotientProductCoordinates (G t) F
        (traceQuotientTripleColumns (B t) F)) S ∧
      ∀ t ∈ S,
        let μ := fun x y : Fin r → ℂ =>
          traceQuotientProductCoordinates (G t) F (traceQuotientTripleColumns (B t) F) *ᵥ
            (fun ij => x ij.1 * y ij.2)
        ∃ E : (Fin r → ℂ) ≃ₗ[ℂ] Matrix (Fin (D t)) (Fin (D t)) ℂ,
          (∀ x, E x = (α₃ t / α₂ t) • Fintype.linearCombination ℂ (A t) (F *ᵥ x)) ∧
          (∀ x y, E (μ x y) = E x * E y) ∧
          (∀ x y z, μ (μ x y) z = μ x (μ y z)) := by
  have hGC : Continuous G := by
    apply continuous_matrix
    intro j i
    simpa only [hG, Function.comp_apply] using (((continuous_apply i).comp hB).matrix_mul
      ((continuous_apply j).comp hB)).matrix_trace
  have hRank : ∀ t, (G t).rank = r := fun t =>
    (rank_traceGram_of_pair (A t) (hA t) (G t) (α₂ t) (hα₂ t)
      (fun j i => (hG t j i).trans (hPair t i j))).trans (hD t)
  obtain ⟨F, S, hS, ht₀, hCont, hSection⟩ :=
    exists_local_continuous_traceQuotientProductCoordinates G hGC hRank t₀
      (fun F t => traceQuotientTripleColumns (B t) F)
      (fun F => continuous_traceQuotientTripleColumns B hB F)
  exact ⟨F, S, hS, ht₀, hCont, fun t ht =>
    traceQuotientProductCoordinates_algebraRecovery_of_two_three_trace_eq
      (A t) (B t) (G t) (hG t) F (α₂ t) (α₃ t) (hα₂ t) (hα₃ t)
      (hD t).symm (hSection t ht).1 (hPair t) (hTriple t)⟩

end Matrix
