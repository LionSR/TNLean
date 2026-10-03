/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixGramLeftInverse
import TNLean.Algebra.MatrixFixedSection
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Coordinates for multiplication on a trace quotient

Let G be the complex-bilinear two-site trace form and F a fixed section of its
coefficient quotient. The matrix C = G F carries these coordinates into the
trace-dual space. The positive Hermitian Gram matrix C† C is used only to invert
this section; it is distinct from the bilinear form G. Contracted three-site
trace data R then give multiplication coefficients (C† C)⁻¹ C† R.

This file establishes continuity of those coefficients on a constant-rank
neighborhood where a fixed section persists (see
`TNLean.Algebra.MatrixFixedSection`). Identifying the coefficients with the
quotient product is a separate algebraic step.
Auxiliary context: arXiv:1010.3732, Section II.F.2, lines 953–993.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder

namespace Matrix

/-- Multiplication coordinates obtained by inverting the positive Hermitian
Gram matrix of a fixed section of the trace quotient. -/
noncomputable def traceQuotientProductCoordinates {d r : ℕ}
    (G : Matrix (Fin d) (Fin d) ℂ) (F : Matrix (Fin d) (Fin r) ℂ)
    (R : Matrix (Fin d) (Fin r × Fin r) ℂ) :
    Matrix (Fin r) (Fin r × Fin r) ℂ :=
  ((G * F)ᴴ * (G * F))⁻¹ * (G * F)ᴴ * R

/-- Continuous two- and three-site trace data yield continuous multiplication
coordinates whenever the chosen section is injective. -/
theorem continuous_traceQuotientProductCoordinates
    {T : Type*} [TopologicalSpace T] {d r : ℕ}
    (G : T → Matrix (Fin d) (Fin d) ℂ) (hG : Continuous G)
    (F : Matrix (Fin d) (Fin r) ℂ)
    (R : T → Matrix (Fin d) (Fin r × Fin r) ℂ) (hR : Continuous R)
    (hInj : ∀ t, Function.Injective (G t * F).mulVec) :
    Continuous fun t => traceQuotientProductCoordinates (G t) F (R t) := by
  have hC : Continuous fun t => G t * F := hG.matrix_mul continuous_const
  exact (continuous_gramLeftInverse _ hC hInj).matrix_mul hR

/-- A constant-rank two-site trace family and continuous contracted three-site
trace data admit continuous multiplication coordinates on a fixed local section. -/
theorem exists_open_continuous_traceQuotientProductCoordinates
    {T : Type*} [TopologicalSpace T] {d r : ℕ}
    (G : T → Matrix (Fin d) (Fin d) ℂ) (hG : Continuous G)
    (hRank : ∀ t, (G t).rank = r) (t₀ : T)
    (F : Matrix (Fin d) (Fin r) ℂ)
    (hBase : Function.Injective (G t₀ * F).mulVec)
    (R : T → Matrix (Fin d) (Fin r × Fin r) ℂ) (hR : Continuous R) :
    ∃ S : Set T, IsOpen S ∧ t₀ ∈ S ∧
      ContinuousOn (fun t => traceQuotientProductCoordinates (G t) F (R t)) S ∧
      ∀ t ∈ S, Function.Injective (G t * F).mulVec ∧
        LinearMap.range (G t * F).mulVecLin = LinearMap.range (G t).mulVecLin := by
  obtain ⟨S, hS, ht₀, hSection⟩ := exists_open_fixedSection_range G hG hRank t₀ F hBase
  refine ⟨S, hS, ht₀, ?_, hSection⟩
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_traceQuotientProductCoordinates
    (fun t : S => G t) (hG.comp continuous_subtype_val) F
    (fun t : S => R t) (hR.comp continuous_subtype_val)
    (fun t => (hSection t t.property).1)

/-- Continuous trace data of constant rank admit locally continuous quotient
multiplication coordinates, with the base section supplied as a conclusion. -/
theorem exists_local_continuous_traceQuotientProductCoordinates
    {T : Type*} [TopologicalSpace T] {d r : ℕ}
    (G : T → Matrix (Fin d) (Fin d) ℂ) (hG : Continuous G)
    (hRank : ∀ t, (G t).rank = r) (t₀ : T)
    (R : Matrix (Fin d) (Fin r) ℂ → T → Matrix (Fin d) (Fin r × Fin r) ℂ)
    (hR : ∀ F, Continuous (R F)) :
    ∃ (F : Matrix (Fin d) (Fin r) ℂ) (S : Set T), IsOpen S ∧ t₀ ∈ S ∧
      ContinuousOn (fun t => traceQuotientProductCoordinates (G t) F (R F t)) S ∧
      ∀ t ∈ S, Function.Injective (G t * F).mulVec ∧
        LinearMap.range (G t * F).mulVecLin = LinearMap.range (G t).mulVecLin := by
  obtain ⟨F, hF⟩ := exists_fixedSection_of_rank (G t₀) (hRank t₀)
  obtain ⟨S, hS⟩ := exists_open_continuous_traceQuotientProductCoordinates
    G hG hRank t₀ F hF (R F) (hR F)
  exact ⟨F, S, hS⟩

end Matrix
