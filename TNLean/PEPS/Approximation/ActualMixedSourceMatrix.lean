/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ActualPartySourceMatrix
import TNLean.PEPS.Approximation.BasisMatrixOperator
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Actual source columns with an intervening source-free word

An operator given by an actual source-free input word may be placed between the
literal chronological ket and bra columns. Changing the input coordinates to
party coordinates gives the product of the actual local mixed matrices. This
identity applies to each word in a sampled sum separately.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–355,
409–434 and 565–588.
-/

noncomputable section
open scoped Matrix
namespace TNLean.PEPS.PairEffect

private theorem mixed_toMatrix_basis_independent
    {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
    [DecidableEq I] [DecidableEq J]
    (b : OrthonormalBasis I ℂ E) (c : OrthonormalBasis J ℂ E)
    (d : OrthonormalBasis K ℂ F) (A B : E →ₗ[ℂ] F) (U : E →ₗ[ℂ] E) :
    LinearMap.toMatrix b.toBasis d.toBasis A *
        LinearMap.toMatrix b.toBasis b.toBasis U *
        (LinearMap.toMatrix b.toBasis d.toBasis B)ᴴ =
      LinearMap.toMatrix c.toBasis d.toBasis A *
        LinearMap.toMatrix c.toBasis c.toBasis U *
        (LinearMap.toMatrix c.toBasis d.toBasis B)ᴴ := by
  classical
  let : FiniteDimensional ℂ E := b.toBasis.finiteDimensional_of_finite
  let : FiniteDimensional ℂ F := d.toBasis.finiteDimensional_of_finite
  rw [← LinearMap.toMatrix_adjoint b d, ← LinearMap.toMatrix_adjoint c d,
    ← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp,
    ← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp]

/-- Combine literal column matrices and a grouped mixed-coordinate identity
before instantiating any dependent source-word data.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434 and 565–588. -/
private theorem mixed_matrix_eq_of_column_eq
    {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
    [DecidableEq I]
    (b : OrthonormalBasis I ℂ E) (c : OrthonormalBasis J ℂ E)
    (d : OrthonormalBasis K ℂ F) (A B : E →L[ℂ] F) (U : E →L[ℂ] E)
    (M N : Matrix K I ℂ) (H : Matrix K K ℂ)
    (hM : M = LinearMap.toMatrix b.toBasis d.toBasis A.toLinearMap)
    (hN : N = LinearMap.toMatrix b.toBasis d.toBasis B.toLinearMap)
    (hGrouped : Matrix.of (fun i j ↦ d.repr (A (c j)) i) *
      Matrix.of (fun i j ↦ c.repr (U (c j)) i) *
      (Matrix.of (fun i j ↦ d.repr (B (c j)) i))ᴴ = H) :
    M * LinearMap.toMatrix b.toBasis b.toBasis U.toLinearMap * Nᴴ = H := by
  classical
  have hcolumns := congrArg₂
    (fun M N : Matrix K I ℂ ↦
      M * LinearMap.toMatrix b.toBasis b.toBasis U.toLinearMap * Nᴴ) hM hN
  have hchange := mixed_toMatrix_basis_independent b c d
    A.toLinearMap B.toLinearMap U.toLinearMap
  have h := hGrouped
  simp only [matrix_repr_eval_eq_toMatrix] at h
  exact hcolumns.trans (hchange.trans h)


namespace SourceCircuit
variable {P : Type} [Fintype P] [DecidableEq P] {a b : Layout P}
variable {I O : Option {_p : P // true = true} → Type}
variable [∀ q, Fintype (I q)] [∀ q, Fintype (O q)]

open Classical in
/-- A literal source-input word between the actual prepared ket and bra columns
factors through its actual singleton restrictions. This is a coordinate identity
for an individual input word, without any factorization hypothesis on a sum.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–355,
409–434 and 565–588. -/
theorem partialSourceGlobalMatrix_mixed_word
    (w : SourceCircuit a b) (ψ : ProductInput a)
    (ξ ζ : Choices (fun _ : P ↦ true) w)
    (u : Word (w.allResidualSourceLayout ++ []) (w.allResidualSourceLayout ++ []))
    (hu : u.sources = [])
    (B : ∀ q, OrthonormalBasis (I q) ℂ
      (Mem (Layout.atParty q (w.allResidualSourceLayout ++ []))))
    (C : ∀ q, OrthonormalBasis (O q) ℂ
      (Mem (Layout.atParty q (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) b))))
    (ps : List (Option {_p : P // true = true})) (hn : ps.Nodup)
    (hc : ∀ q, q ∈ ps) :
    w.partialSourceGlobalMatrix ψ ξ
        (partyGroupedBasis (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) b)
          C ps hn hc) *
      LinearMap.toMatrix w.actualSourceInputBasis.toBasis w.actualSourceInputBasis.toBasis
        u.eval.toLinearMap *
      (w.partialSourceGlobalMatrix ψ ζ
        (partyGroupedBasis (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) b)
          C ps hn hc))ᴴ =
      dependentPhysicalProductFamilyMatrix (fun q ↦
        w.partialSourcePartyMatrix ψ ξ B C q *
          LinearMap.toMatrix (B q).toBasis (B q).toBasis
            (u.restrict (partySelector q) hu).eval.toLinearMap *
          (w.partialSourcePartyMatrix ψ ζ B C q)ᴴ) := by
  classical
  let bIn := partyGroupedBasis (w.allResidualSourceLayout ++ []) B ps hn hc
  let bOut := partyGroupedBasis
    (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) b) C ps hn hc
  refine mixed_matrix_eq_of_column_eq w.actualSourceInputBasis bIn bOut
    (w.partialSourceWord ψ ξ).eval (w.partialSourceWord ψ ζ).eval u.eval _ _ _
    (partialSourceGlobalMatrix_eq_toMatrix w ψ ξ bOut)
    (partialSourceGlobalMatrix_eq_toMatrix w ψ ζ bOut) ?_
  have hWord := Word.partyGroupedBasis_mixed_matrix (w.partialSourceWord ψ ξ)
    (w.partialSourceWord ψ ζ) u (sources_partialSourceWord w ψ ξ)
    (sources_partialSourceWord w ψ ζ) hu B C ps hn hc
  simp only [matrix_repr_eval_eq_toMatrix] at hWord
  simp only [bIn, bOut, partialSourcePartyMatrix,
    matrix_repr_eval_eq_toMatrix]
  convert hWord using 1
  rfl

end SourceCircuit
end TNLean.PEPS.PairEffect
