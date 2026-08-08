/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Schwarz.TwoPositive
import TNLean.Channel.PartialTranspose
import TNLean.Channel.TensorMap

/-!
# Decomposable positive maps preserve positivity on PPT states

Wolf Chapter 3 defines a **decomposable** positive map `E` as a sum `E = Ecp + Eccp`
of a completely positive map and a completely copositive map. This file records the
structural fact that makes decomposable maps unable to detect PPT-entangled states:
if `ρ` is positive semidefinite with positive partial transpose (`ρ` is a PPT
state), then the ampliation `(E ⊗ id)(ρ)` of a decomposable `E` is again positive
semidefinite. Contrapositively, exhibiting a PPT state `ρ` on which `(E ⊗ id)(ρ)`
fails to be positive semidefinite proves that the positive map `E` is
indecomposable — the standard route for constructing indecomposable positive maps
and nondecomposable entanglement witnesses.

## Main declarations

* `Matrix.tensorMapId_comp_transposeLinearMapComplex` -- ampliating a map
  precomposed with transposition equals ampliating the map itself after taking the
  first-factor partial transpose of the input.
* `IsCPMap.tensorMapId_posSemidef` -- the ampliation of a completely positive map
  sends positive semidefinite bipartite matrices to positive semidefinite matrices.
* `IsDecomposablePositiveMap.tensorMapId_posSemidef_of_isPPT` -- the ampliation of
  a decomposable positive map sends PPT states to positive semidefinite matrices.
* `not_isDecomposablePositiveMap_of_isPPT_not_tensorMapId_posSemidef` -- a PPT
  state detected by the ampliation of `E` witnesses that `E` is not decomposable.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 3][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix

variable {d : ℕ}

namespace Matrix

/-- Ampliating `F` precomposed with transposition equals ampliating `F` after
taking the first-factor partial transpose of the input. Both sides evaluate `F`
on the matrix `X(j₁, i₂)(i₁, j₂)` at entry `(i₁, j₁)`: the left side transposes the
`(i₂, j₂)`-slice of `X` before feeding it to `F`, and the right side reads that
same transposed slice directly off `partialTransposeLeft X`. -/
theorem tensorMapId_comp_transposeLinearMapComplex {d' : ℕ}
    (F : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ)
    (X : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    tensorMapId (F.comp (Matrix.transposeLinearMapComplex (Fin d))) X
      = tensorMapId F (partialTransposeLeft X) := by
  have hslice : ∀ i₂ j₂ : Fin d,
      (bipartiteSlice X i₂ j₂)ᵀ = bipartiteSlice (partialTransposeLeft X) i₂ j₂ := by
    intro i₂ j₂
    ext i₁ j₁
    simp [Matrix.transpose_apply, partialTransposeLeft_apply]
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  change (F ((bipartiteSlice X i₂ j₂)ᵀ)) i₁ j₁
      = (F (bipartiteSlice (partialTransposeLeft X) i₂ j₂)) i₁ j₁
  rw [hslice]

/-- The ampliation of a completely positive map sends positive semidefinite
bipartite matrices to positive semidefinite matrices: this is exactly the
statement that `E` is `d`-positive, unfolded at the ancilla dimension matching
`E`'s domain. -/
theorem _root_.IsCPMap.tensorMapId_posSemidef
    {E : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ} (hE : IsCPMap E)
    {ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ} (hρ : ρ.PosSemidef) :
    (tensorMapId E ρ).PosSemidef :=
  hE.isNPositiveMap d ρ hρ

end Matrix

/-- **Decomposable maps cannot detect PPT entanglement (Wolf Ch. 3).** If `E` is a
decomposable positive map and `ρ` is a PPT state (positive semidefinite with
positive partial transpose), then the ampliation `(E ⊗ id)(ρ)` is positive
semidefinite. The completely positive summand preserves positivity of `ρ`
directly; the completely copositive summand preserves positivity of `ρ`'s
partial transpose, which is exactly the PPT hypothesis. -/
theorem IsDecomposablePositiveMap.tensorMapId_posSemidef_of_isPPT
    {E : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ}
    (hE : IsDecomposablePositiveMap E)
    {ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (hρ : ρ.PosSemidef) (hPPT : Matrix.IsPPT ρ) :
    (Matrix.tensorMapId E ρ).PosSemidef := by
  obtain ⟨Ecp, Eccp, hcp, hccp, rfl⟩ := hE
  have hsum : Matrix.tensorMapId (Ecp + Eccp) ρ
      = Matrix.tensorMapId Ecp ρ + Matrix.tensorMapId Eccp ρ := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    simp [Matrix.tensorMapId_apply, LinearMap.add_apply, Matrix.add_apply]
  rw [hsum]
  have h1 : (Matrix.tensorMapId Ecp ρ).PosSemidef := hcp.tensorMapId_posSemidef hρ
  have heq : Matrix.tensorMapId (Eccp.comp (Matrix.transposeLinearMapComplex (Fin d)))
      (Matrix.partialTransposeLeft ρ) = Matrix.tensorMapId Eccp ρ := by
    rw [Matrix.tensorMapId_comp_transposeLinearMapComplex Eccp (Matrix.partialTransposeLeft ρ),
      Matrix.partialTransposeLeft_partialTransposeLeft]
  have h2 : (Matrix.tensorMapId Eccp ρ).PosSemidef :=
    heq ▸ (hccp.tensorMapId_posSemidef hPPT)
  exact h1.add h2

/-- **Witness criterion for indecomposability (Wolf Ch. 3).** A PPT state on
which the ampliation of a positive map `E` fails to be positive semidefinite
witnesses that `E` is not decomposable, since decomposable maps preserve
positivity on PPT states
(`IsDecomposablePositiveMap.tensorMapId_posSemidef_of_isPPT`). -/
theorem not_isDecomposablePositiveMap_of_isPPT_not_tensorMapId_posSemidef
    {E : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ}
    {ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (hρ : ρ.PosSemidef) (hPPT : Matrix.IsPPT ρ)
    (hneg : ¬ (Matrix.tensorMapId E ρ).PosSemidef) :
    ¬ IsDecomposablePositiveMap E :=
  fun hE => hneg (hE.tensorMapId_posSemidef_of_isPPT hρ hPPT)
