/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Chain.Defs

/-!
# The two-site cyclic MPS bond-uniformity claim is false

The Applications-section corollary of arXiv:1804.04964, printed at line 1804
of `Papers/1804.04964/paper_normal.tex`, omits the standing assumption that the
chain has at least three sites.  This file gives a nondegenerate two-site
counterexample to its bond-uniformity conclusion.

Take physical dimension two and virtual dimensions `D₁ = 1`, `D₂ = 2`.
For the standard basis vectors `e₀,e₁`, let the first tensor consist of the
rows `eᵢᵀ` and the second tensor of the columns `eᵢ`.  Both local maps from
the two-dimensional virtual space to the two-dimensional physical space are
isomorphisms.  Their two-site coefficient is

\[
  \operatorname{tr}(A_1^i A_2^j)=\delta_{ij}
    =\operatorname{tr}(A_2^i A_1^j),
\]

so the state is invariant under the cyclic shift, although `D₁ ≠ D₂`.

This is a genuine positive-dimensional example, not a zero-bond degeneracy.
It explains why the source's injective MPS Fundamental Theorem is stated for
at least three sites at lines 688--725 and why the surrounding section declares
that standing hypothesis at line 145.

## Reference

* Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Applications-section corollary and proof, lines 1803--1890 of the local
  source.
-/

open scoped Matrix

namespace TNLean
namespace PEPS
namespace CycleMPSTwoSiteCounterexample

/-- A rectangular MPS tensor is injective when its virtual basis vectors give
a linearly independent family of physical vectors.

This is the two-leg form of the source definition at arXiv:1804.04964,
lines 196--205. -/
def IsRectangularInjective {d Dₗ Dᵣ : ℕ}
    (A : Fin d → Matrix (Fin Dₗ) (Fin Dᵣ) ℂ) : Prop :=
  LinearIndependent ℂ (fun p : Fin Dₗ × Fin Dᵣ ↦ fun i ↦ A i p.1 p.2)

/-- The coefficient equality expressing invariance of a two-site closed MPS
under the cyclic shift of its two local tensors.

Source: arXiv:1804.04964, lines 1807--1827. -/
def IsTwoSiteCyclicShiftInvariantState {d D₁ D₂ : ℕ}
    (A₁ : Fin d → Matrix (Fin D₁) (Fin D₂) ℂ)
    (A₂ : Fin d → Matrix (Fin D₂) (Fin D₁) ℂ) : Prop :=
  ∀ i j, Matrix.trace (A₁ i * A₂ j) = Matrix.trace (A₂ i * A₁ j)

/-- The first tensor: the two standard row vectors in `Mat₁×₂(ℂ)`. -/
noncomputable def rowTensor (i : Fin 2) : Matrix (Fin 1) (Fin 2) ℂ :=
  fun _ b ↦ (Pi.single b (1 : ℂ) : Fin 2 → ℂ) i

/-- The second tensor: the two standard column vectors in `Mat₂×₁(ℂ)`. -/
noncomputable def columnTensor (i : Fin 2) : Matrix (Fin 2) (Fin 1) ℂ :=
  fun b _ ↦ (Pi.single b (1 : ℂ) : Fin 2 → ℂ) i

/-- The two row tensors form a basis of the two-dimensional physical space. -/
theorem rowTensor_isRectangularInjective :
    IsRectangularInjective rowTensor := by
  have hinj : Function.Injective (fun p : Fin 1 × Fin 2 ↦ p.2) := by
    intro p q hpq
    exact Prod.ext (Subsingleton.elim _ _) hpq
  have h := (Pi.basisFun ℂ (Fin 2)).linearIndependent.comp
    (fun p : Fin 1 × Fin 2 ↦ p.2) hinj
  rw [IsRectangularInjective]
  convert h using 1
  funext p i
  simp [rowTensor, Pi.basisFun_apply]

/-- The two column tensors form a basis of the two-dimensional physical space. -/
theorem columnTensor_isRectangularInjective :
    IsRectangularInjective columnTensor := by
  have hinj : Function.Injective (fun p : Fin 2 × Fin 1 ↦ p.1) := by
    intro p q hpq
    exact Prod.ext hpq (Subsingleton.elim _ _)
  have h := (Pi.basisFun ℂ (Fin 2)).linearIndependent.comp
    (fun p : Fin 2 × Fin 1 ↦ p.1) hinj
  rw [IsRectangularInjective]
  convert h using 1
  funext p i
  simp [columnTensor, Pi.basisFun_apply]

/-- The row--column contraction is the Kronecker delta. -/
theorem trace_rowTensor_mul_columnTensor (i j : Fin 2) :
    Matrix.trace (rowTensor i * columnTensor j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [rowTensor, columnTensor, Matrix.trace, Matrix.mul_apply, Pi.single_apply]

/-- The column--row contraction has the same trace, by the same direct
Kronecker-delta calculation. -/
theorem trace_columnTensor_mul_rowTensor (i j : Fin 2) :
    Matrix.trace (columnTensor i * rowTensor j) = if i = j then 1 else 0 := by
  rw [Matrix.trace_mul_comm, trace_rowTensor_mul_columnTensor]
  simp only [eq_comm]

/-- The state of the rectangular two-site chain is invariant under its cyclic
shift. -/
theorem twoSite_cyclicShiftInvariant :
    IsTwoSiteCyclicShiftInvariantState rowTensor columnTensor := by
  intro i j
  rw [trace_rowTensor_mul_columnTensor, trace_columnTensor_mul_rowTensor]

/-- The literal two-site bond-uniformity specialization of the source
corollary at arXiv:1804.04964, line 1804. -/
def TwoSiteBondUniformityStatement : Prop :=
  ∀ {d D₁ D₂ : ℕ}
    (A₁ : Fin d → Matrix (Fin D₁) (Fin D₂) ℂ)
    (A₂ : Fin d → Matrix (Fin D₂) (Fin D₁) ℂ),
    0 < D₁ →
    0 < D₂ →
    IsRectangularInjective A₁ →
    IsRectangularInjective A₂ →
    IsTwoSiteCyclicShiftInvariantState A₁ A₂ →
    D₁ = D₂

/-- **False source result:** The source corollary is false when read literally
at two sites: the
positive-dimensional tensors `rowTensor`, `columnTensor` satisfy both local
injectivity hypotheses and cyclic state invariance, but their adjacent bond
dimensions are `1` and `2`.

Source: arXiv:1804.04964, Applications-section corollary, lines 1803--1804.
The false printed statement and its corrected at-least-three-site scope are
documented in
`docs/paper-gaps/peps_cyclic_mps_two_site_bond_uniformity.tex`. -/
theorem twoSiteBondUniformityStatement_false :
    ¬ TwoSiteBondUniformityStatement := by
  intro h
  have hdim := h rowTensor columnTensor (by omega) (by omega)
    rowTensor_isRectangularInjective columnTensor_isRectangularInjective
    twoSite_cyclicShiftInvariant
  omega

end CycleMPSTwoSiteCounterexample
end PEPS
end TNLean
