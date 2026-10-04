/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixGramLeftInverse
import TNLean.Algebra.MatrixBilinearCoordinates
import TNLean.MPS.Structure.ContinuousTraceQuotientMultiplication
import TNLean.MPS.Core.TracePairing
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Matrix-algebra recovery from finite-ring trace data

A section of the two-site trace quotient identifies its coordinates with the
minimal bond matrix space. Contracting the three-site vector with that section
recovers a product on the coordinates. If the two-site and three-site raw
vectors are proportional to those of a minimal tensor by nonzero scalars
α₂ and α₃, the product is transported by (α₃ / α₂) times the minimal coefficient
map. It is therefore associative and isomorphic to the full matrix algebra.

These are finite-data consequences relevant to tensor reconstruction in
arXiv:1010.3732, Section II.F.2, lines 953–993. Combined with a continuous
full-rank section, they yield continuous quotient multiplication at constant
rank. They do not construct a continuous unital tensor realization across a
change of minimal bond dimension. That analytic step remains separate; see
`docs/paper-gaps/spc11_spt_interpolation_upper_range.tex`.

The two-site trace form is complex bilinear, not Hermitian positive. Only the
Gram matrix of the coordinate section is used as a positive matrix. The
pointwise minimal tensor and its coordinate identification need not be
continuous. Zero-dimensional matrix algebras are allowed, and no scalar
consistency identity is asserted in that case.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open scoped Matrix BigOperators ComplexOrder

namespace Matrix
/-- The raw three-site trace vector contracted with two columns of a physical
coefficient section.
Auxiliary context: arXiv:1010.3732, Section II.F.2, lines 953–993. -/
noncomputable def traceQuotientTripleColumns {d r D : ℕ}
    (B : MPSTensor d D) (F : Matrix (Fin d) (Fin r) ℂ) :
    Matrix (Fin d) (Fin r × Fin r) ℂ :=
  Matrix.of fun j ab => Matrix.trace
    (Fintype.linearCombination ℂ B (F *ᵥ Pi.single ab.1 1) *
      Fintype.linearCombination ℂ B (F *ᵥ Pi.single ab.2 1) * B j)

/-- Contracting the two-site trace form with a physical coefficient section
is trace pairing against the corresponding bond matrix.
Auxiliary context: arXiv:1010.3732, Section II.F.2, lines 953–993. -/
theorem traceQuotientSection_pair {d r D : ℕ} (A : MPSTensor d D)
    (G : Matrix (Fin d) (Fin d) ℂ) (F : Matrix (Fin d) (Fin r) ℂ) (α₂ : ℂ)
    (hG : ∀ j i, G j i = α₂ * Matrix.trace (A i * A j)) :
    ∀ x, (G * F) *ᵥ x = α₂ • MPSTensor.traceMulRightPi A
      (Fintype.linearCombination ℂ A (F *ᵥ x)) := by
  intro x
  ext j
  rw [← Matrix.mulVec_mulVec]
  simp only [Matrix.mulVec, dotProduct, hG,
    Fintype.linearCombination_apply, MPSTensor.traceMulRightPi_apply,
    Matrix.sum_mul, Matrix.trace_sum, Matrix.smul_mul, Matrix.trace_smul,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_comm, mul_left_comm]


/-- The three-site proportionality identity persists after contracting its
first two physical indices with arbitrary coefficient vectors.
Auxiliary context: arXiv:1010.3732, Section II.F.2, lines 953–993. -/
theorem traceQuotientSection_triple {d D E : ℕ}
    (A : MPSTensor d D) (B : MPSTensor d E) (α₃ : ℂ)
    (hTriple : ∀ i k j, Matrix.trace (B i * B k * B j) =
      α₃ * Matrix.trace (A i * A k * A j)) :
    ∀ u v j, Matrix.trace
      (Fintype.linearCombination ℂ B u * Fintype.linearCombination ℂ B v * B j) =
      α₃ * Matrix.trace
        (Fintype.linearCombination ℂ A u * Fintype.linearCombination ℂ A v * A j) := by
  intro u v j
  have hTriple' : ∀ i k j, Matrix.trace (B i * (B k * B j)) =
      α₃ * Matrix.trace (A i * (A k * A j)) := by
    simpa only [Matrix.mul_assoc] using hTriple
  simp only [Fintype.linearCombination_apply, Matrix.sum_mul,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
    smul_eq_mul, hTriple', Finset.mul_sum, mul_assoc, mul_left_comm]


/-- Contracted three-site columns determine the full bilinear product data.
Auxiliary context: arXiv:1010.3732, Section II.F.2, lines 953–993. -/
theorem traceQuotientProductColumns_triple {d r D : ℕ}
    (A : MPSTensor d D) (Q : (Fin r → ℂ) →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (R : Matrix (Fin d) (Fin r × Fin r) ℂ) (α₃ : ℂ)
    (hR : ∀ a b j, R j (a, b) = α₃ * Matrix.trace
      (Q (Pi.single a 1) * Q (Pi.single b 1) * A j)) :
    ∀ x y, R *ᵥ (fun ij => x ij.1 * y ij.2) =
      α₃ • MPSTensor.traceMulRightPi A (Q x * Q y) := by
  have hMaps : Matrix.toLinearMap₂' ℂ (Matrix.of fun a b => fun j => R j (a, b)) =
      α₃ • ((LinearMap.mul ℂ (Matrix (Fin D) (Fin D) ℂ)).compl₁₂ Q Q).compr₂
        (MPSTensor.traceMulRightPi A) := by
    ext a b j
    simpa [LinearMap.comp_apply, LinearMap.single_apply,
      Matrix.toLinearMap₂'_apply (R := ℂ), Pi.single_apply, ite_apply, Matrix.of_apply,
      LinearMap.smul_apply,
      LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.mul_apply',
      MPSTensor.traceMulRightPi_apply, Pi.smul_apply, smul_eq_mul] using hR a b j
  exact fun x y => by
    simpa only [toLinearMap₂'_apply_mulVec_prod, LinearMap.smul_apply,
      LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.mul_apply']
      using congrArg (fun f => f x y) hMaps


/-- Exact trace data recover the quotient product, including the ratio of
its two-site and three-site normalizations.
Auxiliary context: arXiv:1010.3732, Section II.F.2, lines 953–993. -/
theorem traceQuotientProductCoordinates_recover {d r D : ℕ}
    (A : MPSTensor d D) (Q : (Fin r → ℂ) ≃ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (G : Matrix (Fin d) (Fin d) ℂ) (F : Matrix (Fin d) (Fin r) ℂ)
    (R : Matrix (Fin d) (Fin r × Fin r) ℂ) (α₂ α₃ : ℂ) (hα₂ : α₂ ≠ 0)
    (hInj : Function.Injective (G * F).mulVec)
    (hPair : ∀ x, (G * F) *ᵥ x = α₂ • MPSTensor.traceMulRightPi A (Q x))
    (hTriple : ∀ x y, R *ᵥ (fun ij => x ij.1 * y ij.2) =
      α₃ • MPSTensor.traceMulRightPi A (Q x * Q y)) :
    ∀ x y, Q (traceQuotientProductCoordinates G F R *ᵥ
      (fun ij => x ij.1 * y ij.2)) = (α₃ / α₂) • (Q x * Q y) := by
  intro x y
  have hR : R *ᵥ (fun ij => x ij.1 * y ij.2) =
      (G * F) *ᵥ Q.symm ((α₃ / α₂) • (Q x * Q y)) := by
    simp only [hTriple, hPair, Q.apply_symm_apply, map_smul, smul_smul,
      mul_div_cancel₀ _ hα₂]
  rw [traceQuotientProductCoordinates, ← Matrix.mulVec_mulVec, hR,
    Matrix.mulVec_mulVec, Matrix.gramLeftInverse_mul (G * F) hInj,
    Matrix.one_mulVec, Q.apply_symm_apply]

/-- A full-rank section identifies the coefficient quotient with the bond
matrix space.
Auxiliary context: arXiv:1010.3732, Section II.F.2, lines 953–993. -/
theorem exists_linearEquiv_traceQuotientSection {d r D : ℕ}
    (A : MPSTensor d D) (Q : (Fin r → ℂ) →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (C : Matrix (Fin d) (Fin r) ℂ) (α₂ : ℂ)
    (hPair : ∀ x, C *ᵥ x = α₂ • MPSTensor.traceMulRightPi A (Q x))
    (hInj : Function.Injective C.mulVec) (hr : r = D * D) :
    ∃ E : (Fin r → ℂ) ≃ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ,
      E.toLinearMap = Q := by
  have hQ : Function.Injective Q := by
    intro x y hxy
    apply hInj
    simp only [hPair, hxy]
  have hdim : Module.finrank ℂ (Fin r → ℂ) =
      Module.finrank ℂ (Matrix (Fin D) (Fin D) ℂ) := by
    simpa [Module.finrank_matrix] using hr
  exact ⟨Q.linearEquivOfInjective hQ hdim, rfl⟩

/-- Trace quotient coordinates have an associative product and a normalized
multiplicative identification with the minimal bond matrix algebra.
Auxiliary context: arXiv:1010.3732, Section II.F.2, lines 953–993. -/
theorem traceQuotientProductCoordinates_algebraRecovery {d r D : ℕ}
    (A : MPSTensor d D) (Q : (Fin r → ℂ) →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (G : Matrix (Fin d) (Fin d) ℂ) (F : Matrix (Fin d) (Fin r) ℂ)
    (R : Matrix (Fin d) (Fin r × Fin r) ℂ) (α₂ α₃ : ℂ)
    (hα₂ : α₂ ≠ 0) (hα₃ : α₃ ≠ 0) (hr : r = D * D)
    (hInj : Function.Injective (G * F).mulVec)
    (hPair : ∀ x, (G * F) *ᵥ x = α₂ • MPSTensor.traceMulRightPi A (Q x))
    (hTriple : ∀ x y, R *ᵥ (fun ij => x ij.1 * y ij.2) =
      α₃ • MPSTensor.traceMulRightPi A (Q x * Q y)) :
    let μ := fun x y : Fin r → ℂ =>
      traceQuotientProductCoordinates G F R *ᵥ (fun ij => x ij.1 * y ij.2)
    ∃ E : (Fin r → ℂ) ≃ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ,
      (∀ x, E x = (α₃ / α₂) • Q x) ∧
      (∀ x y, E (μ x y) = E x * E y) ∧ (∀ x y z, μ (μ x y) z = μ x (μ y z)) := by
  dsimp only
  obtain ⟨E₀, hE₀⟩ := exists_linearEquiv_traceQuotientSection A Q (G * F)
    α₂ hPair hInj hr
  let E := E₀.trans (LinearEquiv.smulOfNeZero ℂ
    (Matrix (Fin D) (Fin D) ℂ) (α₃ / α₂) (div_ne_zero hα₃ hα₂))
  have hE : ∀ x, E x = (α₃ / α₂) • Q x := by
    intro x
    change (α₃ / α₂) • E₀ x = (α₃ / α₂) • Q x
    exact congrArg ((α₃ / α₂) • ·) (congrArg (fun f => f x) hE₀)
  have hRec := traceQuotientProductCoordinates_recover A E₀ G F R α₂ α₃
    hα₂ hInj (by simpa only [← hE₀, LinearEquiv.coe_coe] using hPair)
    (by simpa only [← hE₀, LinearEquiv.coe_coe] using hTriple)
  have hMul : ∀ x y, E (traceQuotientProductCoordinates G F R *ᵥ
      (fun ij => x ij.1 * y ij.2)) = E x * E y := by
    intro x y
    simp only [hE, ← hE₀, LinearEquiv.coe_coe, hRec, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  refine ⟨E, hE, hMul, fun x y z => E.injective ?_⟩
  rw [hMul, hMul, hMul, hMul, Matrix.mul_assoc]

/-- A section of the raw two-site trace form reconstructs an associative
matrix algebra from the raw three-site vector. The minimal tensor is used
only pointwise; its coefficient identification need not vary continuously.
Auxiliary context: arXiv:1010.3732, Section II.F.2, lines 953–993. -/
theorem traceQuotientProductCoordinates_algebraRecovery_of_two_three_trace_eq
    {d r D K : ℕ} (A : MPSTensor d D) (B : MPSTensor d K)
    (G : Matrix (Fin d) (Fin d) ℂ) (hG : ∀ j i, G j i = Matrix.trace (B i * B j))
    (F : Matrix (Fin d) (Fin r) ℂ) (α₂ α₃ : ℂ)
    (hα₂ : α₂ ≠ 0) (hα₃ : α₃ ≠ 0) (hr : r = D * D)
    (hInj : Function.Injective (G * F).mulVec)
    (hPair : ∀ i j, Matrix.trace (B i * B j) = α₂ * Matrix.trace (A i * A j))
    (hTriple : ∀ i k j, Matrix.trace (B i * B k * B j) =
      α₃ * Matrix.trace (A i * A k * A j)) :
    let μ := fun x y : Fin r → ℂ =>
      traceQuotientProductCoordinates G F (traceQuotientTripleColumns B F) *ᵥ
        (fun ij => x ij.1 * y ij.2)
    ∃ E : (Fin r → ℂ) ≃ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ,
      (∀ x, E x = (α₃ / α₂) • Fintype.linearCombination ℂ A (F *ᵥ x)) ∧
      (∀ x y, E (μ x y) = E x * E y) ∧
      (∀ x y z, μ (μ x y) z = μ x (μ y z)) := by
  apply traceQuotientProductCoordinates_algebraRecovery A
    ((Fintype.linearCombination ℂ A).comp F.mulVecLin) G F
    (traceQuotientTripleColumns B F) α₂ α₃ hα₂ hα₃ hr hInj
  · exact traceQuotientSection_pair A G F α₂
      (fun j i => (hG j i).trans (hPair i j))
  · apply traceQuotientProductColumns_triple A
      ((Fintype.linearCombination ℂ A).comp F.mulVecLin)
      (traceQuotientTripleColumns B F) α₃
    exact fun a b j => traceQuotientSection_triple A B α₃ hTriple
      (F *ᵥ Pi.single a 1) (F *ᵥ Pi.single b 1) j

end Matrix
