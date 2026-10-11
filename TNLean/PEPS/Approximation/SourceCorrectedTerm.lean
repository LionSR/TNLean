/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceCircuitSubstitution
import TNLean.Algebra.MatrixDensitySum

/-!
# Corrected source terms on the original circuit

A selected original source position carries a local ket label, a local bra
label, and independent endpoint coordinates on both sides. Basis substitutions
are zero at all other labels of the same gate. Thus different selected slots at
one gate retain their common local label, while the gate's scalar coefficient
appears only once on each side of the density calculation.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 338–381.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-subset-expansion.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.
-/

noncomputable section
open scoped TensorProduct Matrix ComplexConjugate
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type}

/-- Basis indices at the selected positions, including their original local gate labels.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 342–355. -/
def SourceBasisChoice {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w)) : Type :=
  ∀ e : S, branchLabels w e.1.1 ×
    (Fin (sourceDims w e.1).1 × Fin (sourceDims w e.1).2)

/-- The selected original local labels and endpoint coordinates form a finite type. -/
instance sourceBasisChoiceFintype {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w)) : Fintype (SourceBasisChoice w S) := by
  classical
  exact inferInstanceAs (Fintype (∀ e : S, branchLabels w e.1.1 ×
    (Fin (sourceDims w e.1).1 × Fin (sourceDims w e.1).2)))

/-- An endpoint basis tensor at the selected local label, and zero at other labels.
The values outside the selected positions are zero and will not be used.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 342–381. -/
def labelBasisVectors {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w)) (u : SourceBasisChoice w S)
    (e : sourceLocations w) (ξ : branchLabels w e.1) :
    euc (Fin (sourceDims w e).1) ⊗[ℂ] euc (Fin (sourceDims w e).2) := by
  classical
  exact if he : e ∈ S then
    if ξ = (u ⟨e, he⟩).1 then
      EuclideanSpace.basisFun (Fin (sourceDims w e).1) ℂ (u ⟨e, he⟩).2.1 ⊗ₜ[ℂ]
        EuclideanSpace.basisFun (Fin (sourceDims w e).2) ℂ (u ⟨e, he⟩).2.2
    else 0
  else 0

/-- The actual circuit matrix after a prescribed label-selective basis substitution.
Only the original input and output memories are given finite orthonormal coordinates.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 342–381. -/
def sourceBasisMatrix {m n : Type} [Fintype m] [Fintype n]
    {a b : Layout P} (w : SourceCircuit a b) (S : Finset (sourceLocations w))
    (u : SourceBasisChoice w S) (bIn : OrthonormalBasis n ℂ (Mem a))
    (bOut : OrthonormalBasis m ℂ (Mem b)) : Matrix m n ℂ := by
  classical
  exact LinearMap.toMatrix bIn.toBasis bOut.toBasis
    (evalWithSources w (selectedSourceVectors w S (labelBasisVectors w S u))).toLinearMap

/-- A corrected density term attached to original source positions and local label pairs.
This definition is independent of any affected set or partial expansion.
Source: polynomial-PEPS Theorem 5.2, `eq:compression-subset-expansion`,
`04-compression.tex`, lines 338–381. -/
def correctedSourceTerm {m n : Type} [Fintype m] [Fintype n]
    {a b : Layout P} (w : SourceCircuit a b) (S : Finset (sourceLocations w))
    (E : ∀ e : sourceLocations w, branchLabels w e.1 → branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).1 × Fin (sourceDims w e).2)
        (Fin (sourceDims w e).1 × Fin (sourceDims w e).2) ℂ)
    (bIn : OrthonormalBasis n ℂ (Mem a)) (bOut : OrthonormalBasis m ℂ (Mem b))
    (ρ : Matrix n n ℂ) : Matrix m m ℂ :=
  ∑ u : SourceBasisChoice w S, ∑ v : SourceBasisChoice w S,
    (∏ e : S, E e.1 (u e).1 (v e).1 (u e).2 (v e).2) •
      (sourceBasisMatrix w S u bIn bOut * ρ * (sourceBasisMatrix w S v bIn bOut)ᴴ)

open Classical in
/-- The empty corrected set is exactly the density of the original circuit.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 342–355. -/
theorem correctedSourceTerm_empty {m n : Type} [Fintype m] [Fintype n]
    {a b : Layout P} (w : SourceCircuit a b)
    (E : ∀ e : sourceLocations w, branchLabels w e.1 → branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).1 × Fin (sourceDims w e).2)
        (Fin (sourceDims w e).1 × Fin (sourceDims w e).2) ℂ)
    (bIn : OrthonormalBasis n ℂ (Mem a)) (bOut : OrthonormalBasis m ℂ (Mem b))
    (ρ : Matrix n n ℂ) :
    correctedSourceTerm w ∅ E bIn bOut ρ =
      LinearMap.toMatrix bIn.toBasis bOut.toBasis w.eval.toLinearMap * ρ *
        (LinearMap.toMatrix bIn.toBasis bOut.toBasis w.eval.toLinearMap)ᴴ := by
  let : Unique (SourceBasisChoice w ∅) := by
    unfold SourceBasisChoice
    infer_instance
  have hη (u : SourceBasisChoice w ∅) :
      selectedSourceVectors w ∅ (labelBasisVectors w ∅ u) = sourceVectorAt w := by
    funext e ξ
    simp [selectedSourceVectors]
  simp only [correctedSourceTerm, sourceBasisMatrix, hη, evalWithSources_original]
  simp only [Fintype.sum_unique]
  simp

/-- A label-selective basis substitution in an actual partial monomial, expressed
in the original input and output coordinates by the canonical owner isometries.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–381. -/
def partialSourceBasisMatrix {m n : Type} [Fintype m] [Fintype n]
    (A : P → Bool) {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w)) (u : SourceBasisChoice w S) (ξ : Choices A w)
    (bIn : OrthonormalBasis n ℂ (Mem a)) (bOut : OrthonormalBasis m ℂ (Mem b)) :
    Matrix m n ℂ := by
  classical
  exact LinearMap.toMatrix bIn.toBasis bOut.toBasis
    (isoL (Layout.mapOwnerIso (affectedOwner A) b).symm ∘L
      (partialWithSources A w (selectedSourceVectors w S (labelBasisVectors w S u)) ξ).eval ∘L
        isoL (Layout.mapOwnerIso (affectedOwner A) a)).toLinearMap

/-- The same original source basis substitution is obtained by expanding only
gates touching the affected parties. All other gates remain aggregate operators.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–381. -/
theorem sourceBasisMatrix_eq_sum_partial {m n : Type} [Fintype m] [Fintype n]
    (A : P → Bool) {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w)) (u : SourceBasisChoice w S)
    (hS : ∀ e ∈ S, A (endpoints w e).1 = true ∨ A (endpoints w e).2 = true)
    (bIn : OrthonormalBasis n ℂ (Mem a)) (bOut : OrthonormalBasis m ℂ (Mem b)) :
    sourceBasisMatrix w S u bIn bOut =
      ∑ ξ, coefficient A w ξ • partialSourceBasisMatrix A w S u ξ bIn bOut := by
  classical
  have h := eval_selectedSourceVectors_eq_sum A w S (labelBasisVectors w S u) hS
  ext i j
  have he := congrArg (fun z ↦
    bOut.toBasis.repr ((Layout.mapOwnerIso (affectedOwner A) b).symm z) i)
      (DFunLike.congr_fun h (bIn j))
  simpa [sourceBasisMatrix, partialSourceBasisMatrix, LinearMap.toMatrix_apply,
    comp_apply, sum_apply, smul_apply, isoL_apply, Matrix.sum_apply, Matrix.smul_apply]
    using he.symm

/-- The globally defined corrected term admits the partial expansion for every
mask meeting each selected source. The same original positions and local labels
are retained; gates outside the mask are not expanded.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–381. -/
theorem correctedSourceTerm_eq_sum_partial {m n : Type} [Fintype m] [Fintype n]
    (A : P → Bool) {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w))
    (hS : ∀ e ∈ S, A (endpoints w e).1 = true ∨ A (endpoints w e).2 = true)
    (E : ∀ e : sourceLocations w, branchLabels w e.1 → branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).1 × Fin (sourceDims w e).2)
        (Fin (sourceDims w e).1 × Fin (sourceDims w e).2) ℂ)
    (bIn : OrthonormalBasis n ℂ (Mem a)) (bOut : OrthonormalBasis m ℂ (Mem b))
    (ρ : Matrix n n ℂ) :
    correctedSourceTerm w S E bIn bOut ρ =
      ∑ ξ, ∑ ζ, (coefficient A w ξ * conj (coefficient A w ζ)) •
        (∑ u : SourceBasisChoice w S, ∑ v : SourceBasisChoice w S,
          (∏ e : S, E e.1 (u e).1 (v e).1 (u e).2 (v e).2) •
            (partialSourceBasisMatrix A w S u ξ bIn bOut * ρ *
              (partialSourceBasisMatrix A w S v ζ bIn bOut)ᴴ)) := by
  classical
  unfold correctedSourceTerm
  simp_rw [sourceBasisMatrix_eq_sum_partial A w S _ hS bIn bOut,
    Matrix.sum_smul_mul_mul_conjTranspose, Finset.smul_sum, smul_smul]
  conv_lhs => arg 2; ext u; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext ξ; arg 2; ext u; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext ξ; rw [Finset.sum_comm]
  simp only [mul_comm]

end TNLean.PEPS.PairEffect.SourceCircuit
