/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Channel.PhysicalPortDilation
import QICLean.Channel.MaximalOverlap
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Pure outputs of actual physical-port unitary dilations

If an actual physical-port channel sends a pure input to a normalized pure
output, its compiled unitary dilation produces that output tensored with a
normalized pure environment vector. The same physical ports and intersite
depth are retained. The environment is derived from the actual joint output;
no system--environment factorization is supplied as a premise.

Source context: Piroli, Styliaris and Cirac, arXiv:2103.13367, main text
"Quantum circuits and LOCC" and "State transformations with QC and LOCC".
The environment need not be a product over spatial sites or reset to zero.
This result does not assert a source QCcc block decomposition or control order.
-/

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder

namespace QuantumCircuit

private theorem exists_product_of_pure_marginal
    {S E : Type*} [Fintype S] [Fintype E]
    (Ω : S × E → ℂ) (φ : S → ℂ) (hφ : star φ ⬝ᵥ φ = 1)
    (hMarginal : partialTraceRight (vecMulVec Ω (star Ω)) = vecMulVec φ (star φ)) :
    ∃ η : E → ℂ, star η ⬝ᵥ η = 1 ∧ ∀ s e, Ω (s, e) = φ s * η e := by
  classical
  let C := schmidtCoeffMatrix Ω
  let P := vecMulVec φ (star φ)
  have hGram : C * Cᴴ = P :=
    (partialTraceRight_vecMulVec_eq Ω).symm.trans hMarginal
  have hIdem : P * P = P := by
    dsimp [P]
    rw [vecMulVec_mul_vecMulVec, hφ, one_smul]
  have hzero : (1 - P) * (C * Cᴴ) = 0 := by
    rw [hGram, Matrix.sub_mul, Matrix.one_mul, hIdem, sub_self]
  have hFix : P * C = C := by
    have h := (Matrix.mul_self_mul_conjTranspose_eq_zero C (1 - P)).mp hzero
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h
    exact h.symm
  let η : E → ℂ := (star φ) ᵥ* C
  have hfactor (s : S) (e : E) : Ω (s, e) = φ s * η e := by
    calc
      Ω (s, e) = C s e := rfl
      _ = (P * C) s e := congrArg (fun M ↦ M s e) hFix.symm
      _ = φ s * η e := by
        change (vecMulVec φ (star φ) * C) s e = φ s * η e
        rw [vecMulVec_mul]
        rfl
  have hTotal : star Ω ⬝ᵥ Ω = 1 := by
    calc
      _ = Ω ⬝ᵥ star Ω := dotProduct_comm _ _
      _ = Matrix.trace (vecMulVec Ω (star Ω)) := (trace_vecMulVec _ _).symm
      _ = Matrix.trace (partialTraceRight (vecMulVec Ω (star Ω))) :=
        (trace_partialTraceRight _).symm
      _ = Matrix.trace (vecMulVec φ (star φ)) := congrArg Matrix.trace hMarginal
      _ = φ ⬝ᵥ star φ := trace_vecMulVec _ _
      _ = 1 := (dotProduct_comm _ _).trans hφ
  have hProduct : star Ω ⬝ᵥ Ω = (star φ ⬝ᵥ φ) * (star η ⬝ᵥ η) := by
    simp only [dotProduct, Fintype.sum_prod_type, Pi.star_apply, hfactor,
      star_mul', Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro e _
    ring
  refine ⟨η, ?_, hfactor⟩
  rw [hφ, one_mul] at hProduct
  exact hProduct.symm.trans hTotal

variable {d N W : ℕ} [NeZero d] [NeZero N]

/-- An exact pure output of a physical-port channel has an actual unitary
realization whose complete output factors into that pure system vector and
a derived normalized environment vector. All fresh environments start in
the existing product-zero initializer, and the intersite depth is unchanged.
No reset or spatial product condition on the final environment is asserted.
Source: arXiv:2103.13367, the pure-state transformation convention in the
main-text paragraphs "Quantum circuits and LOCC" and "State transformations
with QC and LOCC". -/
theorem IsPhysicalPortProtocol.exists_appended_unitary_dilation_pure_output
    {P : PhysicalPortLayout N W} {T : ℕ}
    {Φ : Module.End ℂ (Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ)}
    (hΦ : IsPhysicalPortProtocol P T Φ)
    (ψ φ : (Fin W → Fin d) → ℂ) (hφ : star φ ⬝ᵥ φ = 1)
    (hOutput : Φ (vecMulVec ψ (star ψ)) = vecMulVec φ (star φ)) :
    ∃ A : ℕ, ∃ owner : Fin A → Fin N,
      ∃ U : Matrix (Fin (W + A) → Fin d) (Fin (W + A) → Fin d) ℂ,
        ∃ η : (Fin A → Fin d) → ℂ,
          IsPhysicalPortUnitary (P.append owner) T U ∧
          discardAppendedEnvironment W A d ∘ₗ singleKrausMap U ∘ₗ
            appendEnvironmentInput W A d = Φ ∧
          star η ⬝ᵥ η = 1 ∧ ∀ x e,
            ((appendMatrixSplit W A d U) *ᵥ
              (fixedEnvEmbedding (0 : Fin A → Fin d) *ᵥ ψ)) (x, e) = φ x * η e := by
  obtain ⟨A, owner, U, hU, hDilation⟩ := hΦ.exists_appended_unitary_dilation
  let Ω := (appendMatrixSplit W A d U) *ᵥ
    (fixedEnvEmbedding (0 : Fin A → Fin d) *ᵥ ψ)
  have hMarginal : partialTraceRight (vecMulVec Ω (star Ω)) = vecMulVec φ (star φ) := by
    have h := LinearMap.congr_fun hDilation (vecMulVec ψ (star ψ))
    change discardAppendedEnvironment W A d
      (U * appendEnvironmentInput W A d (vecMulVec ψ (star ψ)) * Uᴴ) = _ at h
    rw [discardAppendedEnvironment_conj] at h
    change partialTraceRight
      (appendMatrixSplit W A d U *
        (fixedEnvEmbedding (0 : Fin A → Fin d) * vecMulVec ψ (star ψ) *
          (fixedEnvEmbedding (0 : Fin A → Fin d))ᴴ) *
        (appendMatrixSplit W A d U)ᴴ) = _ at h
    simp only [mul_vecMulVec, vecMulVec_mul, ← star_mulVec] at h
    exact h.trans hOutput
  obtain ⟨η, hη, hfactor⟩ := exists_product_of_pure_marginal Ω φ hφ hMarginal
  exact ⟨A, owner, U, η, hU, hDilation, hη, hfactor⟩

end QuantumCircuit
