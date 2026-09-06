/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.InverseCompatibleSourceTransport
import TNLean.MPS.MPU.SourceXPhysicalNormalization

/-!
# Normalizations and physical closures of inverse-compatible source factors

The proved unitary transport of the first source factors preserves their
external Gram matrices and conjugates the first source-rank Gram matrix by
a unitary matrix. The second source factors remain unchanged. This transfers
the two physical $Y$ closures (`eq:MPUnice2`), the two source-rank $Y$
normalizations (`eq:MPUnice3`), and the two physical $X$ closures
(`eq:MPUnice4`) to the actual inverse-compatible source record.

Source: arXiv:2502.20257, the normalization transport following comparison
unitarity at `main.tex` lines 5486–5487. The rank normalizations and physical
$X$ closures retain the simplicity premise on the physical adjoint used by
the existing source results. This file does not eliminate that premise,
replace the canonical weight by the identity, or assert the complete
inverse-compatible proposition. Gate movement and truncated gates are not
addressed here; no transport of a chosen right inverse is asserted.
-/

open scoped ComplexOrder Matrix BigOperators

namespace MPOTensor

variable {d D : ℕ} (U : MPOTensor d D) (T : Matrix.unitaryGroup (Fin D) ℂ)
  (hU : IsMPUCanonicalFormII U) (hsimple : IsMPUSimple U)
  (hT : ∀ i j, physicalAdjointTensor U i j =
    (T : Matrix (Fin D) (Fin D) ℂ)ᴴ * U i j * T)
  (σ : ℂ) (hσ : (T : Matrix (Fin D) (Fin D) ℂ) *
    (T : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) = σ • 1)

/-- The two physical $Y$ closures hold for the actual inverse-compatible
record. The first follows from the external Gram equality; the second factor
is unchanged. No adjoint-simplicity premise is needed.
Source: arXiv:2502.20257, `eq:MPUnice2`, transported at lines 5486–5487. -/
theorem inverseCompatibleSourceFactors_Y_physical_contractions (p q : Fin d) :
    let S := inverseCompatibleSourceFactors U T hU hsimple hT σ hσ
    (∑ r : Fin r[U], ∑ α : Fin D,
      star (S.Y₁ r (α, p)) * S.Y₁ r (α, q)) = (if p = q then 1 else 0) ∧
    (∑ l : Fin ℓ[U], ∑ α : Fin D, ∑ β : Fin D,
      star (S.Y₂ l (p, α)) * S.Y₂ l (q, β) * hU.ρ β α) =
        (if p = q then 1 else 0) := by
  have hgram := (inverseCompatibleSourceFactors_gram_eq U T hU hsimple hT σ hσ).2
  change (inverseCompatibleSourceFactors U T hU hsimple hT σ hσ).Y₁ᴴ *
      (inverseCompatibleSourceFactors U T hU hsimple hT σ hσ).Y₁ =
    (sourceY₁ U hU.ρ hU.ρ_posDef)ᴴ * sourceY₁ U hU.ρ hU.ρ_posDef at hgram
  constructor
  · rw [← hU.sourceY₁_physical_contraction hsimple p q]
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ ↦ ?_
    have h := congrArg (fun M ↦ M (α, p) (α, q)) hgram
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply] using h
  · simpa only [inverseCompatibleSourceFactors_Y₂] using
      hU.sourceY₂_physical_contraction hsimple p q

/-- The first source-rank $Y$ normalization is conjugated by the unitary
comparison, preserving its scalar; the weighted second normalization is
unchanged. Adjoint simplicity is retained from the existing source theorems.
Source: arXiv:2502.20257, `eq:MPUnice3`, transported at lines 5486–5487. -/
theorem inverseCompatibleSourceFactors_Y_rank_normalizations
    (hadjoint : IsMPUSimple (physicalAdjointTensor U)) :
    let S := inverseCompatibleSourceFactors U T hU hsimple hT σ hσ
    S.Y₁ * S.Y₁ᴴ = ((d : ℂ) / (r[U] : ℂ)) • 1 ∧
      S.Y₂ * sourceWeight (d := d) hU.ρ * S.Y₂ᴴ =
        ((d : ℂ) / (ℓ[U] : ℂ)) • 1 := by
  obtain ⟨hC, _, hY⟩ :=
    inverseCompatibleSourceFactors_unitary_transport U T hU hsimple hT σ hσ
  let C := Matrix.reindex (Equiv.refl _) (inverseCompatibleRankEquiv U T hT)
    (inverseCompatibleComparisonK U T hU.ρ hU.ρ_posDef)
  have hCC : Cᴴ * C = 1 := hC.1
  constructor
  · rw [hY, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      _ = Cᴴ * ((sourceFactors U hU.ρ hU.ρ_posDef).Y₁ *
          (sourceFactors U hU.ρ hU.ρ_posDef).Y₁ᴴ) * C := by
        simp only [C, Matrix.mul_assoc]
      _ = _ := by
        rw [hU.sourceY₁_mul_conjTranspose hsimple hadjoint]
        simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hCC]
  · have h := hU.sourceY₂_weighted_mul_conjTranspose hsimple hadjoint
    change sourceY₂ U * sourceWeight (d := d) hU.ρ * (sourceY₂ U)ᴴ =
      ((d : ℂ) / (ℓ[U] : ℂ)) • 1 at h
    simpa only [inverseCompatibleSourceFactors_Y₂] using h

/-- Both physical $X$ closures hold for the inverse-compatible record, with
the original canonical weight and dimension constants. The first is a
weighted sum of entries of the external Gram equality; the second factor
is unchanged. Adjoint simplicity is retained from the existing source proofs.
Source: arXiv:2502.20257, `eq:MPUnice4`, transported at lines 5486–5487. -/
theorem inverseCompatibleSourceFactors_X_physical_contractions
    (hadjoint : IsMPUSimple (physicalAdjointTensor U)) (i j : Fin d) :
    let S := inverseCompatibleSourceFactors U T hU hsimple hT σ hσ
    (∑ r : Fin r[U], ∑ α : Fin D, ∑ β : Fin D,
      S.X₁ (i, α) r * hU.ρ β α * star (S.X₁ (j, β) r)) =
        ((r[U] : ℂ) / (d : ℂ)) * (if i = j then 1 else 0) ∧
    (∑ l : Fin ℓ[U], ∑ x : Fin D,
      S.X₂ (x, i) l * star (S.X₂ (x, j) l)) =
        ((ℓ[U] : ℂ) / (d : ℂ)) * (if i = j then 1 else 0) := by
  have hgram := (inverseCompatibleSourceFactors_gram_eq U T hU hsimple hT σ hσ).1
  change (inverseCompatibleSourceFactors U T hU hsimple hT σ hσ).X₁ *
      (inverseCompatibleSourceFactors U T hU hsimple hT σ hσ).X₁ᴴ =
    sourceX₁ U hU.ρ hU.ρ_posDef * (sourceX₁ U hU.ρ hU.ρ_posDef)ᴴ at hgram
  constructor
  · rw [← hU.sourceX₁_physical_contraction hsimple hadjoint i j]
    conv_lhs => rw [Fintype.sum_reverse_three]
    conv_rhs => rw [Fintype.sum_reverse_three]
    refine Finset.sum_congr₂ fun β _ α _ ↦ ?_
    have h := congrArg (fun M ↦ M (i, α) (j, β) * hU.ρ β α) hgram
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul,
      mul_right_comm] using h
  · simpa only [inverseCompatibleSourceFactors_X₂] using
      hU.sourceX₂_physical_contraction hsimple hadjoint i j

end MPOTensor
