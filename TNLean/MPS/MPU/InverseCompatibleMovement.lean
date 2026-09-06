/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.InverseCompatibleSourceTransport
import TNLean.MPS.MPU.StaircaseUnitarity

/-!
# Movement gates for the inverse-compatible source factors

Let $S_0$ be the chosen source factors, $S$ the inverse-compatible factors,
and $C$ the actual comparison transported to the common first-rank coordinates.
The second factors are unchanged, so $w_L(S)=w_L(S_0)$. The first-factor
transport gives
$w_R(S)=(I_d\otimes C^\dagger)w_R(S_0)(C\otimes I_d)$.
Rows of $w_R$ have order (physical, first rank), and columns have order
(first rank, physical); no permutation is inserted.

The chosen movement gates and $C$ are unitary, hence both new movement gates
are unitary by composition. Source: arXiv:2502.20257, `eq:wLR` (lines 811–869)
and transport after comparison unitarity at lines 5486–5487. No simplicity
premise on the physical adjoint is needed. This file does not assert the
complete inverse-compatible proposition, `eq:UUU`, or transport of $Z_1$.
-/

open scoped ComplexOrder Matrix Kronecker BigOperators

namespace MPOTensor

variable {d D : ℕ} (U : MPOTensor d D) (T : Matrix.unitaryGroup (Fin D) ℂ)
  (hU : IsMPUCanonicalFormII U) (hsimple : IsMPUSimple U)
  (hT : ∀ i j, physicalAdjointTensor U i j =
    (T : Matrix (Fin D) (Fin D) ℂ)ᴴ * U i j * T)
  (σ : ℂ) (hσ : (T : Matrix (Fin D) (Fin D) ℂ) *
    (T : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) = σ • 1)

/-- The left movement gate is unchanged; the right movement gate transforms
by the explicit first-rank unitary on its two rank legs.
Source: arXiv:2502.20257, `eq:wLR` (lines 811–869), transported at lines 5486–5487. -/
theorem inverseCompatibleSourceFactors_movement_transport :
    let S₀ := sourceFactors U hU.ρ hU.ρ_posDef
    let S := inverseCompatibleSourceFactors U T hU hsimple hT σ hσ
    let C := Matrix.reindex (Equiv.refl _) (inverseCompatibleRankEquiv U T hT)
      (inverseCompatibleComparisonK U T hU.ρ hU.ρ_posDef)
    SourceFactors.sourceWL U S = SourceFactors.sourceWL U S₀ ∧
      SourceFactors.sourceWR U S =
        ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ Cᴴ) * SourceFactors.sourceWR U S₀ *
          (C ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) := by
  obtain ⟨_, hX, hY⟩ :=
    inverseCompatibleSourceFactors_unitary_transport U T hU hsimple hT σ hσ
  constructor
  · rfl
  · ext ⟨i, r⟩ ⟨r', j⟩
    simp only [SourceFactors.sourceWR, hX, hY, Matrix.mul_apply,
      Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum,
      mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul,
      Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [Fintype.sum_reverse_three]
    refine Finset.sum_congr₂ fun a _ b _ ↦ ?_
    exact Finset.sum_congr rfl fun β _ ↦ by ring

/-- Both movement gates of the inverse-compatible record are unitary between
their stated leg spaces. This follows from the movement transport, the chosen
movement-gate theorem, and Kronecker products and compositions of unitaries.
Source: arXiv:2502.20257, `eq:wLR` and lines 5486–5487. -/
theorem inverseCompatibleSourceFactors_movement_isUnitaryBetween :
    let S := inverseCompatibleSourceFactors U T hU hsimple hT σ hσ
    (SourceFactors.sourceWL U S).IsUnitaryBetween ∧
      (SourceFactors.sourceWR U S).IsUnitaryBetween := by
  let C := Matrix.reindex (Equiv.refl _) (inverseCompatibleRankEquiv U T hT)
    (inverseCompatibleComparisonK U T hU.ρ hU.ρ_posDef)
  have hC : C.IsUnitaryBetween :=
    (inverseCompatibleSourceFactors_unitary_transport U T hU hsimple hT σ hσ).1
  obtain ⟨hL, hR⟩ := hU.sourceWL_sourceWR_isUnitaryBetween hsimple
  obtain ⟨hWL, hWR⟩ :=
    inverseCompatibleSourceFactors_movement_transport U T hU hsimple hT σ hσ
  have hI : (1 : Matrix (Fin d) (Fin d) ℂ).IsUnitaryBetween := by
    constructor <;> simp [Matrix.IsIsometry, Matrix.IsCoisometry]
  constructor
  · rw [hWL]
    exact hL
  · rw [hWR]
    exact ((hI.kronecker _ _ (hC.conjTranspose _)).mul _ _ hR).mul _ _
      (hC.kronecker _ _ hI)

end MPOTensor
