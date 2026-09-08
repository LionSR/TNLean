/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.InverseCompatibleComparisonUnitarity

/-!
# Literal gates of the inverse-compatible decomposition

The candidate first factors $X,Y$ and the second source factors $X_2,Y_2$
define new gates $u_{\mathrm{new}}=Y_2\mathbin{-}Y$ and
$v_{\mathrm{new}}=X\mathbin{-}X_2$. Both use the same rank-pair space
$\mathrm{Fin}(\ell)\times\mathrm{Fin}(\ell)$, so the literal equation
$u_{\mathrm{new}}=\sigma v_{\mathrm{new}}^\dagger$ needs no rank transport or swap.

The source route compares these contractions with the old source gates:
$u_{\mathrm{new}}=(I_\ell\otimes J)u$ and
$v_{\mathrm{new}}=v(K\otimes I_\ell)$. Once comparison unitarity and
$J=K^\dagger$ have been proved, the old gate identity and $K^\dagger K=I$
give the phase equation; composition with the old unitary gates gives unitarity.

Source: arXiv:2502.20257, `main.tex` lines 5390–5432 and 5440–5487.
This covers the new-gate part of the decomposition at lines 5342–5348, not
all pleasant properties, the truncated-chain assertion `eq:UUU`, or the full proposition.
The actual weighted comparison is retained throughout.
-/

open scoped ComplexOrder Matrix Kronecker
open Matrix

namespace MPOTensor

variable {d D : ℕ} (U : MPOTensor d D) (T : Matrix.unitaryGroup (Fin D) ℂ)

/-- The literal new $u$ contraction, with both rank coordinates in `Fin ℓ[U]`.
Source: arXiv:2502.20257, candidate factors at lines 5390–5432 and gates at lines 5486–5487. -/
noncomputable def inverseCompatibleU :
    Matrix (Fin ℓ[U] × Fin ℓ[U]) (Fin d × Fin d) ℂ :=
  fun (l, s) (i, j) ↦ ∑ β : Fin D,
    sourceY₂ U l (i, β) * inverseCompatibleY₁ U T s (β, j)

/-- The literal new $v$ contraction, with both rank coordinates in `Fin ℓ[U]`.
Source: arXiv:2502.20257, candidate factors at lines 5390–5432 and gates at lines 5486–5487. -/
noncomputable def inverseCompatibleV :
    Matrix (Fin d × Fin d) (Fin ℓ[U] × Fin ℓ[U]) ℂ :=
  fun (i, j) (l, s) ↦ ∑ β : Fin D,
    inverseCompatibleX₁ U T (i, β) l * sourceX₂ U (β, j) s

/-- The new $u$ is the old weighted source gate dressed by the actual inverse comparison.
This is algebraic: no adjoint identification of $J$ or unitarity is assumed.
Source: arXiv:2502.20257, comparison at lines 5432–5443 and new gates at lines 5486–5487. -/
theorem inverseCompatibleU_eq_comparisonJ_mul_sourceU
    (hT : ∀ i j, physicalAdjointTensor U i j =
      (T : Matrix (Fin D) (Fin D) ℂ)ᴴ * U i j * T)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    inverseCompatibleU U T =
      ((1 : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ) ⊗ₖ inverseCompatibleComparisonJ U T ρ hρ) *
        sourceU U ρ hρ := by
  have hY := (inverseCompatibleComparison U T hT ρ hρ).2.2.2.2.2.1
  ext ⟨l, s⟩ ⟨i, j⟩
  change (∑ β : Fin D, sourceY₂ U l (i, β) * inverseCompatibleY₁ U T s (β, j)) = _
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
    Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Fintype.sum_ite_eq]
  simp only [hY, Matrix.mul_apply, sourceU_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr₂
  intro r _ β _
  ring

/-- The new $v$ is the old weighted source gate dressed by the comparison $K$.
Source: arXiv:2502.20257, comparison at lines 5432–5443 and new gates at lines 5486–5487. -/
theorem inverseCompatibleV_eq_sourceV_mul_comparisonK
    (hT : ∀ i j, physicalAdjointTensor U i j =
      (T : Matrix (Fin D) (Fin D) ℂ)ᴴ * U i j * T)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    inverseCompatibleV U T = sourceV U ρ hρ *
      (inverseCompatibleComparisonK U T ρ hρ ⊗ₖ
        (1 : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ)) := by
  have hX := (inverseCompatibleComparison U T hT ρ hρ).2.1
  ext ⟨i, j⟩ ⟨l, s⟩
  simp only [inverseCompatibleV, hX, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.one_apply, sourceV_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_mul, Fintype.sum_ite_eq']
  rw [Finset.sum_comm]
  apply Finset.sum_congr₂
  intro r _ β _
  ring

/-- The literal new gates are unitary and satisfy
$u_{\mathrm{new}}=\sigma v_{\mathrm{new}}^\dagger$.
The comparison transport follows the source proof, using its established unitarity,
not a new normalization or a rank-space identification.
Source: arXiv:2502.20257, lines 5440–5487, for the decomposition at lines 5342–5348. -/
theorem inverseCompatibleGates_unitary_and_phase
    (hU : IsMPUCanonicalFormII U) (hsimple : IsMPUSimple U)
    (hT : ∀ i j, physicalAdjointTensor U i j =
      (T : Matrix (Fin D) (Fin D) ℂ)ᴴ * U i j * T)
    (σ : ℂ) (hσ : (T : Matrix (Fin D) (Fin D) ℂ) *
      (T : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) = σ • 1) :
    (inverseCompatibleU U T).IsUnitaryBetween ∧
      (inverseCompatibleV U T).IsUnitaryBetween ∧
      inverseCompatibleU U T = σ • (inverseCompatibleV U T)ᴴ := by
  let K := inverseCompatibleComparisonK U T hU.ρ hU.ρ_posDef
  let I : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ := 1
  have hI : I.IsUnitaryBetween := by constructor <;> simp [I, Matrix.IsIsometry,
    Matrix.IsCoisometry]
  have hK : K.IsUnitaryBetween :=
    inverseCompatibleComparisonK_isUnitaryBetween U T hU hsimple hT σ hσ
  have hu : (sourceU U hU.ρ hU.ρ_posDef).IsUnitaryBetween :=
    (hU.isMPUSimple_tfae.out 0 2).mp hsimple
  have hv : (sourceV U hU.ρ hU.ρ_posDef).IsUnitaryBetween :=
    (hU.isMPUSimple_tfae.out 0 3).mp hsimple
  have hnewu : inverseCompatibleU U T = (I ⊗ₖ Kᴴ) * sourceU U hU.ρ hU.ρ_posDef := by
    rw [inverseCompatibleU_eq_comparisonJ_mul_sourceU U T hT hU.ρ hU.ρ_posDef,
      inverseCompatibleComparisonJ_eq_conjTranspose U T hU hsimple hT σ hσ]
  have hnewv : inverseCompatibleV U T = sourceV U hU.ρ hU.ρ_posDef * (K ⊗ₖ I) :=
    inverseCompatibleV_eq_sourceV_mul_comparisonK U T hT hU.ρ hU.ρ_posDef
  refine ⟨?_, ?_, ?_⟩
  · rw [hnewu]
    exact (hI.kronecker I Kᴴ (hK.conjTranspose K)).mul _ _ hu
  · rw [hnewv]
    exact hv.mul _ _ (hK.kronecker K I hI)
  · have hgram : Kᴴ * K = 1 := hK.1
    rw [hnewu, sourceU_eq_smul_inverseCompatibleComparisonK_kronecker_sourceV_adjoint
      U T hT hU.ρ hU.ρ_posDef σ hσ, hnewv, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_kronecker, Matrix.mul_smul]
    change σ • ((I ⊗ₖ Kᴴ) * ((Kᴴ ⊗ₖ K) * (sourceV U hU.ρ hU.ρ_posDef)ᴴ)) =
      σ • ((Kᴴ ⊗ₖ Iᴴ) * (sourceV U hU.ρ hU.ρ_posDef)ᴴ)
    rw [← Matrix.mul_assoc, ← Matrix.mul_kronecker_mul, hgram]
    simp only [I, Matrix.one_mul, Matrix.conjTranspose_one]

namespace GroupFamily

/-- At an involutive element, the existing chosen gauge and scalar give literal
unitary new gates with the self-adjoint phase relation. The representation supplies
simplicity, the gauge equation, and the phase equation.
Source: arXiv:2502.20257, `eq:defT`, `eq:intro_sigma` (lines 1552–1562),
and the new-gate step at lines 5440–5487. -/
theorem IsRepresentation.inverseCompatibleGates_unitary_and_phase_of_inv_eq
    {G : Type*} [Group G] (F : MPOTensor.GroupFamily G d) (hF : F.IsRepresentation)
    (hcanonical : ∀ g : G,
      MPSTensor.IsLeftCanonical (F.tensor g).normalizedFlattening)
    (g : G) (hg : g⁻¹ = g) (hU : IsMPUCanonicalFormII (F.tensor g)) :
    let T := hF.daggerInverseGauge F hcanonical g
    let σ := hF.daggerInverseScalar F hcanonical g
    (inverseCompatibleU (F.tensor g) T).IsUnitaryBetween ∧
      (inverseCompatibleV (F.tensor g) T).IsUnitaryBetween ∧
      inverseCompatibleU (F.tensor g) T = σ • (inverseCompatibleV (F.tensor g) T)ᴴ := by
  exact inverseCompatibleGates_unitary_and_phase _ _ hU (hF.isSimple g)
    (hF.physicalAdjointTensor_eq_daggerInverseGauge_of_inv_eq F hcanonical g hg) _
    (hF.daggerInverseGauge_mul_mapStar_self_eq_smul_one_of_inv_eq F hcanonical g hg)

end GroupFamily

end MPOTensor
