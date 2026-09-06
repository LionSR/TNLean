/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.UnitaryAdjointKronecker
import TNLean.Algebra.UnitaryEntrywiseConjugation
import TNLean.MPS.MPU.InverseCompatibleGateIdentity
import TNLean.MPS.MPU.SimpleTensorEquivalence

/-!
# Unitarity of the inverse-compatible comparison

For a simple tensor in canonical form II, the source gates $u$ and $v$ are
unitary. The literal identity $u=\sigma(K^\dagger\otimes K)v^\dagger$ and
$T\overline T=\sigma I$ then imply that $K$ is unitary: the gauge equation
gives $\sigma\overline\sigma=1$, cancellation removes $v^\dagger$, and
both Gram equations remove the phase. The adjoint-Kronecker converse gives
unitarity of $K$ without transporting its rectangular index types.

Consequently the inverse comparison $J$ equals $K^\dagger$, and the candidate
first left factor satisfies $X^\dagger(I_d\otimes\rho)X=I$.

Source: arXiv:2502.20257, `main.tex` lines 5444–5487. This is the printed
gate-unitarity argument and its first weighted-normalization consequence;
it does not assert all pleasant properties or `eq:UUU`, and does not replace
the weighted comparison by an unweighted formula.
-/

open scoped ComplexOrder Matrix Kronecker

namespace MPOTensor

variable {d D : ℕ} (U : MPOTensor d D) (T : Matrix.unitaryGroup (Fin D) ℂ)

/-- The actual first-cut comparison is unitary, by the printed gate identity
and the adjoint-Kronecker converse. Unit modulus of the scalar and nonempty
rank spaces are derived, not assumed.
Source: arXiv:2502.20257, lines 5444–5487. -/
theorem inverseCompatibleComparisonK_isUnitaryBetween
    (hU : IsMPUCanonicalFormII U) (hsimple : IsMPUSimple U)
    (hT : ∀ i j, physicalAdjointTensor U i j =
      (T : Matrix (Fin D) (Fin D) ℂ)ᴴ * U i j * T)
    (σ : ℂ) (hσ : (T : Matrix (Fin D) (Fin D) ℂ) *
      (T : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) = σ • 1) :
    (inverseCompatibleComparisonK U T hU.ρ hU.ρ_posDef).IsUnitaryBetween := by
  have := hU.neZero_phys
  have := hU.neZero_bond
  have hrl : 0 < r[U] * ℓ[U] :=
    lt_of_lt_of_le (Nat.mul_pos (NeZero.pos d) (NeZero.pos d))
      hU.mul_self_le_rightRank_mul_leftRank
  let : NeZero r[U] := ⟨Nat.ne_of_gt (Nat.pos_of_mul_pos_right hrl)⟩
  let : NeZero ℓ[U] := ⟨Nat.ne_of_gt (Nat.pos_of_mul_pos_left hrl)⟩
  have hphase : σ * star σ = 1 :=
    Matrix.scalar_mul_star_eq_one_of_mul_map_star_eq_smul_one T T σ hσ
  have hphase' : star σ * σ = 1 := by rw [mul_comm, hphase]
  have hu : (sourceU U hU.ρ hU.ρ_posDef).IsUnitaryBetween :=
    (hU.isMPUSimple_tfae.out 0 2).mp hsimple
  have hv : (sourceV U hU.ρ hU.ρ_posDef).IsUnitaryBetween :=
    (hU.isMPUSimple_tfae.out 0 3).mp hsimple
  let K := inverseCompatibleComparisonK U T hU.ρ hU.ρ_posDef
  have hgate := sourceU_eq_smul_inverseCompatibleComparisonK_kronecker_sourceV_adjoint
    U T hT hU.ρ hU.ρ_posDef σ hσ
  have hscaled : (σ • (Kᴴ ⊗ₖ K)).IsUnitaryBetween := by
    apply Matrix.IsUnitaryBetween.of_mul_right _ (sourceV U hU.ρ hU.ρ_posDef)ᴴ
      (hv.conjTranspose _)
    rw [Matrix.smul_mul, ← hgate]
    exact hu
  apply Matrix.isUnitaryBetween_of_conjTranspose_kronecker
  constructor
  · simpa only [Matrix.IsIsometry, Matrix.conjTranspose_smul,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, hphase, one_smul] using hscaled.1
  · simpa only [Matrix.IsCoisometry, Matrix.conjTranspose_smul,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, hphase', one_smul] using hscaled.2

/-- After comparison unitarity has been proved, the algebraic inverse is
indeed the adjoint. This justifies the adjoint notation used earlier in the
source's comparison paragraph, without assuming it there.
Source: arXiv:2502.20257, lines 5432–5443 and 5444–5487. -/
theorem inverseCompatibleComparisonJ_eq_conjTranspose
    (hU : IsMPUCanonicalFormII U) (hsimple : IsMPUSimple U)
    (hT : ∀ i j, physicalAdjointTensor U i j =
      (T : Matrix (Fin D) (Fin D) ℂ)ᴴ * U i j * T)
    (σ : ℂ) (hσ : (T : Matrix (Fin D) (Fin D) ℂ) *
      (T : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) = σ • 1) :
    inverseCompatibleComparisonJ U T hU.ρ hU.ρ_posDef =
      (inverseCompatibleComparisonK U T hU.ρ hU.ρ_posDef)ᴴ := by
  let K := inverseCompatibleComparisonK U T hU.ρ hU.ρ_posDef
  let J := inverseCompatibleComparisonJ U T hU.ρ hU.ρ_posDef
  have hK : Kᴴ * K = 1 :=
    (inverseCompatibleComparisonK_isUnitaryBetween U T hU hsimple hT σ hσ).1
  have hKJ : K * J = 1 :=
    (inverseCompatibleComparison U T hT hU.ρ hU.ρ_posDef).2.2.2.2.2.2.1
  change J = Kᴴ
  calc
    J = (Kᴴ * K) * J := by rw [hK, Matrix.one_mul]
    _ = Kᴴ := by rw [Matrix.mul_assoc, hKJ, Matrix.mul_one]

/-- The candidate first left factor inherits the actual weighted source
normalization by $X=\tilde X K$ and $K^\dagger K=I$.
Source: arXiv:2502.20257, lines 5486–5487, with the source normalization
of arXiv:1703.09188, `Y1Y1X1X1` (lines 487–494). -/
theorem inverseCompatibleX₁_weighted_isometry
    (hU : IsMPUCanonicalFormII U) (hsimple : IsMPUSimple U)
    (hT : ∀ i j, physicalAdjointTensor U i j =
      (T : Matrix (Fin D) (Fin D) ℂ)ᴴ * U i j * T)
    (σ : ℂ) (hσ : (T : Matrix (Fin D) (Fin D) ℂ) *
      (T : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) = σ • 1) :
    (inverseCompatibleX₁ U T)ᴴ * sourceWeight (d := d) hU.ρ *
      inverseCompatibleX₁ U T = 1 := by
  let K := inverseCompatibleComparisonK U T hU.ρ hU.ρ_posDef
  have hK : Kᴴ * K = 1 :=
    (inverseCompatibleComparisonK_isUnitaryBetween U T hU hsimple hT σ hσ).1
  have hX := (inverseCompatibleComparison U T hT hU.ρ hU.ρ_posDef).2.1
  rw [hX, Matrix.conjTranspose_mul]
  calc
    _ = Kᴴ * ((sourceX₁ U hU.ρ hU.ρ_posDef)ᴴ * sourceWeight (d := d) hU.ρ *
        sourceX₁ U hU.ρ hU.ρ_posDef) * K := by simp only [K, Matrix.mul_assoc]
    _ = 1 := by rw [sourceX₁_weighted_isometry U hU.ρ hU.ρ_posDef, Matrix.mul_one, hK]

namespace GroupFamily

/-- At an involutive element of a canonical representation family, the chosen
gauge and chosen scalar give a unitary comparison, its adjoint inverse, and
the candidate's weighted normalization. The gauge equation, scalar equation,
and simplicity are supplied by the representation, rather than new premises.
Source: arXiv:2502.20257, `eq:defT`, `eq:intro_sigma` (lines 1552–1562),
and the inverse-compatible construction at lines 5444–5487. -/
theorem IsRepresentation.inverseCompatibleComparison_unitary_of_inv_eq
    {G : Type*} [Group G] (F : MPOTensor.GroupFamily G d) (hF : F.IsRepresentation)
    (hcanonical : ∀ g : G,
      MPSTensor.IsLeftCanonical (F.tensor g).normalizedFlattening)
    (g : G) (hg : g⁻¹ = g) (hU : IsMPUCanonicalFormII (F.tensor g)) :
    let T := hF.daggerInverseGauge F hcanonical g
    let K := inverseCompatibleComparisonK (F.tensor g) T hU.ρ hU.ρ_posDef
    let J := inverseCompatibleComparisonJ (F.tensor g) T hU.ρ hU.ρ_posDef
    K.IsUnitaryBetween ∧ J = Kᴴ ∧
      (inverseCompatibleX₁ (F.tensor g) T)ᴴ * sourceWeight (d := d) hU.ρ *
        inverseCompatibleX₁ (F.tensor g) T = 1 := by
  let T := hF.daggerInverseGauge F hcanonical g
  let σ := hF.daggerInverseScalar F hcanonical g
  have hT : ∀ i j, physicalAdjointTensor (F.tensor g) i j =
      (T : Matrix (Fin (F.bondDim g)) (Fin (F.bondDim g)) ℂ)ᴴ * F.tensor g i j * T :=
    hF.physicalAdjointTensor_eq_daggerInverseGauge_of_inv_eq F hcanonical g hg
  have hσ : (T : Matrix (Fin (F.bondDim g)) (Fin (F.bondDim g)) ℂ) *
      (T : Matrix (Fin (F.bondDim g)) (Fin (F.bondDim g)) ℂ).map (starRingEnd ℂ) =
      σ • 1 :=
    hF.daggerInverseGauge_mul_mapStar_self_eq_smul_one_of_inv_eq F hcanonical g hg
  exact ⟨inverseCompatibleComparisonK_isUnitaryBetween _ T hU (hF.isSimple g) hT σ hσ,
    inverseCompatibleComparisonJ_eq_conjTranspose _ T hU (hF.isSimple g) hT σ hσ,
    inverseCompatibleX₁_weighted_isometry _ T hU (hF.isSimple g) hT σ hσ⟩

end GroupFamily

end MPOTensor
