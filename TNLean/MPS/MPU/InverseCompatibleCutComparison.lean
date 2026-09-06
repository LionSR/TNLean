/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.UnitaryKroneckerComparison
import TNLean.MPS.MPU.InverseCompatibleFirstCut

/-!
# Inverse comparison for the first inverse-compatible cut

For the candidate factors $X=AY_2^\dagger$ and $Y=X_2^\dagger B$, the
explicit inverses $L=Z_2^\dagger A^\dagger$ and $R=B^\dagger X_2$ give
$L\mathcal M_1R=I_\ell$. Together with $\mathcal M_1=XY$, this proves
$r=\ell$ without a positivity or simplicity assumption.

For a positive-definite weight $\rho$, let $\tilde X,\tilde Y,\tilde Z$
be the existing first source factors and put
$\tilde L=\tilde X^\dagger(I_d\otimes\rho)$. The comparison matrices
$K=\tilde L X$ and $J=L\tilde X$ satisfy $KJ=I_r$ and $JK=I_\ell$.
We retain their rectangular index types, without transporting along $r=\ell$.

Source: arXiv:2502.20257, `main.tex` lines 5432–5443. This is the algebraic
invertible-comparison step only. The source writes an adjoint for the inverse
before its subsequent unitarity argument. Here the inverse is kept as $J$;
neither $J=K^\dagger$ nor unitarity nor an unweighted formula for $K$ is asserted.
-/

open scoped ComplexOrder Matrix

namespace MPOTensor

variable {d D : ℕ} (U : MPOTensor d D) (T : Matrix.unitaryGroup (Fin D) ℂ)

/-- The inverse-compatible first factorization has the same intermediate
size as the first source cut. This uses $L\mathcal M_1R=I_\ell$ and
$\operatorname{rank}(XY)\leq\ell$, not normalization or simplicity.
Source: arXiv:2502.20257, the invertible-comparison step at lines 5432–5443. -/
theorem rightRank_eq_leftRank_of_physicalAdjointTensor_eq_unitary_gauge
    (hT : ∀ i j, physicalAdjointTensor U i j =
      (T : Matrix (Fin D) (Fin D) ℂ)ᴴ * U i j * T) :
    r[U] = ℓ[U] := by
  let L := (sourceZ₂ U)ᴴ * (inverseCompatibleLeftGauge (d := d) T)ᴴ
  let R := (inverseCompatibleRightGauge (d := d) T)ᴴ * sourceX₂ U
  have hLMR : L * sourceCutM₁ U * R = 1 := by
    rw [sourceCutM₁_eq_inverseCompatibleX₁_mul_inverseCompatibleY₁ U T hT,
      ← Matrix.mul_assoc L (inverseCompatibleX₁ U T) (inverseCompatibleY₁ U T)]
    rw [show L * inverseCompatibleX₁ U T = 1 from inverseCompatibleX₁_leftInverse U T,
      Matrix.one_mul]
    exact inverseCompatibleY₁_rightInverse U T
  change (sourceCutM₁ U).rank = ℓ[U]
  apply le_antisymm
  · rw [sourceCutM₁_eq_inverseCompatibleX₁_mul_inverseCompatibleY₁ U T hT]
    exact (Matrix.rank_mul_le_left _ _).trans
      (by simpa only [Fintype.card_fin] using
        Matrix.rank_le_card_width (inverseCompatibleX₁ U T))
  · calc
      ℓ[U] = (1 : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ).rank := by
        rw [Matrix.rank_one, Fintype.card_fin]
      _ = (L * sourceCutM₁ U * R).rank := by rw [hLMR]
      _ ≤ (L * sourceCutM₁ U).rank := Matrix.rank_mul_le_left _ _
      _ ≤ (sourceCutM₁ U).rank := Matrix.rank_mul_le_right _ _

/-- The comparison $K=\tilde L X$, where
$\tilde L=\tilde X^\dagger(I_d\otimes\rho)$ is the actual weighted left inverse.
Source: arXiv:2502.20257, lines 5432–5443, retaining the source normalization
of arXiv:1703.09188, `Y1Y1X1X1` (lines 487–494). -/
noncomputable def inverseCompatibleComparisonK
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    Matrix (Fin r[U]) (Fin ℓ[U]) ℂ :=
  ((sourceX₁ U ρ hρ)ᴴ * sourceWeight (d := d) ρ) * inverseCompatibleX₁ U T

/-- The inverse comparison $J=L\tilde X$, using the actual left inverse
$L=Z_2^\dagger A^\dagger$, without identifying $J$ with $K^\dagger$.
Source: arXiv:2502.20257, lines 5432–5443. -/
noncomputable def inverseCompatibleComparisonJ
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    Matrix (Fin ℓ[U]) (Fin r[U]) ℂ :=
  ((sourceZ₂ U)ᴴ * (inverseCompatibleLeftGauge (d := d) T)ᴴ) * sourceX₁ U ρ hρ

/-- The rectangular comparison matrices intertwine the candidate first cut
with the chosen first source factors and are mutual inverses. All inverse
identities are derived from the actual source factorizations and one-sided
inverses. No adjoint comparison or new normalization is assumed.
Source: arXiv:2502.20257, lines 5432–5443. -/
theorem inverseCompatibleComparison
    (hT : ∀ i j, physicalAdjointTensor U i j =
      (T : Matrix (Fin D) (Fin D) ℂ)ᴴ * U i j * T)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    let X := inverseCompatibleX₁ U T
    let Y := inverseCompatibleY₁ U T
    let Xt := sourceX₁ U ρ hρ
    let Yt := sourceY₁ U ρ hρ
    let K := inverseCompatibleComparisonK U T ρ hρ
    let J := inverseCompatibleComparisonJ U T ρ hρ
    K = Yt * ((inverseCompatibleRightGauge (d := d) T)ᴴ * sourceX₂ U) ∧
      X = Xt * K ∧ Yt = K * Y ∧ J = Y * sourceZ₁ U ρ hρ ∧
      Xt = X * J ∧ Y = J * Yt ∧ K * J = 1 ∧ J * K = 1 := by
  let X := inverseCompatibleX₁ U T
  let Y := inverseCompatibleY₁ U T
  let Xt := sourceX₁ U ρ hρ
  let Yt := sourceY₁ U ρ hρ
  let Lt := (sourceX₁ U ρ hρ)ᴴ * sourceWeight (d := d) ρ
  let L := (sourceZ₂ U)ᴴ * (inverseCompatibleLeftGauge (d := d) T)ᴴ
  let R := (inverseCompatibleRightGauge (d := d) T)ᴴ * sourceX₂ U
  have hfac : X * Y = Xt * Yt :=
    (sourceCutM₁_eq_inverseCompatibleX₁_mul_inverseCompatibleY₁ U T hT).symm.trans
      (sourceCutM₁_eq_sourceX₁_mul_sourceY₁ U ρ hρ)
  have hLt : Lt * Xt = 1 := sourceX₁_weighted_isometry U ρ hρ
  have hL : L * X = 1 := inverseCompatibleX₁_leftInverse U T
  have hR : Y * R = 1 := inverseCompatibleY₁_rightInverse U T
  have hZt : Yt * sourceZ₁ U ρ hρ = 1 := sourceY₁_mul_sourceZ₁ U ρ hρ
  obtain ⟨hK, hX, hYt⟩ :=
    Matrix.factorization_comparison_of_one_sided_inverses hfac hLt hR
  obtain ⟨hJ, hXt, hY⟩ :=
    Matrix.factorization_comparison_of_one_sided_inverses hfac.symm hL hZt
  refine ⟨hK, hX, hYt, hJ, hXt, hY, ?_, ?_⟩
  · change (Lt * X) * (L * Xt) = 1
    rw [hJ, ← Matrix.mul_assoc, ← hYt, hZt]
  · change (L * Xt) * (Lt * X) = 1
    rw [hK, ← Matrix.mul_assoc, ← hY, hR]

end MPOTensor
