/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.Isometry.UnitaryKronecker
import TNLean.MPS.MPU.Representation.InverseCompatibleFirstCut
import QICLean.Algebra.Combinatorics.FinSumPermutation
import TNLean.MPS.Operator.Unitary.SourceUV
import TNLean.MPS.MPU.Simple.SimpleTensorEquivalence

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
invertible-comparison step only.

**Local fix (weighted comparison matrix):** the source prints
$K=\tilde X^\dagger X=\tilde Y Y^\dagger$. Only $\tilde X^\dagger(I_d\otimes\rho)$
is a left inverse of $\tilde X$, by the weighted normalization of
arXiv:1703.09188, lines 480–500, so the first expression carries that weight
here; the second holds as printed and is proved. Documented in
`docs/paper-gaps/fbc25_inverse_compatible_comparison_matrix.tex`.

**Scope restriction (inverse comparison):** the source pairs $K$ with
$K^\dagger$, using the unitarity it establishes afterwards. Here the inverse is
the separately constructed $J$, with $KJ=I_r$ and $JK=I_\ell$; neither
$J=K^\dagger$ nor unitarity of $K$ is asserted. Documented in
`docs/paper-gaps/fbc25_inverse_compatible_comparison_matrix.tex`. The
restriction is lifted in `TNLean/MPS/MPU/InverseCompatibleComparisonUnitarity.lean`:
for a simple tensor in canonical form II whose physical adjoint is carried by a
unitary gauge $T$ with $T\overline T=\sigma I$,
`inverseCompatibleComparisonK_isUnitaryBetween` proves $K$ unitary and
`inverseCompatibleComparisonJ_eq_conjTranspose` proves $J=K^\dagger$.

## The literal inverse-compatible gate identity

For a tensor $U$, a positive-definite weight $\rho$, and a unitary virtual gauge $T$
relating $U$ to its physical adjoint, let $K$ be the weighted first-cut comparison.
If $T\overline T=\sigma I$, the actual source gates obey
$u=\sigma(K^\dagger\otimes K)v^\dagger$.

This follows the contraction in arXiv:2502.20257, `main.tex` lines 5444–5487:
adjoint the first comparison to express $Y_2$, substitute the comparison for
$\tilde Y_1$, and contract $\overline T T$.

**Local fix:** `Papers/2502.20257/main.tex` lines 5440–5443 print $Y_1$
without a tilde in the first comparison; we retain the $\tilde Y_1$ explicitly
shown in the following gate diagram (lines 5444–5487, label at line 5457).
See `docs/paper-gaps/fbc25_inverse_compatible_tilde_omission.tex`.
This correction concerns only that missing tilde. The weight remains
in the chosen source factors and $K$. No identification of the inverse comparison
with $K^\dagger$, gate unitarity, simplicity, or unit modulus of $\sigma$ is assumed.
The row orders of $u$ and $v^\dagger$ are respectively $(\ell,r)$ and $(r,\ell)$;
there is no additional swap.

## Physical dimensions of the inverse-compatible source ranks

For a simple canonical-form-II MPU whose physical adjoint is related to the
same tensor by a unitary virtual gauge, the existing cut comparison gives
$r=\ell$. The simple-MPU rank product $r\ell=d^2$ then yields $\ell=d$ and
$r=d$. A single equivalence identifies the common raw source rank with the
physical index; no independent endpoint casts are chosen.

Source: CPSV17, `ThmFund1` (arXiv:1703.09188, lines 563–571), and FBC25,
`eq:defT` in the self-inverse case (arXiv:2502.20257, lines 1552–1563), with
the cut comparison at lines 5432–5443. This is a consequence of the stated
self-adjoint gauge hypothesis, not the general finite-group index argument
at line 1547. No scalar relation, adjoint simplicity, additional positivity,
or new virtual gauge is required. Only ranks and their coordinates are
identified here, not physical composition or the complementary relation.
-/

section

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

end

section

open scoped ComplexOrder Matrix Kronecker

namespace MPOTensor

variable {d D : ℕ} (U : MPOTensor d D) (T : Matrix.unitaryGroup (Fin D) ℂ)

/-- Adjointing the first comparison gives the second source factor in terms
of the weighted first source factor. This does not use $J=K^\dagger$.
Source: arXiv:2502.20257, lines 5440–5443, with the maintained product-index order. -/
theorem sourceY₂_eq_inverseCompatibleComparisonK_adjoint
    (hT : ∀ i j, physicalAdjointTensor U i j =
      (T : Matrix (Fin D) (Fin D) ℂ)ᴴ * U i j * T)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    sourceY₂ U = (inverseCompatibleComparisonK U T ρ hρ)ᴴ *
      (sourceX₁ U ρ hρ)ᴴ * inverseCompatibleLeftGauge (d := d) T := by
  have hX := (inverseCompatibleComparison U T hT ρ hρ).2.1
  have hA : (inverseCompatibleLeftGauge (d := d) T)ᴴ *
      inverseCompatibleLeftGauge (d := d) T = 1 :=
    (Matrix.kronecker_mem_unitary (show (1 : Matrix (Fin d) (Fin d) ℂ) ∈
      unitary (Matrix (Fin d) (Fin d) ℂ) from one_mem _)
      (Matrix.map_star_mem_unitaryGroup_iff.mpr T.property)).1
  have h := congrArg (fun M ↦ Mᴴ * inverseCompatibleLeftGauge (d := d) T) hX
  simpa only [inverseCompatibleX₁, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, hA, Matrix.mul_one] using h

/-- The literal $u=\sigma(K^\dagger\otimes K)v^\dagger$ contraction, with
$K$ the actual weighted comparison and no permutation of the gate indices.
Source: arXiv:2502.20257, lines 5444–5487. This is an algebraic gate identity,
not the subsequent unitarity conclusion. -/
theorem sourceU_eq_smul_inverseCompatibleComparisonK_kronecker_sourceV_adjoint
    (hT : ∀ i j, physicalAdjointTensor U i j =
      (T : Matrix (Fin D) (Fin D) ℂ)ᴴ * U i j * T)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) (σ : ℂ)
    (hσ : (T : Matrix (Fin D) (Fin D) ℂ) *
      (T : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) = σ • 1) :
    let K := inverseCompatibleComparisonK U T ρ hρ
    sourceU U ρ hρ = σ • ((Kᴴ ⊗ₖ K) * (sourceV U ρ hρ)ᴴ) := by
  let K := inverseCompatibleComparisonK U T ρ hρ
  let Tc := (T : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ)
  have hunit : (T : Matrix (Fin D) (Fin D) ℂ)ᴴ * T = 1 := T.property.1
  have hphase : Tc * (T : Matrix (Fin D) (Fin D) ℂ) = σ • 1 := by
    have h := congrArg (fun M ↦ (T : Matrix (Fin D) (Fin D) ℂ)ᴴ * M * T) hσ
    simpa only [← Matrix.mul_assoc, hunit, Matrix.one_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one] using h
  have hY₂ := sourceY₂_eq_inverseCompatibleComparisonK_adjoint U T hT ρ hρ
  have hY₁ := (inverseCompatibleComparison U T hT ρ hρ).2.2.1
  change sourceY₂ U = Kᴴ * (sourceX₁ U ρ hρ)ᴴ *
    inverseCompatibleLeftGauge (d := d) T at hY₂
  change sourceY₁ U ρ hρ = K * inverseCompatibleY₁ U T at hY₁
  ext ⟨l, s⟩ ⟨i, j⟩
  let C : Matrix (Fin r[U]) (Fin D) ℂ := fun r γ ↦ star (sourceX₁ U ρ hρ (i, γ) r)
  let E : Matrix (Fin D) (Fin ℓ[U]) ℂ := fun δ t ↦ star (sourceX₂ U (δ, j) t)
  have hleft (β : Fin D) : sourceY₂ U l (i, β) = (Kᴴ * C * Tc) l β := by
    rw [hY₂]
    simp only [inverseCompatibleLeftGauge, Matrix.mul_apply, Fintype.sum_prod_type,
      Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.conjTranspose_apply,
      ite_mul, one_mul, zero_mul, mul_ite, mul_zero,
      Finset.sum_ite_irrel, Finset.sum_const_zero, Fintype.sum_ite_eq']
    rfl
  have hright (β : Fin D) : sourceY₁ U ρ hρ s (β, j) =
      ((T : Matrix (Fin D) (Fin D) ℂ) * E * Kᵀ) β s := by
    rw [hY₁]
    simp only [inverseCompatibleY₁, inverseCompatibleRightGauge, Matrix.mul_apply,
      Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Matrix.conjTranspose_apply, Matrix.transpose_apply, Finset.mul_sum,
      Finset.sum_mul, mul_ite, mul_one, mul_zero, Fintype.sum_ite_eq']
    simp only [E]
    apply Finset.sum_congr₂
    intro t _ δ _
    ring
  have hcontract : (Kᴴ * C * Tc) * ((T : Matrix (Fin D) (Fin D) ℂ) * E * Kᵀ) =
      σ • (Kᴴ * C * E * Kᵀ) := by
    calc
      _ = Kᴴ * C * (Tc * (T : Matrix (Fin D) (Fin D) ℂ)) * E * Kᵀ := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hphase]; simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  rw [sourceU_apply]
  simp_rw [hleft, hright]
  rw [← Matrix.mul_apply, hcontract]
  simp only [Matrix.smul_apply, smul_eq_mul]
  congr 1
  change (Kᴴ * C * E * Kᵀ) l s = ((Kᴴ ⊗ₖ K) * (sourceV U ρ hρ)ᴴ) (l, s) (i, j)
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
    Matrix.conjTranspose_apply, sourceV_apply, star_sum, star_mul, Matrix.transpose_apply,
    Finset.mul_sum, Finset.sum_mul]
  dsimp only [C, E]
  rw [Fintype.sum_reverse_three]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr₂
  intro t _ γ _
  ring

end MPOTensor

end

section

open scoped ComplexOrder Matrix

namespace MPOTensor

variable {d D : ℕ} (U : MPOTensor d D) (T : Matrix.unitaryGroup (Fin D) ℂ)
  (hU : IsMPUCanonicalFormII U) (hsimple : IsMPUSimple U)
  (hT : ∀ i j, physicalAdjointTensor U i j =
    (T : Matrix (Fin D) (Fin D) ℂ)ᴴ * U i j * T)

include hU hsimple hT in
/-- Both source ranks equal the physical dimension under the self-adjoint
unitary gauge. Source: CPSV17 `ThmFund1` (lines 563–571), combined with the
FBC25 cut comparison (lines 5432–5443). No phase relation is assumed. -/
theorem inverseCompatible_sourceRanks_eq_physical : ℓ[U] = d ∧ r[U] = d := by
  have hr := rightRank_eq_leftRank_of_physicalAdjointTensor_eq_unitary_gauge U T hT
  have hprod : r[U] * ℓ[U] = d * d := (hU.isMPUSimple_tfae.out 1 2).mp hsimple
  rw [hr] at hprod
  have hl : ℓ[U] = d := Nat.mul_self_inj.mp hprod
  exact ⟨hl, hr.trans hl⟩

/-- The single common-rank-to-physical equivalence used for raw endpoint
coordinates. Source: the rank consequence of CPSV17 `ThmFund1` (lines 563–571)
and FBC25's self-adjoint cut comparison (lines 5432–5443). -/
noncomputable def inverseCompatiblePhysicalEquiv : Fin ℓ[U] ≃ Fin d :=
  finCongr (inverseCompatible_sourceRanks_eq_physical U T hU hsimple hT).1

end MPOTensor

end
