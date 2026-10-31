/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.SimpleTensorEquivalence

/-!
# The three-legged decomposition of a simple MPU in canonical form II

This file assembles Theorem `thm:mpu` of arXiv:2502.20257 (`main.tex`,
lines 657--809): for a simple MPU tensor $\mathcal U$ in canonical form II
there are left-invertible tensors $X_1,X_2$ and right-invertible tensors
$Y_1,Y_2$ such that

* (a) `eq:3-leg`: $\mathcal U=X_1Y_1=X_2Y_2$, the first joined along the
  curly leg and the second along the thick leg;
* (b) `eq:uv`: the gates $u=Y_2\mathbin{-}Y_1$ and $v=X_1\mathbin{-}X_2$ are
  unitary;
* (c) `eq:thm1c`: $X_2^\dagger X_2=\Id$ on the thick leg and
  $X_1^\dagger(I_d\otimes\rho)X_1=\Id$ on the curly leg.

Moreover the thick and curly leg dimensions $d_l$ and $d_r$ satisfy
$d_ld_r=d^2$ (line 809).

The source proves the theorem by citing arXiv:1703.09188, Section III.  The
assembly here follows that chain and adds no new argument.  The source factors
`MPOTensor.sourceFactors` (`eq:sf-svd`--`YZ=1`, lines 479--506) carry
clauses (a) and (c) and both one-sided inverses as fields; the thick leg is
the second source-cut rank $\ell$ and the curly leg is the first source-cut
rank $r$.  Clause (b) and the dimension identity are items 2--4 of
Theorem `ThmFund1` (lines 563--601), `MPOTensor.IsMPUCanonicalFormII.isMPUSimple_tfae`.

## Length convention

The canonical-form-II convention `MPOTensor.IsMPUCanonicalFormII` asks the
periodic operator to be unitary on every chain of length $N\geq2$, following
arXiv:1703.09188, lines 317--356.  arXiv:2502.20257, lines 198--209, asks
unitarity on every nonempty chain (`MPOTensor.IsMPUPos`).  The latter implies
the former (`MPOTensor.IsMPUPos.isMPU`), and the length-one operator is used
nowhere in the proof, so the theorem below applies verbatim to every MPU in the
sense of arXiv:2502.20257.

## Main definitions

* `MPOTensor.SourceFactors.IsThreeLegged`: clause (b) of `thm:mpu` together
  with $d_ld_r=d^2$, for supplied source factors.

## Main results

* `MPOTensor.SourceFactors.X₁_leftInverse`, `MPOTensor.SourceFactors.X₂_leftInverse`:
  the left inverses of $X_1$ and $X_2$.
* `MPOTensor.IsMPUCanonicalFormII.sourceFactors_isThreeLegged`: the compact-SVD
  source factors of a simple MPU in canonical form II satisfy `thm:mpu`.
* `MPOTensor.IsMPUCanonicalFormII.exists_threeLegged`: Theorem `thm:mpu` in
  existential form.
-/

open scoped Matrix ComplexOrder
open Matrix

namespace MPOTensor

variable {d D : ℕ} {U : MPOTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}

namespace SourceFactors

/-- The first left factor is left-invertible, with left inverse
$X_1^\dagger(I_d\otimes\rho)$.  This is the left-invertibility of $X_1$ in
arXiv:2502.20257, Theorem `thm:mpu`, read off from the weighted normalization
`eq:thm1c` (arXiv:1703.09188, `Y1Y1X1X1`, lines 487--494). -/
theorem X₁_leftInverse (S : SourceFactors U ρ) :
    (S.X₁ᴴ * sourceWeight (d := d) ρ) * S.X₁ = 1 :=
  S.X₁_weighted_isometry

/-- The second left factor is left-invertible, with left inverse $X_2^\dagger$.
This is the left-invertibility of $X_2$ in arXiv:2502.20257, Theorem `thm:mpu`,
read off from the normalization `eq:thm1c` (arXiv:1703.09188, `Y1Y1X1X1`,
lines 487--494). -/
theorem X₂_leftInverse (S : SourceFactors U ρ) : S.X₂ᴴ * S.X₂ = 1 :=
  S.X₂_isometry

/-- Clause (b) of Theorem `thm:mpu` of arXiv:2502.20257, together with the
dimension identity following it, for supplied source factors.

The remaining content of the theorem is carried by the fields of
`MPOTensor.SourceFactors`:

* clause (a), `eq:3-leg`, is `sourceCutM₁_eq` and `sourceCutM₂_eq`, in entry form
  `MPOTensor.SourceFactors.X₁_mul_Y₁_apply` and
  `MPOTensor.SourceFactors.X₂_mul_Y₂_apply`;
* clause (c), `eq:thm1c`, is `X₂_isometry` and `X₁_weighted_isometry`;
* the right inverses of $Y_1,Y_2$ are `Y₁_mul_Z₁` and `Y₂_mul_Z₂`, and the left
  inverses of $X_1,X_2$ are `MPOTensor.SourceFactors.X₁_leftInverse` and
  `MPOTensor.SourceFactors.X₂_leftInverse`.

The thick leg of the source has dimension $d_l=\ell$ and the curly leg has
dimension $d_r=r$.

Source: arXiv:2502.20257, Theorem `thm:mpu`, equations `eq:uv` (lines 704--760)
and the sentence at line 809. -/
structure IsThreeLegged (S : SourceFactors U ρ) : Prop where
  /-- The leg dimensions satisfy $d_ld_r=d^2$ (arXiv:2502.20257, line 809). -/
  leftRank_mul_rightRank : ℓ[U] * r[U] = d * d
  /-- The gate $u=Y_2\mathbin{-}Y_1$ is unitary (arXiv:2502.20257, `eq:uv`). -/
  sourceU_isUnitaryBetween : (sourceU U S).IsUnitaryBetween
  /-- The gate $v=X_1\mathbin{-}X_2$ is unitary (arXiv:2502.20257, `eq:uv`). -/
  sourceV_isUnitaryBetween : (sourceV U S).IsUnitaryBetween

end SourceFactors

namespace IsMPUCanonicalFormII

/-- **Theorem `thm:mpu` of arXiv:2502.20257** for the compact-SVD source factors:
for a simple MPU tensor in canonical form II, with the recorded diagonal fixed
point $\rho>0$, the factors $X_1,Y_1,X_2,Y_2$ of
arXiv:1703.09188, `Y1Y1X1X1`--`Z1Z2`, give unitary gates $u$ and $v$, and the
thick and curly leg dimensions satisfy $d_ld_r=d^2$.  Clauses (a) and (c) and
the one-sided inverses are fields of the source factors.

Every clause is read off from arXiv:1703.09188, Theorem `ThmFund1`
(lines 563--601), as `MPOTensor.IsMPUCanonicalFormII.isMPUSimple_tfae`.

Source: arXiv:2502.20257, Theorem `thm:mpu`, lines 657--809. -/
theorem sourceFactors_isThreeLegged (hU : IsMPUCanonicalFormII U)
    (hsimple : IsMPUSimple U) :
    (sourceFactors U hU.ρ hU.ρ_posDef).IsThreeLegged where
  leftRank_mul_rightRank := by
    rw [mul_comm]
    exact (hU.isMPUSimple_tfae.out 1 2).mp hsimple
  sourceU_isUnitaryBetween := (hU.isMPUSimple_tfae.out 1 3).mp hsimple
  sourceV_isUnitaryBetween := (hU.isMPUSimple_tfae.out 1 4).mp hsimple

/-- **Theorem `thm:mpu` of arXiv:2502.20257**, existential form: a simple MPU
tensor in canonical form II admits source factors whose tensors
$X_1,Y_1,X_2,Y_2$ satisfy the three-legged decompositions `eq:3-leg`, the
normalized contractions `eq:thm1c` for the recorded fixed point $\rho$, and
have one-sided inverses, such that the gates $u$ and $v$ of `eq:uv` are unitary
and the leg dimensions satisfy $d_ld_r=d^2$.

The hypothesis asks unitarity on chains of length $N\geq2$; unitarity on every
nonempty chain, the convention of arXiv:2502.20257 (lines 198--209), implies it.

Source: arXiv:2502.20257, Theorem `thm:mpu` and line 809. -/
theorem exists_threeLegged (hU : IsMPUCanonicalFormII U) (hsimple : IsMPUSimple U) :
    ∃ S : SourceFactors U hU.ρ,
      (∀ (i j : Fin d) (α β : Fin D),
        (S.X₁ * S.Y₁) (i, β) (α, j) = U i j α β ∧
          (S.X₂ * S.Y₂) (α, i) (j, β) = U i j α β) ∧
      (SourceFactors.sourceU U S).IsUnitaryBetween ∧
      (SourceFactors.sourceV U S).IsUnitaryBetween ∧
      S.X₂ᴴ * S.X₂ = 1 ∧ S.X₁ᴴ * sourceWeight (d := d) hU.ρ * S.X₁ = 1 ∧
      S.Y₁ * S.Z₁ = 1 ∧ S.Y₂ * S.Z₂ = 1 ∧
      ℓ[U] * r[U] = d * d := by
  let S := sourceFactors U hU.ρ hU.ρ_posDef
  have h := hU.sourceFactors_isThreeLegged hsimple
  exact ⟨S, fun i j α β ↦ ⟨S.X₁_mul_Y₁_apply U i β α j, S.X₂_mul_Y₂_apply U α i j β⟩,
    h.sourceU_isUnitaryBetween, h.sourceV_isUnitaryBetween, S.X₂_isometry,
    S.X₁_weighted_isometry, S.Y₁_mul_Z₁, S.Y₂_mul_Z₂, h.leftRank_mul_rightRank⟩

end IsMPUCanonicalFormII

end MPOTensor
