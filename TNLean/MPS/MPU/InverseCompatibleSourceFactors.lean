/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.InverseCompatibleComparisonUnitarity

/-!
# The inverse-compatible source factors

The candidate first factors are exactly $X=AY_2^\dagger$ and $Y=X_2^\dagger B$,
where $A=I_d\otimes\overline T$ and $B=T^T\otimes I_d$. Their intermediate
space has dimension $\ell$, whereas the existing source-factor record uses
$r$ for the first cut. We therefore transport this space along the proved
rank equality, using $e:\operatorname{Fin}\ell\simeq\operatorname{Fin}r$.
The first factors in the record are the reindexed $X,Y,Y^\dagger$; the second
factors remain the chosen $X_2,Y_2,Z_2$ without alteration.

Source: arXiv:2502.20257, `eq:modif_XY` (label at line 1995), constructed at lines 5390–5432,
with normalization transported by the comparison unitarity argument
(lines 5444–5487). This constructs the existing `SourceFactors` record at the
actual canonical weight. Its claims are precisely the cut factorizations,
weighted first isometry, ordinary second isometry, and right-inverse identities;
no assertion of all pleasant properties or `eq:UUU` is made here.
-/

open scoped ComplexOrder Matrix

namespace MPOTensor

variable {d D : ℕ} (U : MPOTensor d D) (T : Matrix.unitaryGroup (Fin D) ℂ)

/-- The explicit identification from the candidate first factor space to the
first source-cut factor space. It is `finCongr` of the proved equality
$\ell=r$, not a definitional identification or an arbitrary basis change.
Source: arXiv:2502.20257, lines 5432–5443. -/
noncomputable def inverseCompatibleRankEquiv
    (hT : ∀ i j, physicalAdjointTensor U i j =
      (T : Matrix (Fin D) (Fin D) ℂ)ᴴ * U i j * T) :
    Fin ℓ[U] ≃ Fin r[U] :=
  finCongr (rightRank_eq_leftRank_of_physicalAdjointTensor_eq_unitary_gauge U T hT).symm

variable (hU : IsMPUCanonicalFormII U) (hsimple : IsMPUSimple U)
  (hT : ∀ i j, physicalAdjointTensor U i j =
    (T : Matrix (Fin D) (Fin D) ℂ)ᴴ * U i j * T)
  (σ : ℂ) (hσ : (T : Matrix (Fin D) (Fin D) ℂ) *
    (T : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) = σ • 1)

/-- The actual inverse-compatible candidates, with their first intermediate
space explicitly transported, form source factors at the canonical weight.
The chosen second factors are retained exactly. The first right inverse is
the adjoint of the candidate $Y$, transported by the same rank equivalence.
Source: arXiv:2502.20257, `eq:modif_XY`, constructed at lines 5390–5432, and the normalization
consequence of comparison unitarity (lines 5444–5487). -/
noncomputable def inverseCompatibleSourceFactors : SourceFactors U hU.ρ := by
  let e := inverseCompatibleRankEquiv U T hT
  have hY : inverseCompatibleY₁ U T * (inverseCompatibleY₁ U T)ᴴ = 1 := by
    simpa only [inverseCompatibleY₁, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose] using inverseCompatibleY₁_rightInverse U T
  refine { sourceFactors U hU.ρ hU.ρ_posDef with
    X₁ := Matrix.reindex (Equiv.refl _) e (inverseCompatibleX₁ U T)
    Y₁ := Matrix.reindex e (Equiv.refl _) (inverseCompatibleY₁ U T)
    Z₁ := Matrix.reindex (Equiv.refl _) e ((inverseCompatibleY₁ U T)ᴴ)
    sourceCutM₁_eq := ?_
    X₁_weighted_isometry := ?_
    Y₁_mul_Z₁ := ?_ }
  · change sourceCutM₁ U =
      Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) e (inverseCompatibleX₁ U T) *
        Matrix.reindexLinearEquiv ℂ ℂ e (Equiv.refl _) (inverseCompatibleY₁ U T)
    rw [Matrix.reindexLinearEquiv_mul,
      ← sourceCutM₁_eq_inverseCompatibleX₁_mul_inverseCompatibleY₁ U T hT]
    rfl
  · rw [Matrix.conjTranspose_reindex]
    change Matrix.reindexLinearEquiv ℂ ℂ e (Equiv.refl _) ((inverseCompatibleX₁ U T)ᴴ) *
        Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) (Equiv.refl _) (sourceWeight hU.ρ) *
        Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) e (inverseCompatibleX₁ U T) = 1
    rw [Matrix.reindexLinearEquiv_mul, Matrix.reindexLinearEquiv_mul,
      inverseCompatibleX₁_weighted_isometry U T hU hsimple hT σ hσ,
      Matrix.reindexLinearEquiv_one]
  · change Matrix.reindexLinearEquiv ℂ ℂ e (Equiv.refl _) (inverseCompatibleY₁ U T) *
      Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) e ((inverseCompatibleY₁ U T)ᴴ) = 1
    rw [Matrix.reindexLinearEquiv_mul, hY, Matrix.reindexLinearEquiv_one]

/-- The first left factor is exactly the rank-transported candidate $AY_2^\dagger$.
Source: arXiv:2502.20257, `eq:modif_XY`, constructed at lines 5390–5432. -/
@[simp] theorem inverseCompatibleSourceFactors_X₁ :
    (inverseCompatibleSourceFactors U T hU hsimple hT σ hσ).X₁ =
      Matrix.reindex (Equiv.refl _) (inverseCompatibleRankEquiv U T hT)
        (inverseCompatibleX₁ U T) := rfl

/-- The first right factor is exactly the rank-transported candidate $X_2^\dagger B$.
Source: arXiv:2502.20257, `eq:modif_XY`, constructed at lines 5390–5432. -/
@[simp] theorem inverseCompatibleSourceFactors_Y₁ :
    (inverseCompatibleSourceFactors U T hU hsimple hT σ hσ).Y₁ =
      Matrix.reindex (inverseCompatibleRankEquiv U T hT) (Equiv.refl _)
        (inverseCompatibleY₁ U T) := rfl

/-- The first right inverse is the transported adjoint of the candidate $Y$.
Source: arXiv:2502.20257, lines 5390–5432; its right-inverse property follows
from the original $X_2$ isometry and the unitary dressing $B$. -/
@[simp] theorem inverseCompatibleSourceFactors_Z₁ :
    (inverseCompatibleSourceFactors U T hU hsimple hT σ hσ).Z₁ =
      Matrix.reindex (Equiv.refl _) (inverseCompatibleRankEquiv U T hT)
        ((inverseCompatibleY₁ U T)ᴴ) := rfl

/-- The second left factor is unchanged by the inverse-compatible construction.
Source: arXiv:2502.20257, `eq:modif_XY`, constructed at lines 5390–5432. -/
@[simp] theorem inverseCompatibleSourceFactors_X₂ :
    (inverseCompatibleSourceFactors U T hU hsimple hT σ hσ).X₂ = sourceX₂ U := rfl

/-- The second right factor is unchanged by the inverse-compatible construction.
Source: arXiv:2502.20257, `eq:modif_XY`, constructed at lines 5390–5432. -/
@[simp] theorem inverseCompatibleSourceFactors_Y₂ :
    (inverseCompatibleSourceFactors U T hU hsimple hT σ hσ).Y₂ = sourceY₂ U := rfl

/-- The second right inverse remains the chosen source $Z_2$.
Source: arXiv:2502.20257, lines 5390–5432, using arXiv:1703.09188, `YZ=1`
(lines 503–506) for the unchanged second factorization. -/
@[simp] theorem inverseCompatibleSourceFactors_Z₂ :
    (inverseCompatibleSourceFactors U T hU hsimple hT σ hσ).Z₂ = sourceZ₂ U := rfl

/-- Coordinate correspondence with the literal dressed first-cut candidates:
only the intermediate rank index is transported. This witnesses `eq:modif_XY`
without identifying the two rank types definitionally.
Source: arXiv:2502.20257, lines 5390–5432. -/
theorem inverseCompatibleSourceFactors_apply
    (a : Fin d × Fin D) (b : Fin D × Fin d) (l : Fin ℓ[U]) :
    let S := inverseCompatibleSourceFactors U T hU hsimple hT σ hσ
    let e := inverseCompatibleRankEquiv U T hT
    S.X₁ a (e l) = inverseCompatibleX₁ U T a l ∧
      S.Y₁ (e l) b = inverseCompatibleY₁ U T l b ∧
      S.Z₁ b (e l) = star (inverseCompatibleY₁ U T l b) := by
  simp only [inverseCompatibleSourceFactors_X₁, inverseCompatibleSourceFactors_Y₁,
    inverseCompatibleSourceFactors_Z₁, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.refl_symm, Equiv.refl_apply, Equiv.symm_apply_apply, Matrix.conjTranspose_apply,
    and_self]

end MPOTensor
