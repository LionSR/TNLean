/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Representation.InverseCompatibleComparisonUnitarity
import TNLean.MPS.MPU.Simple.StaircaseUnitarity

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

## Unitary transport of the inverse-compatible source factors

Let $S_0$ be the chosen source factors and $S$ the inverse-compatible source
factors at the same canonical weight. Transport the columns of the proved
unitary comparison $K:r\times\ell$ along the explicit rank equivalence
$e:\operatorname{Fin}\ell\simeq\operatorname{Fin}r$ to obtain a square matrix
$C$. Then $C$ is unitary and $S.X_1=S_0.X_1C$, $S.Y_1=C^\dagger S_0.Y_1$.
Consequently $S.X_1S.X_1^\dagger=S_0.X_1S_0.X_1^\dagger$ and
$S.Y_1^\dagger S.Y_1=S_0.Y_1^\dagger S_0.Y_1$.

Source: arXiv:2502.20257, the comparison at lines 5432–5443, justified as
unitary at lines 5444–5487. This is coordinate transport after that unitarity
proof, not an assumption that the inverse comparison is an adjoint. No
transport formula is asserted for the chosen source right inverse $Z_1$.

## Movement gates for the inverse-compatible source factors

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

section

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

end

section

open scoped ComplexOrder Matrix

namespace MPOTensor

variable {d D : ℕ} (U : MPOTensor d D) (T : Matrix.unitaryGroup (Fin D) ℂ)
  (hU : IsMPUCanonicalFormII U) (hsimple : IsMPUSimple U)
  (hT : ∀ i j, physicalAdjointTensor U i j =
    (T : Matrix (Fin D) (Fin D) ℂ)ᴴ * U i j * T)
  (σ : ℂ) (hσ : (T : Matrix (Fin D) (Fin D) ℂ) *
    (T : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) = σ • 1)

/-- The source records are related by the actual comparison after its column
rank index is transported. Its unitarity is inherited from the proved
rectangular comparison, and the right-factor formula uses the proved
identity $J=K^\dagger$.
Source: arXiv:2502.20257, lines 5432–5443 and 5444–5487. -/
theorem inverseCompatibleSourceFactors_unitary_transport :
    let S₀ := sourceFactors U hU.ρ hU.ρ_posDef
    let S := inverseCompatibleSourceFactors U T hU hsimple hT σ hσ
    let e := inverseCompatibleRankEquiv U T hT
    let K := inverseCompatibleComparisonK U T hU.ρ hU.ρ_posDef
    let C := Matrix.reindex (Equiv.refl _) e K
    C.IsUnitaryBetween ∧ S.X₁ = S₀.X₁ * C ∧ S.Y₁ = Cᴴ * S₀.Y₁ := by
  let e := inverseCompatibleRankEquiv U T hT
  let K := inverseCompatibleComparisonK U T hU.ρ hU.ρ_posDef
  have hK := inverseCompatibleComparisonK_isUnitaryBetween U T hU hsimple hT σ hσ
  have hX := (inverseCompatibleComparison U T hT hU.ρ hU.ρ_posDef).2.1
  have hY := (inverseCompatibleComparison U T hT hU.ρ hU.ρ_posDef).2.2.2.2.2.1
  rw [inverseCompatibleComparisonJ_eq_conjTranspose U T hU hsimple hT σ hσ] at hY
  refine ⟨hK.reindex _ (Equiv.refl _) e, ?_, ?_⟩
  · rw [inverseCompatibleSourceFactors_X₁, hX]
    change Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) e
        (sourceX₁ U hU.ρ hU.ρ_posDef * K) =
      Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) (Equiv.refl _)
        (sourceX₁ U hU.ρ hU.ρ_posDef) *
      Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) e K
    rw [Matrix.reindexLinearEquiv_mul]
  · rw [inverseCompatibleSourceFactors_Y₁, hY, Matrix.conjTranspose_reindex]
    change Matrix.reindexLinearEquiv ℂ ℂ e (Equiv.refl _)
        (Kᴴ * sourceY₁ U hU.ρ hU.ρ_posDef) =
      Matrix.reindexLinearEquiv ℂ ℂ e (Equiv.refl _) Kᴴ *
      Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) (Equiv.refl _)
        (sourceY₁ U hU.ρ hU.ρ_posDef)
    rw [Matrix.reindexLinearEquiv_mul]

/-- The two first-factor Gram matrices on the external source-cut spaces
are unchanged under the proved unitary transport. This does not compare
chosen right inverses or assert further pleasant properties.
Source: arXiv:2502.20257, the normalization transport at lines 5486–5487. -/
theorem inverseCompatibleSourceFactors_gram_eq :
    let S₀ := sourceFactors U hU.ρ hU.ρ_posDef
    let S := inverseCompatibleSourceFactors U T hU hsimple hT σ hσ
    S.X₁ * S.X₁ᴴ = S₀.X₁ * S₀.X₁ᴴ ∧
      S.Y₁ᴴ * S.Y₁ = S₀.Y₁ᴴ * S₀.Y₁ := by
  obtain ⟨hC, hX, hY⟩ :=
    inverseCompatibleSourceFactors_unitary_transport U T hU hsimple hT σ hσ
  let C := Matrix.reindex (Equiv.refl _) (inverseCompatibleRankEquiv U T hT)
    (inverseCompatibleComparisonK U T hU.ρ hU.ρ_posDef)
  have hCC : C * Cᴴ = 1 := hC.2
  constructor
  · rw [hX, Matrix.conjTranspose_mul]
    calc
      _ = (sourceFactors U hU.ρ hU.ρ_posDef).X₁ * (C * Cᴴ) *
          (sourceFactors U hU.ρ hU.ρ_posDef).X₁ᴴ := by simp only [C, Matrix.mul_assoc]
      _ = _ := by rw [hCC, Matrix.mul_one]
  · rw [hY, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      _ = (sourceFactors U hU.ρ hU.ρ_posDef).Y₁ᴴ * (C * Cᴴ) *
          (sourceFactors U hU.ρ hU.ρ_posDef).Y₁ := by simp only [C, Matrix.mul_assoc]
      _ = _ := by rw [hCC, Matrix.mul_one]

end MPOTensor

end

section

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

end
