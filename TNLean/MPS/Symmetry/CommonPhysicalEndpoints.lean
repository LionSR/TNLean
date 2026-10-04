/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.UnitaryGeneralLinearInverse
import TNLean.MPS.Symmetry.PolarFrameEmbedding
import TNLean.MPS.Symmetry.PolarFixedPointEmbedding
import TNLean.MPS.Symmetry.FixedPointGappedPathWitness

/-!
# Two polar embeddings in one physical space

For bond dimensions \(D_0,D_1\), put \(K=D_0+D_1\). The common physical
space is \(\mathbb C^{K^2}\oplus\mathbb C^{d_0}\oplus\mathbb C^{d_1}\).
Each occupied polar frame is sent to its coordinate matrix-unit frame in
the first summand. Its orthogonal complement is retained in its own physical
summand. Thus both embeddings preserve the full physical inner product.

Source context: arXiv:1010.3732, Section II.F.2,
equation eq:1d-sym:jointsym. The two additional summands retain the original
physical directions which do not belong to the isometric polar frame.
-/

open scoped Matrix
namespace MPSTensor

/-- Inclusion in the first physical summand, with zero second component.
Source context: arXiv:1010.3732, Section II.F.2,
equation eq:1d-sym:jointsym. -/
def physicalSumInclusion (m d : ℕ) : Matrix (Fin (m + d)) (Fin m) ℂ :=
  (Matrix.fromRows (1 : Matrix (Fin m) (Fin m) ℂ) (0 : Matrix (Fin d) (Fin m) ℂ)).submatrix
    finSumFinEquiv.symm id

/-- Inclusion of a physical summand preserves the inner product.
Source context: arXiv:1010.3732, Section II.F.2,
equation eq:1d-sym:jointsym. -/
theorem physicalSumInclusion_isometry (m d : ℕ) :
    (physicalSumInclusion m d)ᴴ * physicalSumInclusion m d = 1 := by
  rw [physicalSumInclusion, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  simp [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromRows]

/-- A physical summand is invariant under the direct-sum unitary action.
Source context: arXiv:1010.3732, Section II.F.2,
equation eq:1d-sym:jointsym. -/
theorem physicalSumInclusion_intertwiner {m d : ℕ}
    (V : Matrix.unitaryGroup (Fin m) ℂ) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    (Matrix.unitaryDirectSum V U : Matrix (Fin (m + d)) (Fin (m + d)) ℂ) *
        physicalSumInclusion m d =
      physicalSumInclusion m d * (V : Matrix (Fin m) (Fin m) ℂ) := by
  change (Matrix.fromBlocks (V : Matrix (Fin m) (Fin m) ℂ) 0 0
      (U : Matrix (Fin d) (Fin d) ℂ)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm *
      (Matrix.fromRows 1 0).submatrix finSumFinEquiv.symm id =
    (Matrix.fromRows 1 0).submatrix finSumFinEquiv.symm id * (V : Matrix (Fin m) (Fin m) ℂ)
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_mul_fromRows]
  simpa only [Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    Matrix.fromRows_mul, Matrix.one_mul, Equiv.coe_refl, Matrix.submatrix_id_id] using
    (Matrix.submatrix_mul_equiv
      (Matrix.fromRows (1 : Matrix (Fin m) (Fin m) ℂ) (0 : Matrix (Fin d) (Fin m) ℂ))
      (V : Matrix (Fin m) (Fin m) ℂ) finSumFinEquiv.symm (Equiv.refl (Fin m)) id).symm

/-- Padding a physical matrix adds zero rows after its original rows.
Source context: arXiv:1010.3732, Section II.F.2,
equation eq:1d-sym:jointsym. -/
theorem physicalSumInclusion_mul {m d r : ℕ} (W : Matrix (Fin m) (Fin r) ℂ) :
    physicalSumInclusion m d * W =
      (Matrix.fromRows W (0 : Matrix (Fin d) (Fin r) ℂ)).submatrix finSumFinEquiv.symm id := by
  simpa only [physicalSumInclusion, Matrix.fromRows_mul, Matrix.one_mul, Matrix.zero_mul,
    Equiv.coe_refl, Matrix.submatrix_id_id] using Matrix.submatrix_mul_equiv
      (Matrix.fromRows (1 : Matrix (Fin m) (Fin m) ℂ) (0 : Matrix (Fin d) (Fin m) ℂ))
      W finSumFinEquiv.symm (Equiv.refl (Fin m)) id

/-- The common physical action, with the original two actions retained
on the spectator summands. Source context: arXiv:1010.3732, Section II.F.2,
equation eq:1d-sym:jointsym. -/
def commonPhysicalAction {G : Type} [Group G] {m d₀ d₁ : ℕ}
    (V : G →* Matrix.unitaryGroup (Fin m) ℂ)
    (U₀ : G →* Matrix.unitaryGroup (Fin d₀) ℂ)
    (U₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ) :
    G →* Matrix.unitaryGroup (Fin ((m + d₀) + d₁)) ℂ :=
  Matrix.unitaryDirectSumHom.comp ((Matrix.unitaryDirectSumHom.comp (V.prod U₀)).prod U₁)

/-- The first polar frame enters the first coordinate matrix-unit sector;
its complement is retained in the first spectator space. Source context:
arXiv:1010.3732, Section II.F.2, equation eq:1d-sym:jointsym. -/
noncomputable def commonPhysicalEmbeddingLeft {d₀ D₀ : ℕ} (d₁ D₁ : ℕ)
    (A : MPSTensor d₀ D₀) :
    Matrix (Fin ((((D₀ + D₁) * (D₀ + D₁)) + d₀) + d₁)) (Fin d₀) ℂ :=
  physicalSumInclusion (((D₀ + D₁) * (D₀ + D₁)) + d₀) d₁ *
    polarFrameEmbedding A
      (Matrix.coordinateInclusion (sptPhysicalEmbedding (D := D₀) (Fin.castAddEmb D₁)))

/-- The second polar frame enters the second coordinate matrix-unit sector;
its complement is retained in the second spectator space. Source context:
arXiv:1010.3732, Section II.F.2, equation eq:1d-sym:jointsym. -/
noncomputable def commonPhysicalEmbeddingRight {d₁ D₁ : ℕ} (d₀ D₀ : ℕ)
    (A : MPSTensor d₁ D₁) :
    Matrix (Fin ((((D₀ + D₁) * (D₀ + D₁)) + d₀) + d₁)) (Fin d₁) ℂ :=
  polarFrameEmbedding A
    (physicalSumInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ *
      Matrix.coordinateInclusion (sptPhysicalEmbedding (D := D₁) (Fin.natAddEmb D₀)))

/-- The first full physical embedding is isometric. Source context:
arXiv:1010.3732, Section II.F.2, equation eq:1d-sym:jointsym. -/
theorem commonPhysicalEmbeddingLeft_isometry {d₀ D₀ : ℕ} (d₁ D₁ : ℕ)
    {A : MPSTensor d₀ D₀} (hA : Kraus.IsInjective A) :
    (commonPhysicalEmbeddingLeft d₁ D₁ A)ᴴ * commonPhysicalEmbeddingLeft d₁ D₁ A = 1 := by
  rw [commonPhysicalEmbeddingLeft, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (physicalSumInclusion _ _)ᴴ,
    physicalSumInclusion_isometry, Matrix.one_mul]
  exact polarFrameEmbedding_isometry hA _ (Matrix.coordinateInclusion_isometry _)

/-- The second full physical embedding is isometric. Source context:
arXiv:1010.3732, Section II.F.2, equation eq:1d-sym:jointsym. -/
theorem commonPhysicalEmbeddingRight_isometry {d₁ D₁ : ℕ} (d₀ D₀ : ℕ)
    {A : MPSTensor d₁ D₁} (hA : Kraus.IsInjective A) :
    (commonPhysicalEmbeddingRight d₀ D₀ A)ᴴ * commonPhysicalEmbeddingRight d₀ D₀ A = 1 := by
  have hW :
      (physicalSumInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ *
          Matrix.coordinateInclusion (sptPhysicalEmbedding (D := D₁) (Fin.natAddEmb D₀)))ᴴ *
        (physicalSumInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ *
          Matrix.coordinateInclusion (sptPhysicalEmbedding (D := D₁) (Fin.natAddEmb D₀))) =
        (1 : Matrix (Fin (D₁ * D₁)) (Fin (D₁ * D₁)) ℂ) := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (physicalSumInclusion _ _)ᴴ,
      physicalSumInclusion_isometry, Matrix.one_mul, Matrix.coordinateInclusion_isometry]
  exact polarFrameEmbedding_isometry hA _ hW

private theorem sptKron_mem_unitaryGroup {D : ℕ} (X : GL (Fin D) ℂ)
    (hX : (X : Matrix (Fin D) (Fin D) ℂ) ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    sptKron X ∈ Matrix.unitaryGroup (Fin D × Fin D) ℂ := by
  rw [sptKron, Matrix.coe_gl_inv_eq_conjTranspose_of_mem_unitaryGroup X hX,
    ← Matrix.star_eq_conjTranspose]
  exact Matrix.kronecker_mem_unitary
    (Matrix.transpose_mem_unitaryGroup_iff.mpr hX) (Unitary.star_mem hX)

/-- The common action for two unitary virtual representations with the same
factor system, together with the original physical actions. Source context:
arXiv:1010.3732, Section II.F.2, equation eq:1d-sym:jointsym. -/
noncomputable def commonSptPhysicalAction {G : Type} [Group G] {d₀ d₁ D₀ D₁ : ℕ}
    {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (U₀ : G →* Matrix.unitaryGroup (Fin d₀) ℂ)
    (U₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ) :
    G →* Matrix.unitaryGroup (Fin ((((D₀ + D₁) * (D₀ + D₁)) + d₀) + d₁)) ℂ :=
  commonPhysicalAction
    (sptFixedPointUnitaryAction (ρ₀.directSum ρ₁)
      (fun g => ρ₀.directSum_mem_unitaryGroup ρ₁ g (h₀ g) (h₁ g))) U₀ U₁

/-- The first embedding intertwines the supplied on-site action with the
actual common action. The virtual pair uses the inverse-group convention
of the fixed-point construction. Source: arXiv:1010.3732, Section II.F.2,
equation eq:1d-sym:jointsym. -/
theorem commonPhysicalEmbeddingLeft_intertwiner
    {G : Type} [Group G] {d₀ d₁ D₀ D₁ : ℕ} [NeZero D₀]
    {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (U₀ : G →* Matrix.unitaryGroup (Fin d₀) ℂ)
    (U₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ)
    {A : MPSTensor d₀ D₀} (hA : Kraus.IsInjective A) (g : G)
    (hCov : (U₀ g : Matrix (Fin d₀) (Fin d₀) ℂ) * physicalMatrix A =
      physicalMatrix A * sptKron (sptGauge ρ₀ g)) :
    (commonSptPhysicalAction ρ₀ ρ₁ h₀ h₁ U₀ U₁ g : Matrix _ _ ℂ) *
        commonPhysicalEmbeddingLeft d₁ D₁ A =
      commonPhysicalEmbeddingLeft d₁ D₁ A * (U₀ g : Matrix (Fin d₀) (Fin d₀) ℂ) := by
  let V := sptFixedPointUnitaryAction (ρ₀.directSum ρ₁)
    (fun g => ρ₀.directSum_mem_unitaryGroup ρ₁ g (h₀ g) (h₁ g))
  let K : Matrix.unitaryGroup (Fin D₀ × Fin D₀) ℂ :=
    ⟨sptKron (sptGauge ρ₀ g), sptKron_mem_unitaryGroup _ (h₀ g⁻¹)⟩
  have hE := polarFrameEmbedding_intertwiner hA
    (Matrix.coordinateInclusion (sptPhysicalEmbedding (D := D₀) (Fin.castAddEmb D₁)))
    (U₀ g) (V g) K hCov (sptPhysicalEmbedding_left_intertwiner ρ₀ ρ₁ g)
  change (Matrix.unitaryDirectSum (Matrix.unitaryDirectSum (V g) (U₀ g)) (U₁ g) :
      Matrix (Fin ((((D₀ + D₁) * (D₀ + D₁)) + d₀) + d₁))
        (Fin ((((D₀ + D₁) * (D₀ + D₁)) + d₀) + d₁)) ℂ) *
      (physicalSumInclusion (((D₀ + D₁) * (D₀ + D₁)) + d₀) d₁ * polarFrameEmbedding A
        (Matrix.coordinateInclusion (sptPhysicalEmbedding (D := D₀) (Fin.castAddEmb D₁)))) =
    (physicalSumInclusion (((D₀ + D₁) * (D₀ + D₁)) + d₀) d₁ * polarFrameEmbedding A
      (Matrix.coordinateInclusion (sptPhysicalEmbedding (D := D₀) (Fin.castAddEmb D₁)))) *
      (U₀ g : Matrix (Fin d₀) (Fin d₀) ℂ)
  rw [← Matrix.mul_assoc, physicalSumInclusion_intertwiner, Matrix.mul_assoc, hE,
    ← Matrix.mul_assoc]

/-- The second embedding intertwines the supplied on-site action with the
same common action. Its target intertwiner is derived from the actual
second coordinate matrix-unit sector. Source: arXiv:1010.3732,
Section II.F.2, equation eq:1d-sym:jointsym. -/
theorem commonPhysicalEmbeddingRight_intertwiner
    {G : Type} [Group G] {d₀ d₁ D₀ D₁ : ℕ} [NeZero D₁]
    {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (U₀ : G →* Matrix.unitaryGroup (Fin d₀) ℂ)
    (U₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ)
    {A : MPSTensor d₁ D₁} (hA : Kraus.IsInjective A) (g : G)
    (hCov : (U₁ g : Matrix (Fin d₁) (Fin d₁) ℂ) * physicalMatrix A =
      physicalMatrix A * sptKron (sptGauge ρ₁ g)) :
    (commonSptPhysicalAction ρ₀ ρ₁ h₀ h₁ U₀ U₁ g : Matrix _ _ ℂ) *
        commonPhysicalEmbeddingRight d₀ D₀ A =
      commonPhysicalEmbeddingRight d₀ D₀ A * (U₁ g : Matrix (Fin d₁) (Fin d₁) ℂ) := by
  let V := sptFixedPointUnitaryAction (ρ₀.directSum ρ₁)
    (fun g => ρ₀.directSum_mem_unitaryGroup ρ₁ g (h₀ g) (h₁ g))
  let K : Matrix.unitaryGroup (Fin D₁ × Fin D₁) ℂ :=
    ⟨sptKron (sptGauge ρ₁ g), sptKron_mem_unitaryGroup _ (h₁ g⁻¹)⟩
  have hW :
      (Matrix.unitaryDirectSum (V g) (U₀ g) :
          Matrix (Fin (((D₀ + D₁) * (D₀ + D₁)) + d₀))
            (Fin (((D₀ + D₁) * (D₀ + D₁)) + d₀)) ℂ) *
        (physicalSumInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ *
          Matrix.coordinateInclusion (sptPhysicalEmbedding (D := D₁) (Fin.natAddEmb D₀))) =
      (physicalSumInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ *
        Matrix.coordinateInclusion (sptPhysicalEmbedding (D := D₁) (Fin.natAddEmb D₀)) :
          Matrix (Fin (((D₀ + D₁) * (D₀ + D₁)) + d₀)) (Fin (D₁ * D₁)) ℂ) *
          (Matrix.reindex finProdFinEquiv finProdFinEquiv
            (K : Matrix (Fin D₁ × Fin D₁) (Fin D₁ × Fin D₁) ℂ) :
              Matrix (Fin (D₁ * D₁)) (Fin (D₁ * D₁)) ℂ) := by
    rw [← Matrix.mul_assoc, physicalSumInclusion_intertwiner, Matrix.mul_assoc]
    rw [Matrix.mul_assoc]
    convert congrArg
      (fun M : Matrix (Fin ((D₀ + D₁) * (D₀ + D₁))) (Fin (D₁ * D₁)) ℂ =>
        physicalSumInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ * M)
      (sptPhysicalEmbedding_right_intertwiner ρ₀ ρ₁ g) using 1 <;> rfl
  exact polarFrameEmbedding_intertwiner hA _ (U₁ g)
    (Matrix.unitaryDirectSum (V g) (U₀ g)) K hCov hW

/-- The active matrix-unit space is included in the first of the three
physical summands. Source context: arXiv:1010.3732, Section II.F.2,
equation eq:1d-sym:jointsym. -/
def commonFixedPointInclusion (m d₀ d₁ : ℕ) :
    Matrix (Fin ((m + d₀) + d₁)) (Fin m) ℂ :=
  physicalSumInclusion (m + d₀) d₁ * physicalSumInclusion m d₀

/-- The shared active-space inclusion is isometric. Source context:
arXiv:1010.3732, Section II.F.2, equation eq:1d-sym:jointsym. -/
theorem commonFixedPointInclusion_isometry (m d₀ d₁ : ℕ) :
    (commonFixedPointInclusion m d₀ d₁)ᴴ * commonFixedPointInclusion m d₀ d₁ = 1 := by
  rw [commonFixedPointInclusion, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (physicalSumInclusion (m + d₀) d₁)ᴴ, physicalSumInclusion_isometry,
    Matrix.one_mul, physicalSumInclusion_isometry]

/-- The first polar frame becomes the first coordinate frame under the
shared active-space inclusion. Source context: arXiv:1010.3732,
Section II.F.2, equation eq:1d-sym:jointsym. -/
theorem commonPhysicalEmbeddingLeft_mul_polarIsoMatrix {d₀ D₀ : ℕ} (d₁ D₁ : ℕ)
    {A : MPSTensor d₀ D₀} (hA : Kraus.IsInjective A) :
    commonPhysicalEmbeddingLeft d₁ D₁ A * polarIsoMatrix A =
      commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁ *
        Matrix.coordinateInclusion (sptPhysicalEmbedding (D := D₀) (Fin.castAddEmb D₁)) := by
  rw [commonPhysicalEmbeddingLeft, Matrix.mul_assoc, polarFrameEmbedding,
    Matrix.finIsometricFrameEmbedding_mul_frame _ _
      (isIsometry_polarIsoMatrix_of_isInjective hA), ← physicalSumInclusion_mul,
    commonFixedPointInclusion, Matrix.mul_assoc]

/-- The second polar frame becomes the second coordinate frame under the
same shared active-space inclusion. Source context: arXiv:1010.3732,
Section II.F.2, equation eq:1d-sym:jointsym. -/
theorem commonPhysicalEmbeddingRight_mul_polarIsoMatrix {d₁ D₁ : ℕ} (d₀ D₀ : ℕ)
    {A : MPSTensor d₁ D₁} (hA : Kraus.IsInjective A) :
    commonPhysicalEmbeddingRight d₀ D₀ A * polarIsoMatrix A =
      commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁ *
        Matrix.coordinateInclusion (sptPhysicalEmbedding (D := D₁) (Fin.natAddEmb D₀)) := by
  rw [commonPhysicalEmbeddingRight, polarFrameEmbedding,
    Matrix.finIsometricFrameEmbedding_mul_frame _ _
      (isIsometry_polarIsoMatrix_of_isInjective hA), ← physicalSumInclusion_mul,
    commonFixedPointInclusion, Matrix.mul_assoc]

private theorem sptScale_smul_rotatePhysical_of_polar_frame {d m D : ℕ}
    (A : MPSTensor d D) (E : Matrix (Fin m) (Fin d) ℂ)
    (W : Matrix (Fin m) (Fin (D * D)) ℂ) (h : E * polarIsoMatrix A = W) :
    sptScale D • rotatePhysical E (polarIsometricTensor A) =
      rotatePhysical W (sptFixedPointTensor D) := by
  rw [rotatePhysical_sptFixedPointTensor_eq_ofPhysicalMatrix]
  apply physicalMatrix_injective
  ext i p
  simpa only [physicalMatrix, rotatePhysical_apply, polarIsometricTensor, polarIsoMatrix,
    virtualPairEquiv, ofPhysicalMatrix, Matrix.mul_apply, Matrix.submatrix_apply,
    Pi.smul_apply, Matrix.smul_apply, Finset.sum_apply, Matrix.sum_apply, Prod.eta,
    smul_eq_mul, id_eq,
    Equiv.symm_apply_apply, Finset.mul_sum] using congrArg (sptScale D * ·)
      (congrFun (congrFun h i) (finProdFinEquiv p))

/-- After the standard nonzero normalization, the first polar endpoint is
the first fixed-point tensor in the shared active summand. Source context:
arXiv:1010.3732, Section II.F.2, equation eq:1d-sym:jointsym. -/
theorem sptScale_smul_commonPhysicalEmbeddingLeft_polar_endpoint
    {d₀ D₀ : ℕ} (d₁ D₁ : ℕ) {A : MPSTensor d₀ D₀} (hA : Kraus.IsInjective A) :
    sptScale D₀ • rotatePhysical (commonPhysicalEmbeddingLeft d₁ D₁ A)
        (polarIsometricTensor A) =
      rotatePhysical (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁)
        (embeddedSptFixedPointLeft D₀ D₁) := by
  simpa only [embeddedSptFixedPointLeft_eq_rotatePhysical, rotatePhysical_rotatePhysical]
    using sptScale_smul_rotatePhysical_of_polar_frame A _ _
      (commonPhysicalEmbeddingLeft_mul_polarIsoMatrix d₁ D₁ hA)

/-- After the same standard normalization, the second polar endpoint is
the second fixed-point tensor in the shared active summand. Source context:
arXiv:1010.3732, Section II.F.2, equation eq:1d-sym:jointsym. -/
theorem sptScale_smul_commonPhysicalEmbeddingRight_polar_endpoint
    {d₁ D₁ : ℕ} (d₀ D₀ : ℕ) {A : MPSTensor d₁ D₁} (hA : Kraus.IsInjective A) :
    sptScale D₁ • rotatePhysical (commonPhysicalEmbeddingRight d₀ D₀ A)
        (polarIsometricTensor A) =
      rotatePhysical (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁)
        (embeddedSptFixedPointRight D₀ D₁) := by
  simpa only [embeddedSptFixedPointRight_eq_rotatePhysical, rotatePhysical_rotatePhysical]
    using sptScale_smul_rotatePhysical_of_polar_frame A _ _
      (commonPhysicalEmbeddingRight_mul_polarIsoMatrix d₀ D₀ hA)

/-- The first polar endpoint has the canonical parent interaction of the
first fixed point in the shared active summand. Source context:
arXiv:1010.3732, Sections II.C and II.F.2, equation eq:1d-sym:jointsym. -/
theorem parentInteraction_commonPhysicalEmbeddingLeft_polar_endpoint
    {d₀ D₀ : ℕ} [NeZero D₀] (d₁ D₁ : ℕ)
    {A : MPSTensor d₀ D₀} (hA : Kraus.IsInjective A) (L : ℕ) :
    parentInteraction (rotatePhysical (commonPhysicalEmbeddingLeft d₁ D₁ A)
        (polarIsometricTensor A)) L =
      parentInteraction
        (rotatePhysical (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁)
          (embeddedSptFixedPointLeft D₀ D₁)) L := by
  apply parentInteraction_eq_of_groundSpace_eq
  rw [← sptScale_smul_commonPhysicalEmbeddingLeft_polar_endpoint d₁ D₁ hA,
    groundSpace_smul_eq _ _ sptScale_ne_zero]

/-- The second polar endpoint has the canonical parent interaction of the
second fixed point in the same shared active summand. Source context:
arXiv:1010.3732, Sections II.C and II.F.2, equation eq:1d-sym:jointsym. -/
theorem parentInteraction_commonPhysicalEmbeddingRight_polar_endpoint
    {d₁ D₁ : ℕ} [NeZero D₁] (d₀ D₀ : ℕ)
    {A : MPSTensor d₁ D₁} (hA : Kraus.IsInjective A) (L : ℕ) :
    parentInteraction (rotatePhysical (commonPhysicalEmbeddingRight d₀ D₀ A)
        (polarIsometricTensor A)) L =
      parentInteraction
        (rotatePhysical (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁)
          (embeddedSptFixedPointRight D₀ D₁)) L := by
  apply parentInteraction_eq_of_groundSpace_eq
  rw [← sptScale_smul_commonPhysicalEmbeddingRight_polar_endpoint d₀ D₀ hA,
    groundSpace_smul_eq _ _ sptScale_ne_zero]

/-- The shared active-space inclusion intertwines the active action with
the full three-summand physical action. Source context: arXiv:1010.3732,
Section II.F.2, equation eq:1d-sym:jointsym. -/
theorem commonFixedPointInclusion_intertwiner
    {G : Type} [Group G] {m d₀ d₁ : ℕ}
    (V : G →* Matrix.unitaryGroup (Fin m) ℂ)
    (U₀ : G →* Matrix.unitaryGroup (Fin d₀) ℂ)
    (U₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ) (g : G) :
    (commonPhysicalAction V U₀ U₁ g : Matrix (Fin ((m + d₀) + d₁))
        (Fin ((m + d₀) + d₁)) ℂ) * commonFixedPointInclusion m d₀ d₁ =
      commonFixedPointInclusion m d₀ d₁ * (V g : Matrix (Fin m) (Fin m) ℂ) := by
  change (Matrix.unitaryDirectSum (Matrix.unitaryDirectSum (V g) (U₀ g)) (U₁ g) :
      Matrix (Fin ((m + d₀) + d₁)) (Fin ((m + d₀) + d₁)) ℂ) *
      (physicalSumInclusion (m + d₀) d₁ * physicalSumInclusion m d₀) =
    (physicalSumInclusion (m + d₀) d₁ * physicalSumInclusion m d₀) *
      (V g : Matrix (Fin m) (Fin m) ℂ)
  rw [← Matrix.mul_assoc, physicalSumInclusion_intertwiner, Matrix.mul_assoc,
    physicalSumInclusion_intertwiner, ← Matrix.mul_assoc]

end MPSTensor
