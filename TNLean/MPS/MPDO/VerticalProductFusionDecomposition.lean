/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.VerticalBlockedOperatorRepresentations
import TNLean.MPS.MPDO.VerticalCoisometry
import TNLean.MPS.MPDO.HorizontalBlocking
import TNLean.MPS.CanonicalForm.BNTCharacterization
import TNLean.MPS.CanonicalForm.BNTTransport
import TNLean.MPS.CanonicalForm.NormalCommutant
import TNLean.MPS.MPDO.FigureEightPairwise
import TNLean.MPS.MPDO.NormalizedGroupedSectors
import TNLean.MPS.MPDO.VerticalBNTConstruction
import TNLean.MPS.MPDO.VerticalBNT
import TNLean.MPS.MPDO.VerticalSpectral
import TNLean.MPS.Tactic.Basic

/-!
# Positive fusion decompositions of vertical product tensors

This file begins the construction of the positive unitary decompositions of
the products of vertical basis-of-normal-tensors sectors in CPSV16,
Appendix C.4, lines 2020--2029.

## Main results

* `RetainedProductSpectralFamily`: the simultaneous active normal corners of
  all retained copy-pair tensors, with their local inclusions.
* `exists_retainedProductSpectralFamily`: existence under the vertical
  reconstruction, horizontal canonical-form, and positivity hypotheses.
* `RetainedProductSpectralFamily.flat_sameMPV₂Pos`: the single enumerated
  active family reconstructs the retained product at every positive length.
* `FlatBlockedBNTComparison`: the one-way gauge-phase comparison from active
  product corners to a blocked two-site BNT.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.4, lines 2020--2029
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

noncomputable section

namespace MPSTensor

/-- Projector closure and absence of periodic vectors pass through an exact
coisometric reconstruction.

If $U$ maps the ambient bond space onto retained coordinates, then $U^\dagger$
is an isometry intertwining the retained tensor with the ambient tensor. Exact
reconstruction makes its range reducing, so projector closure descends by
compression and every peripheral eigenvector of the retained tensor is also
one of the ambient tensor.

Source: CPSV16, canonical nonzero-sector decomposition at lines 214--230. -/
theorem projectorClosure_and_noPeriodicVectors_of_coisometry_reconstruction
    {d D n : ℕ} (A : MPSTensor d D) (C : MPSTensor d n)
    (U : Matrix (Fin n) (Fin D) ℂ) (hU : U * Uᴴ = 1)
    (hreconstruct : ∀ i, A i = Uᴴ * C i * U)
    (hClosure : HasInvariantProjectorClosure A)
    (hPer : HasNoPeriodicVectors A) :
    HasInvariantProjectorClosure C ∧ HasNoPeriodicVectors C := by
  let V : Matrix (Fin D) (Fin n) ℂ := Uᴴ
  have hV : Vᴴ * V = 1 := by
    simpa [V] using hU
  have hint : ∀ i, A i * V = V * C i := by
    intro i
    calc
      A i * V = (Uᴴ * C i * U) * Uᴴ := by rw [hreconstruct]
      _ = Uᴴ * C i * (U * Uᴴ) := by simp only [Matrix.mul_assoc]
      _ = V * C i := by rw [hU, Matrix.mul_one]
  have hComm : ∀ i, A i * (V * Vᴴ) = (V * Vᴴ) * A i := by
    intro i
    have hsupportLeft : A i * (V * Vᴴ) = A i := by
      calc
        A i * (V * Vᴴ) = (A i * V) * Vᴴ := (Matrix.mul_assoc _ _ _).symm
        _ = (V * C i) * Vᴴ := by rw [hint]
        _ = A i := by simpa [V] using (hreconstruct i).symm
    have hsupportRight : (V * Vᴴ) * A i = A i := by
      calc
        (V * Vᴴ) * A i = (V * Vᴴ) * (V * C i * Vᴴ) := by
          rw [show A i = V * C i * Vᴴ by simpa [V] using hreconstruct i]
        _ = V * C i * Vᴴ := by
          simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ V, hV,
            Matrix.one_mul]
        _ = A i := by simpa [V] using (hreconstruct i).symm
    rw [hsupportLeft, hsupportRight]
  have hcompress : (fun i => Vᴴ * A i * V) = C := by
    funext i
    calc
      Vᴴ * A i * V = Vᴴ * (V * C i * Vᴴ) * V := by
        rw [show A i = V * C i * Vᴴ by simpa [V] using hreconstruct i]
      _ = C i := by
        simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ V, hV,
          Matrix.one_mul, Matrix.mul_one]
  constructor
  · rw [← hcompress]
    exact hasInvariantProjectorClosure_compress_of_commutes A hClosure V hV hComm
  · exact hPer.of_isometry_intertwine V hV hint

end MPSTensor

namespace MPOTensor

/-- The Kronecker square of a rectangular vertical coisometry, with both
product index spaces encoded by the standard finite-product equivalence. -/
noncomputable def verticalCoisometrySquare {d n : ℕ}
    (U : Matrix (Fin n) (Fin d) ℂ) :
    Matrix (Fin (n * n)) (Fin (d * d)) ℂ :=
  (U ⊗ₖ U).submatrix finProdFinEquiv.symm finProdFinEquiv.symm

/-- The Kronecker square of a coisometry is again a coisometry. -/
theorem verticalCoisometrySquare_isCoisometry {d n : ℕ}
    (U : Matrix (Fin n) (Fin d) ℂ) (hU : U * Uᴴ = 1) :
    verticalCoisometrySquare U * (verticalCoisometrySquare U)ᴴ = 1 := by
  unfold verticalCoisometrySquare
  rw [Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv _ _ _ finProdFinEquiv.symm _,
    Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hU,
    Matrix.one_kronecker_one, Matrix.submatrix_one_equiv]

private def verticalCopyLabelEquiv {g : ℕ} (dim mult : Fin g → ℕ) :
    ((α : Fin g) × (Fin (mult α) × Fin (dim α))) ≃
      (p : (α : Fin g) × Fin (mult α)) × Fin (dim p.1) where
  toFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  invFun x := ⟨x.1.1, (x.1.2, x.2)⟩
  left_inv x := by
    rcases x with ⟨α, q, i⟩
    rfl
  right_inv x := by
    rcases x with ⟨⟨α, q⟩, i⟩
    rfl

/-- The assembled vertical bond coordinates, grouped first by a retained BNT
copy and then by a coordinate in its simple bond space.

Source: CPSV16, Appendix C.4, lines 1955--1971. -/
def verticalCopyCoordinateEquiv {g : ℕ} (dim mult : Fin g → ℕ) :
    Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q) ≃
      (p : (α : Fin g) × Fin (mult α)) × Fin (dim p.1) :=
  (verticalSectorFinEquiv dim mult).symm.trans
    (verticalCopyLabelEquiv dim mult)

/-- The inverse copy-coordinate map is the canonical vertical-sector
coordinate map.

Source: CPSV16, Appendix C.4, lines 1955--1971. -/
@[simp]
theorem verticalCopyCoordinateEquiv_symm_apply
    {g : ℕ} (dim mult : Fin g → ℕ)
    (p : (α : Fin g) × Fin (mult α)) (i : Fin (dim p.1)) :
    (verticalCopyCoordinateEquiv dim mult).symm ⟨p, i⟩ =
      verticalSectorFinEquiv dim mult ⟨p.1, (p.2, i)⟩ := by
  rfl

private theorem verticalAssembledTensor_apply_copy_same
    {g d : ℕ} (dim mult : Fin g → ℕ)
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (B : (α : Fin g) → MPSTensor d (dim α))
    (α : Fin g) (q : Fin (mult α)) (v : Fin d) (i j : Fin (dim α)) :
    verticalAssembledTensor dim mult weight B v
        (verticalSectorFinEquiv dim mult ⟨α, (q, i)⟩)
        (verticalSectorFinEquiv dim mult ⟨α, (q, j)⟩) =
      weight α q * B α v i j := by
  unfold verticalAssembledTensor MPSTensor.toTensorFromBlocks
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
    verticalSectorFinEquiv_outer_symm]
  rw [Matrix.blockDiagonal'_apply_eq]
  let p := finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨α, q⟩)
  have hp : p = ⟨α, q⟩ := finSigmaFinEquiv.symm_apply_apply ⟨α, q⟩
  have hdim : dim p.1 = dim α := congrArg (fun s => dim s.1) hp
  have hweight : weight p.1 p.2 = weight α q :=
    congrArg (fun s => weight s.1 s.2) hp
  let block (s : (α : Fin g) × Fin (mult α)) := B s.1 v
  let packed (s : (α : Fin g) × Fin (mult α)) :
      (r : (α : Fin g) × Fin (mult α)) ×
        Matrix (Fin (dim r.1)) (Fin (dim r.1)) ℂ :=
    ⟨s, block s⟩
  have hpacked : packed p = packed ⟨α, q⟩ := congrArg packed hp
  have hblock : HEq (block p) (block ⟨α, q⟩) :=
    (Sigma.mk.inj_iff.mp hpacked).2
  have hentry := (Fin.heq_fun₂_iff hdim.symm hdim.symm).mp hblock.symm i j
  simp only [verticalCopyWeights, verticalCopyBlocks]
  change weight p.1 p.2 * block p (Fin.cast _ i) (Fin.cast _ j) = _
  rw [hweight]
  exact congrArg (weight α q * ·) hentry.symm

private theorem verticalAssembledTensor_apply_copy_ne
    {g d : ℕ} (dim mult : Fin g → ℕ)
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (B : (α : Fin g) → MPSTensor d (dim α))
    {α β : Fin g} {q : Fin (mult α)} {r : Fin (mult β)}
    (h : (⟨α, q⟩ : (α : Fin g) × Fin (mult α)) ≠ ⟨β, r⟩)
    (v : Fin d) (i : Fin (dim α)) (j : Fin (dim β)) :
    verticalAssembledTensor dim mult weight B v
        (verticalSectorFinEquiv dim mult ⟨α, (q, i)⟩)
        (verticalSectorFinEquiv dim mult ⟨β, (r, j)⟩) = 0 := by
  have hflat : finSigmaFinEquiv ⟨α, q⟩ ≠ finSigmaFinEquiv ⟨β, r⟩ :=
    fun hEq => h (finSigmaFinEquiv.injective hEq)
  simp [verticalAssembledTensor, MPSTensor.toTensorFromBlocks,
    Matrix.reindex_apply, Matrix.submatrix_apply,
    verticalSectorFinEquiv_outer_symm, Matrix.blockDiagonal'_apply_ne,
    hflat]

/-- In retained-copy coordinates, the assembled vertical tensor is the
block diagonal of its weighted simple blocks.

Source: CPSV16, Appendix C.4, lines 1955--1971. -/
theorem verticalAssembledTensor_reindex_copyCoordinates
    {g d : ℕ} (dim mult : Fin g → ℕ)
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (A : (α : Fin g) → MPSTensor d (dim α)) (v : Fin d) :
    verticalAssembledTensor dim mult weight A v =
      Matrix.reindex (verticalCopyCoordinateEquiv dim mult).symm
        (verticalCopyCoordinateEquiv dim mult).symm
        (Matrix.blockDiagonal' fun p => weight p.1 p.2 • A p.1 v) := by
  apply Matrix.ext
  intro i j
  obtain ⟨⟨p, ip⟩, rfl⟩ :=
    (verticalCopyCoordinateEquiv dim mult).symm.surjective i
  obtain ⟨⟨q, jq⟩, rfl⟩ :=
    (verticalCopyCoordinateEquiv dim mult).symm.surjective j
  simp only [Matrix.reindex_apply, Equiv.symm_symm,
    Matrix.submatrix_apply, Equiv.apply_symm_apply]
  by_cases hpq : p = q
  · subst q
    rw [Matrix.blockDiagonal'_apply_eq]
    exact verticalAssembledTensor_apply_copy_same
      dim mult weight A p.1 p.2 v ip jq
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hpq]
    exact verticalAssembledTensor_apply_copy_ne
      dim mult weight A hpq v ip jq

/-- The canonical inclusion of one retained copy into the assembled vertical
bond space.

Source: CPSV16, Appendix C.4, lines 1955--1971. -/
noncomputable def verticalCopyBlockInclusion
    {g : ℕ} (dim mult : Fin g → ℕ)
    (p : (α : Fin g) × Fin (mult α)) :
    Matrix
      (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin (dim p.1)) ℂ :=
  (Matrix.sigmaBlockInclusion
    (fun q : (α : Fin g) × Fin (mult α) ↦ Fin (dim q.1)) p).submatrix
      (verticalCopyCoordinateEquiv dim mult) (Equiv.refl _)

/-- Every retained-copy inclusion is an isometry, including when its domain
has dimension zero.

Source: CPSV16, Appendix C.4, lines 1955--1971. -/
theorem verticalCopyBlockInclusion_isometry
    {g : ℕ} (dim mult : Fin g → ℕ)
    (p : (α : Fin g) × Fin (mult α)) :
    (verticalCopyBlockInclusion dim mult p)ᴴ *
        verticalCopyBlockInclusion dim mult p = 1 := by
  classical
  unfold verticalCopyBlockInclusion
  rw [Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv _ _ _ (verticalCopyCoordinateEquiv dim mult) _,
    Matrix.sigmaBlockInclusion_isometry,
    Matrix.submatrix_one_equiv]

/-- A retained-copy inclusion intertwines its weighted simple block with the
assembled vertical tensor.

Source: CPSV16, Appendix C.4, lines 1955--1971. -/
theorem verticalAssembledTensor_mul_verticalCopyBlockInclusion
    {g d : ℕ} (dim mult : Fin g → ℕ)
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (A : (α : Fin g) → MPSTensor d (dim α))
    (p : (α : Fin g) × Fin (mult α)) (v : Fin d) :
    verticalAssembledTensor dim mult weight A v *
        verticalCopyBlockInclusion dim mult p =
      verticalCopyBlockInclusion dim mult p *
        (weight p.1 p.2 • A p.1 v) := by
  classical
  let blockIndex := fun q : (α : Fin g) × Fin (mult α) ↦ Fin (dim q.1)
  let C := fun q : (α : Fin g) × Fin (mult α) ↦ weight q.1 q.2 • A q.1 v
  let E := Matrix.sigmaBlockInclusion blockIndex p
  have h := Matrix.blockDiagonal'_mul_sigmaBlockInclusion C p
  have hdiag := verticalAssembledTensor_reindex_copyCoordinates
    dim mult weight A v
  have hleft : verticalAssembledTensor dim mult weight A v *
      verticalCopyBlockInclusion dim mult p =
        (Matrix.blockDiagonal' C * E).submatrix
          (verticalCopyCoordinateEquiv dim mult) (Equiv.refl _) := by
    rw [hdiag]
    simpa only [verticalCopyBlockInclusion, blockIndex, C, E,
      Matrix.reindex_apply, Equiv.symm_symm,
      Matrix.submatrix_id_id] using
      (Matrix.submatrix_mul_equiv (Matrix.blockDiagonal' C) E
        (verticalCopyCoordinateEquiv dim mult)
        (verticalCopyCoordinateEquiv dim mult) (Equiv.refl _))
  have hright : verticalCopyBlockInclusion dim mult p *
      (weight p.1 p.2 • A p.1 v) =
        (E * C p).submatrix
          (verticalCopyCoordinateEquiv dim mult) (Equiv.refl _) := by
    have hC : (C p).submatrix (Equiv.refl _) (Equiv.refl _) = C p := by
      rfl
    calc
      verticalCopyBlockInclusion dim mult p * C p =
          verticalCopyBlockInclusion dim mult p *
            (C p).submatrix (Equiv.refl _) (Equiv.refl _) := by
        rw [hC]
      _ = (E * C p).submatrix
          (verticalCopyCoordinateEquiv dim mult) (Equiv.refl _) := by
        simpa only [verticalCopyBlockInclusion, blockIndex, C, E] using
          (Matrix.submatrix_mul_equiv E (C p)
            (verticalCopyCoordinateEquiv dim mult)
            (Equiv.refl _) (Equiv.refl _))
  have hpull := congrArg
    (fun X ↦ X.submatrix
      (verticalCopyCoordinateEquiv dim mult) (Equiv.refl _)) h
  exact hleft.trans (hpull.trans hright.symm)

/-- The adjoint retained-copy inclusion satisfies the reverse intertwining
identity.

Source: CPSV16, Appendix C.4, lines 1955--1971. -/
theorem verticalCopyBlockInclusion_conjTranspose_mul_verticalAssembledTensor
    {g d : ℕ} (dim mult : Fin g → ℕ)
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (A : (α : Fin g) → MPSTensor d (dim α))
    (p : (α : Fin g) × Fin (mult α)) (v : Fin d) :
    (verticalCopyBlockInclusion dim mult p)ᴴ *
        verticalAssembledTensor dim mult weight A v =
      (weight p.1 p.2 • A p.1 v) *
        (verticalCopyBlockInclusion dim mult p)ᴴ := by
  classical
  let blockIndex := fun q : (α : Fin g) × Fin (mult α) ↦ Fin (dim q.1)
  let C := fun q : (α : Fin g) × Fin (mult α) ↦ weight q.1 q.2 • A q.1 v
  let E := Matrix.sigmaBlockInclusion blockIndex p
  have h := Matrix.sigmaBlockInclusion_conjTranspose_mul_blockDiagonal' C p
  have hdiag := verticalAssembledTensor_reindex_copyCoordinates
    dim mult weight A v
  have hleft : (verticalCopyBlockInclusion dim mult p)ᴴ *
      verticalAssembledTensor dim mult weight A v =
        (Eᴴ * Matrix.blockDiagonal' C).submatrix
          (Equiv.refl _) (verticalCopyCoordinateEquiv dim mult) := by
    rw [hdiag]
    simpa only [verticalCopyBlockInclusion, blockIndex, C, E,
      Matrix.reindex_apply, Equiv.symm_symm, Matrix.conjTranspose_submatrix,
      Matrix.submatrix_id_id] using
      (Matrix.submatrix_mul_equiv Eᴴ (Matrix.blockDiagonal' C)
        (Equiv.refl _) (verticalCopyCoordinateEquiv dim mult)
        (verticalCopyCoordinateEquiv dim mult))
  have hright : (weight p.1 p.2 • A p.1 v) *
      (verticalCopyBlockInclusion dim mult p)ᴴ =
        (C p * Eᴴ).submatrix
          (Equiv.refl _) (verticalCopyCoordinateEquiv dim mult) := by
    have hC : (C p).submatrix (Equiv.refl _) (Equiv.refl _) = C p := by
      rfl
    calc
      C p * (verticalCopyBlockInclusion dim mult p)ᴴ =
          (C p).submatrix (Equiv.refl _) (Equiv.refl _) *
            (verticalCopyBlockInclusion dim mult p)ᴴ := by
        rw [hC]
      _ = (C p * Eᴴ).submatrix
          (Equiv.refl _) (verticalCopyCoordinateEquiv dim mult) := by
        simpa only [verticalCopyBlockInclusion, blockIndex, C, E,
          Matrix.conjTranspose_submatrix] using
          (Matrix.submatrix_mul_equiv (C p) Eᴴ
            (Equiv.refl _) (Equiv.refl _)
            (verticalCopyCoordinateEquiv dim mult))
  have hpull := congrArg
    (fun X ↦ X.submatrix
      (Equiv.refl _) (verticalCopyCoordinateEquiv dim mult)) h
  exact hleft.trans (hpull.trans hright.symm)

/-- Compression by a retained-copy inclusion selects its weighted simple
block.

Source: CPSV16, Appendix C.4, lines 1955--1971. -/
theorem verticalCopyBlockInclusion_compression
    {g d : ℕ} (dim mult : Fin g → ℕ)
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (A : (α : Fin g) → MPSTensor d (dim α))
    (p : (α : Fin g) × Fin (mult α)) (v : Fin d) :
    weight p.1 p.2 • A p.1 v =
      (verticalCopyBlockInclusion dim mult p)ᴴ *
        verticalAssembledTensor dim mult weight A v *
          verticalCopyBlockInclusion dim mult p := by
  rw [verticalCopyBlockInclusion_conjTranspose_mul_verticalAssembledTensor,
    Matrix.mul_assoc, verticalCopyBlockInclusion_isometry, Matrix.mul_one]

/-- The inclusion of the first retained copy of a blocked BNT label into the
blocked vertical bond space.

Source: CPSV16, Appendix C.4, lines 2025--2029. -/
noncomputable def blockedReferenceInclusion
    {g d : ℕ} (dim mult : Fin g → ℕ) (hMult : ∀ γ, 0 < mult γ)
    (U : Matrix
      (Fin (∑ q : Fin (∑ γ : Fin g, mult γ), verticalCopyDim dim mult q))
      (Fin (d * d)) ℂ)
    (γ : Fin g) : Matrix (Fin (d * d)) (Fin (dim γ)) ℂ :=
  Uᴴ * verticalCopyBlockInclusion dim mult ⟨γ, ⟨0, hMult γ⟩⟩

/-- The distinguished blocked reference inclusion is an isometry.

Source: CPSV16, Appendix C.4, lines 2025--2029. -/
theorem blockedReferenceInclusion_isometry
    {g d : ℕ} (dim mult : Fin g → ℕ) (hMult : ∀ γ, 0 < mult γ)
    (U : Matrix
      (Fin (∑ q : Fin (∑ γ : Fin g, mult γ), verticalCopyDim dim mult q))
      (Fin (d * d)) ℂ)
    (hU : U * Uᴴ = 1) (γ : Fin g) :
    (blockedReferenceInclusion dim mult hMult U γ)ᴴ *
        blockedReferenceInclusion dim mult hMult U γ = 1 := by
  let E := verticalCopyBlockInclusion dim mult ⟨γ, ⟨0, hMult γ⟩⟩
  calc
    (blockedReferenceInclusion dim mult hMult U γ)ᴴ *
        blockedReferenceInclusion dim mult hMult U γ =
      Eᴴ * U * (Uᴴ * E) := by
        simp only [blockedReferenceInclusion, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_conjTranspose, E, Matrix.mul_assoc]
    _ = Eᴴ * (U * Uᴴ) * E := by
      simp only [Matrix.mul_assoc]
    _ = Eᴴ * E := by rw [hU, Matrix.mul_one]
    _ = 1 := verticalCopyBlockInclusion_isometry dim mult _

/-- The distinguished reference copy intertwines with the blocked vertical
tensor.

Source: CPSV16, Appendix C.4, lines 2025--2029. -/
theorem blockedReference_intertwine
    {g d D : ℕ} (M : MPOTensor d D)
    (dim mult : Fin g → ℕ) (hMult : ∀ γ, 0 < mult γ)
    (weight : (γ : Fin g) → Fin (mult γ) → ℂ)
    (A : (γ : Fin g) → MPSTensor (D * D) (dim γ))
    (U : Matrix
      (Fin (∑ q : Fin (∑ γ : Fin g, mult γ), verticalCopyDim dim mult q))
      (Fin (d * d)) ℂ)
    (hU : U * Uᴴ = 1)
    (hReconstruct : ∀ ab, verticalTensor (blockTwo M) ab =
      Uᴴ * verticalAssembledTensor dim mult weight A ab * U)
    (γ : Fin g) (ab : Fin (D * D)) :
    verticalTensor (blockTwo M) ab *
        blockedReferenceInclusion dim mult hMult U γ =
      blockedReferenceInclusion dim mult hMult U γ *
        (weight γ ⟨0, hMult γ⟩ • A γ ab) := by
  let E := verticalCopyBlockInclusion dim mult ⟨γ, ⟨0, hMult γ⟩⟩
  calc
    verticalTensor (blockTwo M) ab *
        blockedReferenceInclusion dim mult hMult U γ =
      (Uᴴ * verticalAssembledTensor dim mult weight A ab * U) *
        (Uᴴ * E) := by rw [hReconstruct ab]; rfl
    _ = Uᴴ * verticalAssembledTensor dim mult weight A ab *
        (U * Uᴴ) * E := by simp only [Matrix.mul_assoc]
    _ = Uᴴ * (verticalAssembledTensor dim mult weight A ab * E) := by
      rw [hU]
      simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = Uᴴ * (E * (weight γ ⟨0, hMult γ⟩ • A γ ab)) := by
      rw [verticalAssembledTensor_mul_verticalCopyBlockInclusion]
    _ = blockedReferenceInclusion dim mult hMult U γ *
        (weight γ ⟨0, hMult γ⟩ • A γ ab) := by
      simp only [blockedReferenceInclusion, E, Matrix.mul_assoc]

/-- The adjoint distinguished reference inclusion satisfies the reverse
intertwining identity.

Source: CPSV16, Appendix C.4, lines 2025--2029. -/
theorem blockedReference_intertwine_adjoint
    {g d D : ℕ} (M : MPOTensor d D)
    (dim mult : Fin g → ℕ) (hMult : ∀ γ, 0 < mult γ)
    (weight : (γ : Fin g) → Fin (mult γ) → ℂ)
    (A : (γ : Fin g) → MPSTensor (D * D) (dim γ))
    (U : Matrix
      (Fin (∑ q : Fin (∑ γ : Fin g, mult γ), verticalCopyDim dim mult q))
      (Fin (d * d)) ℂ)
    (hU : U * Uᴴ = 1)
    (hReconstruct : ∀ ab, verticalTensor (blockTwo M) ab =
      Uᴴ * verticalAssembledTensor dim mult weight A ab * U)
    (γ : Fin g) (ab : Fin (D * D)) :
    (blockedReferenceInclusion dim mult hMult U γ)ᴴ *
        verticalTensor (blockTwo M) ab =
      (weight γ ⟨0, hMult γ⟩ • A γ ab) *
        (blockedReferenceInclusion dim mult hMult U γ)ᴴ := by
  let E := verticalCopyBlockInclusion dim mult ⟨γ, ⟨0, hMult γ⟩⟩
  calc
    (blockedReferenceInclusion dim mult hMult U γ)ᴴ *
        verticalTensor (blockTwo M) ab =
      (Eᴴ * U) *
        (Uᴴ * verticalAssembledTensor dim mult weight A ab * U) := by
      rw [hReconstruct ab]
      simp only [blockedReferenceInclusion, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, E]
    _ = Eᴴ * (U * Uᴴ) * verticalAssembledTensor dim mult weight A ab * U := by
      simp only [Matrix.mul_assoc]
    _ = (Eᴴ * verticalAssembledTensor dim mult weight A ab) * U := by
      rw [hU]
      simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = ((weight γ ⟨0, hMult γ⟩ • A γ ab) * Eᴴ) * U := by
      rw [verticalCopyBlockInclusion_conjTranspose_mul_verticalAssembledTensor]
    _ = (weight γ ⟨0, hMult γ⟩ • A γ ab) *
        (blockedReferenceInclusion dim mult hMult U γ)ᴴ := by
      simp only [blockedReferenceInclusion, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, E, Matrix.mul_assoc]

/-- Compression by the distinguished reference inclusion selects its
distinguished weighted blocked BNT copy.

Source: CPSV16, Appendix C.4, lines 2025--2029. -/
theorem blockedReference_compression
    {g d D : ℕ} (M : MPOTensor d D)
    (dim mult : Fin g → ℕ) (hMult : ∀ γ, 0 < mult γ)
    (weight : (γ : Fin g) → Fin (mult γ) → ℂ)
    (A : (γ : Fin g) → MPSTensor (D * D) (dim γ))
    (U : Matrix
      (Fin (∑ q : Fin (∑ γ : Fin g, mult γ), verticalCopyDim dim mult q))
      (Fin (d * d)) ℂ)
    (hU : U * Uᴴ = 1)
    (hReconstruct : ∀ ab, verticalTensor (blockTwo M) ab =
      Uᴴ * verticalAssembledTensor dim mult weight A ab * U)
    (γ : Fin g) (ab : Fin (D * D)) :
    weight γ ⟨0, hMult γ⟩ • A γ ab =
      (blockedReferenceInclusion dim mult hMult U γ)ᴴ *
        verticalTensor (blockTwo M) ab *
          blockedReferenceInclusion dim mult hMult U γ := by
  rw [blockedReference_intertwine_adjoint M dim mult hMult weight A U hU
      hReconstruct γ ab,
    Matrix.mul_assoc,
    blockedReferenceInclusion_isometry dim mult hMult U hU γ,
    Matrix.mul_one]

private def verticalProductSectorEquiv {g : ℕ} (dim mult : Fin g → ℕ) :
    ((α : Fin g) × (Fin (mult α) × Fin (dim α))) ×
      ((α : Fin g) × (Fin (mult α) × Fin (dim α))) ≃
      (p : ((α : Fin g) × Fin (mult α)) × ((α : Fin g) × Fin (mult α))) ×
        (Fin (dim p.1.1) × Fin (dim p.2.1)) where
  toFun x :=
    ⟨(⟨x.1.1, x.1.2.1⟩, ⟨x.2.1, x.2.2.1⟩), (x.1.2.2, x.2.2.2)⟩
  invFun x :=
    (⟨x.1.1.1, (x.1.1.2, x.2.1)⟩, ⟨x.1.2.1, (x.1.2.2, x.2.2)⟩)
  left_inv x := by
    rcases x with ⟨⟨α, q, i⟩, ⟨β, r, j⟩⟩
    rfl
  right_inv x := by
    rcases x with ⟨⟨⟨α, q⟩, ⟨β, r⟩⟩, ⟨i, j⟩⟩
    rfl

/-- The canonical coordinates on the square of the retained vertical bond:
a pair of BNT copy labels followed by one simple-bond coordinate in each
factor.

Source: CPSV16, Appendix C.4, lines 2020--2025. -/
def productRetainedEquiv {g : ℕ} (dim mult : Fin g → ℕ) :
    Fin ((∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q) *
      (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q)) ≃
      (p : ((α : Fin g) × Fin (mult α)) × ((α : Fin g) × Fin (mult α))) ×
        (Fin (dim p.1.1) × Fin (dim p.2.1)) :=
  finProdFinEquiv.symm |>.trans
    (Equiv.prodCongr (verticalSectorFinEquiv dim mult).symm
      (verticalSectorFinEquiv dim mult).symm |>.trans
        (verticalProductSectorEquiv dim mult))

/-- An ordered pair of retained vertical BNT copy labels. -/
abbrev VerticalCopyPair {g : ℕ} (mult : Fin g → ℕ) :=
  ((α : Fin g) × Fin (mult α)) × ((α : Fin g) × Fin (mult α))

/-- The canonical inclusion of one retained copy-pair bond space into the
square of the full retained vertical bond space.

Source: CPSV16, Appendix C.4, lines 2020--2025. -/
noncomputable def retainedProductBlockInclusion
    {g : ℕ} (dim mult : Fin g → ℕ) (p : VerticalCopyPair mult) :
    Matrix
      (Fin ((∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q) *
        (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q)))
      (Fin (dim p.1.1 * dim p.2.1)) ℂ :=
  (Matrix.sigmaBlockInclusion
    (fun q : VerticalCopyPair mult ↦ Fin (dim q.1.1) × Fin (dim q.2.1)) p).submatrix
      (productRetainedEquiv dim mult) finProdFinEquiv.symm

/-- Each canonical retained copy-pair inclusion is an isometry, including
when its domain has dimension zero. -/
theorem retainedProductBlockInclusion_isometry
    {g : ℕ} (dim mult : Fin g → ℕ) (p : VerticalCopyPair mult) :
    (retainedProductBlockInclusion dim mult p)ᴴ *
        retainedProductBlockInclusion dim mult p = 1 := by
  classical
  unfold retainedProductBlockInclusion
  rw [Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv _ _ _ (productRetainedEquiv dim mult) _,
    Matrix.sigmaBlockInclusion_isometry,
    Matrix.submatrix_one_equiv]

/-- Distinct retained copy-pair inclusions have orthogonal ranges. -/
theorem retainedProductBlockInclusion_orthogonal_of_ne
    {g : ℕ} (dim mult : Fin g → ℕ) {p q : VerticalCopyPair mult}
    (hpq : p ≠ q) :
    (retainedProductBlockInclusion dim mult p)ᴴ *
        retainedProductBlockInclusion dim mult q = 0 := by
  classical
  unfold retainedProductBlockInclusion
  rw [Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv _ _ _ (productRetainedEquiv dim mult) _,
    Matrix.sigmaBlockInclusion_conjTranspose_mul_of_ne _ hpq]
  rfl

/-- Equality of all positive-length closed MPOs gives equality of the
corresponding positive-length matrix product vectors after joining each ket
and bra index into one doubled physical index.

This bridge converts the closed-operator identities preceding the Figure 11
argument into matrix-product-vector identities. It does not isolate any fixed
pair of vertical BNT labels.

Source: CPSV16, Appendix C.4, lines 2011--2020. -/
theorem sameMPV₂Pos_toMPSTensor_of_mpo_eq
    {d D₁ D₂ : ℕ} (M₁ : MPOTensor d D₁) (M₂ : MPOTensor d D₂)
    (h : ∀ L, 0 < L → mpo M₁ L = mpo M₂ L) :
    MPSTensor.SameMPV₂Pos M₁.toMPSTensor M₂.toMPSTensor := by
  mpv_ext
  let ket : Fin N → Fin d := fun n ↦ (σ n).divNat
  let bra : Fin N → Fin d := fun n ↦ (σ n).modNat
  have hpair : (fun n ↦ finProdFinEquiv (ket n, bra n)) = σ := by
    funext n
    exact finProdFinEquiv.apply_symm_apply (σ n)
  calc
    MPSTensor.mpv M₁.toMPSTensor σ =
        MPSTensor.mpv M₁.toMPSTensor
          (fun n ↦ finProdFinEquiv (ket n, bra n)) := by rw [hpair]
    _ = mpo M₁ N ket bra := MPSTensor.mpv_toMPSTensor_pairConfig M₁ ket bra
    _ = mpo M₂ N ket bra := by rw [h N hN]
    _ = MPSTensor.mpv M₂.toMPSTensor
          (fun n ↦ finProdFinEquiv (ket n, bra n)) :=
      (MPSTensor.mpv_toMPSTensor_pairConfig M₂ ket bra).symm
    _ = MPSTensor.mpv M₂.toMPSTensor σ := by rw [hpair]

/-- Squaring an exact one-site vertical reconstruction gives an exact
two-site reconstruction through the Kronecker square of the same coisometry.

The retained two-site tensor is the product of two copies of the retained
one-site tensor. This is a tensor-level identity; it does not infer support
of any fixed pair of BNT labels from the closed-chain sum.

Source: CPSV16, Appendix C.4, lines 2015--2025. -/
theorem verticalTensor_blockTwo_squared_coisometry_reconstruction
    {d D n : ℕ} (M : MPOTensor d D) (A : MPSTensor (D * D) n)
    (U : Matrix (Fin n) (Fin d) ℂ) (hU : U * Uᴴ = 1)
    (hReconstruct : ∀ ab, verticalTensor M ab = Uᴴ * A ab * U) :
    verticalCoisometrySquare U * (verticalCoisometrySquare U)ᴴ = 1 ∧
      ∀ ab, verticalTensor (blockTwo M) ab =
        (verticalCoisometrySquare U)ᴴ *
          (mulTensor (verticalBNTMPO A) (verticalBNTMPO A)).toMPSTensor ab *
            verticalCoisometrySquare U := by
  constructor
  · exact verticalCoisometrySquare_isCoisometry U hU
  · intro ab
    rw [← verticalBNTMPO_toMPSTensor (verticalTensor (blockTwo M)),
      verticalBNTMPO_verticalTensor_blockTwo]
    obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective ab
    unfold verticalCoisometrySquare
    simp only [toMPSTensor, mulTensor_apply, verticalBNTMPO_apply,
      MPSTensor.finProdFinEquiv_divNat, MPSTensor.finProdFinEquiv_modNat]
    rw [Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv _ _ _ finProdFinEquiv.symm _,
      Matrix.submatrix_mul_equiv _ _ _ finProdFinEquiv.symm _]
    congr 1
    rw [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hReconstruct, hReconstruct, Matrix.conjTranspose_kronecker,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]

/-- The squared retained product inherits projector closure and absence of
periodic vectors from the blocked vertical tensor.

The one-site coisometric reconstruction is squared exactly. Horizontal
canonical form and positivity pass to two-site blocking, so the blocked
vertical tensor has the two canonical-form hypotheses. The preceding
coisometric transfer theorem then passes both hypotheses to the retained
product tensor, including when its active support is smaller than the full
product bond space.

Source: CPSV16, Appendix C.4, lines 2015--2025. -/
theorem retainedVerticalProduct_projectorClosure_and_noPeriodicVectors
    {d D n : ℕ} (M : MPOTensor d D) (A : MPSTensor (D * D) n)
    (U : Matrix (Fin n) (Fin d) ℂ) (hU : U * Uᴴ = 1)
    (hReconstruct : ∀ ab, verticalTensor M ab = Uᴴ * A ab * U)
    (hHorizontal : IsHorizontalCF M) (hM : IsMPDO M) :
    let C :=
      (mulTensor (verticalBNTMPO A) (verticalBNTMPO A)).toMPSTensor
    MPSTensor.HasInvariantProjectorClosure C ∧
      MPSTensor.HasNoPeriodicVectors C := by
  dsimp only
  have hsquare := verticalTensor_blockTwo_squared_coisometry_reconstruction
    M A U hU hReconstruct
  have hHorizontalTwo := hHorizontal.blockTwo
  have hMTwo := hM.blockTwo
  exact MPSTensor.projectorClosure_and_noPeriodicVectors_of_coisometry_reconstruction
    (verticalTensor (blockTwo M))
    (mulTensor (verticalBNTMPO A) (verticalBNTMPO A)).toMPSTensor
    (verticalCoisometrySquare U) hsquare.1 hsquare.2
    (hHorizontalTwo.hasInvariantProjectorClosure_verticalTensor (blockTwo M) hMTwo)
    (hasNoPeriodicVectors_verticalTensor_of_horizontalCF
      (blockTwo M) hMTwo hHorizontalTwo)

/-- The retained tensor belonging to one ordered pair of vertical BNT copies.

Its scalar is the product of the two positive copy weights.  The definition
also permits a zero-dimensional simple bond; such a copy pair contributes an
empty block and is not discarded at this stage.

Source: CPSV16, Appendix C.4, lines 2020--2025. -/
noncomputable def weightedVerticalProductBlock
    {g D : ℕ} (dim mult : Fin g → ℕ)
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (B : (α : Fin g) → MPSTensor (D * D) (dim α))
    (p : ((α : Fin g) × Fin (mult α)) ×
      ((α : Fin g) × Fin (mult α))) :
    MPSTensor (D * D) (dim p.1.1 * dim p.2.1) :=
  fun ab ↦ (weight p.1.1 p.1.2 * weight p.2.1 p.2.2) •
    (mulTensor (verticalBNTMPO (B p.1.1))
      (verticalBNTMPO (B p.2.1))).toMPSTensor ab

/-- The square of the retained assembled vertical tensor, before separating
its ordered copy-pair blocks. -/
noncomputable def retainedVerticalProductTensor
    {g D : ℕ} (dim mult : Fin g → ℕ)
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (B : (α : Fin g) → MPSTensor (D * D) (dim α)) :
    MPSTensor (D * D)
      ((∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q) *
        (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q)) :=
  (mulTensor (verticalBNTMPO (verticalAssembledTensor dim mult weight B))
    (verticalBNTMPO (verticalAssembledTensor dim mult weight B))).toMPSTensor

/-- The product of two assembled vertical tensors is block diagonal over
pairs of active BNT copies. The block for copies `(α, q)` and `(β, r)` is the
raw product tensor for `(α, β)`, multiplied by the product of their diagonal
weights.

This is an entrywise distribution identity. It does not assert that any
fixed pair of BNT labels occurs in a decomposition of a prescribed tensor.

Source: CPSV16, Appendix C.4, lines 2020--2025. -/
theorem mulTensor_verticalAssembledTensor_reindex
    {g D : ℕ} (dim mult : Fin g → ℕ)
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (B : (α : Fin g) → MPSTensor (D * D) (dim α)) (ab : Fin (D * D)) :
    Matrix.reindex (productRetainedEquiv dim mult)
        (productRetainedEquiv dim mult)
        (retainedVerticalProductTensor dim mult weight B ab) =
      Matrix.blockDiagonal' fun p :
          ((α : Fin g) × Fin (mult α)) × ((α : Fin g) × Fin (mult α)) =>
        Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
          (weightedVerticalProductBlock dim mult weight B p ab) := by
  classical
  obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective ab
  ext x y
  rcases x with ⟨⟨⟨α, q⟩, ⟨β, r⟩⟩, ⟨i, j⟩⟩
  rcases y with ⟨⟨⟨α', q'⟩, ⟨β', r'⟩⟩, ⟨i', j'⟩⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  simp [productRetainedEquiv, verticalProductSectorEquiv,
    retainedVerticalProductTensor, weightedVerticalProductBlock,
    toMPSTensor, mulTensor_apply, verticalBNTMPO_apply]
  by_cases hp :
      ((⟨α, q⟩ : (α : Fin g) × Fin (mult α)),
        (⟨β, r⟩ : (α : Fin g) × Fin (mult α))) =
      ((⟨α', q'⟩ : (α : Fin g) × Fin (mult α)),
        (⟨β', r'⟩ : (α : Fin g) × Fin (mult α)))
  · cases hp
    simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply,
      Matrix.blockDiagonal'_apply_eq,
      verticalAssembledTensor_apply_copy_same]
    simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply,
      Matrix.kroneckerMap_apply]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hp]
    simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply]
    apply Finset.sum_eq_zero
    intro x _
    by_cases hleft :
        (⟨α, q⟩ : (α : Fin g) × Fin (mult α)) = ⟨α', q'⟩
    · have hright :
          (⟨β, r⟩ : (α : Fin g) × Fin (mult α)) ≠ ⟨β', r'⟩ := by
        intro h
        exact hp (Prod.ext hleft h)
      rw [verticalAssembledTensor_apply_copy_ne dim mult weight B hright]
      exact mul_zero _
    · rw [verticalAssembledTensor_apply_copy_ne dim mult weight B hleft]
      exact zero_mul _

/-- The retained product tensor is the sum of its weighted copy-pair blocks
conjugated by their canonical inclusions. -/
theorem retainedVerticalProductTensor_eq_sum_pairBlocks
    {g D : ℕ} (dim mult : Fin g → ℕ)
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (B : (α : Fin g) → MPSTensor (D * D) (dim α))
    (ab : Fin (D * D)) :
    retainedVerticalProductTensor dim mult weight B ab =
      ∑ p : VerticalCopyPair mult,
        retainedProductBlockInclusion dim mult p *
          weightedVerticalProductBlock dim mult weight B p ab *
            (retainedProductBlockInclusion dim mult p)ᴴ := by
  classical
  let blockIndex := fun q : VerticalCopyPair mult ↦
    Fin (dim q.1.1) × Fin (dim q.2.1)
  let C := fun q : VerticalCopyPair mult ↦
    Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
      (weightedVerticalProductBlock dim mult weight B q ab)
  let I := fun q : VerticalCopyPair mult ↦
    Matrix.sigmaBlockInclusion blockIndex q
  have hdiag := mulTensor_verticalAssembledTensor_reindex dim mult weight B ab
  have hsum := Matrix.blockDiagonal'_eq_sum_sigmaBlockInclusion C
  rw [← hdiag] at hsum
  have hterm : ∀ p : VerticalCopyPair mult,
      retainedProductBlockInclusion dim mult p *
          weightedVerticalProductBlock dim mult weight B p ab *
            (retainedProductBlockInclusion dim mult p)ᴴ =
        (I p * C p * (I p)ᴴ).submatrix
          (productRetainedEquiv dim mult) (productRetainedEquiv dim mult) := by
    intro p
    have hB : weightedVerticalProductBlock dim mult weight B p ab =
        (C p).submatrix finProdFinEquiv.symm finProdFinEquiv.symm := by
      simp [C, Matrix.reindex_apply, Matrix.submatrix_submatrix]
    simp only [retainedProductBlockInclusion, I,
      Matrix.conjTranspose_submatrix]
    rw [hB, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv]
  calc
    retainedVerticalProductTensor dim mult weight B ab =
        (Matrix.reindex (productRetainedEquiv dim mult)
          (productRetainedEquiv dim mult)
          (retainedVerticalProductTensor dim mult weight B ab)).submatrix
            (productRetainedEquiv dim mult) (productRetainedEquiv dim mult) := by
      simp [Matrix.reindex_apply, Matrix.submatrix_submatrix]
    _ = (∑ p, I p * C p * (I p)ᴴ).submatrix
          (productRetainedEquiv dim mult) (productRetainedEquiv dim mult) := by
      rw [hsum]
    _ = ∑ p, (I p * C p * (I p)ᴴ).submatrix
          (productRetainedEquiv dim mult) (productRetainedEquiv dim mult) := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.sum_apply]
    _ = _ := by
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      exact (hterm p).symm

/-- A retained copy-pair inclusion intertwines its weighted block with the
full retained product tensor. -/
theorem retainedVerticalProductTensor_mul_retainedProductBlockInclusion
    {g D : ℕ} (dim mult : Fin g → ℕ)
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (B : (α : Fin g) → MPSTensor (D * D) (dim α))
    (p : VerticalCopyPair mult) (ab : Fin (D * D)) :
    retainedVerticalProductTensor dim mult weight B ab *
        retainedProductBlockInclusion dim mult p =
      retainedProductBlockInclusion dim mult p *
        weightedVerticalProductBlock dim mult weight B p ab := by
  classical
  let blockIndex := fun q : VerticalCopyPair mult ↦
    Fin (dim q.1.1) × Fin (dim q.2.1)
  let C := fun q : VerticalCopyPair mult ↦
    Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
      (weightedVerticalProductBlock dim mult weight B q ab)
  let E := Matrix.sigmaBlockInclusion blockIndex p
  have h := Matrix.blockDiagonal'_mul_sigmaBlockInclusion C p
  rw [← mulTensor_verticalAssembledTensor_reindex dim mult weight B ab] at h
  have hleft : retainedVerticalProductTensor dim mult weight B ab *
      retainedProductBlockInclusion dim mult p =
        (Matrix.reindex (productRetainedEquiv dim mult)
          (productRetainedEquiv dim mult)
          (retainedVerticalProductTensor dim mult weight B ab) * E).submatrix
            (productRetainedEquiv dim mult) finProdFinEquiv.symm := by
    simpa only [retainedProductBlockInclusion, E, Matrix.reindex_apply,
      Matrix.submatrix_submatrix, Equiv.symm_comp_self,
      Matrix.submatrix_id_id] using
      (Matrix.submatrix_mul_equiv
        (Matrix.reindex (productRetainedEquiv dim mult)
          (productRetainedEquiv dim mult)
          (retainedVerticalProductTensor dim mult weight B ab)) E
        (productRetainedEquiv dim mult) (productRetainedEquiv dim mult)
        finProdFinEquiv.symm)
  have hright : retainedProductBlockInclusion dim mult p *
      weightedVerticalProductBlock dim mult weight B p ab =
        (E * C p).submatrix
          (productRetainedEquiv dim mult) finProdFinEquiv.symm := by
    simpa only [retainedProductBlockInclusion, E, C, Matrix.reindex_apply,
      Matrix.submatrix_submatrix, Equiv.symm_comp_self,
      Matrix.submatrix_id_id] using
      (Matrix.submatrix_mul_equiv E (C p)
        (productRetainedEquiv dim mult) finProdFinEquiv.symm
        finProdFinEquiv.symm)
  have hpull := congrArg
    (fun X ↦ X.submatrix (productRetainedEquiv dim mult) finProdFinEquiv.symm) h
  exact hleft.trans (hpull.trans hright.symm)

/-- The adjoint retained copy-pair inclusion satisfies the reverse
intertwining identity. -/
theorem retainedProductBlockInclusion_conjTranspose_mul_retainedVerticalProductTensor
    {g D : ℕ} (dim mult : Fin g → ℕ)
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (B : (α : Fin g) → MPSTensor (D * D) (dim α))
    (p : VerticalCopyPair mult) (ab : Fin (D * D)) :
    (retainedProductBlockInclusion dim mult p)ᴴ *
        retainedVerticalProductTensor dim mult weight B ab =
      weightedVerticalProductBlock dim mult weight B p ab *
        (retainedProductBlockInclusion dim mult p)ᴴ := by
  classical
  let blockIndex := fun q : VerticalCopyPair mult ↦
    Fin (dim q.1.1) × Fin (dim q.2.1)
  let C := fun q : VerticalCopyPair mult ↦
    Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
      (weightedVerticalProductBlock dim mult weight B q ab)
  let E := Matrix.sigmaBlockInclusion blockIndex p
  have h := Matrix.sigmaBlockInclusion_conjTranspose_mul_blockDiagonal' C p
  rw [← mulTensor_verticalAssembledTensor_reindex dim mult weight B ab] at h
  have hleft : (retainedProductBlockInclusion dim mult p)ᴴ *
      retainedVerticalProductTensor dim mult weight B ab =
        (Eᴴ * Matrix.reindex (productRetainedEquiv dim mult)
          (productRetainedEquiv dim mult)
          (retainedVerticalProductTensor dim mult weight B ab)).submatrix
            finProdFinEquiv.symm (productRetainedEquiv dim mult) := by
    simpa only [retainedProductBlockInclusion, E, Matrix.reindex_apply,
      Matrix.conjTranspose_submatrix, Matrix.submatrix_submatrix,
      Equiv.symm_comp_self, Matrix.submatrix_id_id] using
      (Matrix.submatrix_mul_equiv Eᴴ
        (Matrix.reindex (productRetainedEquiv dim mult)
          (productRetainedEquiv dim mult)
          (retainedVerticalProductTensor dim mult weight B ab))
        finProdFinEquiv.symm (productRetainedEquiv dim mult)
        (productRetainedEquiv dim mult))
  have hright : weightedVerticalProductBlock dim mult weight B p ab *
      (retainedProductBlockInclusion dim mult p)ᴴ =
        (C p * Eᴴ).submatrix
          finProdFinEquiv.symm (productRetainedEquiv dim mult) := by
    simpa only [retainedProductBlockInclusion, E, C, Matrix.reindex_apply,
      Matrix.conjTranspose_submatrix, Matrix.submatrix_submatrix,
      Equiv.symm_comp_self, Matrix.submatrix_id_id] using
      (Matrix.submatrix_mul_equiv (C p) Eᴴ finProdFinEquiv.symm
        finProdFinEquiv.symm (productRetainedEquiv dim mult))
  have hpull := congrArg
    (fun X ↦ X.submatrix finProdFinEquiv.symm
      (productRetainedEquiv dim mult)) h
  exact hleft.trans (hpull.trans hright.symm)

/-- Every ordered pair of retained vertical BNT copies inherits projector
closure and absence of periodic vectors from the blocked vertical tensor.

The conclusion includes zero-dimensional copy pairs.  It requires no
nonvanishing hypothesis on the product of the two copy weights: a zero block
is passed unchanged to the subsequent spectral decomposition, where it has no
active normal summands.

**Local fix (Figure-11 fixed-pair support):** The conclusion is retained for
every copy pair, but only its nonzero spectral corners become active fusion
summands.  Unused blocked labels are represented later by empty fibers.
Documented in `docs/paper-gaps/cpsv16_figure11_per_pair_support.tex`.

Source: CPSV16, Appendix C.4, lines 2020--2029. -/
theorem weightedVerticalProductBlock_projectorClosure_and_noPeriodicVectors
    {g d D : ℕ} (dim mult : Fin g → ℕ)
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (B : (α : Fin g) → MPSTensor (D * D) (dim α))
    (M : MPOTensor d D)
    (U : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ)
    (hU : U * Uᴴ = 1)
    (hReconstruct : ∀ ab, verticalTensor M ab =
      Uᴴ * verticalAssembledTensor dim mult weight B ab * U)
    (hHorizontal : IsHorizontalCF M) (hM : IsMPDO M)
    (p : ((α : Fin g) × Fin (mult α)) ×
      ((α : Fin g) × Fin (mult α))) :
    MPSTensor.HasInvariantProjectorClosure
        (weightedVerticalProductBlock dim mult weight B p) ∧
      MPSTensor.HasNoPeriodicVectors
        (weightedVerticalProductBlock dim mult weight B p) := by
  let C := (mulTensor
    (verticalBNTMPO (verticalAssembledTensor dim mult weight B))
    (verticalBNTMPO (verticalAssembledTensor dim mult weight B))).toMPSTensor
  have hCanonical : MPSTensor.HasInvariantProjectorClosure C ∧
      MPSTensor.HasNoPeriodicVectors C := by
    simpa only [C] using
      retainedVerticalProduct_projectorClosure_and_noPeriodicVectors M
        (verticalAssembledTensor dim mult weight B) U hU hReconstruct
        hHorizontal hM
  exact MPSTensor.projectorClosure_and_noPeriodicVectors_block_of_reindex_eq_blockDiagonal
    (fun p : ((α : Fin g) × Fin (mult α)) ×
      ((α : Fin g) × Fin (mult α)) ↦ dim p.1.1 * dim p.2.1)
    (fun p : ((α : Fin g) × Fin (mult α)) ×
      ((α : Fin g) × Fin (mult α)) ↦
        Fin (dim p.1.1) × Fin (dim p.2.1))
    (fun _ ↦ finProdFinEquiv.symm) C
    (weightedVerticalProductBlock dim mult weight B)
    (productRetainedEquiv dim mult)
    (mulTensor_verticalAssembledTensor_reindex dim mult weight B)
    hCanonical.1 hCanonical.2 p

/-- Every retained copy-pair tensor has an exact decomposition into its
nonzero normal corners, with the corner isometries retained.

The active family may be empty.  Thus a zero-dimensional copy pair, or a
copy-pair tensor whose every letter vanishes, contributes no artificial
normal sector.  No division by the outer copy weight occurs in this theorem.

Source: CPSV16, Appendix C.4, lines 2020--2029. -/
theorem exists_weightedVerticalProductBlock_normalDecomposition
    {g d D : ℕ} (dim mult : Fin g → ℕ)
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (B : (α : Fin g) → MPSTensor (D * D) (dim α))
    (M : MPOTensor d D)
    (U : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ)
    (hU : U * Uᴴ = 1)
    (hReconstruct : ∀ ab, verticalTensor M ab =
      Uᴴ * verticalAssembledTensor dim mult weight B ab * U)
    (hHorizontal : IsHorizontalCF M) (hM : IsMPDO M)
    (p : ((α : Fin g) × Fin (mult α)) ×
      ((α : Fin g) × Fin (mult α))) :
    ∃ (r : ℕ) (localDim : Fin r → ℕ) (coefficient : Fin r → ℂ)
      (blocks : (k : Fin r) → MPSTensor (D * D) (localDim k))
      (V : (k : Fin r) →
        Matrix (Fin (dim p.1.1 * dim p.2.1)) (Fin (localDim k)) ℂ),
      (∀ k, 0 < localDim k) ∧
      (∀ k, (0 : ℂ) < coefficient k) ∧
      (∀ k, MPSTensor.IsNormalTensor (blocks k)) ∧
      (∀ k, (V k)ᴴ * V k = 1) ∧
      (∀ k l, k ≠ l → (V k)ᴴ * V l = 0) ∧
      (∀ (k : Fin r) (ab : Fin (D * D)),
        weightedVerticalProductBlock dim mult weight B p ab * V k =
          V k * (coefficient k • blocks k ab)) ∧
      (∀ (k : Fin r) (ab : Fin (D * D)),
        (V k)ᴴ * weightedVerticalProductBlock dim mult weight B p ab =
          (coefficient k • blocks k ab) * (V k)ᴴ) ∧
      (∀ (k : Fin r) (ab : Fin (D * D)),
        coefficient k • blocks k ab =
          (V k)ᴴ * weightedVerticalProductBlock dim mult weight B p ab * V k) ∧
      (∀ ab : Fin (D * D),
        weightedVerticalProductBlock dim mult weight B p ab =
          ∑ k, V k * (coefficient k • blocks k ab) * (V k)ᴴ) ∧
      MPSTensor.SameMPV₂Pos
        (weightedVerticalProductBlock dim mult weight B p)
        (MPSTensor.toTensorFromBlocks (d := D * D)
          (μ := coefficient) blocks) ∧
      (∑ k, localDim k) ≤ dim p.1.1 * dim p.2.1 := by
  have hCanonical :=
    weightedVerticalProductBlock_projectorClosure_and_noPeriodicVectors
      dim mult weight B M U hU hReconstruct hHorizontal hM p
  exact MPSTensor.exists_normalTensor_blockDecomp_with_isometry_of_hasInvariantProjectorClosure
    (weightedVerticalProductBlock dim mult weight B p)
    hCanonical.1 hCanonical.2

/-- The simultaneous isometry-retaining spectral decompositions of all
retained copy-pair tensors.  The local inclusions are kept explicitly because
their range projections are the projectors used in the subsequent positivity
comparison.

Source: CPSV16, Appendix C.4, lines 2020--2029. -/
structure RetainedProductSpectralFamily
    {g D : ℕ} (dim mult : Fin g → ℕ)
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (B : (α : Fin g) → MPSTensor (D * D) (dim α)) where
  /-- Number of nonzero spectral corners in a copy-pair tensor. -/
  count : VerticalCopyPair mult → ℕ
  /-- Bond dimension of a local spectral corner. -/
  localDim : (p : VerticalCopyPair mult) → Fin (count p) → ℕ
  /-- Positive spectral coefficient of a local corner. -/
  coefficient : (p : VerticalCopyPair mult) → Fin (count p) → ℂ
  /-- Normal tensor of a local corner. -/
  block : (p : VerticalCopyPair mult) → (k : Fin (count p)) →
    MPSTensor (D * D) (localDim p k)
  /-- Inclusion of a local corner into its copy-pair bond space. -/
  localInclusion : (p : VerticalCopyPair mult) → (k : Fin (count p)) →
    Matrix (Fin (dim p.1.1 * dim p.2.1)) (Fin (localDim p k)) ℂ
  /-- Every retained local corner has positive bond dimension. -/
  localDim_pos : ∀ p k, 0 < localDim p k
  /-- Every retained spectral coefficient is positive. -/
  coefficient_pos : ∀ p k, (0 : ℂ) < coefficient p k
  /-- Every retained local corner is a normal tensor. -/
  block_normal : ∀ p k, MPSTensor.IsNormalTensor (block p k)
  /-- Each local corner inclusion is an isometry. -/
  localInclusion_isometry : ∀ p k,
    (localInclusion p k)ᴴ * localInclusion p k = 1
  /-- Distinct local corners of one copy pair have orthogonal ranges. -/
  localInclusion_orthogonal : ∀ p k l, k ≠ l →
    (localInclusion p k)ᴴ * localInclusion p l = 0
  /-- Each local inclusion intertwines its weighted normal corner with the
  copy-pair tensor. -/
  local_intertwine : ∀ p k ab,
    weightedVerticalProductBlock dim mult weight B p ab * localInclusion p k =
      localInclusion p k * (coefficient p k • block p k ab)
  /-- The adjoint local inclusion satisfies the reverse intertwining
  identity. -/
  local_intertwine_adjoint : ∀ p k ab,
    (localInclusion p k)ᴴ * weightedVerticalProductBlock dim mult weight B p ab =
      (coefficient p k • block p k ab) * (localInclusion p k)ᴴ
  /-- Compression to a local corner gives its weighted normal tensor. -/
  local_compression : ∀ p k ab,
    coefficient p k • block p k ab =
      (localInclusion p k)ᴴ *
        weightedVerticalProductBlock dim mult weight B p ab *
          localInclusion p k
  /-- The local corners reconstruct every letter of their copy-pair tensor. -/
  local_reconstruction : ∀ p ab,
    weightedVerticalProductBlock dim mult weight B p ab =
      ∑ k, localInclusion p k * (coefficient p k • block p k ab) *
        (localInclusion p k)ᴴ
  /-- The local decomposition preserves every positive-length closed chain. -/
  local_sameMPV₂Pos : ∀ p, MPSTensor.SameMPV₂Pos
    (weightedVerticalProductBlock dim mult weight B p)
      (MPSTensor.toTensorFromBlocks (d := D * D)
      (μ := coefficient p) (block p))
  /-- The total local bond dimension does not exceed the copy-pair bond
  dimension. -/
  local_dimension_bound : ∀ p,
    (∑ k, localDim p k) ≤ dim p.1.1 * dim p.2.1

/-- The local spectral decompositions may be chosen simultaneously for every
retained copy pair.  Empty active families are preserved. -/
theorem exists_retainedProductSpectralFamily
    {g d D : ℕ} (dim mult : Fin g → ℕ)
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (B : (α : Fin g) → MPSTensor (D * D) (dim α))
    (M : MPOTensor d D)
    (U : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ)
    (hU : U * Uᴴ = 1)
    (hReconstruct : ∀ ab, verticalTensor M ab =
      Uᴴ * verticalAssembledTensor dim mult weight B ab * U)
    (hHorizontal : IsHorizontalCF M) (hM : IsMPDO M) :
    Nonempty (RetainedProductSpectralFamily dim mult weight B) := by
  classical
  have hExists := fun p ↦
    exists_weightedVerticalProductBlock_normalDecomposition
      dim mult weight B M U hU hReconstruct hHorizontal hM p
  choose count localDim coefficient block localInclusion
    localDim_pos coefficient_pos block_normal localInclusion_isometry
    localInclusion_orthogonal local_intertwine local_intertwine_adjoint
    local_compression local_reconstruction local_sameMPV₂Pos
    local_dimension_bound using hExists
  exact ⟨{
    count := count
    localDim := localDim
    coefficient := coefficient
    block := block
    localInclusion := localInclusion
    localDim_pos := localDim_pos
    coefficient_pos := coefficient_pos
    block_normal := block_normal
    localInclusion_isometry := localInclusion_isometry
    localInclusion_orthogonal := localInclusion_orthogonal
    local_intertwine := local_intertwine
    local_intertwine_adjoint := local_intertwine_adjoint
    local_compression := local_compression
    local_reconstruction := local_reconstruction
    local_sameMPV₂Pos := local_sameMPV₂Pos
    local_dimension_bound := local_dimension_bound }⟩

namespace RetainedProductSpectralFamily

variable {g D : ℕ} {dim mult : Fin g → ℕ}
  {weight : (α : Fin g) → Fin (mult α) → ℂ}
  {B : (α : Fin g) → MPSTensor (D * D) (dim α)}

/-- The dependent type of all active local corners over all retained copy
pairs. -/
abbrev ActiveLabel (S : RetainedProductSpectralFamily dim mult weight B) :=
  (p : VerticalCopyPair mult) × Fin (S.count p)

/-- Enumeration of all active local corners by one finite type. -/
noncomputable def activeLabelEquiv
    (S : RetainedProductSpectralFamily dim mult weight B) :
    Fin (Fintype.card S.ActiveLabel) ≃ S.ActiveLabel :=
  (Fintype.equivFin S.ActiveLabel).symm

/-- The inclusion of an active local corner into the complete retained
product bond space. -/
noncomputable def retainedInclusion
    (S : RetainedProductSpectralFamily dim mult weight B)
    (x : S.ActiveLabel) :
    Matrix
      (Fin ((∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q) *
        (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q)))
      (Fin (S.localDim x.1 x.2)) ℂ :=
  retainedProductBlockInclusion dim mult x.1 * S.localInclusion x.1 x.2

/-- The inclusion of an active local corner into the bond space of the
blocked vertical tensor. -/
noncomputable def ambientInclusion {d : ℕ}
    (S : RetainedProductSpectralFamily dim mult weight B)
    (U : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ)
    (x : S.ActiveLabel) :
    Matrix (Fin (d * d)) (Fin (S.localDim x.1 x.2)) ℂ :=
  (verticalCoisometrySquare U)ᴴ * S.retainedInclusion x

/-- Every flattened retained inclusion is an isometry. -/
theorem retainedInclusion_isometry
    (S : RetainedProductSpectralFamily dim mult weight B)
    (x : S.ActiveLabel) :
    (S.retainedInclusion x)ᴴ * S.retainedInclusion x = 1 := by
  rw [retainedInclusion, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (retainedProductBlockInclusion dim mult x.1)ᴴ,
    retainedProductBlockInclusion_isometry, Matrix.one_mul,
    S.localInclusion_isometry]

/-- Distinct active corners have orthogonal ranges in the retained product
bond space. -/
theorem retainedInclusion_orthogonal_of_ne
    (S : RetainedProductSpectralFamily dim mult weight B)
    (p q : VerticalCopyPair mult) (k : Fin (S.count p))
    (l : Fin (S.count q))
    (h : (⟨p, k⟩ : S.ActiveLabel) ≠ ⟨q, l⟩) :
    (S.retainedInclusion ⟨p, k⟩)ᴴ * S.retainedInclusion ⟨q, l⟩ = 0 := by
  by_cases hpq : p = q
  · subst q
    have hkl : k ≠ l := by
      intro hEq
      subst l
      exact h rfl
    rw [retainedInclusion, retainedInclusion, Matrix.conjTranspose_mul,
      Matrix.mul_assoc,
      ← Matrix.mul_assoc (retainedProductBlockInclusion dim mult p)ᴴ,
      retainedProductBlockInclusion_isometry, Matrix.one_mul,
      S.localInclusion_orthogonal p k l hkl]
  · rw [retainedInclusion, retainedInclusion, Matrix.conjTranspose_mul,
      Matrix.mul_assoc,
      ← Matrix.mul_assoc (retainedProductBlockInclusion dim mult p)ᴴ,
      retainedProductBlockInclusion_orthogonal_of_ne dim mult hpq,
      Matrix.zero_mul, Matrix.mul_zero]

/-- Every flattened retained inclusion intertwines its active normal corner
with the full retained product tensor. -/
theorem retained_intertwine
    (S : RetainedProductSpectralFamily dim mult weight B)
    (x : S.ActiveLabel) (ab : Fin (D * D)) :
    retainedVerticalProductTensor dim mult weight B ab * S.retainedInclusion x =
      S.retainedInclusion x * (S.coefficient x.1 x.2 • S.block x.1 x.2 ab) := by
  rw [retainedInclusion, ← Matrix.mul_assoc,
    retainedVerticalProductTensor_mul_retainedProductBlockInclusion,
    Matrix.mul_assoc, S.local_intertwine]
  exact (Matrix.mul_assoc _ _ _).symm

/-- The adjoint flattened retained inclusion satisfies the reverse
intertwining identity. -/
theorem retained_intertwine_adjoint
    (S : RetainedProductSpectralFamily dim mult weight B)
    (x : S.ActiveLabel) (ab : Fin (D * D)) :
    (S.retainedInclusion x)ᴴ * retainedVerticalProductTensor dim mult weight B ab =
      (S.coefficient x.1 x.2 • S.block x.1 x.2 ab) *
        (S.retainedInclusion x)ᴴ := by
  rw [retainedInclusion, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    retainedProductBlockInclusion_conjTranspose_mul_retainedVerticalProductTensor,
    ← Matrix.mul_assoc, S.local_intertwine_adjoint]
  exact Matrix.mul_assoc _ _ _

/-- Compressing the retained product tensor by a flattened inclusion recovers
its weighted normal corner. -/
theorem retained_compression
    (S : RetainedProductSpectralFamily dim mult weight B)
    (x : S.ActiveLabel) (ab : Fin (D * D)) :
    S.coefficient x.1 x.2 • S.block x.1 x.2 ab =
      (S.retainedInclusion x)ᴴ *
        retainedVerticalProductTensor dim mult weight B ab *
          S.retainedInclusion x := by
  rw [S.retained_intertwine_adjoint,
    Matrix.mul_assoc, S.retainedInclusion_isometry, Matrix.mul_one]

/-- Exact reconstruction of the retained product tensor by all active local
corners, before enumerating their dependent label type. -/
theorem retained_reconstruction_active
    (S : RetainedProductSpectralFamily dim mult weight B)
    (ab : Fin (D * D)) :
    retainedVerticalProductTensor dim mult weight B ab =
      ∑ x : S.ActiveLabel,
        S.retainedInclusion x *
          (S.coefficient x.1 x.2 • S.block x.1 x.2 ab) *
            (S.retainedInclusion x)ᴴ := by
  calc
    retainedVerticalProductTensor dim mult weight B ab =
        ∑ p : VerticalCopyPair mult,
          retainedProductBlockInclusion dim mult p *
            weightedVerticalProductBlock dim mult weight B p ab *
              (retainedProductBlockInclusion dim mult p)ᴴ :=
      retainedVerticalProductTensor_eq_sum_pairBlocks dim mult weight B ab
    _ = ∑ p : VerticalCopyPair mult,
        retainedProductBlockInclusion dim mult p *
          (∑ k, S.localInclusion p k *
            (S.coefficient p k • S.block p k ab) *
              (S.localInclusion p k)ᴴ) *
            (retainedProductBlockInclusion dim mult p)ᴴ := by
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      rw [← S.local_reconstruction p ab]
    _ = ∑ p : VerticalCopyPair mult, ∑ k,
        S.retainedInclusion ⟨p, k⟩ *
          (S.coefficient p k • S.block p k ab) *
            (S.retainedInclusion ⟨p, k⟩)ᴴ := by
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      rw [Matrix.mul_sum, Matrix.sum_mul]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      simp only [retainedInclusion, Matrix.conjTranspose_mul,
        Matrix.mul_assoc]
    _ = _ := by
      simpa only [ActiveLabel] using
        (Fintype.sum_sigma (fun x : S.ActiveLabel ↦
          S.retainedInclusion x *
            (S.coefficient x.1 x.2 • S.block x.1 x.2 ab) *
              (S.retainedInclusion x)ᴴ)).symm

/-- Bond dimension of an active corner after enumerating all dependent active
labels by one finite type. -/
noncomputable def flatDim
    (S : RetainedProductSpectralFamily dim mult weight B)
    (j : Fin (Fintype.card S.ActiveLabel)) : ℕ :=
  S.localDim (S.activeLabelEquiv j).1 (S.activeLabelEquiv j).2

/-- Positive coefficient of an enumerated active corner. -/
noncomputable def flatCoefficient
    (S : RetainedProductSpectralFamily dim mult weight B)
    (j : Fin (Fintype.card S.ActiveLabel)) : ℂ :=
  S.coefficient (S.activeLabelEquiv j).1 (S.activeLabelEquiv j).2

/-- Normal tensor of an enumerated active corner. -/
noncomputable def flatBlock
    (S : RetainedProductSpectralFamily dim mult weight B)
    (j : Fin (Fintype.card S.ActiveLabel)) :
    MPSTensor (D * D) (S.flatDim j) :=
  S.block (S.activeLabelEquiv j).1 (S.activeLabelEquiv j).2

/-- Retained inclusion of an enumerated active corner. -/
noncomputable def flatInclusion
    (S : RetainedProductSpectralFamily dim mult weight B)
    (j : Fin (Fintype.card S.ActiveLabel)) :
    Matrix
      (Fin ((∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q) *
        (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q)))
      (Fin (S.flatDim j)) ℂ :=
  S.retainedInclusion (S.activeLabelEquiv j)

/-- Every enumerated active corner has positive bond dimension. -/
theorem flatDim_pos
    (S : RetainedProductSpectralFamily dim mult weight B)
    (j : Fin (Fintype.card S.ActiveLabel)) : 0 < S.flatDim j :=
  S.localDim_pos (S.activeLabelEquiv j).1 (S.activeLabelEquiv j).2

/-- Every enumerated active coefficient is positive. -/
theorem flatCoefficient_pos
    (S : RetainedProductSpectralFamily dim mult weight B)
    (j : Fin (Fintype.card S.ActiveLabel)) : (0 : ℂ) < S.flatCoefficient j :=
  S.coefficient_pos (S.activeLabelEquiv j).1 (S.activeLabelEquiv j).2

/-- Every enumerated active coefficient is nonzero. -/
theorem flatCoefficient_ne
    (S : RetainedProductSpectralFamily dim mult weight B)
    (j : Fin (Fintype.card S.ActiveLabel)) : S.flatCoefficient j ≠ 0 :=
  (S.flatCoefficient_pos j).ne'

/-- Every enumerated active block is a normal tensor. -/
theorem flatBlock_normal
    (S : RetainedProductSpectralFamily dim mult weight B)
    (j : Fin (Fintype.card S.ActiveLabel)) :
    MPSTensor.IsNormalTensor (S.flatBlock j) :=
  S.block_normal (S.activeLabelEquiv j).1 (S.activeLabelEquiv j).2

/-- Enumerated active-corner inclusions are isometries. -/
theorem flatInclusion_isometry
    (S : RetainedProductSpectralFamily dim mult weight B)
    (j : Fin (Fintype.card S.ActiveLabel)) :
    (S.flatInclusion j)ᴴ * S.flatInclusion j = 1 := by
  exact S.retainedInclusion_isometry (S.activeLabelEquiv j)

/-- Distinct enumerated active-corner inclusions have orthogonal ranges. -/
theorem flatInclusion_orthogonal_of_ne
    (S : RetainedProductSpectralFamily dim mult weight B)
    (j l : Fin (Fintype.card S.ActiveLabel)) (hjl : j ≠ l) :
    (S.flatInclusion j)ᴴ * S.flatInclusion l = 0 := by
  apply S.retainedInclusion_orthogonal_of_ne
  intro hEq
  exact hjl (S.activeLabelEquiv.injective hEq)

/-- Enumerated active-corner inclusions satisfy the forward intertwining
identity. -/
theorem flat_intertwine
    (S : RetainedProductSpectralFamily dim mult weight B)
    (j : Fin (Fintype.card S.ActiveLabel)) (ab : Fin (D * D)) :
    retainedVerticalProductTensor dim mult weight B ab * S.flatInclusion j =
      S.flatInclusion j * (S.flatCoefficient j • S.flatBlock j ab) :=
  S.retained_intertwine (S.activeLabelEquiv j) ab

/-- Enumerated active-corner inclusions satisfy the adjoint intertwining
identity. -/
theorem flat_intertwine_adjoint
    (S : RetainedProductSpectralFamily dim mult weight B)
    (j : Fin (Fintype.card S.ActiveLabel)) (ab : Fin (D * D)) :
    (S.flatInclusion j)ᴴ * retainedVerticalProductTensor dim mult weight B ab =
      (S.flatCoefficient j • S.flatBlock j ab) * (S.flatInclusion j)ᴴ := by
  exact S.retained_intertwine_adjoint (S.activeLabelEquiv j) ab

/-- Compression by an enumerated inclusion gives its weighted active
corner. -/
theorem flat_compression
    (S : RetainedProductSpectralFamily dim mult weight B)
    (j : Fin (Fintype.card S.ActiveLabel)) (ab : Fin (D * D)) :
    S.flatCoefficient j • S.flatBlock j ab =
      (S.flatInclusion j)ᴴ *
        retainedVerticalProductTensor dim mult weight B ab *
          S.flatInclusion j :=
  S.retained_compression (S.activeLabelEquiv j) ab

/-- Literal reconstruction of the retained product tensor by the enumerated
active corners. -/
theorem flat_reconstruction
    (S : RetainedProductSpectralFamily dim mult weight B)
    (ab : Fin (D * D)) :
    retainedVerticalProductTensor dim mult weight B ab =
      ∑ j, S.flatInclusion j * (S.flatCoefficient j • S.flatBlock j ab) *
        (S.flatInclusion j)ᴴ := by
  rw [S.retained_reconstruction_active ab]
  exact (S.activeLabelEquiv.sum_comp (fun x : S.ActiveLabel ↦
    S.retainedInclusion x *
      (S.coefficient x.1 x.2 • S.block x.1 x.2 ab) *
        (S.retainedInclusion x)ᴴ)).symm

/-- The retained product tensor and the single finite direct sum of all its
active normal corners have the same positive-length closed chains. -/
theorem flat_sameMPV₂Pos
    (S : RetainedProductSpectralFamily dim mult weight B) :
    MPSTensor.SameMPV₂Pos (retainedVerticalProductTensor dim mult weight B)
      (MPSTensor.toTensorFromBlocks (d := D * D)
        (μ := S.flatCoefficient) S.flatBlock) :=
  MPSTensor.sameMPV₂Pos_toTensorFromBlocks_of_reconstruction
    (retainedVerticalProductTensor dim mult weight B)
    S.flatCoefficient S.flatBlock S.flatInclusion
    S.flatInclusion_isometry S.flat_intertwine_adjoint S.flat_reconstruction

/-- Every active normal corner of the retained product is gauge-phase
equivalent to some normal tensor in a BNT for the blocked vertical tensor.

This is only the coverage direction: a blocked BNT label need not occur in
the product of a prescribed pair, or even among the active product corners.
The conclusion therefore chooses a blocked label for each active corner and
makes no converse assertion.

**Scope restriction (active product BNT):** Proposition 2.7 classifies the
nonzero canonical-form coefficients.  Hence this theorem covers active
product corners only and does not assert surjectivity onto the blocked BNT.
Documented in
`docs/paper-gaps/cpsv16_bnt_uniqueness_zero_coefficient.tex`.

**Local fix (Figure-11 fixed-pair support):** A fixed product pair may have no
corner of a given blocked label; such a label has an empty multiplicity fiber.
Documented in `docs/paper-gaps/cpsv16_figure11_per_pair_support.tex`.

Source: CPSV16, Appendix C.4, lines 2025--2029, using Proposition 2.7
(`prop:char-BNT`). -/
theorem exists_blockedBNT_gaugePhase_of_flatBlock
    {d g₂ : ℕ}
    (S : RetainedProductSpectralFamily dim mult weight B)
    (M : MPOTensor d D)
    (U : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ)
    (hU : U * Uᴴ = 1)
    (hReconstruct : ∀ ab, verticalTensor M ab =
      Uᴴ * verticalAssembledTensor dim mult weight B ab * U)
    (dim₂ : Fin g₂ → ℕ)
    (A₂ : (γ : Fin g₂) → MPSTensor (D * D) (dim₂ γ))
    [∀ γ, NeZero (dim₂ γ)]
    (hBNT₂ : MPSTensor.IsCPSVBasisOfNormalTensors
      (verticalTensor (blockTwo M)) (fun γ ↦ ⟨dim₂ γ, A₂ γ⟩)) :
    ∀ j : Fin (Fintype.card S.ActiveLabel),
      ∃ γ : Fin g₂, ∃ hdim : dim₂ γ = S.flatDim j,
      ∃ X : GL (Fin (S.flatDim j)) ℂ, ∃ ζ : ℂ, ‖ζ‖ = 1 ∧
        ∀ ab, S.flatBlock j ab = ζ •
          ((X : Matrix (Fin (S.flatDim j)) (Fin (S.flatDim j)) ℂ) *
            (cast (congr_arg (MPSTensor (D * D)) hdim) (A₂ γ)) ab *
              (↑(X⁻¹) : Matrix (Fin (S.flatDim j))
                (Fin (S.flatDim j)) ℂ)) := by
  letI : ∀ j, NeZero (S.flatDim j) := fun j ↦
    ⟨(S.flatDim_pos j).ne'⟩
  have hsquare := verticalTensor_blockTwo_squared_coisometry_reconstruction
    M (verticalAssembledTensor dim mult weight B) U hU hReconstruct
  have hSame : MPSTensor.SameMPV₂Pos (verticalTensor (blockTwo M))
      (retainedVerticalProductTensor dim mult weight B) :=
    MPSTensor.sameMPV₂Pos_of_coisometry_reconstruction
      (verticalTensor (blockTwo M))
      (retainedVerticalProductTensor dim mult weight B)
      (verticalCoisometrySquare U) hsquare.1 hsquare.2
  have hBNTProduct : MPSTensor.IsCPSVBasisOfNormalTensors
      (retainedVerticalProductTensor dim mult weight B)
      (fun γ ↦ ⟨dim₂ γ, A₂ γ⟩) :=
    hBNT₂.of_sameMPV₂Pos hSame
  have hCharacterization :=
    (MPSTensor.isCPSVBasisOfNormalTensors_iff_canonicalForm_covered_and_minimal
      (retainedVerticalProductTensor dim mult weight B)
      S.flatCoefficient S.flatBlock A₂ S.flatBlock_normal
      S.flat_sameMPV₂Pos).mp hBNTProduct
  intro j
  exact hCharacterization.2.1 j (S.flatCoefficient_ne j)

/-- A simultaneous choice of the blocked BNT label, dimension equality,
gauge, and phase for every enumerated active product corner.

The map `label` need not be surjective: unused blocked BNT labels are allowed.

**Scope restriction (active product BNT):** This structure records only the
one-way coverage of active product corners.  Empty fibers record unused
blocked labels.  Documented in
`docs/paper-gaps/cpsv16_bnt_uniqueness_zero_coefficient.tex`.

**Local fix (Figure-11 fixed-pair support):** No nonempty multiplicity space is
asserted for an unused blocked label.  Documented in
`docs/paper-gaps/cpsv16_figure11_per_pair_support.tex`.

Source: CPSV16, Appendix C.4, lines 2025--2029. -/
structure FlatBlockedBNTComparison {g₂ : ℕ}
    (S : RetainedProductSpectralFamily dim mult weight B)
    (dim₂ : Fin g₂ → ℕ)
    (A₂ : (γ : Fin g₂) → MPSTensor (D * D) (dim₂ γ)) where
  /-- Blocked BNT label covering an active product corner. -/
  label : Fin (Fintype.card S.ActiveLabel) → Fin g₂
  /-- Equality of the blocked and active corner bond dimensions. -/
  dim_eq : ∀ j, dim₂ (label j) = S.flatDim j
  /-- Invertible gauge from the chosen blocked tensor to the active corner. -/
  gauge : ∀ j, GL (Fin (S.flatDim j)) ℂ
  /-- Unit-modulus proportionality phase. -/
  phase : Fin (Fintype.card S.ActiveLabel) → ℂ
  /-- Every chosen phase has modulus one. -/
  phase_norm : ∀ j, ‖phase j‖ = 1
  /-- Exact gauge-phase relation for every tensor letter. -/
  block_eq : ∀ j ab, S.flatBlock j ab = phase j •
    ((gauge j : Matrix (Fin (S.flatDim j)) (Fin (S.flatDim j)) ℂ) *
      (cast (congr_arg (MPSTensor (D * D)) (dim_eq j))
        (A₂ (label j))) ab *
      (↑((gauge j)⁻¹) : Matrix (Fin (S.flatDim j))
        (Fin (S.flatDim j)) ℂ))

/-- The active normal corners of every retained copy pair, transported back
to the original one-site BNT labels and normalized by isometries.

Source: CPSV16, Appendix C.4, lines 2020--2029. -/
structure OriginalCornerFamily
    (S : RetainedProductSpectralFamily dim mult weight B) where
  /-- Original BNT label carried by each active copy-pair corner.

  Source: CPSV16, Appendix C.4, lines 2025--2029. -/
  label : ∀ p : VerticalCopyPair mult, Fin (S.count p) → Fin g
  /-- Positive coefficient of the transported original BNT tensor.

  Source: CPSV16, Appendix C.4, lines 2025--2029. -/
  coefficient : ∀ p : VerticalCopyPair mult, Fin (S.count p) → ℂ
  /-- Every transported coefficient is positive.

  Source: CPSV16, Appendix C.4, lines 2025--2029. -/
  coefficient_pos : ∀ p k, (0 : ℂ) < coefficient p k
  /-- Isometric inclusion of an original-label corner into its raw copy-pair
  bond space.

  Source: CPSV16, Appendix C.4, lines 2025--2029. -/
  inclusion : ∀ (p : VerticalCopyPair mult) (k : Fin (S.count p)),
    Matrix (Fin (dim p.1.1 * dim p.2.1)) (Fin (dim (label p k))) ℂ
  /-- Every original-label corner inclusion is an isometry.

  Source: CPSV16, Appendix C.4, lines 2025--2029. -/
  inclusion_isometry : ∀ p k, (inclusion p k)ᴴ * inclusion p k = 1
  /-- Distinct active corners of a fixed copy pair have orthogonal ranges.

  Source: CPSV16, Appendix C.4, lines 2025--2029. -/
  inclusion_orthogonal : ∀ p k l, k ≠ l →
    (inclusion p k)ᴴ * inclusion p l = 0
  /-- Each inclusion intertwines the raw product tensor with its positive
  multiple of the original BNT tensor.

  Source: CPSV16, Appendix C.4, lines 2025--2029. -/
  intertwine : ∀ p k ab,
    (mulTensor (verticalBNTMPO (B p.1.1))
        (verticalBNTMPO (B p.2.1))).toMPSTensor ab * inclusion p k =
      inclusion p k * (coefficient p k • B (label p k) ab)
  /-- The original-label corners reconstruct every letter of the raw product
  tensor.

  Source: CPSV16, Appendix C.4, lines 2025--2029. -/
  reconstruction : ∀ p ab,
    (mulTensor (verticalBNTMPO (B p.1.1))
        (verticalBNTMPO (B p.2.1))).toMPSTensor ab =
      ∑ k, inclusion p k * (coefficient p k • B (label p k) ab) *
        (inclusion p k)ᴴ

private theorem castBondColumns_isometry
    {r m n : ℕ} (V : Matrix (Fin r) (Fin m) ℂ)
    (hV : Vᴴ * V = 1) (h : m = n) :
    let V' := cast (congrArg (fun k ↦ Matrix (Fin r) (Fin k) ℂ) h) V
    V'ᴴ * V' = 1 := by
  cases h
  simpa using hV

private theorem castBondColumns_compression
    {r m n e : ℕ} (T : MPSTensor e r) (A : MPSTensor e m)
    (V : Matrix (Fin r) (Fin m) ℂ) (c : ℂ)
    (hcorner : ∀ v, c • A v = Vᴴ * T v * V) (h : m = n)
    (v : Fin e) :
    let A' := cast (congrArg (MPSTensor e) h) A
    let V' := cast (congrArg (fun k ↦ Matrix (Fin r) (Fin k) ℂ) h) V
    c • A' v = V'ᴴ * T v * V' := by
  cases h
  simpa using hcorner v

/-- The distinguished blocked reference inclusion transported to the bond
dimension of an active product corner.

Source: CPSV16, Appendix C.4, lines 2025--2029. -/
noncomputable def FlatBlockedBNTComparison.referenceInclusion
    {g₂ d : ℕ} {dim₂ : Fin g₂ → ℕ}
    {A₂ : (γ : Fin g₂) → MPSTensor (D * D) (dim₂ γ)}
    {S : RetainedProductSpectralFamily dim mult weight B}
    (C : FlatBlockedBNTComparison S dim₂ A₂)
    (mult₂ : Fin g₂ → ℕ) (hMult₂ : ∀ γ, 0 < mult₂ γ)
    (U₂ : Matrix
      (Fin (∑ q : Fin (∑ γ : Fin g₂, mult₂ γ),
        verticalCopyDim dim₂ mult₂ q))
      (Fin (d * d)) ℂ)
    (j : Fin (Fintype.card S.ActiveLabel)) :
    Matrix (Fin (d * d)) (Fin (S.flatDim j)) ℂ :=
  cast (congrArg (fun n ↦ Matrix (Fin (d * d)) (Fin n) ℂ) (C.dim_eq j))
    (blockedReferenceInclusion dim₂ mult₂ hMult₂ U₂ (C.label j))

/-- Every transported distinguished reference inclusion is an isometry.

Source: CPSV16, Appendix C.4, lines 2025--2029. -/
theorem FlatBlockedBNTComparison.referenceInclusion_isometry
    {g₂ d : ℕ} {dim₂ : Fin g₂ → ℕ}
    {A₂ : (γ : Fin g₂) → MPSTensor (D * D) (dim₂ γ)}
    {S : RetainedProductSpectralFamily dim mult weight B}
    (C : FlatBlockedBNTComparison S dim₂ A₂)
    (mult₂ : Fin g₂ → ℕ) (hMult₂ : ∀ γ, 0 < mult₂ γ)
    (U₂ : Matrix
      (Fin (∑ q : Fin (∑ γ : Fin g₂, mult₂ γ),
        verticalCopyDim dim₂ mult₂ q))
      (Fin (d * d)) ℂ)
    (hU₂ : U₂ * U₂ᴴ = 1)
    (j : Fin (Fintype.card S.ActiveLabel)) :
    (C.referenceInclusion mult₂ hMult₂ U₂ j)ᴴ *
        C.referenceInclusion mult₂ hMult₂ U₂ j = 1 := by
  exact castBondColumns_isometry
    (blockedReferenceInclusion dim₂ mult₂ hMult₂ U₂ (C.label j))
    (blockedReferenceInclusion_isometry dim₂ mult₂ hMult₂ U₂ hU₂ (C.label j))
    (C.dim_eq j)

/-- Compression by the transported reference inclusion is the distinguished
weighted blocked BNT copy, transported to the active bond dimension.

Source: CPSV16, Appendix C.4, lines 2025--2029. -/
theorem FlatBlockedBNTComparison.reference_compression
    {g₂ d : ℕ} {dim₂ : Fin g₂ → ℕ}
    {A₂ : (γ : Fin g₂) → MPSTensor (D * D) (dim₂ γ)}
    {S : RetainedProductSpectralFamily dim mult weight B}
    (C : FlatBlockedBNTComparison S dim₂ A₂)
    (M : MPOTensor d D)
    (mult₂ : Fin g₂ → ℕ) (hMult₂ : ∀ γ, 0 < mult₂ γ)
    (weight₂ : (γ : Fin g₂) → Fin (mult₂ γ) → ℂ)
    (U₂ : Matrix
      (Fin (∑ q : Fin (∑ γ : Fin g₂, mult₂ γ),
        verticalCopyDim dim₂ mult₂ q))
      (Fin (d * d)) ℂ)
    (hU₂ : U₂ * U₂ᴴ = 1)
    (hReconstruct₂ : ∀ ab, verticalTensor (blockTwo M) ab =
      U₂ᴴ * verticalAssembledTensor dim₂ mult₂ weight₂ A₂ ab * U₂)
    (j : Fin (Fintype.card S.ActiveLabel)) (ab : Fin (D * D)) :
    weight₂ (C.label j) ⟨0, hMult₂ (C.label j)⟩ •
        (cast (congrArg (MPSTensor (D * D)) (C.dim_eq j))
          (A₂ (C.label j))) ab =
      (C.referenceInclusion mult₂ hMult₂ U₂ j)ᴴ *
        verticalTensor (blockTwo M) ab *
          C.referenceInclusion mult₂ hMult₂ U₂ j := by
  exact castBondColumns_compression
    (verticalTensor (blockTwo M)) (A₂ (C.label j))
    (blockedReferenceInclusion dim₂ mult₂ hMult₂ U₂ (C.label j))
    (weight₂ (C.label j) ⟨0, hMult₂ (C.label j)⟩)
    (blockedReference_compression M dim₂ mult₂ hMult₂ weight₂ A₂ U₂ hU₂
      hReconstruct₂ (C.label j))
    (C.dim_eq j) ab

/-- The active-to-blocked BNT comparisons can be chosen simultaneously.

**Scope restriction (active product BNT):** The chosen label map need not be
surjective.  Documented in
`docs/paper-gaps/cpsv16_bnt_uniqueness_zero_coefficient.tex`.

**Local fix (Figure-11 fixed-pair support):** Unused blocked labels are left
for empty multiplicity fibers.  Documented in
`docs/paper-gaps/cpsv16_figure11_per_pair_support.tex`.

Source: CPSV16, Appendix C.4, lines 2025--2029. -/
theorem exists_flatBlockedBNTComparison
    {d g₂ : ℕ}
    (S : RetainedProductSpectralFamily dim mult weight B)
    (M : MPOTensor d D)
    (U : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ)
    (hU : U * Uᴴ = 1)
    (hReconstruct : ∀ ab, verticalTensor M ab =
      Uᴴ * verticalAssembledTensor dim mult weight B ab * U)
    (dim₂ : Fin g₂ → ℕ)
    (A₂ : (γ : Fin g₂) → MPSTensor (D * D) (dim₂ γ))
    [∀ γ, NeZero (dim₂ γ)]
    (hBNT₂ : MPSTensor.IsCPSVBasisOfNormalTensors
      (verticalTensor (blockTwo M)) (fun γ ↦ ⟨dim₂ γ, A₂ γ⟩)) :
    Nonempty (FlatBlockedBNTComparison S dim₂ A₂) := by
  classical
  have hExists := exists_blockedBNT_gaugePhase_of_flatBlock
    S M U hU hReconstruct dim₂ A₂ hBNT₂
  choose label dim_eq gauge phase phase_norm block_eq using hExists
  exact ⟨{
    label := label
    dim_eq := dim_eq
    gauge := gauge
    phase := phase
    phase_norm := phase_norm
    block_eq := block_eq }⟩

/-- Composing with the squared vertical reconstruction gives an isometry into
the blocked ambient bond space. -/
theorem ambientInclusion_isometry {d : ℕ}
    (S : RetainedProductSpectralFamily dim mult weight B)
    (U : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ)
    (hU : U * Uᴴ = 1) (x : S.ActiveLabel) :
    (S.ambientInclusion U x)ᴴ * S.ambientInclusion U x = 1 := by
  have hsquare := verticalCoisometrySquare_isCoisometry U hU
  unfold ambientInclusion
  calc
    (((verticalCoisometrySquare U)ᴴ * S.retainedInclusion x)ᴴ *
          ((verticalCoisometrySquare U)ᴴ * S.retainedInclusion x)) =
        (S.retainedInclusion x)ᴴ *
          (verticalCoisometrySquare U * (verticalCoisometrySquare U)ᴴ) *
            S.retainedInclusion x := by
      simp only [Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    _ = (S.retainedInclusion x)ᴴ * S.retainedInclusion x := by
      rw [hsquare, Matrix.mul_one]
    _ = 1 := S.retainedInclusion_isometry x

/-- The composite ambient inclusion intertwines an active weighted corner
with the blocked vertical tensor.

Source: CPSV16, Appendix C.4, lines 2025--2029. -/
theorem ambient_intertwine {d : ℕ}
    (S : RetainedProductSpectralFamily dim mult weight B)
    (M : MPOTensor d D)
    (U : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ)
    (hU : U * Uᴴ = 1)
    (hReconstruct : ∀ ab, verticalTensor M ab =
      Uᴴ * verticalAssembledTensor dim mult weight B ab * U)
    (x : S.ActiveLabel) (ab : Fin (D * D)) :
    verticalTensor (blockTwo M) ab * S.ambientInclusion U x =
      S.ambientInclusion U x *
        (S.coefficient x.1 x.2 • S.block x.1 x.2 ab) := by
  have hsquare := verticalTensor_blockTwo_squared_coisometry_reconstruction
    M (verticalAssembledTensor dim mult weight B) U hU hReconstruct
  let W := verticalCoisometrySquare U
  let R := S.retainedInclusion x
  let C := retainedVerticalProductTensor dim mult weight B
  calc
    verticalTensor (blockTwo M) ab * S.ambientInclusion U x =
        (Wᴴ * C ab * W) * (Wᴴ * R) := by
      rw [hsquare.2 ab]
      rfl
    _ = Wᴴ * C ab * (W * Wᴴ) * R := by
      simp only [Matrix.mul_assoc]
    _ = Wᴴ * (C ab * R) := by
      rw [hsquare.1]
      simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = Wᴴ * (R * (S.coefficient x.1 x.2 • S.block x.1 x.2 ab)) := by
      rw [S.retained_intertwine x ab]
    _ = S.ambientInclusion U x *
        (S.coefficient x.1 x.2 • S.block x.1 x.2 ab) := by
      simp only [ambientInclusion, W, R, Matrix.mul_assoc]

/-- The adjoint composite ambient inclusion satisfies the reverse
intertwining identity.

Source: CPSV16, Appendix C.4, lines 2025--2029. -/
theorem ambient_intertwine_adjoint {d : ℕ}
    (S : RetainedProductSpectralFamily dim mult weight B)
    (M : MPOTensor d D)
    (U : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ)
    (hU : U * Uᴴ = 1)
    (hReconstruct : ∀ ab, verticalTensor M ab =
      Uᴴ * verticalAssembledTensor dim mult weight B ab * U)
    (x : S.ActiveLabel) (ab : Fin (D * D)) :
    (S.ambientInclusion U x)ᴴ * verticalTensor (blockTwo M) ab =
      (S.coefficient x.1 x.2 • S.block x.1 x.2 ab) *
        (S.ambientInclusion U x)ᴴ := by
  have hsquare := verticalTensor_blockTwo_squared_coisometry_reconstruction
    M (verticalAssembledTensor dim mult weight B) U hU hReconstruct
  let W := verticalCoisometrySquare U
  let R := S.retainedInclusion x
  let C := retainedVerticalProductTensor dim mult weight B
  calc
    (S.ambientInclusion U x)ᴴ * verticalTensor (blockTwo M) ab =
        (Rᴴ * W) * (Wᴴ * C ab * W) := by
      rw [hsquare.2 ab]
      simp only [ambientInclusion, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, W, R, C,
        retainedVerticalProductTensor]
    _ = Rᴴ * (W * Wᴴ) * C ab * W := by
      simp only [Matrix.mul_assoc]
    _ = (Rᴴ * C ab) * W := by
      rw [hsquare.1]
      simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = ((S.coefficient x.1 x.2 • S.block x.1 x.2 ab) * Rᴴ) * W := by
      rw [S.retained_intertwine_adjoint x ab]
    _ = (S.coefficient x.1 x.2 • S.block x.1 x.2 ab) *
        (S.ambientInclusion U x)ᴴ := by
      simp only [ambientInclusion, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, W, R, Matrix.mul_assoc]

/-- Compression of the blocked vertical tensor by a composite ambient
inclusion gives its active weighted corner.

Source: CPSV16, Appendix C.4, lines 2025--2029. -/
theorem ambient_compression {d : ℕ}
    (S : RetainedProductSpectralFamily dim mult weight B)
    (M : MPOTensor d D)
    (U : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ)
    (hU : U * Uᴴ = 1)
    (hReconstruct : ∀ ab, verticalTensor M ab =
      Uᴴ * verticalAssembledTensor dim mult weight B ab * U)
    (x : S.ActiveLabel) (ab : Fin (D * D)) :
    S.coefficient x.1 x.2 • S.block x.1 x.2 ab =
      (S.ambientInclusion U x)ᴴ * verticalTensor (blockTwo M) ab *
        S.ambientInclusion U x := by
  rw [S.ambient_intertwine_adjoint M U hU hReconstruct x ab,
    Matrix.mul_assoc, S.ambientInclusion_isometry U hU x,
    Matrix.mul_one]

/-- The scalar multiplying the blocked BNT representative in every active
product corner is positive.

Source: CPSV16, Appendix C.4, lines 2025--2029, using the sector-weight
positivity argument from Proposition 4.13, lines 1898--1902. -/
theorem FlatBlockedBNTComparison.activeCoefficient_mul_phase_pos
    {g₂ d : ℕ} {dim₂ : Fin g₂ → ℕ}
    {A₂ : (γ : Fin g₂) → MPSTensor (D * D) (dim₂ γ)}
    {S : RetainedProductSpectralFamily dim mult weight B}
    (C : FlatBlockedBNTComparison S dim₂ A₂)
    (M : MPOTensor d D) (hHorizontal : IsHorizontalCF M) (hM : IsMPDO M)
    (U₁ : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ)
    (hU₁ : U₁ * U₁ᴴ = 1)
    (hReconstruct₁ : ∀ ab, verticalTensor M ab =
      U₁ᴴ * verticalAssembledTensor dim mult weight B ab * U₁)
    (mult₂ : Fin g₂ → ℕ) (hMult₂ : ∀ γ, 0 < mult₂ γ)
    (weight₂ : (γ : Fin g₂) → Fin (mult₂ γ) → ℂ)
    (hWeight₂ : ∀ γ q, (0 : ℂ) < weight₂ γ q)
    (U₂ : Matrix
      (Fin (∑ q : Fin (∑ γ : Fin g₂, mult₂ γ),
        verticalCopyDim dim₂ mult₂ q))
      (Fin (d * d)) ℂ)
    (hU₂ : U₂ * U₂ᴴ = 1)
    (hReconstruct₂ : ∀ ab, verticalTensor (blockTwo M) ab =
      U₂ᴴ * verticalAssembledTensor dim₂ mult₂ weight₂ A₂ ab * U₂)
    (hNormal₂ : ∀ γ, MPSTensor.IsNormalTensor (A₂ γ))
    (j : Fin (Fintype.card S.ActiveLabel)) :
    (0 : ℂ) < S.flatCoefficient j * C.phase j := by
  let x := S.activeLabelEquiv j
  let A := cast (congrArg (MPSTensor (D * D)) (C.dim_eq j))
    (A₂ (C.label j))
  let Vact := S.ambientInclusion U₁ x
  let Vref := C.referenceInclusion mult₂ hMult₂ U₂ j
  let c := S.flatCoefficient j * C.phase j
  let c₀ := weight₂ (C.label j) ⟨0, hMult₂ (C.label j)⟩
  letI : NeZero (S.flatDim j) := ⟨(S.flatDim_pos j).ne'⟩
  have hA : MPSTensor.IsNormalTensor A :=
    (MPSTensor.isNormalTensor_cast_iff (C.dim_eq j) (A₂ (C.label j))).2
      (hNormal₂ (C.label j))
  have hVact : Vactᴴ * Vact = 1 := by
    exact S.ambientInclusion_isometry U₁ hU₁ x
  have hVref : Vrefᴴ * Vref = 1 := by
    exact C.referenceInclusion_isometry mult₂ hMult₂ U₂ hU₂ j
  have hphase : C.phase j ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [C.phase_norm j]
    exact one_ne_zero
  have hc : c ≠ 0 := mul_ne_zero (S.flatCoefficient_ne j) hphase
  have hActiveCorner : ∀ ab,
      c • ((C.gauge j : Matrix (Fin (S.flatDim j))
          (Fin (S.flatDim j)) ℂ) * A ab *
        (↑((C.gauge j)⁻¹) : Matrix (Fin (S.flatDim j))
          (Fin (S.flatDim j)) ℂ)) =
        Vactᴴ * verticalTensor (blockTwo M) ab * Vact := by
    intro ab
    calc
      c • ((C.gauge j : Matrix (Fin (S.flatDim j))
            (Fin (S.flatDim j)) ℂ) * A ab *
          (↑((C.gauge j)⁻¹) : Matrix (Fin (S.flatDim j))
            (Fin (S.flatDim j)) ℂ)) =
        S.flatCoefficient j • S.flatBlock j ab := by
          rw [C.block_eq j ab]
          simp only [c, A, smul_smul]
      _ = Vactᴴ * verticalTensor (blockTwo M) ab * Vact := by
        change S.coefficient x.1 x.2 • S.block x.1 x.2 ab = _
        exact S.ambient_compression M U₁ hU₁ hReconstruct₁ x ab
  have hReferenceCorner : ∀ ab, c₀ • A ab =
      Vrefᴴ * verticalTensor (blockTwo M) ab * Vref := by
    intro ab
    exact C.reference_compression M mult₂ hMult₂ weight₂ U₂ hU₂
      hReconstruct₂ j ab
  have hSectorAct := sectorProjectorData_of_gauge_corner
    (blockTwo M) A Vact hVact (C.gauge j) c hActiveCorner
  have hSectorRef := sectorProjectorData_of_gauge_corner
    (blockTwo M) A Vref hVref 1 c₀ (by
      intro ab
      simpa using hReferenceCorner ab)
  have hRange := exists_rangeProjection_corner_ne_zero
    (blockTwo M) A hA Vact hVact (C.gauge j) c hc hActiveCorner
  obtain ⟨N, hne⟩ :=
    (hHorizontal.blockTwo).exists_sectorCompression_ne_zero_of_corner
      (blockTwo M) (Vact * Vactᴴ) hRange
  exact sector_weight_pos hM.blockTwo hSectorRef
    (hWeight₂ (C.label j) ⟨0, hMult₂ (C.label j)⟩)
    hSectorAct N hne

/-- Every active product gauge has scalar positive Gram matrix and becomes
unitary after division by the square root of that scalar.

Source: CPSV16, Appendix C.4, lines 2025--2029, using the Figure 8 Gram
comparison and unitary normalization from Proposition 4.13, lines 1903--1921. -/
theorem FlatBlockedBNTComparison.exists_unitaryNormalization
    {g₂ d : ℕ} {dim₂ : Fin g₂ → ℕ}
    {A₂ : (γ : Fin g₂) → MPSTensor (D * D) (dim₂ γ)}
    {S : RetainedProductSpectralFamily dim mult weight B}
    (C : FlatBlockedBNTComparison S dim₂ A₂)
    (M : MPOTensor d D) (hHorizontal : IsHorizontalCF M) (hM : IsMPDO M)
    (U₁ : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ)
    (hU₁ : U₁ * U₁ᴴ = 1)
    (hReconstruct₁ : ∀ ab, verticalTensor M ab =
      U₁ᴴ * verticalAssembledTensor dim mult weight B ab * U₁)
    (mult₂ : Fin g₂ → ℕ) (hMult₂ : ∀ γ, 0 < mult₂ γ)
    (weight₂ : (γ : Fin g₂) → Fin (mult₂ γ) → ℂ)
    (hWeight₂ : ∀ γ q, (0 : ℂ) < weight₂ γ q)
    (U₂ : Matrix
      (Fin (∑ q : Fin (∑ γ : Fin g₂, mult₂ γ),
        verticalCopyDim dim₂ mult₂ q))
      (Fin (d * d)) ℂ)
    (hU₂ : U₂ * U₂ᴴ = 1)
    (hReconstruct₂ : ∀ ab, verticalTensor (blockTwo M) ab =
      U₂ᴴ * verticalAssembledTensor dim₂ mult₂ weight₂ A₂ ab * U₂)
    (hNormal₂ : ∀ γ, MPSTensor.IsNormalTensor (A₂ γ))
    (j : Fin (Fintype.card S.ActiveLabel)) :
    ∃ ω : ℝ, 0 < ω ∧
      (C.gauge j : Matrix (Fin (S.flatDim j)) (Fin (S.flatDim j)) ℂ)ᴴ *
          C.gauge j = (ω : ℂ) • 1 ∧
      ((Real.sqrt ω : ℂ))⁻¹ •
          (C.gauge j : Matrix (Fin (S.flatDim j))
            (Fin (S.flatDim j)) ℂ) ∈
        Matrix.unitaryGroup (Fin (S.flatDim j)) ℂ := by
  let x := S.activeLabelEquiv j
  let A := cast (congrArg (MPSTensor (D * D)) (C.dim_eq j))
    (A₂ (C.label j))
  let Vact := S.ambientInclusion U₁ x
  let Vref := C.referenceInclusion mult₂ hMult₂ U₂ j
  let c := S.flatCoefficient j * C.phase j
  let c₀ := weight₂ (C.label j) ⟨0, hMult₂ (C.label j)⟩
  letI : NeZero (S.flatDim j) := ⟨(S.flatDim_pos j).ne'⟩
  have hA : MPSTensor.IsNormalTensor A :=
    (MPSTensor.isNormalTensor_cast_iff (C.dim_eq j) (A₂ (C.label j))).2
      (hNormal₂ (C.label j))
  have hc : (0 : ℂ) < c :=
    C.activeCoefficient_mul_phase_pos M hHorizontal hM U₁ hU₁ hReconstruct₁
      mult₂ hMult₂ weight₂ hWeight₂ U₂ hU₂ hReconstruct₂ hNormal₂ j
  have hc₀ : (0 : ℂ) < c₀ :=
    hWeight₂ (C.label j) ⟨0, hMult₂ (C.label j)⟩
  have hActiveCorner : ∀ ab,
      Vactᴴ * verticalTensor (blockTwo M) ab * Vact =
        c • ((C.gauge j : Matrix (Fin (S.flatDim j))
            (Fin (S.flatDim j)) ℂ) * A ab *
          (↑((C.gauge j)⁻¹) : Matrix (Fin (S.flatDim j))
            (Fin (S.flatDim j)) ℂ)) := by
    intro ab
    symm
    calc
      c • ((C.gauge j : Matrix (Fin (S.flatDim j))
            (Fin (S.flatDim j)) ℂ) * A ab *
          (↑((C.gauge j)⁻¹) : Matrix (Fin (S.flatDim j))
            (Fin (S.flatDim j)) ℂ)) =
        S.flatCoefficient j • S.flatBlock j ab := by
          rw [C.block_eq j ab]
          simp only [c, A, smul_smul]
      _ = Vactᴴ * verticalTensor (blockTwo M) ab * Vact := by
        change S.coefficient x.1 x.2 • S.block x.1 x.2 ab = _
        exact S.ambient_compression M U₁ hU₁ hReconstruct₁ x ab
  have hReferenceCorner : ∀ ab,
      Vrefᴴ * verticalTensor (blockTwo M) ab * Vref = c₀ • A ab := by
    intro ab
    exact (C.reference_compression M mult₂ hMult₂ weight₂ U₂ hU₂
      hReconstruct₂ j ab).symm
  have hDress :=
    (hHorizontal.blockTwo).gramDressing_eq_of_two_grouped_corners
      (blockTwo M) hM.blockTwo A Vact Vref (C.gauge j) 1 c c₀ hc hc₀
      hActiveCorner (by
        intro ab
        simpa using hReferenceCorner ab)
  have hXdet : IsUnit
      (C.gauge j : Matrix (Fin (S.flatDim j))
        (Fin (S.flatDim j)) ℂ).det :=
    Matrix.isUnits_det_units (C.gauge j)
  have hOneDet : IsUnit
      (1 : Matrix (Fin (S.flatDim j)) (Fin (S.flatDim j)) ℂ).det := by
    simp
  have hGramConj : ∀ ab,
      (C.gauge j : Matrix (Fin (S.flatDim j))
          (Fin (S.flatDim j)) ℂ)ᴴ * C.gauge j * A ab *
          (((C.gauge j : Matrix (Fin (S.flatDim j))
            (Fin (S.flatDim j)) ℂ)ᴴ * C.gauge j)⁻¹) =
        (1 : Matrix (Fin (S.flatDim j))
            (Fin (S.flatDim j)) ℂ)ᴴ * 1 * A ab *
          (((1 : Matrix (Fin (S.flatDim j))
            (Fin (S.flatDim j)) ℂ)ᴴ * 1)⁻¹) := by
    intro ab
    simpa [gramDressing] using congrFun hDress ab
  obtain ⟨ω, hω, hGram⟩ :=
    hA.isNormal.gram_eq_pos_smul_gram_of_gram_conj_eq
      hXdet hOneDet hGramConj
  have hGramOne :
      (C.gauge j : Matrix (Fin (S.flatDim j))
          (Fin (S.flatDim j)) ℂ)ᴴ * C.gauge j = (ω : ℂ) • 1 := by
    simpa using hGram
  exact ⟨ω, hω, hGramOne,
    Matrix.smul_mem_unitaryGroup_of_conjTranspose_mul_self_eq_smul_one
      hω hGramOne⟩

end RetainedProductSpectralFamily

end MPOTensor
