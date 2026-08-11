/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.VerticalProductReconstruction

/-!
# Copy blocks of a retained vertical product

This file establishes retained-copy coordinate identities, canonical copy
inclusions, and distinguished blocked-reference inclusions.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.4, lines 1955--1971 and 2025--2029
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

noncomputable section

namespace MPOTensor

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

end MPOTensor
