/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinSum
import TNLean.MPS.MPDO.VerticalProductReconstruction

/-!
# Copy inclusions and pair blocks of a retained vertical product

This file establishes the retained-copy coordinate identities and separates
the retained vertical product into its weighted copy-pair blocks.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.4, lines 2020--2029
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

The one-site coisometric reconstruction is squared exactly. The preceding
coisometric transfer theorem then passes both hypotheses to the retained
product tensor, including when its active support is smaller than the full
product bond space.

Source: CPSV16, Proposition 4.13, lines 1873--1893, and Appendix C.4,
lines 2015--2025. -/
theorem retainedVerticalProduct_projectorClosure_and_noPeriodicVectors_of_blockTwo
    {d D n : ℕ} (M : MPOTensor d D) (A : MPSTensor (D * D) n)
    (U : Matrix (Fin n) (Fin d) ℂ) (hU : U * Uᴴ = 1)
    (hReconstruct : ∀ ab, verticalTensor M ab = Uᴴ * A ab * U)
    (hClosure : MPSTensor.HasInvariantProjectorClosure (verticalTensor (blockTwo M)))
    (hPer : MPSTensor.HasNoPeriodicVectors (verticalTensor (blockTwo M))) :
    let C :=
      (mulTensor (verticalBNTMPO A) (verticalBNTMPO A)).toMPSTensor
    MPSTensor.HasInvariantProjectorClosure C ∧
      MPSTensor.HasNoPeriodicVectors C := by
  dsimp only
  have hsquare := verticalTensor_blockTwo_squared_coisometry_reconstruction
    M A U hU hReconstruct
  exact MPSTensor.projectorClosure_and_noPeriodicVectors_of_coisometry_reconstruction
    (verticalTensor (blockTwo M))
    (mulTensor (verticalBNTMPO A) (verticalBNTMPO A)).toMPSTensor
    (verticalCoisometrySquare U) hsquare.1 hsquare.2
    hClosure hPer

/-- The squared retained product of a tensor in normalized BNT-refined
horizontal form has projector closure and no periodic vectors.

Source: CPSV16, Proposition 4.13, lines 1873--1893, and Appendix C.4,
lines 2015--2025. -/
theorem retainedVerticalProduct_projectorClosure_and_noPeriodicVectors
    {d D n : ℕ} (M : MPOTensor d D) (A : MPSTensor (D * D) n)
    (U : Matrix (Fin n) (Fin d) ℂ) (hU : U * Uᴴ = 1)
    (hReconstruct : ∀ ab, verticalTensor M ab = Uᴴ * A ab * U)
    (hHorizontal : IsHorizontalCF M) (hM : IsMPDO M) :
    let C :=
      (mulTensor (verticalBNTMPO A) (verticalBNTMPO A)).toMPSTensor
    MPSTensor.HasInvariantProjectorClosure C ∧
      MPSTensor.HasNoPeriodicVectors C := by
  have hHorizontalTwo := hHorizontal.blockTwo
  have hMTwo := hM.blockTwo
  exact retainedVerticalProduct_projectorClosure_and_noPeriodicVectors_of_blockTwo
    M A U hU hReconstruct
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
  simp only [retainedVerticalProductTensor, toMPSTensor, MPSTensor.finProdFinEquiv_divNat,
    MPSTensor.finProdFinEquiv_modNat, productRetainedEquiv, verticalProductSectorEquiv,
    Equiv.symm_trans, Equiv.symm_mk, Equiv.prodCongr_symm, Equiv.symm_symm,
    Equiv.trans_apply, Equiv.coe_fn_mk, Equiv.prodCongr_apply, Prod.map_apply,
    mulTensor_apply, verticalBNTMPO_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, weightedVerticalProductBlock]
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
    simpa only [mul_comm, mul_left_comm, mul_assoc] using
      Fintype.sum_mul_mul_eq_mul_sum_mul (weight α q * weight β r)
        (fun x => B α (finProdFinEquiv (a, x)) i i')
        (fun x => B β (finProdFinEquiv (x, b)) j j')
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
theorem weightedVerticalProductBlock_projectorClosure_and_noPeriodicVectors_of_blockTwo
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
    (hClosure : MPSTensor.HasInvariantProjectorClosure (verticalTensor (blockTwo M)))
    (hPer : MPSTensor.HasNoPeriodicVectors (verticalTensor (blockTwo M)))
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
      retainedVerticalProduct_projectorClosure_and_noPeriodicVectors_of_blockTwo M
        (verticalAssembledTensor dim mult weight B) U hU hReconstruct
        hClosure hPer
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

/-- Every ordered pair of retained vertical BNT copies of a tensor in
normalized BNT-refined horizontal form has projector closure and no periodic
vectors.

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
  have hHorizontalTwo := hHorizontal.blockTwo
  have hMTwo := hM.blockTwo
  exact weightedVerticalProductBlock_projectorClosure_and_noPeriodicVectors_of_blockTwo
    dim mult weight B M U hU hReconstruct
    (hHorizontalTwo.hasInvariantProjectorClosure_verticalTensor (blockTwo M) hMTwo)
    (hasNoPeriodicVectors_verticalTensor_of_horizontalCF
      (blockTwo M) hMTwo hHorizontalTwo) p

/-- Every retained copy-pair tensor has an exact decomposition into its
nonzero normal corners, with the corner isometries retained.

The active family may be empty.  Thus a zero-dimensional copy pair, or a
copy-pair tensor whose every letter vanishes, contributes no artificial
normal sector.  No division by the outer copy weight occurs in this theorem.

Source: CPSV16, Appendix C.4, lines 2020--2029. -/
theorem exists_weightedVerticalProductBlock_normalDecomposition_of_blockTwo
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
    (hClosure : MPSTensor.HasInvariantProjectorClosure (verticalTensor (blockTwo M)))
    (hPer : MPSTensor.HasNoPeriodicVectors (verticalTensor (blockTwo M)))
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
    weightedVerticalProductBlock_projectorClosure_and_noPeriodicVectors_of_blockTwo
      dim mult weight B M U hU hReconstruct hClosure hPer p
  exact MPSTensor.exists_normalTensor_blockDecomp_with_isometry_of_hasInvariantProjectorClosure
    (weightedVerticalProductBlock dim mult weight B p)
    hCanonical.1 hCanonical.2

/-- Every retained copy-pair tensor of a tensor in normalized BNT-refined
horizontal form has an exact decomposition into its nonzero normal corners,
with the corner isometries retained.

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
  have hHorizontalTwo := hHorizontal.blockTwo
  have hMTwo := hM.blockTwo
  exact exists_weightedVerticalProductBlock_normalDecomposition_of_blockTwo
    dim mult weight B M U hU hReconstruct
    (hHorizontalTwo.hasInvariantProjectorClosure_verticalTensor (blockTwo M) hMTwo)
    (hasNoPeriodicVectors_verticalTensor_of_horizontalCF
      (blockTwo M) hMTwo hHorizontalTwo) p

end MPOTensor
