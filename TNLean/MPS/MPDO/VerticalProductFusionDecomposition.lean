/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.VerticalBlockedOperatorRepresentations
import TNLean.MPS.MPDO.VerticalCoisometry
import TNLean.MPS.MPDO.HorizontalBlocking
import TNLean.MPS.MPDO.VerticalBNTConstruction
import TNLean.MPS.MPDO.VerticalSpectral
import TNLean.MPS.Tactic.Basic

/-!
# Positive fusion decompositions of vertical product tensors

This file begins the construction of the positive unitary decompositions of
the products of vertical basis-of-normal-tensors sectors in CPSV16,
Appendix C.4, lines 2020--2029.

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
  localDim_pos : ∀ p k, 0 < localDim p k
  coefficient_pos : ∀ p k, (0 : ℂ) < coefficient p k
  block_normal : ∀ p k, MPSTensor.IsNormalTensor (block p k)
  localInclusion_isometry : ∀ p k,
    (localInclusion p k)ᴴ * localInclusion p k = 1
  localInclusion_orthogonal : ∀ p k l, k ≠ l →
    (localInclusion p k)ᴴ * localInclusion p l = 0
  local_intertwine : ∀ p k ab,
    weightedVerticalProductBlock dim mult weight B p ab * localInclusion p k =
      localInclusion p k * (coefficient p k • block p k ab)
  local_intertwine_adjoint : ∀ p k ab,
    (localInclusion p k)ᴴ * weightedVerticalProductBlock dim mult weight B p ab =
      (coefficient p k • block p k ab) * (localInclusion p k)ᴴ
  local_compression : ∀ p k ab,
    coefficient p k • block p k ab =
      (localInclusion p k)ᴴ *
        weightedVerticalProductBlock dim mult weight B p ab *
          localInclusion p k
  local_reconstruction : ∀ p ab,
    weightedVerticalProductBlock dim mult weight B p ab =
      ∑ k, localInclusion p k * (coefficient p k • block p k ab) *
        (localInclusion p k)ᴴ
  local_sameMPV₂Pos : ∀ p, MPSTensor.SameMPV₂Pos
    (weightedVerticalProductBlock dim mult weight B p)
    (MPSTensor.toTensorFromBlocks (d := D * D)
      (μ := coefficient p) (block p))
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

end RetainedProductSpectralFamily

end MPOTensor
