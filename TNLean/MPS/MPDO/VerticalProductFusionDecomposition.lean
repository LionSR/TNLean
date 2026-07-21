/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.VerticalBlockedOperatorRepresentations
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

open scoped Matrix BigOperators Kronecker

noncomputable section

namespace MPOTensor

/-- The Kronecker square of a rectangular vertical coisometry, with both
product index spaces encoded by the standard finite-product equivalence. -/
noncomputable def verticalCoisometrySquare {d n : ℕ}
    (U : Matrix (Fin n) (Fin d) ℂ) :
    Matrix (Fin (n * n)) (Fin (d * d)) ℂ :=
  (U ⊗ₖ U).submatrix finProdFinEquiv.symm finProdFinEquiv.symm

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
  · unfold verticalCoisometrySquare
    rw [Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv _ _ _ finProdFinEquiv.symm _,
      Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hU,
      Matrix.one_kronecker_one, Matrix.submatrix_one_equiv]
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
        ((mulTensor
          (verticalBNTMPO (verticalAssembledTensor dim mult weight B))
          (verticalBNTMPO (verticalAssembledTensor dim mult weight B))).toMPSTensor ab) =
      Matrix.blockDiagonal' fun p :
          ((α : Fin g) × Fin (mult α)) × ((α : Fin g) × Fin (mult α)) =>
        (weight p.1.1 p.1.2 * weight p.2.1 p.2.2) •
          Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
            ((mulTensor (verticalBNTMPO (B p.1.1))
              (verticalBNTMPO (B p.2.1))).toMPSTensor ab) := by
  classical
  obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective ab
  ext x y
  rcases x with ⟨⟨⟨α, q⟩, ⟨β, r⟩⟩, ⟨i, j⟩⟩
  rcases y with ⟨⟨⟨α', q'⟩, ⟨β', r'⟩⟩, ⟨i', j'⟩⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  simp [productRetainedEquiv, verticalProductSectorEquiv, toMPSTensor,
    mulTensor_apply, verticalBNTMPO_apply]
  by_cases hp :
      ((⟨α, q⟩ : (α : Fin g) × Fin (mult α)),
        (⟨β, r⟩ : (α : Fin g) × Fin (mult α))) =
      ((⟨α', q'⟩ : (α : Fin g) × Fin (mult α)),
        (⟨β', r'⟩ : (α : Fin g) × Fin (mult α)))
  · cases hp
    simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply,
      Matrix.blockDiagonal'_apply_eq,
      verticalAssembledTensor_apply_copy_same]
    simp only [Matrix.smul_apply, smul_eq_mul]
    simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply]
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

end MPOTensor
