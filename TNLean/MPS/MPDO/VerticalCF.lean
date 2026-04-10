/- 
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.Defs
import TNLean.MPS.BNT.Basic
import TNLean.MPS.SharedInfra.BlockAssembly

/-!
# Vertical canonical form for MPO tensors

This file introduces a Lean-facing version of the vertical canonical-form
structure used in the MPDO analysis of arXiv:1606.00608, §4.4.

The paper's Proposition IV.12 writes the tensor, after a local isometry on the
physical indices, as a direct sum
`⊕_α μ_α ⊗ M_α`, where the `μ_α` are positive diagonal matrices and the
`M_α` form a basis of normal tensors (BNT). The current repository infrastructure
packages canonical-form and BNT data using scalar block weights. We therefore
encode the paper's diagonal matrices by **flattening** each diagonal entry of
`μ_α` into a repeated positive scalar weight attached to the same block `M_α`.

The resulting predicate `IsVerticalCF` should be read as a repository-friendly
surrogate for the paper's vertical canonical form.

## Main definitions

* `diagonalTensor`:
  the MPS tensor `i ↦ M i i` extracted from the diagonal MPO entries.
* `verticalTransferMap`:
  the transfer map of `diagonalTensor`, i.e. `E_vert(X) = Σ_i M^{ii} X (M^{ii})†`.
* `HorizontalCFData` / `IsHorizontalCF`:
  lightweight horizontal canonical-form data for an MPO, expressed via the
  doubled-index MPS tensor `M.toMPSTensor`.
* `IsVerticalCF`:
  a flattened positive-weight BNT decomposition for `diagonalTensor M`.
* `lemmaL_blockwise_insert_eq`:
  a scaffold for Lemma L from the paper.
* `verticalCF_of_horizontalCF`:
  the Proposition IV.12 / Prop. 4.13 scaffold.

## References

* [CPGSV17] arXiv:1606.00608, Proposition IV.12 and the auxiliary Lemma L in the appendix
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d D : ℕ}

/-- The diagonal MPS tensor extracted from an MPO by restricting to equal ket
and bra indices. This is the tensor whose transfer map is the "vertical"
transfer map used in the MPDO vertical-canonical-form discussion. -/
def diagonalTensor (M : MPOTensor d D) : MPSTensor d D :=
  fun i => M i i

@[simp] lemma diagonalTensor_apply (M : MPOTensor d D) (i : Fin d) :
    diagonalTensor M i = M i i :=
  rfl

/-- The vertical transfer map of an MPO tensor:
`E_vert(X) = Σ_i M^{ii} X (M^{ii})†`. -/
noncomputable def verticalTransferMap (M : MPOTensor d D) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
  MPSTensor.transferMap (diagonalTensor M)

lemma verticalTransferMap_apply (M : MPOTensor d D)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    verticalTransferMap M X = ∑ i : Fin d, M i i * X * (M i i)ᴴ := by
  simp [verticalTransferMap, diagonalTensor, MPSTensor.transferMap_apply]

/-- Positive real scalar weights, used to flatten the positive diagonal matrices
appearing in the paper's `⊕_α μ_α ⊗ M_α` decomposition. -/
def IsPositiveReal (z : ℂ) : Prop :=
  0 < z.re ∧ z.im = 0

/-- A "first-site insertion" on an MPS tensor. The resulting local tensor is the
one obtained by contracting the physical index with `Y` at a single site. -/
noncomputable def insertedTensor
    (Y : Matrix (Fin d) (Fin d) ℂ) (A : MPSTensor d D) : MPSTensor d D :=
  fun i => ∑ j : Fin d, Y i j • A j

/-- Coefficient-level formulation of "acting with `Y` on the first spin" of an
MPV. This is the hypothesis used in the paper's Lemma L. -/
def FirstSiteActionAgree (A : MPSTensor d D)
    (Y Z : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ (N : ℕ) (σ : Fin (N + 1) → Fin d),
    ∑ i : Fin d, Y (σ 0) i * MPSTensor.mpv A (Fin.cons i (σ ∘ Fin.succ)) =
      ∑ i : Fin d, Z (σ 0) i * MPSTensor.mpv A (Fin.cons i (σ ∘ Fin.succ))

/-- Lightweight horizontal canonical-form data for a family of blocks.

This is the fragment of the full canonical-form package needed for the MPDO
vertical-canonical-form interface in this file: injective blocks, the
left-canonical normalization, and nonzero block weights. -/
structure HorizontalCFData {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k)) : Prop where
  /-- Each block is algebraically injective. -/
  block_injective : ∀ k, MPSTensor.IsInjective (A k)
  /-- Each block is left-canonical. -/
  leftCanonical : ∀ k, ∑ i : Fin d, (A k i)ᴴ * (A k i) = 1
  /-- No block weight vanishes. -/
  weight_ne_zero : ∀ k, μ k ≠ 0

/-- Horizontal canonical form for an MPO tensor, expressed via a canonical-form
decomposition of the doubled-index MPS tensor `M.toMPSTensor`. -/
def IsHorizontalCF (M : MPOTensor d D) : Prop :=
  ∃ (r : ℕ) (dim : Fin r → ℕ) (μ : Fin r → ℂ)
    (A : (k : Fin r) → MPSTensor (d * d) (dim k)),
    HorizontalCFData (d := d * d) μ A ∧
      MPSTensor.SameMPV₂ M.toMPSTensor
        (MPSTensor.toTensorFromBlocks (d := d * d) (μ := μ) A)

/-- The multiplicity-expanded block dimensions corresponding to a family of
positive diagonal weights. -/
def verticalCopyDim {g : ℕ} (dim : Fin g → ℕ) (mult : Fin g → ℕ) :
    Fin (∑ α : Fin g, mult α) → ℕ :=
  fun q => dim ((finSigmaFinEquiv.symm q).1)

/-- The multiplicity-expanded block family obtained by repeating the same BNT
block across all diagonal entries of its positive weight matrix. -/
def verticalCopyBlocks {g : ℕ} (dim : Fin g → ℕ) (mult : Fin g → ℕ)
    (A : (α : Fin g) → MPSTensor d (dim α)) :
    (q : Fin (∑ α : Fin g, mult α)) → MPSTensor d (verticalCopyDim dim mult q) :=
  fun q => A ((finSigmaFinEquiv.symm q).1)

/-- The multiplicity-expanded scalar weights obtained by flattening the
positive diagonal matrices from the paper's vertical decomposition. -/
def verticalCopyWeights {g : ℕ} (mult : Fin g → ℕ)
    (ω : (α : Fin g) → Fin (mult α) → ℂ) :
    Fin (∑ α : Fin g, mult α) → ℂ :=
  fun q =>
    let p := finSigmaFinEquiv.symm q
    ω p.1 p.2

/-- The flattened repeated tensor corresponding to the paper's
`⊕_α μ_α ⊗ M_α` block structure. -/
noncomputable def verticalAssembledTensor {g : ℕ}
    (dim : Fin g → ℕ) (mult : Fin g → ℕ)
    (ω : (α : Fin g) → Fin (mult α) → ℂ)
    (A : (α : Fin g) → MPSTensor d (dim α)) :
    MPSTensor d (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q) :=
  MPSTensor.toTensorFromBlocks
    (μ := verticalCopyWeights mult ω)
    (A := verticalCopyBlocks dim mult A)

/-- A Lean-friendly version of the paper's vertical canonical form:

there is a basis of normal tensors `A α`, together with positive scalar weights
obtained by flattening the positive diagonal matrices `μ_α`, such that the
diagonal MPO tensor `diagonalTensor M` generates the same MPV family as the
flattened repeated tensor built from those blocks. -/
def IsVerticalCF (M : MPOTensor d D) : Prop :=
  ∃ (g : ℕ) (dim : Fin g → ℕ) (mult : Fin g → ℕ)
    (ω : (α : Fin g) → Fin (mult α) → ℂ)
    (A : (α : Fin g) → MPSTensor d (dim α)),
    (∀ α q, IsPositiveReal (ω α q)) ∧
      MPSTensor.IsBNT (verticalAssembledTensor dim mult ω A) g dim A ∧
      MPSTensor.SameMPV₂ (diagonalTensor M) (verticalAssembledTensor dim mult ω A)

/-- **Lemma L** (arXiv:1606.00608, appendix): if two operators act identically
on the first site of every MPV generated by a canonical-form tensor, then their
insertions agree blockwise.

This is the precise blockwise statement needed in the proof of Proposition
IV.12. The intended proof follows the paper: use block separation for the
canonical-form decomposition together with the nonvanishing of the Newton-Girard
sums of the block weights. -/
theorem lemmaL_blockwise_insert_eq
    {r : ℕ} {dim : Fin r → ℕ} {μ : Fin r → ℂ}
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : HorizontalCFData (d := d) μ A)
    {Y Z : Matrix (Fin d) (Fin d) ℂ}
    (hAct :
      FirstSiteActionAgree
        (MPSTensor.toTensorFromBlocks (d := d) (μ := μ) A) Y Z) :
    ∀ k, insertedTensor Y (A k) = insertedTensor Z (A k) := by
  sorry

/-- **Proposition IV.12 / Prop. 4.13** (arXiv:1606.00608): a horizontal
canonical-form MPDO is also in vertical canonical form.

In the current repository this is stated using the Lean-facing predicates
`IsHorizontalCF` and `IsVerticalCF` defined above. The proof is expected to
follow the paper's route through Lemma L and the positivity of the horizontal
MPDO family. -/
theorem verticalCF_of_horizontalCF (M : MPOTensor d D)
    (hMPDO : IsMPDO M) (hHCF : IsHorizontalCF M) :
    IsVerticalCF M := by
  sorry

end MPOTensor
