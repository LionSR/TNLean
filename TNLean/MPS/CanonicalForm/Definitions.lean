/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.DirectSum.IrreducibleDecomposition
import TNLean.MPS.Tensor.Defs
import QICLean.Kraus.Transfer
import TNLean.MPS.Tensor.Overlap
import TNLean.MPS.Tensor.DirectSum.BlockAssembly
import QICLean.Channel.Peripheral.Spectrum.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.IsDiag

/-!
# CPSV canonical forms and normal tensors

This module records four central notions
from arXiv:1606.00608 (Cirac–Pérez-García–Schuch–Verstraete, "Matrix product density
operators: Renormalization fixed points and boundary theories"):

* normal tensor (NT), `MPTensor.IsNormalTensor`,
* canonical form (CF), `MPTensor.IsCPSVCanonicalForm`,
* canonical form II (CFII), `MPSTensor.IsCPSVCanonicalFormII`, and
* basis of normal tensors (BNT), `MPSTensor.IsCPSVBasisOfNormalTensors`.

The literal canonical-form (CF) decomposition of arXiv:1606.00608 eq. `II_CF1`
is recorded by `MPTensor.CPSVCanonicalFormData` and
`MPTensor.IsCPSVCanonicalForm`.  A coisometry embeds the retained weighted
direct sum into the original bond space, whose remaining coordinates are zero.
The line-246 normalization convention is the separate predicate
`MPTensor.CPSVCanonicalFormData.IsWeightNormalized`; it is not part of literal
CF membership.  None of these definitions adds weight ordering or BNT
separation.

The predicates in this file are the CPSV formulations; statements needing left-canonical
normalization or gauge-phase separated blocks take those as separate hypotheses.

## Paper anchors

* `MPTensor.IsNormalTensor`: `Papers/1606.00608/MPDO-22-12-17-2.tex:233-235`
  (Definition: NT is no nontrivial invariant projector + unique modulus-1
  eigenvalue of the associated CPM equal to its spectral radius equal to one).
* `MPSTensor.IsCPSVBasisOfNormalTensors`: `Papers/1606.00608/MPDO-22-12-17-2.tex:271-274`
  (Definition: BNT `{A_j}` of `A` is `A_j` all normal, MPV family of `A`
  spanned by MPV families of the `A_j` at every positive length, and
  eventually linearly independent).

## Relation to the existing primitive-channel predicate

CPSV16's clause "the associated CPM has a unique eigenvalue of magnitude
equal to its spectral radius which is equal to one" has two parts.  The field
`spectral_radius_one` records the spectral-radius normalization, while
`primitive_transfer` uses `_root_.IsPrimitive`
(`TNLean.Channel.Peripheral.Spectrum`) to state that the only eigenvalue on
the unit circle is `1`.  Together they give the paper's peripheral-spectrum
condition (cf. `MPDO-22-12-17-2.tex:231`, the block-then-renormalize paragraph
immediately preceding Definition NT).

The TN-Review formulation (`Papers/2011.12127/TN-Review-main.tex:1827-1830`)
"the transfer operator is a primitive channel" is the same clause and is not
duplicated.

## Connections to existing predicates

`IsCPSVBasisOfNormalTensors` is the only basis-of-normal-tensors predicate.  Its
normality clause is `IsNormalTensor`; algebraic normality `Kraus.IsNormal` together
with transfer spectral radius one is equivalent to it
(`isNormalTensor_iff_isNormal_and_spectralRadius_eq_one` in
`TNLean.MPS.CanonicalForm.NormalBlocks.NormalTensorGauge`).

## Style

Follows the Mathlib style and naming conventions (`lean-conventions` skill).

## Single-block canonical form II

A normal left-canonical tensor with a positive definite diagonal fixed matrix
is in canonical form II, with one block of weight one and no omitted bond
coordinates.

Source: arXiv:1606.00608, Appendix A, lines 1054–1077.
-/

open MPTensor

section

open scoped Matrix BigOperators Matrix.Norms.Operator ComplexOrder MatrixOrder Kraus

namespace MPTensor

universe u v

/-! ## Normal tensor (NT) -/

/--
`MPTensor.IsNormalTensor A` is the **normal tensor** predicate from
arXiv:1606.00608, Definition before eq. `II_CF1` (`Papers/1606.00608/MPDO-22-12-17-2.tex:233-235`):

* (i) `A` admits no nontrivial invariant orthogonal projection, and
* (ii) the associated CPM (the transfer map `E_A(X) = ∑_i A_i X A_i^†`) has a unique
  eigenvalue of magnitude equal to its spectral radius which is equal to one.

Clause (ii) is encoded by an explicit spectral-radius-one field together with
`_root_.IsPrimitive (Kraus.transferMap A)`, which states that the eigenvalues of norm
one form exactly `{1}`.  The explicit field is essential: unit-circle
uniqueness alone does not exclude eigenvalues of norm greater than one.

This predicate does not require left-canonical normalization.
-/
structure IsNormalTensor {α : Type u} {β : Type v} [Fintype α] [Fintype β] [DecidableEq β]
    (A : MPTensor α β) : Prop where
  /-- (i) no nontrivial invariant orthogonal projection. -/
  no_invariant_proj : Kraus.IsIrreducibleFamily A
  /-- (ii-a) the associated CPM has spectral radius one, as required after the
  rescaling of arXiv:1606.00608, lines 224--225 and 233--235. -/
  spectral_radius_one :
    spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix β β ℂ)) (Kraus.transferMap A)) = 1
  /-- (ii-b) the associated CPM has no unit-modulus eigenvalue other than one. -/
  primitive_transfer : _root_.IsPrimitive (Kraus.transferMap A)

/-- A normal tensor has nonzero bond dimension.

Indeed, at bond dimension zero the matrix space, and hence its continuous
endomorphism algebra, is subsingleton. The transfer operator is therefore zero
and has spectral radius zero, contradicting the spectral-radius-one clause in
arXiv:1606.00608, lines 233--235. -/
theorem IsNormalTensor.bondDim_ne_zero {α : Type u} [Fintype α] {D : ℕ}
    {A : MPTensor α (Fin D)} (h : IsNormalTensor A) : D ≠ 0 :=
  matrix_dim_ne_zero_of_spectralRadius_eq_one
    ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) (Kraus.transferMap A))
    h.spectral_radius_one

/-! ## Retained-block reconstruction and CPSV canonical form (CF) -/

/-- Common exact reconstruction of a tensor from nonzero weighted blocks in
coisometrically embedded coordinates. The canonical-form conventions below
specify separately whether an unused ambient complement is permitted.

Source: arXiv:1606.00608, eq. `II_CF1`, lines 214--245, and
arXiv:1703.09188, canonical form, lines 259--265. -/
structure RetainedBlockReconstructionData {α : Type u} {D : ℕ} (A : MPTensor α (Fin D)) where
  /-- Number of retained blocks (CPSV16, eq. `II_CF1`; CPSV17, lines 259--265). -/
  r : ℕ
  /-- Bond dimension of each retained block (CPSV16, eq. `II_CF1`;
  CPSV17, lines 259--265). -/
  dim : Fin r → ℕ
  /-- Every retained block has positive bond dimension (CPSV16, lines 219--225;
  CPSV17, lines 259--265). -/
  dim_pos : ∀ k, 0 < dim k
  /-- Scalar weight of each retained block (CPSV16, eq. `II_CF1`;
  CPSV17, lines 259--265). -/
  weights : Fin r → ℂ
  /-- **Local fix (nonzero coefficients):** Every retained block contributes
  nontrivially. CPSV16, lines 224--225,
  normalize the transfer map of each weighted block, so its weight cannot
  vanish. In CPSV17, the same convention excludes listed blocks that contribute
  nothing at any length. See
  `docs/paper-gaps/cpsv16_bnt_uniqueness_zero_coefficient.tex` and
  `docs/paper-gaps/mpu_canonical_form_nonzero_weights.tex`. -/
  weights_ne_zero : ∀ k, weights k ≠ 0
  /-- The retained blocks (CPSV16, eq. `II_CF1`; CPSV17, lines 259--265). -/
  blocks : (k : Fin r) → MPTensor α (Fin (dim k))
  /-- Coisometric inclusion of retained coordinates into the ambient space
  (CPSV16, lines 219--225; CPSV17, lines 259--265). -/
  ambient_coisometry : Matrix (Fin (∑ k : Fin r, dim k)) (Fin D) ℂ
  /-- The retained coordinates embed coisometrically (CPSV16, lines 219--225;
  CPSV17, lines 259--265). -/
  coisometric : ambient_coisometry * ambient_coisometryᴴ = 1
  /-- Exact reconstruction from the weighted retained blocks (CPSV16, eq. `II_CF1`;
  CPSV17, lines 259--265). -/
  reconstruct : ∀ i,
    A i = ambient_coisometryᴴ * toTensorFromBlocks weights blocks i *
      ambient_coisometry

/-- Witness data for the literal CPSV canonical form of `A`.

This is arXiv:1606.00608, Section 2.3, lines 214--245 and eq. `II_CF1`.
The retained weighted direct sum occupies a coisometrically embedded subspace
of the original bond space.  Its orthogonal complement consists literally of
the omitted zero coordinates. -/
structure CPSVCanonicalFormData {α : Type u} [Fintype α] {D : ℕ} (A : MPTensor α (Fin D))
    extends RetainedBlockReconstructionData A where
  /-- Every retained block is normal (CPSV16, lines 233--245 and eq. `II_CF1`). -/
  blocks_normal : ∀ k, IsNormalTensor (blocks k)
  /-- The retained direct sum fits inside the original bond space (CPSV16, lines 219--225). -/
  total_dim_le : ∑ k : Fin r, dim k ≤ D

/-- A tensor is in literal CPSV canonical form when it has an exact retained-block
reconstruction in its ambient bond space.

Source: arXiv:1606.00608, Section 2.3, lines 214--245 and eq. `II_CF1`. -/
def IsCPSVCanonicalForm {α : Type u} [Fintype α] {D : ℕ} (A : MPTensor α (Fin D)) : Prop :=
  Nonempty (CPSVCanonicalFormData A)

/-- Witness data determine the corresponding CPSV canonical-form predicate. -/
theorem CPSVCanonicalFormData.isCPSVCanonicalForm {α : Type u} [Fintype α] {D : ℕ}
    {A : MPTensor α (Fin D)} (data : CPSVCanonicalFormData A) : IsCPSVCanonicalForm A :=
  ⟨data⟩

/-- Choose retained-block witness data from a CPSV canonical-form predicate. -/
noncomputable def IsCPSVCanonicalForm.data {α : Type u} [Fintype α] {D : ℕ}
    {A : MPTensor α (Fin D)} (h : IsCPSVCanonicalForm A) : CPSVCanonicalFormData A :=
  Classical.choice h

end MPTensor

namespace MPSTensor

variable {d D : ℕ} {A : MPSTensor d D}

/-- Every tensor of bond dimension one is irreducible: the only orthogonal
projections on its one-dimensional bond space are zero and the identity. -/
theorem isIrreducibleFamily_of_bondDim_one {α : Type*} (A : MPTensor α (Fin 1)) :
    Kraus.IsIrreducibleFamily A := by
  rintro ⟨P, ⟨_, hIdem⟩, hP0, hP1, _⟩
  have h00 := congrFun (congrFun hIdem (0 : Fin 1)) (0 : Fin 1)
  simp only [Matrix.mul_apply, Finset.univ_unique, Fin.default_eq_zero,
    Fin.isValue, Finset.sum_singleton] at h00
  have hfactor : P 0 0 * (P 0 0 - 1) = 0 := by
    linear_combination h00
  rcases mul_eq_zero.mp hfactor with hzero | hone
  · apply hP0
    ext x y
    fin_cases x
    fin_cases y
    simpa using hzero
  · apply hP1
    ext x y
    fin_cases x
    fin_cases y
    simpa using sub_eq_zero.mp hone

/-- A bond-dimension-one tensor whose transfer map is the identity is a normal
tensor. -/
theorem isNormalTensor_of_bondDim_one_of_transferMap_eq_id {α : Type*} [Fintype α]
    (A : MPTensor α (Fin 1)) (hA : Kraus.transferMap A = LinearMap.id) :
    IsNormalTensor A := by
  refine ⟨isIrreducibleFamily_of_bondDim_one A, ?_, ?_⟩
  · rw [hA]
    change spectralRadius ℂ
      (1 : Matrix (Fin 1) (Fin 1) ℂ →L[ℂ] Matrix (Fin 1) (Fin 1) ℂ) = 1
    exact spectrum.spectralRadius_one
  · rw [hA]
    apply isPrimitive_of_unique_norm_one LinearMap.id
      (1 : Matrix (Fin 1) (Fin 1) ℂ)
    · rfl
    · exact one_ne_zero
    · intro μ hμ _hμnorm
      obtain ⟨X, hX⟩ := hμ.exists_hasEigenvector
      have hEq := hX.apply_eq_smul
      have hX00 : X 0 0 ≠ 0 := by
        intro hzero
        apply hX.2
        ext x y
        fin_cases x
        fin_cases y
        simpa using hzero
      have hEq00 := congrFun (congrFun hEq (0 : Fin 1)) (0 : Fin 1)
      simp only [LinearMap.id_apply, Matrix.smul_apply, smul_eq_mul] at hEq00
      apply mul_right_cancel₀ hX00
      simpa using hEq00.symm

section CPSVCanonicalFormData

/-- The weighted direct sum of positive-dimensional normal blocks is in literal
CPSV canonical form, with the retained coordinates equal to the ambient
coordinates.

Source: arXiv:1606.00608, eq. `II_CF1`, lines 237--244. -/
noncomputable def _root_.MPTensor.CPSVCanonicalFormData.ofBlocks {r : ℕ} {dim : Fin r → ℕ}
    (dim_pos : ∀ k, 0 < dim k) (weights : Fin r → ℂ)
    (weights_ne_zero : ∀ k, weights k ≠ 0)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (blocks_normal : ∀ k, IsNormalTensor (blocks k)) :
    CPSVCanonicalFormData (toTensorFromBlocks (α := Fin d) weights blocks) where
  r := r
  dim := dim
  dim_pos := dim_pos
  weights := weights
  weights_ne_zero := weights_ne_zero
  blocks := blocks
  blocks_normal := blocks_normal
  total_dim_le := le_rfl
  ambient_coisometry := 1
  coisometric := by simp
  reconstruct := by simp

/-- Literal CPSV canonical-form data reconstruct the same positive-length MPV
family as their retained weighted direct sum.

Source: arXiv:1606.00608, eq. `II_CF1`, lines 237--244. -/
theorem _root_.MPTensor.CPSVCanonicalFormData.sameMPV₂Pos_toTensorFromBlocks
    (data : CPSVCanonicalFormData A) :
    SameMPV₂Pos A (toTensorFromBlocks (α := Fin d) data.weights data.blocks) :=
  sameMPV₂Pos_of_coisometry_reconstruction A
    (toTensorFromBlocks (α := Fin d) data.weights data.blocks)
    data.ambient_coisometry data.coisometric data.reconstruct

/-- The closed-chain coefficients of a CPSV canonical-form tensor are the
sum of the block coefficients weighted by the corresponding powers.

Source: arXiv:1606.00608, eq. `II_Psi_k`, lines 259--263. -/
theorem _root_.MPTensor.CPSVCanonicalFormData.mpv_eq_sum_weight_pow (data : CPSVCanonicalFormData A)
    {N : ℕ} (hN : 0 < N) (σ : Fin N → Fin d) :
    mpv A σ =
      ∑ k : Fin data.r, data.weights k ^ N * mpv (data.blocks k) σ := by
  rw [data.sameMPV₂Pos_toTensorFromBlocks N hN σ]
  simpa [smul_eq_mul] using
    mpv_toTensorFromBlocks_eq_sum data.weights data.blocks σ

/-- CPSV16 line 246's weight convention, separated from literal canonical-form
membership.  The unit weight is required exactly when the ambient tensor is
nonzero.

Source: arXiv:1606.00608, Section 2.3, line 246. -/
structure _root_.MPTensor.CPSVCanonicalFormData.IsWeightNormalized
    (data : CPSVCanonicalFormData A) : Prop where
  /-- Every retained weight has modulus at most one (CPSV16, line 246). -/
  weight_norm_le_one : ∀ k, ‖data.weights k‖ ≤ 1
  /-- A nonzero ambient tensor has a retained unit-modulus weight (CPSV16, line 246). -/
  weight_unit_exists : A ≠ 0 → ∃ k, ‖data.weights k‖ = 1

end CPSVCanonicalFormData

/-! ## CPSV canonical form II (CFII) -/

/-- Witness data for literal CPSV canonical form II.

This is arXiv:1606.00608, Appendix A, lines 1054--1077.  It extends the exact
ambient reconstruction in `CPSVCanonicalFormData` by the two blockwise
normalization conditions: left-canonical form and a diagonal positive-definite
fixed point of the transfer map. -/
structure CPSVCanonicalFormIIData {α : Type*} [Fintype α] (A : MPTensor α (Fin D))
    extends CPSVCanonicalFormData A where
  /-- Every retained block is left-canonical (CPSV16, Appendix A, eq. `TP`). -/
  blocks_left_canonical : ∀ k, IsLeftCanonical (blocks k)
  /-- Every block has diagonal positive-definite fixed-point data (CPSV16,
  Appendix A, eq. `Lambda`). -/
  blocks_fixed_point :
    ∀ k, ∃ Λ : Matrix (Fin (dim k)) (Fin (dim k)) ℂ,
      Λ.PosDef ∧ Λ.IsDiag ∧ Kraus.transferMap (blocks k) Λ = Λ

/-- A tensor is in literal CPSV canonical form II when it admits exactly
reconstructed, blockwise normalized retained-block data.

Source: arXiv:1606.00608, Appendix A, lines 1054--1077. -/
def IsCPSVCanonicalFormII {α : Type*} [Fintype α] (A : MPTensor α (Fin D)) : Prop :=
  Nonempty (CPSVCanonicalFormIIData A)

namespace CPSVCanonicalFormIIData

/-- Canonical-form-II witness data determine the corresponding predicate. -/
theorem isCPSVCanonicalFormII {α : Type*} [Fintype α] {A : MPTensor α (Fin D)}
    (data : CPSVCanonicalFormIIData A) : IsCPSVCanonicalFormII A :=
  ⟨data⟩

end CPSVCanonicalFormIIData

namespace IsCPSVCanonicalFormII

/-- Choose normalized retained-block data from a canonical-form-II predicate. -/
noncomputable def data {α : Type*} [Fintype α] {A : MPTensor α (Fin D)}
    (h : IsCPSVCanonicalFormII A) : CPSVCanonicalFormIIData A :=
  Classical.choice h

end IsCPSVCanonicalFormII

/-! ## Basis of normal tensors (BNT) -/

/--
`MPSTensor.IsCPSVBasisOfNormalTensors A blocks` is the **basis of normal tensors** predicate
from arXiv:1606.00608 (`Papers/1606.00608/MPDO-22-12-17-2.tex:271-274`):

* (i) each `blocks j` is a CPSV16 normal tensor,
* (ii) for each positive system length `N`, the MPV family of `A` is in the linear span of
      the MPV families `{V^{(N)}(blocks j)}_j`, and
* (iii) there is some `N₀` such that for all `N > N₀`, the MPV states
      `mpvState (blocks j) N` are linearly independent.

Here `blocks` is a family `(j : Fin g) → Σ Dj, MPTensor α (Fin Dj)`, allowing
different bond dimensions for different blocks, over any finite physical alphabet `α`.
-/
structure IsCPSVBasisOfNormalTensors {α : Type*} [Fintype α] {g : ℕ} (A : MPTensor α (Fin D))
    (blocks : (j : Fin g) → Σ Dj : ℕ, MPTensor α (Fin Dj)) : Prop where
  /-- (i) each basis tensor `A_j` is a CPSV16 normal tensor. -/
  blocks_normal : ∀ j, IsNormalTensor (blocks j).2
  /-- (ii) at every positive length `N`, the MPV family of `A` is a linear combination of
  the per-block MPV families. -/
  spans_mpv : ∀ N : ℕ, 0 < N → ∃ c : Fin g → ℂ,
    ∀ σ : Fin N → α, mpv A σ = ∑ j : Fin g, c j * mpv (blocks j).2 σ
  /-- (iii) eventually, the MPV states of the basis are linearly independent. -/
  eventually_li : ∃ N₀ : ℕ, ∀ N > N₀,
    LinearIndependent ℂ (fun j : Fin g => mpvState (blocks j).2 N)

/-- Every tensor in a basis of normal tensors has positive bond dimension, since a normal tensor
has transfer spectral radius one.

Source: arXiv:1606.00608, lines 233--235 and 271--274. -/
theorem IsCPSVBasisOfNormalTensors.blocks_dim_pos
    {α : Type*} [Fintype α] {g : ℕ} {dim : Fin g → ℕ}
    {A : MPTensor α (Fin D)} {B : (j : Fin g) → MPTensor α (Fin (dim j))}
    (hBNT : IsCPSVBasisOfNormalTensors A (fun j => ⟨dim j, B j⟩)) :
    ∀ j, 0 < dim j :=
  fun j => Nat.pos_of_ne_zero (hBNT.blocks_normal j).bondDim_ne_zero

end MPSTensor

end

section

open scoped Matrix BigOperators ComplexOrder Kraus

namespace MPSTensor

variable {d D : ℕ}

/-- A normal left-canonical tensor with a diagonal positive fixed matrix is
already in one-block canonical form II in its given bond coordinates.

Source: arXiv:1606.00608, Appendix A, lines 1054–1077. -/
noncomputable def CPSVCanonicalFormIIData.ofNormalLeftCanonical {α : Type*} [Fintype α]
    {A : MPTensor α (Fin D)}
    (hNormal : MPTensor.IsNormalTensor A)
    (hLeft : MPTensor.IsLeftCanonical A)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρpd : ρ.PosDef) (hρdiag : ρ.IsDiag)
    (hρfix : Kraus.transferMap A ρ = ρ) :
    MPSTensor.CPSVCanonicalFormIIData A := by
  have : NeZero D := ⟨hNormal.bondDim_ne_zero⟩
  classical
  refine {
    r := 1
    dim := fun _ => D
    dim_pos := fun _ => NeZero.pos D
    weights := fun _ => 1
    weights_ne_zero := fun _ => one_ne_zero
    blocks := fun _ => A
    blocks_normal := fun _ => hNormal
    total_dim_le := by simp
    ambient_coisometry := MPSTensor.blockInclusion (fun _ : Fin 1 => D) 0
    coisometric := ?_
    reconstruct := ?_
    blocks_left_canonical := fun _ => hLeft
    blocks_fixed_point := fun _ => ⟨ρ, hρpd, hρdiag, hρfix⟩ }
  · let V : Matrix (Fin (∑ _ : Fin 1, D)) (Fin D) ℂ :=
      MPSTensor.blockInclusion (fun _ : Fin 1 => D) 0
    have hV : (Vᴴ * V : Matrix (Fin D) (Fin D) ℂ) = 1 :=
      MPSTensor.blockInclusion_conjTranspose_mul_self _ _
    have hcard : Fintype.card (Fin D) = Fintype.card (Fin (∑ _ : Fin 1, D)) := by simp
    exact (Matrix.mul_eq_one_comm_of_card_eq _ _ ℂ
      (A := (Vᴴ : Matrix (Fin D) (Fin (∑ _ : Fin 1, D)) ℂ))
      (B := V) hcard).mp hV
  · intro i
    let V : Matrix (Fin (∑ _ : Fin 1, D)) (Fin D) ℂ :=
      MPSTensor.blockInclusion (fun _ : Fin 1 => D) 0
    have hV : (Vᴴ * V : Matrix (Fin D) (Fin D) ℂ) = 1 :=
      MPSTensor.blockInclusion_conjTranspose_mul_self _ _
    have hmul := MPSTensor.toTensorFromBlocks_mul_blockInclusion
      (fun _ : Fin 1 => (1 : ℂ)) (fun _ : Fin 1 => A) 0 i
    have hmul' : MPTensor.toTensorFromBlocks (fun _ : Fin 1 => (1 : ℂ))
        (fun _ : Fin 1 => A) i * V = V * A i := by
      simpa only [one_smul] using hmul
    calc
      A i = (Vᴴ * V) * A i := by rw [hV, Matrix.one_mul]
      _ = Vᴴ * (MPTensor.toTensorFromBlocks
            (fun _ : Fin 1 => (1 : ℂ)) (fun _ : Fin 1 => A) i * V) := by
              rw [hmul', Matrix.mul_assoc]
      _ = (Vᴴ * MPTensor.toTensorFromBlocks (fun _ : Fin 1 => (1 : ℂ))
            (fun _ : Fin 1 => A) i) * V :=
              (Matrix.mul_assoc Vᴴ _ V).symm

end MPSTensor

end
