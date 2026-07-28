/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.Reduction
import TNLean.MPS.Core.CanonicalNormalization
import TNLean.MPS.Core.Transfer
import TNLean.MPS.Overlap.Basic
import TNLean.MPS.SharedInfra.BlockAssembly
import TNLean.Channel.Peripheral.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.IsDiag

/-!
# CPSV canonical forms and normal tensors

This module records four central notions
from arXiv:1606.00608 (Cirac–Pérez-García–Schuch–Verstraete, "Matrix product density
operators: Renormalization fixed points and boundary theories"):

* normal tensor (NT), `MPSTensor.IsNormalTensor`,
* canonical form (CF), `MPSTensor.IsCPSVCanonicalForm`,
* canonical form II (CFII), `MPSTensor.IsCPSVCanonicalFormII`, and
* basis of normal tensors (BNT), `MPSTensor.IsCPSVBasisOfNormalTensors`.

The literal canonical-form (CF) decomposition of arXiv:1606.00608 eq. `II_CF1`
is recorded by `MPSTensor.CPSVCanonicalFormData` and
`MPSTensor.IsCPSVCanonicalForm`.  A coisometry embeds the retained weighted
direct sum into the original bond space, whose remaining coordinates are zero.
The line-246 normalization convention is the separate predicate
`MPSTensor.CPSVCanonicalFormData.IsWeightNormalized`; it is not part of literal
CF membership.  None of these definitions adds weight ordering or BNT
separation.

The existing canonical-form layer (`TNLean.PiAlgebra.CanonicalFormSepAux`,
`TNLean.MPS.BNT.Construction`) contains several strengthenings of these definitions
(left-canonical normalization and a basis of gauge-phase-distinct representatives).
The predicates in this file are the CPSV formulations.

## Paper anchors

* `MPSTensor.IsNormalTensor`: `Papers/1606.00608/MPDO-22-12-17-2.tex:233-235`
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

The separate module `TNLean.MPS.BNT.Bridge` provides the source-faithful one-way
implication `IsCPSVBasisOfNormalTensors.isBNT`, using the proved implication
`IsNormalTensor.isNormal` on each positive-dimensional block.  The converse is
intentionally absent: algebraic eventual block injectivity does not by itself
supply the spectral-radius-one normalization and peripheral-spectrum data stored
by `IsNormalTensor`.

## Style

Follows `docs/MATHLIB_style.md` and `docs/MATHLIB_naming.md`.
-/

open scoped Matrix BigOperators Matrix.Norms.Operator ComplexOrder MatrixOrder

namespace MPSTensor

variable {d D : ℕ}

/-! ## Normal tensor (NT) -/

/--
`MPSTensor.IsNormalTensor A` is the **normal tensor** predicate from
arXiv:1606.00608, Definition before eq. `II_CF1` (`Papers/1606.00608/MPDO-22-12-17-2.tex:233-235`):

* (i) `A` admits no nontrivial invariant orthogonal projection, and
* (ii) the associated CPM (the transfer map `E_A(X) = ∑_i A_i X A_i^†`) has a unique
  eigenvalue of magnitude equal to its spectral radius which is equal to one.

Clause (ii) is encoded by an explicit spectral-radius-one field together with
`_root_.IsPrimitive (transferMap A)`, which states that the eigenvalues of norm
one form exactly `{1}`.  The explicit field is essential: unit-circle
uniqueness alone does not exclude eigenvalues of norm greater than one.

This predicate is intentionally *weaker* than the TNLean strong predicate
`MPSTensor.IsCanonicalFormSepAux.IsNormalCanonicalForm` (it does not require
left-canonical normalization or weight ordering).
-/
structure IsNormalTensor (A : MPSTensor d D) : Prop where
  /-- (i) no nontrivial invariant orthogonal projection. -/
  no_invariant_proj : IsIrreducibleTensor A
  /-- (ii-a) the associated CPM has spectral radius one, as required after the
  rescaling of arXiv:1606.00608, lines 224--225 and 233--235. -/
  spectral_radius_one :
    spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
        (transferMap (d := d) (D := D) A)) = 1
  /-- (ii-b) the associated CPM has no unit-modulus eigenvalue other than one. -/
  primitive_transfer : _root_.IsPrimitive (transferMap (d := d) (D := D) A)

/-- A normal tensor has nonzero bond dimension.

Indeed, at bond dimension zero the matrix space, and hence its continuous
endomorphism algebra, is subsingleton. The transfer operator is therefore zero
and has spectral radius zero, contradicting the spectral-radius-one clause in
arXiv:1606.00608, lines 233--235. -/
theorem IsNormalTensor.bondDim_ne_zero {A : MPSTensor d D} (h : IsNormalTensor A) :
    D ≠ 0 := by
  intro hD
  subst D
  have hMap :
      ((Module.End.toContinuousLinearMap (Matrix (Fin 0) (Fin 0) ℂ))
        (transferMap (d := d) (D := 0) A)) = 0 :=
    Subsingleton.elim _ _
  have hspectral := h.spectral_radius_one
  rw [hMap, spectrum.spectralRadius_zero] at hspectral
  exact zero_ne_one hspectral

/-- Every tensor of bond dimension one is irreducible: the only orthogonal
projections on its one-dimensional bond space are zero and the identity. -/
theorem isIrreducibleTensor_of_bondDim_one (A : MPSTensor d 1) :
    IsIrreducibleTensor A := by
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
theorem isNormalTensor_of_bondDim_one_of_transferMap_eq_id
    (A : MPSTensor d 1) (hA : transferMap A = LinearMap.id) :
    IsNormalTensor A := by
  refine ⟨isIrreducibleTensor_of_bondDim_one A, ?_, ?_⟩
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

/-! ## CPSV canonical form (CF) -/

/-- Witness data for the literal CPSV canonical form of `A`.

This is arXiv:1606.00608, Section 2.3, lines 214--245 and eq. `II_CF1`.
The retained weighted direct sum occupies a coisometrically embedded subspace
of the original bond space.  Its orthogonal complement consists literally of
the omitted zero coordinates. -/
structure CPSVCanonicalFormData (A : MPSTensor d D) where
  /-- Number of retained normal blocks (CPSV16, lines 214--225). -/
  r : ℕ
  /-- Bond dimension of each retained block (CPSV16, lines 219--225). -/
  dim : Fin r → ℕ
  /-- Every retained block has positive bond dimension (CPSV16, lines 219--225). -/
  dim_pos : ∀ k, 0 < dim k
  /-- Scalar weight of each retained block (CPSV16, eq. `II_Aiplusk1`). -/
  weights : Fin r → ℂ
  /-- Retained normal blocks (CPSV16, eq. `II_CF1`). -/
  blocks : (k : Fin r) → MPSTensor d (dim k)
  /-- Every retained block is normal (CPSV16, lines 233--245 and eq. `II_CF1`). -/
  blocks_normal : ∀ k, IsNormalTensor (blocks k)
  /-- The retained direct sum fits inside the original bond space (CPSV16, lines 219--225). -/
  total_dim_le : ∑ k : Fin r, dim k ≤ D
  /-- Coisometric inclusion implementing the zero ambient coordinates of CPSV16, lines 219--225. -/
  ambient_coisometry : Matrix (Fin (∑ k : Fin r, dim k)) (Fin D) ℂ
  /-- The retained coordinates embed coisometrically (CPSV16, lines 214--225). -/
  coisometric : ambient_coisometry * ambient_coisometryᴴ = 1
  /-- Exact eq. `II_CF1` reconstruction, including the zero coordinates of
  CPSV16, lines 219--225. -/
  reconstruct : ∀ i,
    A i = ambient_coisometryᴴ * toTensorFromBlocks (d := d) weights blocks i *
      ambient_coisometry

/-- A tensor is in literal CPSV canonical form when it has an exact retained-block
reconstruction in its ambient bond space.

Source: arXiv:1606.00608, Section 2.3, lines 214--245 and eq. `II_CF1`. -/
def IsCPSVCanonicalForm (A : MPSTensor d D) : Prop :=
  Nonempty (CPSVCanonicalFormData A)

namespace CPSVCanonicalFormData

/-- The weighted direct sum of positive-dimensional normal blocks is in literal
CPSV canonical form, with the retained coordinates equal to the ambient
coordinates.

Source: arXiv:1606.00608, eq. `II_CF1`, lines 237--244. -/
noncomputable def ofBlocks {r : ℕ} {dim : Fin r → ℕ}
    (dim_pos : ∀ k, 0 < dim k) (weights : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (blocks_normal : ∀ k, IsNormalTensor (blocks k)) :
    CPSVCanonicalFormData (toTensorFromBlocks (d := d) weights blocks) where
  r := r
  dim := dim
  dim_pos := dim_pos
  weights := weights
  blocks := blocks
  blocks_normal := blocks_normal
  total_dim_le := le_rfl
  ambient_coisometry := 1
  coisometric := by simp
  reconstruct := by simp

/-- Literal CPSV canonical-form data reconstruct the same positive-length MPV
family as their retained weighted direct sum.

Source: arXiv:1606.00608, eq. `II_CF1`, lines 237--244. -/
theorem sameMPV₂Pos_toTensorFromBlocks (data : CPSVCanonicalFormData A) :
    SameMPV₂Pos A (toTensorFromBlocks (d := d) data.weights data.blocks) :=
  sameMPV₂Pos_of_coisometry_reconstruction A
    (toTensorFromBlocks (d := d) data.weights data.blocks)
    data.ambient_coisometry data.coisometric data.reconstruct

/-- The closed-chain coefficients of a CPSV canonical-form tensor are the
sum of the block coefficients weighted by the corresponding powers.

Source: arXiv:1606.00608, eq. `II_Psi_k`, lines 259--263. -/
theorem mpv_eq_sum_weight_pow (data : CPSVCanonicalFormData A)
    {N : ℕ} (hN : 0 < N) (σ : Fin N → Fin d) :
    mpv A σ =
      ∑ k : Fin data.r, data.weights k ^ N * mpv (data.blocks k) σ := by
  rw [data.sameMPV₂Pos_toTensorFromBlocks N hN σ]
  simpa [smul_eq_mul] using
    mpv_toTensorFromBlocks_eq_sum data.weights data.blocks σ

/-- CPSV16 line 246's weight convention, separated from literal canonical-form
membership.  The unit weight is required exactly when the ambient tensor is
nonzero; no retained weight is required to be nonzero.

Source: arXiv:1606.00608, Section 2.3, line 246. -/
structure IsWeightNormalized (data : CPSVCanonicalFormData A) : Prop where
  /-- Every retained weight has modulus at most one (CPSV16, line 246). -/
  weight_norm_le_one : ∀ k, ‖data.weights k‖ ≤ 1
  /-- A nonzero ambient tensor has a retained unit-modulus weight (CPSV16, line 246). -/
  weight_unit_exists : A ≠ 0 → ∃ k, ‖data.weights k‖ = 1

/-- Witness data determine the corresponding CPSV canonical-form predicate. -/
theorem isCPSVCanonicalForm (data : CPSVCanonicalFormData A) :
    IsCPSVCanonicalForm A :=
  ⟨data⟩

end CPSVCanonicalFormData

namespace IsCPSVCanonicalForm

/-- Choose retained-block witness data from a CPSV canonical-form predicate. -/
noncomputable def data (h : IsCPSVCanonicalForm A) : CPSVCanonicalFormData A :=
  Classical.choice h

end IsCPSVCanonicalForm

/-! ## CPSV canonical form II (CFII) -/

/-- Witness data for literal CPSV canonical form II.

This is arXiv:1606.00608, Appendix A, lines 1054--1077.  It extends the exact
ambient reconstruction in `CPSVCanonicalFormData` by the two blockwise
normalization conditions: left-canonical form and a diagonal positive-definite
fixed point of the transfer map. -/
structure CPSVCanonicalFormIIData (A : MPSTensor d D) extends CPSVCanonicalFormData A where
  /-- Every retained block is left-canonical (CPSV16, Appendix A, eq. `TP`). -/
  blocks_left_canonical : ∀ k, IsLeftCanonical (blocks k)
  /-- Every block has diagonal positive-definite fixed-point data (CPSV16,
  Appendix A, eq. `Lambda`). -/
  blocks_fixed_point :
    ∀ k, ∃ Λ : Matrix (Fin (dim k)) (Fin (dim k)) ℂ,
      Λ.PosDef ∧ Λ.IsDiag ∧ transferMap (blocks k) Λ = Λ

/-- A tensor is in literal CPSV canonical form II when it admits exactly
reconstructed, blockwise normalized retained-block data.

Source: arXiv:1606.00608, Appendix A, lines 1054--1077. -/
def IsCPSVCanonicalFormII (A : MPSTensor d D) : Prop :=
  Nonempty (CPSVCanonicalFormIIData A)

namespace CPSVCanonicalFormIIData

/-- Canonical-form-II witness data determine the corresponding predicate. -/
theorem isCPSVCanonicalFormII (data : CPSVCanonicalFormIIData A) :
    IsCPSVCanonicalFormII A :=
  ⟨data⟩

/-- Forgetting the blockwise normalization leaves literal CPSV canonical-form data. -/
theorem isCPSVCanonicalForm (data : CPSVCanonicalFormIIData A) :
    IsCPSVCanonicalForm A :=
  data.toCPSVCanonicalFormData.isCPSVCanonicalForm

end CPSVCanonicalFormIIData

namespace IsCPSVCanonicalFormII

/-- Choose normalized retained-block data from a canonical-form-II predicate. -/
noncomputable def data (h : IsCPSVCanonicalFormII A) : CPSVCanonicalFormIIData A :=
  Classical.choice h

/-- Canonical form II is, in particular, literal CPSV canonical form. -/
theorem isCPSVCanonicalForm (h : IsCPSVCanonicalFormII A) : IsCPSVCanonicalForm A :=
  ⟨h.data.toCPSVCanonicalFormData⟩

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

Here `blocks` is a family `(j : Fin g) → Σ Dj, MPSTensor d Dj`, allowing
different bond dimensions for different blocks.
-/
structure IsCPSVBasisOfNormalTensors {g : ℕ} (A : MPSTensor d D)
    (blocks : (j : Fin g) → Σ Dj : ℕ, MPSTensor d Dj) : Prop where
  /-- (i) each basis tensor `A_j` is a CPSV16 normal tensor. -/
  blocks_normal : ∀ j, IsNormalTensor (blocks j).2
  /-- (ii) at every positive length `N`, the MPV family of `A` is a linear combination of
  the per-block MPV families. -/
  spans_mpv : ∀ N : ℕ, 0 < N → ∃ c : Fin g → ℂ,
    ∀ σ : Fin N → Fin d, mpv A σ = ∑ j : Fin g, c j * mpv (blocks j).2 σ
  /-- (iii) eventually, the MPV states of the basis are linearly independent. -/
  eventually_li : ∃ N₀ : ℕ, ∀ N > N₀,
    LinearIndependent ℂ (fun j : Fin g => mpvState (d := d) (blocks j).2 N)

end MPSTensor
