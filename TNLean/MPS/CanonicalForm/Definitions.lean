/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.Reduction
import TNLean.MPS.Core.Transfer
import TNLean.MPS.Overlap.Basic
import TNLean.MPS.SharedInfra.BlockAssembly
import TNLean.Channel.Peripheral.Spectrum

/-!
# Normal tensor and basis of normal tensors (CPSV16)

This module records the definitions of two of the central notions
from arXiv:1606.00608 (Cirac–Pérez-García–Schuch–Verstraete, "Matrix product density
operators: Renormalization fixed points and boundary theories"):

* normal tensor (NT), `MPSTensor.IsNormalTensor`, and
* basis of normal tensors (BNT), `MPSTensor.IsCPSVBasisOfNormalTensors`.

The canonical-form (CF) decomposition of arXiv:1606.00608 eq. `II_CF1` and its
normalization paragraph (`Papers/1606.00608/MPDO-22-12-17-2.tex:237-246`) are
recorded by `MPSTensor.CPSVCanonicalFormData` and
`MPSTensor.IsCPSVCanonicalForm`.  This source-level predicate retains equality
of positive-length MPV families and allows the sum of the retained block bond
dimensions to be smaller than the original bond dimension.  It does not add
left-canonical normalization, weight ordering, or BNT separation.

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

open scoped Matrix BigOperators Matrix.Norms.Operator

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
left-canonical normalization, weight ordering, or positive bond dimension).
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

/-- Witness data for the CPSV canonical form of `A`.

This is arXiv:1606.00608, Section 2.3, lines 214--246: the positive-length MPV
family of `A` is represented by weighted normal blocks.  Blocks that contribute
only to the length-zero trace may be omitted, so the retained total bond
dimension is bounded above by `D` rather than required to equal it.  The empty
family represents the identically-zero positive-length MPV family; consequently
the unit-modulus normalization is conditional on `0 < r`. -/
structure CPSVCanonicalFormData (A : MPSTensor d D) where
  /-- Number of retained normal blocks. -/
  r : ℕ
  /-- Bond dimension of each retained block. -/
  dim : Fin r → ℕ
  /-- Scalar weight of each retained block. -/
  weights : Fin r → ℂ
  /-- Retained normal blocks. -/
  blocks : (k : Fin r) → MPSTensor d (dim k)
  /-- Every retained block is normal in the sense of CPSV16, lines 233--235. -/
  blocks_normal : ∀ k, IsNormalTensor (blocks k)
  /-- The weighted direct sum represents the same MPV family at every positive length. -/
  sameMPV_pos : SameMPV₂Pos A (toTensorFromBlocks (d := d) weights blocks)
  /-- Removing length-zero-only blocks cannot increase the total bond dimension. -/
  bondDim_le : ∑ k : Fin r, dim k ≤ D
  /-- CPSV16, line 246: all retained weights have modulus at most one. -/
  weight_norm_le_one : ∀ k, ‖weights k‖ ≤ 1
  /-- CPSV16, line 246, with the empty-family exception for the zero MPV family. -/
  weight_unit_exists : 0 < r → ∃ k, ‖weights k‖ = 1

/-- A tensor is in CPSV canonical form when it admits retained-block witness data.

Source: arXiv:1606.00608, Section 2.3, lines 214--246. -/
def IsCPSVCanonicalForm (A : MPSTensor d D) : Prop :=
  Nonempty (CPSVCanonicalFormData A)

namespace CPSVCanonicalFormData

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
