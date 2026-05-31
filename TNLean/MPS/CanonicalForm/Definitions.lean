/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.Reduction
import TNLean.MPS.Core.Transfer
import TNLean.MPS.Overlap.Basic
import TNLean.Channel.Peripheral.Spectrum

/-!
# Normal tensor and basis of normal tensors (CPSV16)

This module records the definitions of two of the central notions
from arXiv:1606.00608 (Cirac–Pérez-García–Schuch–Verstraete, "Matrix product density
operators: Renormalization fixed points and boundary theories"):

* normal tensor (NT), `MPSTensor.IsNormalTensor`, and
* basis of normal tensors (BNT), `MPSTensor.IsCPSVBasisOfNormalTensors`.

The canonical-form (CF) decomposition of arXiv:1606.00608 eq. `II_CF1` plus the
normalization paragraph (`Papers/1606.00608/MPDO-22-12-17-2.tex:237-246`) is not
introduced here as a separate predicate.  The later normal canonical form
predicate `MPSTensor.IsCanonicalFormSepAux.IsNormalCanonicalForm` records the
strengthened form used in the Fundamental Theorem: normal blocks together with
left-canonical normalization, strict nonzero weights, primitive transfer maps,
and positive block dimensions.  The global CPSV normalization
`‖μ k‖ ≤ 1` with a unit-modulus witness remains a separate source hypothesis
when it is needed.

The existing canonical-form layer (`TNLean.PiAlgebra.CanonicalFormSepAux`,
`TNLean.MPS.BNT.Construction`) contains several strengthenings of these definitions
(left-canonical normalization, strict modulus ordering, and one copy per sector).
The predicates in this file are the CPSV formulations.

## Paper anchors

* `MPSTensor.IsNormalTensor`: `Papers/1606.00608/MPDO-22-12-17-2.tex:233-235`
  (Definition: NT is no nontrivial invariant projector + unique modulus-1
  eigenvalue of the associated CPM equal to its spectral radius equal to one).
* `MPSTensor.IsCPSVBasisOfNormalTensors`: `Papers/1606.00608/MPDO-22-12-17-2.tex:271-274`
  (Definition: BNT `{A_j}` of `A` is `A_j` all normal, MPV family of `A`
  spanned by MPV families of the `A_j` at every length, and eventually linearly
  independent).

## Relation to the existing primitive-channel predicate

CPSV16's clause "the associated CPM has a unique eigenvalue of magnitude
equal to its spectral radius which is equal to one" is the standard
*primitive transfer map* condition. We reuse `_root_.IsPrimitive`
(`TNLean.Channel.Peripheral.Spectrum`), which states that the peripheral
eigenvalue set equals `{1}`. This matches the paper after the spectral-radius
normalization the paper assumes (cf. `MPDO-22-12-17-2.tex:231`, the block-then-
renormalize paragraph immediately preceding Definition NT).

The TN-Review formulation (`Papers/2011.12127/TN-Review-main.tex:1827-1830`)
"the transfer operator is a primitive channel" is the same clause and is not
duplicated.

## Connections to existing strong predicates

A connection is intentionally not provided here:

* A BNT connection `IsCPSVBasisOfNormalTensors.of_isBNT` would require the implication
  `MPSTensor.IsNormal → IsNormalTensor` per block, i.e. from algebraic eventual
  block injectivity to the CPSV16 (no-invariant-proj + primitive-transfer)
  formulation. That equivalence requires Wielandt-style spectral arguments not
  developed at this layer.

## Style

Follows `docs/MATHLIB_style.md` and `docs/MATHLIB_naming.md`.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-! ## Normal tensor (NT) -/

/--
`MPSTensor.IsNormalTensor A` is the **normal tensor** predicate from
arXiv:1606.00608, Definition before eq. `II_CF1` (`Papers/1606.00608/MPDO-22-12-17-2.tex:233-235`):

* (i) `A` admits no nontrivial invariant orthogonal projection, and
* (ii) the associated CPM (the transfer map `E_A(X) = ∑_i A_i X A_i^†`) has a unique
  eigenvalue of magnitude equal to its spectral radius which is equal to one.

Clause (ii) is encoded via `_root_.IsPrimitive (transferMap A)`, which states that the
peripheral eigenvalue set of the transfer map is exactly `{1}`. Combined with the
implicit spectral-radius normalization the paper assumes (cf. `MPDO-22-12-17-2.tex:231`),
this is the CPSV formulation.

This predicate is intentionally *weaker* than the TNLean strong predicate
`MPSTensor.IsCanonicalFormSepAux.IsNormalCanonicalForm` (it does not require
left-canonical normalization, weight ordering, or positive bond dimension).
-/
structure IsNormalTensor (A : MPSTensor d D) : Prop where
  /-- (i) no nontrivial invariant orthogonal projection. -/
  no_invariant_proj : IsIrreducibleTensor A
  /-- (ii) the associated CPM has a unique eigenvalue of magnitude equal to its
  spectral radius equal to one (primitive transfer map). -/
  primitive_transfer : _root_.IsPrimitive (transferMap (d := d) (D := D) A)

/-! ## Basis of normal tensors (BNT) -/

/--
`MPSTensor.IsCPSVBasisOfNormalTensors A blocks` is the **basis of normal tensors** predicate
from arXiv:1606.00608 (`Papers/1606.00608/MPDO-22-12-17-2.tex:271-274`):

* (i) each `blocks j` is a CPSV16 normal tensor,
* (ii) for each system length `N`, the MPV family of `A` is in the linear span of
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
  /-- (ii) at every length `N`, the MPV family of `A` is a linear combination of
  the per-block MPV families. -/
  spans_mpv : ∀ N : ℕ, ∃ c : Fin g → ℂ,
    ∀ σ : Fin N → Fin d, mpv A σ = ∑ j : Fin g, c j * mpv (blocks j).2 σ
  /-- (iii) eventually, the MPV states of the basis are linearly independent. -/
  eventually_li : ∃ N₀ : ℕ, ∀ N > N₀,
    LinearIndependent ℂ (fun j : Fin g => mpvState (d := d) (blocks j).2 N)

end MPSTensor
