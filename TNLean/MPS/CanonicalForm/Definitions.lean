/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.Reduction
import TNLean.MPS.Core.Transfer
import TNLean.MPS.Overlap.Basic
import TNLean.MPS.SharedInfra.BlockAssembly
import TNLean.Channel.Peripheral.Spectrum

/-!
# Normal tensor, canonical form, and basis of normal tensors (CPSV16)

This module records the definitions of the three central notions
from arXiv:1606.00608 (Cirac–Pérez-García–Schuch–Verstraete, "Matrix product density
operators: Renormalization fixed points and boundary theories"):

* normal tensor (NT), `MPSTensor.IsNormalTensor`,
* canonical form (CF), `MPSTensor.IsCPSVCanonicalForm`, and
* basis of normal tensors (BNT), `MPSTensor.IsCPSVBasisOfNormalTensors`.

The existing TNLean canonical-form layer (`TNLean.PiAlgebra.CanonicalFormSepAux`,
`TNLean.MPS.BNT.Construction`) ships several *strengthenings* of these definitions
(adding left-canonical normalization, strict modulus ordering, one-copy-per-sector,
etc.) that are convenient for downstream FT proofs but drift from the paper text.
The predicates here are the CPSV formulations.

## Paper anchors

* `MPSTensor.IsNormalTensor`: `Papers/1606.00608/MPDO-22-12-17-2.tex:233-235`
  (Definition: NT is no nontrivial invariant projector + unique modulus-1
  eigenvalue of the associated CPM equal to its spectral radius equal to one).
* `MPSTensor.IsCPSVCanonicalForm`: `Papers/1606.00608/MPDO-22-12-17-2.tex:237-246`
  (Definition: CF is `A^i = ⊕_k μ_k A_k^i` with each `A_k` normal; combined with
  the normalization paragraph at line 246: `|μ_k| ≤ 1` and at least one `|μ_k| = 1`).
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

One direct connection is provided:

* `MPSTensor.IsNormalTensor.of_irreducible_and_primitive` —
  package an `IsIrreducibleTensor` proof with a primitive-transfer-map proof.

Two further connections are intentionally **not** provided here, in keeping with the
"clean layer, no `sorry`" quality bar:

* A CF connection `IsCPSVCanonicalForm.of_isNormalCanonicalForm` would need to import
  `TNLean.PiAlgebra.CanonicalFormSepAux` which transitively imports
  `TNLean.MPS.FundamentalTheorem.*`; we keep `Definitions.lean` in a clean pre-FT
  layer. Such a connection belongs in a separate downstream file.
* A BNT connection `IsCPSVBasisOfNormalTensors.of_isBNT` would require the implication
  `MPSTensor.IsNormal → IsNormalTensor` per block, i.e. from algebraic eventual
  block injectivity to the CPSV16 (no-invariant-proj + primitive-transfer)
  formulation. That equivalence requires Wielandt-style spectral arguments not
  packaged at this layer.

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

/-- An irreducible tensor whose transfer map is primitive is a CPSV16 normal tensor. -/
theorem IsNormalTensor.of_irreducible_and_primitive
    {A : MPSTensor d D}
    (hIrr : IsIrreducibleTensor A)
    (hPrim : _root_.IsPrimitive (transferMap (d := d) (D := D) A)) :
    IsNormalTensor A :=
  { no_invariant_proj := hIrr
    primitive_transfer := hPrim }

/-! ## Canonical form (CF) -/

/--
`MPSTensor.CPSVCanonicalFormData A` is the data of a canonical-form
decomposition of `A` from arXiv:1606.00608 eq. `II_CF1` plus the normalization paragraph
immediately following (`Papers/1606.00608/MPDO-22-12-17-2.tex:237-246`):

* a number `r` of blocks,
* per-block bond dimensions `dim k`,
* per-block weights `weights k : ℂ`,
* per-block tensors `blocks k : MPSTensor d (dim k)`, each normal,
* an MPV-equality witness `A^i = ⊕_k weights k • blocks k^i` (encoded as
  `SameMPV₂ A (toTensorFromBlocks weights blocks)`),
* modulus normalization `‖weights k‖ ≤ 1` for all `k`, and at least one `‖weights k‖ = 1`.

This is **data** (a `Type`); the propositional version is `IsCPSVCanonicalForm` below.
-/
structure CPSVCanonicalFormData (A : MPSTensor d D) where
  /-- Number of blocks `r` in the direct-sum decomposition `A^i = ⊕_{k=1}^r μ_k A_k^i`. -/
  r : ℕ
  /-- Bond dimensions of the blocks `dim k = D_k`. -/
  dim : Fin r → ℕ
  /-- Block weights `μ k` of the decomposition. -/
  weights : Fin r → ℂ
  /-- Per-block MPS tensors `A_k`. -/
  blocks : (k : Fin r) → MPSTensor d (dim k)
  /-- `A` and the direct sum `⊕_k μ_k A_k` have the same MPV family at every length. -/
  sameMPV : SameMPV₂ A (toTensorFromBlocks (d := d) weights blocks)
  /-- Each block `A_k` is a CPSV16 normal tensor. -/
  blocks_normal : ∀ k, IsNormalTensor (blocks k)
  /-- Modulus normalization (`MPDO-22-12-17-2.tex:246`): every weight has modulus at most one. -/
  weight_norm_le_one : ∀ k, ‖weights k‖ ≤ 1
  /-- Modulus normalization (`MPDO-22-12-17-2.tex:246`): at least one weight has unit modulus. -/
  weight_unit_exists : ∃ k, ‖weights k‖ = 1

/--
`MPSTensor.IsCPSVCanonicalForm A` is the propositional **canonical form**
predicate from arXiv:1606.00608
(`Papers/1606.00608/MPDO-22-12-17-2.tex:237-246`): `A` admits a normal-block
direct-sum decomposition with weights normalized to `|μ_k| ≤ 1` and at least one
`|μ_k| = 1`.

This is `Nonempty (CPSVCanonicalFormData A)` — i.e. existence of a CPSV canonical-form
decomposition witness.
-/
def IsCPSVCanonicalForm (A : MPSTensor d D) : Prop :=
  Nonempty (CPSVCanonicalFormData A)

/-- Promote a CPSV canonical-form data witness to the propositional predicate. -/
theorem IsCPSVCanonicalForm.of_data
    {A : MPSTensor d D} (h : CPSVCanonicalFormData A) :
    IsCPSVCanonicalForm A :=
  ⟨h⟩

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
