/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.KrausMap.KrausGauge
import TNLean.MPS.CanonicalForm.NormalBlocks.NormalTensorGauge
import TNLean.MPS.CanonicalForm.NormalBlocks.NormalityChain
import QICLean.Kraus.PrimitiveFixedPoint.Blocking

/-!
# Literal CPSV canonical forms under positive physical blocking

This module proves that CPSV normal tensors and literal CPSV canonical-form
data are preserved by blocking a positive number of physical sites.

The retained block dimensions and the ambient coisometry are unchanged.  Each
normal block is replaced by its physical block tensor and each CPSV weight is
raised to the blocking length.  The reconstruction is the exact blocked
letterwise reconstruction, not only equality of closed-chain coefficients.

## Main definitions

* `MPTensor.CPSVCanonicalFormData.block`: literal canonical-form data
  block exactly.
* `MPSTensor.CPSVCanonicalFormIIData.block`: blockwise canonical-form-II data block
  exactly.

## Main results

* `MPTensor.IsNormalTensor.block`: positive blocking preserves normal
  tensors.
* `MPTensor.IsCPSVCanonicalForm.block`: positive blocking preserves
  literal CPSV canonical form.
* `MPSTensor.exists_common_injective_blocking_of_tp_primitive_irr_family`: one positive
  blocking length makes every member of a finite trace-preserving, primitive,
  irreducible family one-site injective.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608, Section 2.3,
  lines 214--245 and eq. `II_CF1`.
-/

open MPTensor

open scoped Matrix BigOperators ComplexOrder MatrixOrder

namespace MPSTensor

variable {α : Type*} [Fintype α] {D : ℕ}

/-- Gauge equivalence is preserved by blocking the physical alphabet.

Source: arXiv:1606.00608, line 227 defines blocking by matrix products and
lines 264--268 give the invertible gauge relation. -/
theorem _root_.MPTensor.GaugeEquiv.block {A B : MPTensor α (Fin D)} (h : GaugeEquiv A B) (p : ℕ) :
    GaugeEquiv (Kraus.block A p)
      (Kraus.block B p) := by
  obtain ⟨X, hX⟩ := h
  refine ⟨X, fun i ↦ ?_⟩
  simpa [Kraus.block_apply, Matrix.GeneralLinearGroup.coe_inv] using
    evalWord_gauge (A := A) (B := B) X hX (List.ofFn i)

section IsNormalTensor

open MPTensor.IsNormalTensor

/-- Positive physical blocking preserves CPSV normal tensors.

The proof puts the tensor into its trace-preserving Perron gauge.  Positive
blocking preserves trace preservation, transfer-map primitivity, and tensor
irreducibility for that gauge; hence the blocked gauge is a normal tensor.  A
blocked gauge equivalence then transports the result back to the original
blocked tensor.

Source: arXiv:1606.00608, lines 227--235 define physical blocking and normal
tensors; the closure under reblocking is used in the normal-block arguments at
lines 332--345. -/
theorem _root_.MPTensor.IsNormalTensor.block {A : MPTensor α (Fin D)} (hA : IsNormalTensor A)
    (p : ℕ) (hp : 0 < p) :
    IsNormalTensor (Kraus.block A p) := by
  let : NeZero D := ⟨hA.bondDim_ne_zero⟩
  obtain ⟨σ, _hσpos, _hσfix, hTP, hGauge, hPrim, hIrr⟩ := hA.exists_tpGauge
  let B : MPTensor α (Fin D) := Kraus.tpGauge (ι := α) (D := D) A σ
  have hExtra := Kraus.tp_primitive_irreducible_extra_blocking B hTP hPrim hIrr hp
  have hNormalAlg : Kraus.IsNormal (Kraus.block B p) :=
    isNormal_of_tp_primitive_irreducible
      (α := Fin p → α) (D := D)
      (Kraus.block B p) hExtra.1 hExtra.2.1 hExtra.2.2
  have hBlockedGaugeNormal :
      IsNormalTensor (Kraus.block B p) :=
    isNormalTensor_of_isNormal_leftCanonical
      (α := (Fin p → α)) (D := D)
      (Kraus.block B p) hNormalAlg hExtra.1
  exact hBlockedGaugeNormal.of_gaugeEquiv (hGauge.block p)

end IsNormalTensor

/-- Exact word-level transport through a coisometric reconstruction, for
nonempty words.

Source: arXiv:1606.00608, equation `II_CF1` at lines 237--244 gives the
one-site canonical-form reconstruction, and Proposition 4.13 at lines
1917--1921 uses the corresponding coisometric reconstruction.  This theorem is
its nonempty-word iteration, with intermediate coisometries cancelled by
\(UU^*=1\). -/
theorem evalWord_eq_coisometry_reconstruction_of_ne_nil
    {d n : ℕ} {A : MPTensor α (Fin d)} {B : MPTensor α (Fin n)}
    (U : Matrix (Fin n) (Fin d) ℂ)
    (hU : U * Uᴴ = 1)
    (hReconstruct : ∀ v, A v = Uᴴ * B v * U) :
    ∀ w : List α, w ≠ [] →
      Kraus.evalWord A w = Uᴴ * Kraus.evalWord B w * U
  | [], hnil => False.elim (hnil rfl)
  | v :: w, _ => by
      induction w generalizing v with
      | nil =>
          simpa [Kraus.evalWord] using hReconstruct v
      | cons v' w ih =>
          change A v * Kraus.evalWord A (v' :: w) =
            Uᴴ * (B v * Kraus.evalWord B (v' :: w)) * U
          rw [hReconstruct v, ih v' (by simp)]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc U Uᴴ, hU, Matrix.one_mul]

/-- Blocking a weighted direct sum is exactly the weighted direct sum of the
blocked summands, with every weight raised to the blocking length.

Source: arXiv:1606.00608, lines 259--301, especially equations `II_Psi_k`,
`II_ABasicTensors`, and `decBSV`. -/
theorem block_toTensorFromBlocks_apply {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (blocks : (k : Fin r) → MPTensor α (Fin (dim k)))
    (p : ℕ) (i : Fin p → α) :
    Kraus.block
        (toTensorFromBlocks (α := α) (μ := μ) blocks) p i =
      toTensorFromBlocks (α := (Fin p → α))
        (fun k ↦ μ k ^ p)
        (fun k ↦ Kraus.block (blocks k) p) i := by
  simp [Kraus.block_apply, toTensorFromBlocks,
    evalWord_toTensorFromBlocks_eq_reindex_blockDiagonal]

section CPSVCanonicalFormData

open MPTensor.CPSVCanonicalFormData

/-- Literal CPSV canonical-form data are preserved by positive physical
blocking.

The retained dimensions and ambient coisometry are unchanged.  The retained
weights are raised to the blocking length and each retained normal tensor is
blocked by that length.

Source: arXiv:1606.00608, Section 2.3, lines 214--245 and eq. `II_CF1`. -/
noncomputable def _root_.MPTensor.CPSVCanonicalFormData.block {A : MPTensor α (Fin D)}
    (data : CPSVCanonicalFormData A) (p : ℕ) (hp : 0 < p) :
    CPSVCanonicalFormData (Kraus.block A p) where
  r := data.r
  dim := data.dim
  dim_pos := data.dim_pos
  weights := fun k ↦ data.weights k ^ p
  weights_ne_zero := fun k ↦ pow_ne_zero p (data.weights_ne_zero k)
  blocks := fun k ↦ Kraus.block (data.blocks k) p
  blocks_normal := fun k ↦ (data.blocks_normal k).block p hp
  total_dim_le := data.total_dim_le
  ambient_coisometry := data.ambient_coisometry
  coisometric := data.coisometric
  reconstruct := by
    intro i
    have hword_ne : List.ofFn i ≠ [] := by
      intro hnil
      have hlen := congrArg List.length hnil
      simp [List.length_ofFn, hp.ne'] at hlen
    calc
      Kraus.block A p i =
          data.ambient_coisometryᴴ *
            Kraus.evalWord (toTensorFromBlocks (α := α) data.weights data.blocks)
              (List.ofFn i) *
            data.ambient_coisometry := by
            simpa [Kraus.block_apply] using
              evalWord_eq_coisometry_reconstruction_of_ne_nil
                data.ambient_coisometry data.coisometric data.reconstruct
                (List.ofFn i) hword_ne
      _ = data.ambient_coisometryᴴ *
            toTensorFromBlocks (α := (Fin p → α))
              (fun k ↦ data.weights k ^ p)
              (fun k ↦ Kraus.block
                (data.blocks k) p) i *
            data.ambient_coisometry := by
            have hblock := block_toTensorFromBlocks_apply
              (α := α) (dim := data.dim) data.weights data.blocks p i
            rw [← hblock]
            rfl

end CPSVCanonicalFormData

namespace CPSVCanonicalFormIIData

/-- Blockwise CPSV canonical-form-II data are preserved by positive physical blocking.

Each fixed-point matrix remains positive definite and diagonal, and is fixed by the blocked transfer
map because that map is the corresponding positive power of the original transfer map. The same
matrix is retained, so any separately supplied trace normalization is also unchanged.

Source: arXiv:1703.09188, Section II, lines 297--305, and Section III, line 356. -/
noncomputable def block {A : MPTensor α (Fin D)}
    (data : CPSVCanonicalFormIIData A) (p : ℕ) (hp : 0 < p) :
    CPSVCanonicalFormIIData (Kraus.block A p) where
  toCPSVCanonicalFormData := data.toCPSVCanonicalFormData.block p hp
  blocks_left_canonical := fun k ↦
    (Kraus.IsTP.block (A := data.blocks k) (data.blocks_left_canonical k) p)
  blocks_fixed_point := by
    intro k
    obtain ⟨Λ, hΛpos, hΛdiag, hΛfix⟩ := data.blocks_fixed_point k
    exact ⟨Λ, hΛpos, hΛdiag, by
      change Kraus.transferMap (Kraus.block (data.blocks k) p) Λ = Λ
      rw [Kraus.transferMap_block, Module.End.pow_apply, Function.iterate_fixed hΛfix]⟩

end CPSVCanonicalFormIIData

section IsCPSVCanonicalForm

open MPTensor.IsCPSVCanonicalForm

/-- Positive physical blocking preserves literal CPSV canonical form.

Source: arXiv:1606.00608, lines 227--244 define blocking, normal tensors, and
canonical form; lines 259--301 give the weight-power expansion under products. -/
theorem _root_.MPTensor.IsCPSVCanonicalForm.block {A : MPTensor α (Fin D)}
    (hA : IsCPSVCanonicalForm A)
    (p : ℕ) (hp : 0 < p) :
    IsCPSVCanonicalForm (Kraus.block A p) := by
  obtain ⟨data⟩ := hA
  exact ⟨data.block p hp⟩

end IsCPSVCanonicalForm

/-! ## Common injective reblocking for TP / primitive / irreducible families

For an arbitrary finite family of left-canonical, primitive, irreducible blocks
with positive bond dimensions, there is a single positive blocking length `L`
at which every block becomes one-site injective, and at which left-canonical
normalization, transfer-map primitivity, and tensor irreducibility are all
preserved.

This is the finite-family analogue of
`exists_pos_block_isInjective_of_tp_primitive_irreducible`, stated so
that the consumer can feed the resulting prepared blocks into the
`SectorBNT` prepared-block supplier.

Paper anchor: CPSV16 §II.C discussion around blocking to common normal form
(Cirac–Pérez-García–Schuch–Verstraete, arXiv:1606.00608, Section II.C,
lines 237–280).
-/

/-- **Common injective reblocking for TP / primitive / irreducible families.**

Given a finite family of left-canonical, primitive, irreducible MPS tensors
indexed by `Fin r` with positive bond dimensions, there exists a single
positive blocking length `L` at which every block is simultaneously
one-site injective, left-canonical, primitive, and irreducible.

Strategy:

1. For each `k`, the per-block lemma
   `exists_pos_block_isInjective_of_tp_primitive_irreducible` gives a
   positive length `L k` at which the block becomes one-site injective.
2. Setting `L := ∏ k, L k`, fixed-length injectivity persists at positive
   multiples via `block_isInjective_mul_of_block_isInjective`.
3. Trace-preservation, transfer-map primitivity, and tensor irreducibility
   are preserved at any positive blocking length via
   `Kraus.tp_primitive_irreducible_extra_blocking`.
-/
theorem exists_common_injective_blocking_of_tp_primitive_irr_family
    {α : Type*} [Fintype α] {r : ℕ} {dim : Fin r → ℕ}
    (blocks : (k : Fin r) → MPTensor α (Fin (dim k)))
    (hDim : ∀ k, 0 < dim k)
    (hTP : ∀ k, ∑ i : α, (blocks k i)ᴴ * blocks k i = 1)
    (hPrim : ∀ k, _root_.IsPrimitive (Kraus.transferMap (ι := α) (n := Fin (dim k)) (blocks k)))
    (hIrr : ∀ k, Kraus.IsIrreducibleFamily (blocks k)) :
    ∃ L : ℕ, 0 < L ∧ ∀ k : Fin r,
      Kraus.IsInjective (Kraus.block (blocks k) L) ∧
      (∑ i : (Fin L → α),
        (Kraus.block (blocks k) L i)ᴴ *
          Kraus.block (blocks k) L i = 1) ∧
      _root_.IsPrimitive
        (Kraus.transferMap (ι := (Fin L → α)) (n := Fin (dim k))
          (Kraus.block (blocks k) L)) ∧
      Kraus.IsIrreducibleFamily (Kraus.block (blocks k) L) := by
  classical
  -- `NeZero (dim k)` for each `k` from positivity.
  have : ∀ k, NeZero (dim k) := fun k => ⟨(hDim k).ne'⟩
  -- Per-block injective blocking lengths.
  have hBlock : ∀ k : Fin r, ∃ Lk : ℕ, 0 < Lk ∧
      Kraus.IsInjective (Kraus.block (blocks k) Lk) := by
    intro k
    exact MPSTensor.exists_pos_block_isInjective_of_tp_primitive_irreducible
      (blocks k) (hTP k) (hPrim k) (hIrr k)
  let L : Fin r → ℕ := fun k => Classical.choose (hBlock k)
  have hL_pos : ∀ k, 0 < L k := fun k => (Classical.choose_spec (hBlock k)).1
  have hL_inj : ∀ k,
      Kraus.IsInjective (Kraus.block (blocks k) (L k)) :=
    fun k => (Classical.choose_spec (hBlock k)).2
  refine ⟨∏ k : Fin r, L k, Finset.prod_pos fun k _ => hL_pos k, ?_⟩
  intro k
  -- Step 1: rewrite the common length as `(∏_{j≠k} L j) * L k`.
  have hcommon :
      (∏ j : Fin r, L j) = (∏ j ∈ Finset.univ.erase k, L j) * L k := by
    simpa using (Finset.prod_erase_mul (s := Finset.univ) (a := k) (f := L)
      (Finset.mem_univ k)).symm
  have hmult_pos : 0 < ∏ j ∈ Finset.univ.erase k, L j :=
    Finset.prod_pos fun j _ => hL_pos j
  -- Step 2: injectivity at the common length via blockwise multiplication.
  have hInj :
      Kraus.IsInjective
        (Kraus.block (blocks k) (∏ j : Fin r, L j)) := by
    have hmul := MPSTensor.block_isInjective_mul_of_block_isInjective
      (blocks k) hmult_pos (hL_inj k)
    rw [hcommon]
    exact hmul
  -- Step 3: TP + primitive + irreducible preserved at positive blocking length.
  have hL_total_pos : 0 < ∏ j : Fin r, L j :=
    Finset.prod_pos fun j _ => hL_pos j
  obtain ⟨hTPk, hPrimk, hIrrk⟩ :=
    Kraus.tp_primitive_irreducible_extra_blocking
      (blocks k) (hTP k) (hPrim k) (hIrr k) hL_total_pos
  exact ⟨hInj, hTPk, hPrimk, hIrrk⟩

end MPSTensor
