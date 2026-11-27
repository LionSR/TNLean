/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.BNT.Construction
import TNLean.MPS.CanonicalForm.NormalBlocks.TPGauge
import TNLean.MPS.Transfer.Primitivity.Bounds

/-!
# Normality consequences of TP-primitive irreducible blocks

This part of the canonical-form reduction upgrades TP-primitive irreducible
blocks to normal blocks and shows that normality is preserved by blocking.

The core chain is the channel Perron–Frobenius route with all hypotheses kept
separate: trace preservation fixes the normalization convention, peripheral
primitivity says that the peripheral spectrum of the transfer map is `{1}`,
tensor irreducibility rules out nontrivial invariant projections, and these
inputs produce a positive definite Perron fixed point.  The primitive complementary
transfer-map gap together with this faithful fixed point gives eventual full Kraus rank,
which is the normality condition used here. A separate word-span argument then
shows that blocking keeps normality.

## Main statements

* `isNormal_of_tp_primitive_irreducible` — TP, primitive transfer map, and
  tensor irreducibility imply normality.
* `exists_pos_block_isInjective_of_tp_primitive_irreducible` — the same
  hypotheses give a positive blocking whose blocked tensor is one-site injective.
* `exists_common_block_isInjective_of_isNormal` — a finite family of normal
  tensors admits one positive blocking length at which all of them are injective.
* `exists_common_block_isInjective_two_of_isNormal` — the same
  common-blocking conclusion simultaneously for two finite families.

## References

* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:1606.00608, Section 2.3 + Appendix A]
* [Wolf, *Quantum Channels & Operations*, Chapter 6]
* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:2011.12127, Section IV]

## Tags

matrix product states, canonical form, normality, blocking
-/

open MPTensor

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Filter

namespace MPSTensor

variable {α : Type*} [Fintype α] {D : ℕ}

/-!
## Per-block chain from TP + primitive + irreducible to Kraus.IsNormal

For a single block that is TP, has a primitive transfer map, and is irreducible
(all three conditions), the full chain to `Kraus.IsNormal` is available:

1. `_root_.IsPrimitive (Kraus.transferMap A)` + `Kraus.IsIrreducibleFamily A` + TP
   → `Kraus.hasPrimitiveFixedPoint_of_peripheralPrimitive_of_irreducible`
   → `∃ ρ, Kraus.HasComplementaryFixedPointGap A ρ`
2. `Kraus.HasComplementaryFixedPointGap A ρ` + `Kraus.IsIrreducibleFamily A`
   → `Kraus.HasComplementaryFixedPointGap.posDef_of_isIrreducibleFamily` → `ρ.PosDef`
3. `Kraus.HasComplementaryFixedPointGap A ρ` + `ρ.PosDef`
   → `isNormal_of_hasComplementaryFixedPointGap_with_posDef` → `Kraus.IsNormal A`

We state this chain as a single theorem.
-/

private theorem isNormal_of_tp_primitive_irreducible_fin {d : ℕ} [NeZero D]
    (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hPrim : _root_.IsPrimitive (Kraus.transferMap (ι := Fin d) (n := Fin D) A))
    (hIrr : Kraus.IsIrreducibleFamily A) :
    Kraus.IsNormal A := by
  -- Step 1: TP normalization, peripheral primitivity, and irreducibility give
  -- primitive MPS data.
  have hMPSPrim : Kraus.HasPrimitiveFixedPoint A :=
    Kraus.hasPrimitiveFixedPoint_of_peripheralPrimitive_of_irreducible A hIrr hTP hPrim
  -- Step 2: Extract the Perron fixed point.
  obtain ⟨ρ, hPrimMPS⟩ := hMPSPrim
  -- Step 3: Upgrade PSD → PosDef using tensor irreducibility.
  have hPD : ρ.PosDef :=
    hPrimMPS.posDef_of_isIrreducibleFamily hIrr
  -- Step 4: Kraus.IsNormal from the primitive complementary gap and a faithful fixed point.
  exact isNormal_of_hasComplementaryFixedPointGap_with_posDef hPrimMPS hPD

/-- **TP + primitive + irreducible → Kraus.IsNormal** (per-block chain).

For a single MPS tensor that is left-canonical (TP), has a primitive transfer map
(peripheral eigenvalues = {1}), and is irreducible (no nontrivial invariant
projection), the tensor is normal (eventually full Kraus rank).

The transfer-map primitivity hypothesis says that the only peripheral eigenvalue
is `1`.  The conclusion is obtained by the following implications:

* TP + peripheral primitivity + irreducibility give a `Kraus.HasComplementaryFixedPointGap` datum,
  including a Perron fixed point for the transfer map.
* Irreducibility upgrades the nonzero positive semidefinite Perron fixed point
  in that datum to a positive definite, faithful fixed point.
* The primitive complementary transfer-map gap together with the faithful fixed point gives
  eventual full Kraus rank, equivalently `Kraus.IsNormal A`. -/
theorem isNormal_of_tp_primitive_irreducible [NeZero D]
    (A : MPTensor α (Fin D))
    (hTP : ∑ i : α, (A i)ᴴ * A i = 1)
    (hPrim : _root_.IsPrimitive (Kraus.transferMap (ι := α) (n := Fin D) A))
    (hIrr : Kraus.IsIrreducibleFamily A) :
    Kraus.IsNormal A := by
  let f : Fin (Fintype.card α) ≃ α := (Fintype.equivFin α).symm
  refine (isNormal_reindexPhysical_equiv f A).1 (isNormal_of_tp_primitive_irreducible_fin _
    ((Kraus.isTP_reindexPhysical_iff f A).2 hTP)
    ((isPrimitive_transferMap_reindexPhysical_equiv f A).2 hPrim)
    ((Kraus.isIrreducibleFamily_reindexPhysical_equiv f A).2 hIrr))

/-- A trace-preserving scalar tensor has a nonzero Kraus matrix. -/
private theorem exists_nonzero_kraus_of_tp_fin {d : ℕ} [NeZero D]
    (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1) :
    ∃ i : Fin d, A i ≠ 0 := by
  by_contra hnone
  push Not at hnone
  have hsum_zero :
      ∑ i : Fin d, (A i)ᴴ * A i = (0 : Matrix (Fin D) (Fin D) ℂ) := by
    apply Finset.sum_eq_zero
    intro i _
    simp [hnone i]
  have hone_zero : (1 : Matrix (Fin D) (Fin D) ℂ) =
      (0 : Matrix (Fin D) (Fin D) ℂ) := by
    rw [← hTP, hsum_zero]
  let a : Fin D := ⟨0, NeZero.pos D⟩
  have hentry : (1 : Matrix (Fin D) (Fin D) ℂ) a a = 0 := by
    simpa using congr_fun (congr_fun hone_zero a) a
  exact one_ne_zero hentry

/-- **TP + primitive + irreducible → injective after positive blocking**.

The blocking length is positive by the definition of normality. -/
theorem exists_pos_block_isInjective_of_tp_primitive_irreducible [NeZero D]
    (A : MPTensor α (Fin D))
    (hTP : ∑ i : α, (A i)ᴴ * A i = 1)
    (hPrim : _root_.IsPrimitive (Kraus.transferMap (ι := α) (n := Fin D) A))
    (hIrr : Kraus.IsIrreducibleFamily A) :
    ∃ L : ℕ, 0 < L ∧ Kraus.IsInjective (Kraus.block A L) := by
  obtain ⟨L, hLpos, hL⟩ := isNormal_of_tp_primitive_irreducible A hTP hPrim hIrr
  exact ⟨L, hLpos, (Kraus.isNBlkInjective_iff_isInjective_block A L).1 hL⟩

/-!
## Combined reduction: arbitrary → Kraus.IsNormal (per block, for primitive blocks)

For the pre-blocking blocks (which ARE irreducible), the chain to Kraus.IsNormal
works directly. This shows that the original nonzero-weight blocks become
normal once we know their transfer maps are primitive.
-/


private theorem exists_pos_isNBlkInjective_le_pow_four_of_isNormal_leftCanonical_fin {d : ℕ}
    [NeZero D]
    (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hN : Kraus.IsNormal A) :
    ∃ L : ℕ, 0 < L ∧ L ≤ D ^ 4 ∧ Kraus.IsNBlkInjective A L := by
  have hDpos : 0 < D := NeZero.pos D
  let L : ℕ := iIndex A
  have hNonempty : ({n : ℕ | 0 < n ∧ Kraus.wordSpan A n = ⊤}).Nonempty := by
    obtain ⟨N, hNpos, hNblk⟩ := hN
    exact ⟨N, hNpos, hNblk⟩
  have hTop : Kraus.wordSpan A L = ⊤ := by
    simpa [L, iIndex] using (Nat.sInf_mem hNonempty).2
  have hIndexBound : L ≤ (D ^ 2 - krausRank A + 1) * D ^ 2 := by
    simpa [L] using
      iIndex_le_general_of_isNormal A hN
  have hKraus_pos : 1 ≤ krausRank A := by
    rw [krausRank, Nat.one_le_iff_ne_zero]
    intro hzero
    have hbot : Kraus.wordSpan A 1 = (⊥ : Submodule ℂ (Matrix (Fin D) (Fin D) ℂ)) :=
      Submodule.finrank_eq_zero.mp hzero
    obtain ⟨i₀, hi₀⟩ := exists_nonzero_kraus_of_tp_fin A hTP
    have hmem : A i₀ ∈ Kraus.wordSpan A 1 := by
      have := Kraus.evalWord_mem_wordSpan A ([i₀] : List (Fin d))
      simpa [Kraus.evalWord] using this
    rw [hbot] at hmem
    exact hi₀ hmem
  have hDsq_pos : 1 ≤ D ^ 2 := by
    nlinarith
  have hFactor : D ^ 2 - krausRank A + 1 ≤ D ^ 2 := by
    by_cases hKraus_le : krausRank A ≤ D ^ 2
    · omega
    · have hsub : D ^ 2 - krausRank A = 0 :=
        Nat.sub_eq_zero_of_le (le_of_not_ge hKraus_le)
      rw [hsub]
      exact hDsq_pos
  have hBound : L ≤ D ^ 4 := by
    calc
      L ≤ (D ^ 2 - krausRank A + 1) * D ^ 2 := hIndexBound
      _ ≤ D ^ 2 * D ^ 2 := Nat.mul_le_mul_right _ hFactor
      _ = D ^ 4 := by ring
  have hLpos : 0 < L := by
    simpa [L, iIndex] using (Nat.sInf_mem hNonempty).1
  exact ⟨L, hLpos, hBound, hTop⟩

/-- **Left-canonical normal tensor → bounded positive injective length**.

This is the bounded form of the quantum Wielandt bound needed by the canonical-form comparison
chain: some positive length `L ≤ D ^ 4` has `S_L(A) = M_D`.  The trace-preserving/left-canonical
hypothesis rules out the scalar zero-physical-letter edge case and supplies a nonzero one-step
Kraus matrix, which makes the general index bound `(D ^ 2 - krausRank A + 1) * D ^ 2` at most
`D ^ 4`.  Source: arXiv:1606.00608, Section II, line 332; arXiv:0909.5347, Theorem 1. -/
theorem exists_pos_isNBlkInjective_le_pow_four_of_isNormal_leftCanonical [NeZero D]
    (A : MPTensor α (Fin D))
    (hTP : ∑ i : α, (A i)ᴴ * A i = 1)
    (hN : Kraus.IsNormal A) :
    ∃ L : ℕ, 0 < L ∧ L ≤ D ^ 4 ∧ Kraus.IsNBlkInjective A L := by
  let f : Fin (Fintype.card α) ≃ α := (Fintype.equivFin α).symm
  obtain ⟨L, hL, hLle, hInj⟩ :=
    exists_pos_isNBlkInjective_le_pow_four_of_isNormal_leftCanonical_fin
      (Kraus.reindexPhysical f A) ((Kraus.isTP_reindexPhysical_iff f A).2 hTP)
      ((isNormal_reindexPhysical_equiv f A).2 hN)
  exact ⟨L, hL, hLle, (isNBlkInjective_reindexPhysical_equiv f A L).1 hInj⟩

/-- **Left-canonical normal tensor is block injective at length $D^4$.**

The bounded Wielandt theorem above produces an injective length at most
$D^4$.  Positive-length block injectivity propagates to every larger length,
so one may use the same exact length $D^4$ for every tensor of bond dimension
$D$.

Source: arXiv:1606.00608, line 332. -/
theorem isNBlkInjective_pow_four_of_isNormal_leftCanonical [NeZero D]
    (A : MPTensor α (Fin D))
    (hTP : ∑ i : α, (A i)ᴴ * A i = 1)
    (hN : Kraus.IsNormal A) :
    Kraus.IsNBlkInjective A (D ^ 4) := by
  obtain ⟨L, hLpos, hLle, hL⟩ :=
    exists_pos_isNBlkInjective_le_pow_four_of_isNormal_leftCanonical A hTP hN
  exact Kraus.isNBlkInjective_of_le hLpos hL hLle

/-!
## Injectivity under further blocking

Normality is preserved by blocking (`Kraus.IsNormal.block`); one-site injectivity of a
blocked tensor persists after further blocking.
-/

/-- One-site injectivity of a blocked tensor persists after a positive further
blocking, read back as direct blocking of the original tensor. -/
theorem block_isInjective_mul_of_block_isInjective
    (A : MPTensor α (Fin D)) {N m : ℕ} (hm : 0 < m)
    (hN : Kraus.IsInjective (Kraus.block A N)) :
    Kraus.IsInjective (Kraus.block A (m * N)) :=
  (Kraus.isNBlkInjective_iff_isInjective_block A (m * N)).1
    (isNBlkInjective_mul_of_isNBlkInjective A hm
      ((Kraus.isNBlkInjective_iff_isInjective_block A N).2 hN))

/-- **Common exact block-injectivity length for a finite normal left-canonical family.**

Let `blocks k` be a finite family of positive-dimensional left-canonical normal tensors.
Then there is a single positive length `L` such that every block is `L`-block-injective.

The proof first uses the bounded positive blocking theorem for each block, and then takes
the product of the finitely many individual lengths. Exact block-injectivity persists at
positive multiples, so this product is a common length for all sectors. -/
theorem exists_common_isNBlkInjective_of_isNormal_leftCanonical
    {r d : ℕ} {dim : Fin r → ℕ}
    (blocks : (k : Fin r) → MPTensor α (Fin (dim k)))
    (hLeft : ∀ k, ∑ i : α, (blocks k i)ᴴ * blocks k i = 1)
    (hNonzero : ∀ k, dim k ≠ 0)
    (hNormal : ∀ k, Kraus.IsNormal (blocks k)) :
    ∃ L : ℕ, 0 < L ∧ ∀ k : Fin r, Kraus.IsNBlkInjective (blocks k) L := by
  classical
  have : ∀ k : Fin r, NeZero (dim k) := fun k => ⟨hNonzero k⟩
  have hBlock : ∀ k : Fin r, ∃ L : ℕ, 0 < L ∧ L ≤ (dim k) ^ 4 ∧
      Kraus.IsNBlkInjective (blocks k) L := fun k =>
    exists_pos_isNBlkInjective_le_pow_four_of_isNormal_leftCanonical
      (blocks k) (hLeft k) (hNormal k)
  let L : Fin r → ℕ := fun k => Classical.choose (hBlock k)
  have hL_pos : ∀ k, 0 < L k := fun k => (Classical.choose_spec (hBlock k)).1
  refine ⟨∏ k : Fin r, L k, Finset.prod_pos fun k _ => hL_pos k, ?_⟩
  intro k
  have hL_blk : Kraus.IsNBlkInjective (blocks k) (L k) := (Classical.choose_spec (hBlock k)).2.2
  have hcommon : (∏ j : Fin r, L j) = (∏ j ∈ Finset.univ.erase k, L j) * L k := by
    simpa using (Finset.prod_erase_mul (s := Finset.univ) (a := k) (f := L)
      (Finset.mem_univ k)).symm
  have hmult_pos : 0 < ∏ j ∈ Finset.univ.erase k, L j :=
    Finset.prod_pos fun j _ => hL_pos j
  have hmul := isNBlkInjective_mul_of_isNBlkInjective
    (blocks k) hmult_pos hL_blk
  simpa [hcommon] using hmul

/-- **Uniform finite-family injective blocking for normal blocks.**

A finite family of normal tensors (eventually block injective in the sense of
arXiv:0909.5347, the definition after equation (1)) admits one positive blocking
length at which every member is one-site injective. Each member is block injective at
some positive length; the product of these finitely many lengths is a common positive
length, since fixed-length injectivity persists at positive multiples.

This is the common blocking of the normal blocks of a canonical form used in
arXiv:1606.00608, lines 318--344. -/
theorem exists_common_block_isInjective_of_isNormal
    {α : Type*} [Fintype α] {r : ℕ} {dim : Fin r → ℕ} {blocks : (k : Fin r) → MPTensor α (Fin (dim k))}
    (hNormal : ∀ k, Kraus.IsNormal (blocks k)) :
    ∃ L : ℕ, 0 < L ∧
      ∀ k : Fin r,
        Kraus.IsInjective (Kraus.block (blocks k) L) := by
  classical
  choose L hL_pos hL using hNormal
  refine ⟨∏ k : Fin r, L k, Finset.prod_pos fun k _ => hL_pos k, fun k => ?_⟩
  have hcommon : (∏ j : Fin r, L j) = (∏ j ∈ Finset.univ.erase k, L j) * L k := by
    simpa using (Finset.prod_erase_mul (s := Finset.univ) (a := k) (f := L)
      (Finset.mem_univ k)).symm
  rw [hcommon]
  exact (Kraus.isNBlkInjective_iff_isInjective_block (blocks k) _).1
    (isNBlkInjective_mul_of_isNBlkInjective (blocks k)
      (Finset.prod_pos fun j _ => hL_pos j) (hL k))

/-- **Two-sided uniform injective blocking for normal block families.**

Given two finite families of normal tensors with the same physical dimension, there is a
single positive blocking length at which every block on both sides is one-site injective.
This is the common blocking used for the two canonical forms compared in
arXiv:1606.00608, Theorem 2.10, lines 318--344 and 1170--1192. -/
theorem exists_common_block_isInjective_two_of_isNormal
    {rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    {blocksA : (j : Fin rA) → MPTensor α (Fin (dimA j))}
    {blocksB : (k : Fin rB) → MPTensor α (Fin (dimB k))}
    (hA : ∀ j, Kraus.IsNormal (blocksA j))
    (hB : ∀ k, Kraus.IsNormal (blocksB k)) :
    ∃ L : ℕ, 0 < L ∧
      (∀ j : Fin rA,
        Kraus.IsInjective (Kraus.block (blocksA j) L)) ∧
      (∀ k : Fin rB,
        Kraus.IsInjective (Kraus.block (blocksB k) L)) := by
  obtain ⟨LA, hLA_pos, hLA⟩ := exists_common_block_isInjective_of_isNormal hA
  obtain ⟨LB, hLB_pos, hLB⟩ := exists_common_block_isInjective_of_isNormal hB
  refine ⟨LB * LA, Nat.mul_pos hLB_pos hLA_pos, fun j => ?_, fun k => ?_⟩
  · exact block_isInjective_mul_of_block_isInjective (blocksA j) hLB_pos (hLA j)
  · rw [Nat.mul_comm]
    exact block_isInjective_mul_of_block_isInjective (blocksB k) hLA_pos (hLB k)

end MPSTensor
