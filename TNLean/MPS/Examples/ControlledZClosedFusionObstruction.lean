/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.ControlledZCombinedReductions
import TNLean.MPS.Symmetry.MPOSymmetry.ClosedFusion

/-!
# An obstruction to exact closed fusion for controlled-Z tensors

The combined controlled-Z family has actual fusion reductions on every word. It has
no exact letter-by-letter reconstruction of a product from those reductions,
for any choice of fusion caps. Squaring the controlled-Z generator has different zero
and one diagonal physical letters, whereas reconstruction through the identity tensor
would make them equal.

This distinguishes the periodic reduction setting from `fusiontensorG` in
arXiv:2203.12563, lines 641--656 and 1211--1213. It obstructs direct use of that paper's
arbitrary-boundary symmetry definition for this fixed family. It does not exclude a
different admissible symmetry embedding or establish a physical phase obstruction.
-/

open MPOTensor MPOTensor.GroupFamily MPSTensor TNLean.Algebra

namespace ControlledZGauging

private abbrev czGenerator : Multiplicative (ZMod 2 × ZMod 2) :=
  Multiplicative.ofAdd (0, 1)

private theorem stacked_diagonal_ne :
    mulTensor (combinedFamily.tensor czGenerator) (combinedFamily.tensor czGenerator) 0 0 ≠
      mulTensor (combinedFamily.tensor czGenerator) (combinedFamily.tensor czGenerator) 1 1 := by
  intro heq
  rw [← complexOfRing_combinedRationalProduct,
    ← complexOfRing_combinedRationalProduct] at heq
  let k : Fin (czBondDim czGenerator.toAdd.2 * czBondDim czGenerator.toAdd.2) :=
    ⟨0, by decide +kernel⟩
  have hzero : combinedRationalProduct czGenerator czGenerator 0 0 k k = 1 := by
    decide +kernel
  have hone : combinedRationalProduct czGenerator czGenerator 1 1 k k = 0 := by
    decide +kernel
  have hentry := congrArg (fun M ↦ M k k) heq
  simp only [complexOfRing_apply, hzero, hone, map_one, map_zero] at hentry
  exact one_ne_zero hentry

private theorem identity_diagonal_eq :
    combinedFamily.tensor (czGenerator * czGenerator) 0 0 =
      combinedFamily.tensor (czGenerator * czGenerator) 1 1 := by
  rw [← complexOfRing_combinedRationalTensor, ← complexOfRing_combinedRationalTensor]
  rfl

/-- No fusion reduction of the actual combined family reconstructs the stacked tensor
exactly on every letter. This is a failure of the arbitrary-boundary closed-fusion
premise, not of the already proved periodic multiplication or all-word reductions. -/
theorem combinedFamily_not_isClosed (fd : FusionData combinedFamily) : ¬ fd.IsClosed := by
  intro hclosed
  apply stacked_diagonal_ne
  rw [hclosed.mulTensor_apply, hclosed.mulTensor_apply, identity_diagonal_eq]

private theorem blockTensor_constant_diagonal {d D : ℕ} (M : MPOTensor d D)
    (L : ℕ) (i : Fin d) :
    MPOTensor.blockTensor M L ((Kraus.decodeBlockEquiv d L).symm (fun _ ↦ i))
        ((Kraus.decodeBlockEquiv d L).symm (fun _ ↦ i)) = (M i i) ^ L := by
  simp only [MPOTensor.blockTensor_apply, wordOfBlock, Kraus.wordOfBlock,
    Kraus.decodeBlock_decodeBlockEquiv_symm, List.ofFn_const]
  induction L with
  | zero => simp
  | succ L ih => simp only [List.replicate_succ, MPOTensor.evalWord_cons, ih, pow_succ']

private theorem stacked_diagonal_idempotent (i : Fin 2) :
    IsIdempotentElem
      (mulTensor (combinedFamily.tensor czGenerator) (combinedFamily.tensor czGenerator) i i) := by
  change _ * _ = _
  rw [← complexOfRing_combinedRationalProduct]
  let P : Matrix (Fin 4) (Fin 4) ℚ := combinedRationalProduct czGenerator czGenerator i i
  change complexOfRing (Rat.castHom ℂ) P * complexOfRing (Rat.castHom ℂ) P =
    complexOfRing (Rat.castHom ℂ) P
  have hP : P * P = P := by
    -- Finite equality synthesis must unfold the pinned semireducible `ZMod 2`/`Fin 2`
    -- identification in the dependent bond indices of `combinedRationalProduct`.
    set_option backward.isDefEq.respectTransparency false in
      fin_cases i <;> decide +kernel
  rw [← complexOfRing_mul, hP]

/-- Positive physical blocking cannot make the combined family's fusion exactly closed.
The distinct diagonal letters used in the obstruction are idempotent, so every positive
power retains the same discrepancy. This rules out repairing the fixed family's closed
fusion merely by blocking; alternative symmetry embeddings remain a separate question. -/
theorem combinedFamily_block_not_isClosed {L : ℕ} (hL : 0 < L)
    (fd : FusionData (combinedFamily.block L)) : ¬ fd.IsClosed := by
  intro hclosed
  let i₀ := (Kraus.decodeBlockEquiv 2 L).symm (fun _ ↦ (0 : Fin 2))
  let i₁ := (Kraus.decodeBlockEquiv 2 L).symm (fun _ ↦ (1 : Fin 2))
  have hid : (combinedFamily.block L).tensor (czGenerator * czGenerator) i₀ i₀ =
      (combinedFamily.block L).tensor (czGenerator * czGenerator) i₁ i₁ := by
    change MPOTensor.blockTensor _ L i₀ i₀ = MPOTensor.blockTensor _ L i₁ i₁
    rw [blockTensor_constant_diagonal, blockTensor_constant_diagonal, identity_diagonal_eq]
  have heq := (hclosed.mulTensor_apply czGenerator czGenerator i₀ i₀).trans
    ((congrArg (fun M ↦ fd.W czGenerator czGenerator * M * fd.V czGenerator czGenerator)
      hid).trans (hclosed.mulTensor_apply czGenerator czGenerator i₁ i₁).symm)
  have heq' : MPOTensor.blockTensor
        (mulTensor (combinedFamily.tensor czGenerator) (combinedFamily.tensor czGenerator))
        L i₀ i₀ =
      MPOTensor.blockTensor
        (mulTensor (combinedFamily.tensor czGenerator) (combinedFamily.tensor czGenerator))
        L i₁ i₁ := by
    rw [MPOTensor.blockTensor_mulTensor]
    exact heq
  rw [blockTensor_constant_diagonal, blockTensor_constant_diagonal] at heq'
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hL.ne'
  rw [(stacked_diagonal_idempotent 0).pow_succ_eq,
    (stacked_diagonal_idempotent 1).pow_succ_eq] at heq'
  exact stacked_diagonal_ne heq'

end ControlledZGauging
