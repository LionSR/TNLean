/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.MinimalCutRepresentationPadding
import TNLean.MPS.Preparation.VaryingBondBlocks
import QICLean.Channel.KrausCPTP

/-!
# Actual rectangular blocks and their zero padding

The matrices in a block are multiplied on their actual, varying bond spaces. For every
positive block length, zero padding commutes with this product. The corresponding transfer
map is the ordered composition of the rectangular site maps.

The positive-length condition matters: the empty rectangular product is the identity on
its endpoint bond, whose padding is a corner projection rather than the ambient identity.

## References

* arXiv:2307.01696v2, paragraph "Inhomogeneous short-range correlated MPS" and
  Supplemental Material, eq. (S39).
-/

open Matrix MPSTensor
open scoped BigOperators

namespace MPSChainTensor

/-- Ordered multiplication on the actual bond spaces of a rectangular chain. -/
def rectangularEval {d : ℕ} : {n : ℕ} → (b : ℕ → ℕ) →
    (∀ i : Fin n, Fin d → Matrix (Fin (b i.val)) (Fin (b (i.val + 1))) ℂ) →
    (Fin n → Fin d) → Matrix (Fin (b 0)) (Fin (b n)) ℂ
  | 0, _, _, _ => 1
  | _n + 1, b, A, s => A ⟨0, Nat.succ_pos _⟩ (s ⟨0, Nat.succ_pos _⟩) *
      rectangularEval (fun i => b (i + 1)) (fun i => A i.succ) (fun i => s i.succ)

/-- Zero padding commutes with a nonempty ordered rectangular tensor product. -/
theorem zeroPad_rectangularEval {d D n : ℕ} (b : ℕ → ℕ)
    (hb : ∀ i, b i ≤ D)
    (A : ∀ i : Fin n, Fin d → Matrix (Fin (b i.val)) (Fin (b (i.val + 1))) ℂ)
    (s : Fin n → Fin d) (hn : 0 < n) :
    Matrix.zeroPad D (rectangularEval b A s) =
      eval (fun i k => Matrix.zeroPad D (A i k)) s := by
  induction n generalizing b with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => simp [rectangularEval, eval_succ]
    | succ n =>
      rw [rectangularEval, eval_succ, Matrix.zeroPad_mul _ _ (hb 1),
        ih (fun i => b (i + 1)) (fun i => hb (i + 1)) _ _ (Nat.succ_pos _)]
      rfl

/-- The ordered composition of the actual rectangular transfer maps. -/
noncomputable def rectangularTransfer {d : ℕ} : {n : ℕ} → (b : ℕ → ℕ) →
    (∀ i : Fin n, Fin d → Matrix (Fin (b i.val)) (Fin (b (i.val + 1))) ℂ) →
    (Matrix (Fin (b n)) (Fin (b n)) ℂ →ₗ[ℂ]
      Matrix (Fin (b 0)) (Fin (b 0)) ℂ)
  | 0, _, _ => LinearMap.id
  | _n + 1, b, A => (Matrix.rectangularKrausMap (A ⟨0, Nat.succ_pos _⟩)).comp
      (rectangularTransfer (fun i => b (i + 1)) (fun i => A i.succ))

/-- The actual rectangular product has exactly the ordered site transfer map. -/
theorem rectangularTransfer_apply {d n : ℕ} (b : ℕ → ℕ)
    (A : ∀ i : Fin n, Fin d → Matrix (Fin (b i.val)) (Fin (b (i.val + 1))) ℂ)
    (X : Matrix (Fin (b n)) (Fin (b n)) ℂ) :
    rectangularTransfer b A X = ∑ s, rectangularEval b A s * X * (rectangularEval b A s)ᴴ := by
  induction n generalizing b with
  | zero => simp [rectangularTransfer, rectangularEval, Finset.univ_unique]
  | succ n ih =>
    rw [rectangularTransfer, LinearMap.comp_apply, ih]
    simp only [map_sum, Matrix.rectangularKrausMap, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_comm, ← (Fin.consEquiv (fun _ : Fin (n + 1) => Fin d)).sum_comp,
      Fintype.sum_prod_type]
    congr 1
    funext i
    apply Finset.sum_congr rfl
    intro s _
    dsimp only [rectangularEval, Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rfl

end MPSChainTensor

namespace VaryingBondChain

open MPSPreparation

variable {d D N M : ℕ} [NeZero N]

/-- Actual bond dimensions encountered while traversing a block, extended cyclically. -/
def blockBondDim (A : VaryingBondChain d D N) (ℓ : Fin M → ℕ) (k : Fin M) (i : ℕ) : ℕ :=
  A.bondDim ⟨(blockOffset ℓ k.val + i) % N, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne N))⟩

theorem blockBondDim_site (A : VaryingBondChain d D N) {ℓ : Fin M → ℕ}
    (hN : ∑ j, ℓ j = N) (k : Fin M) (i : Fin (ℓ k)) :
    blockBondDim A ℓ k i.val = A.bondDim (blockSite hN k i) := by
  apply congrArg A.bondDim
  apply Fin.ext
  exact Nat.mod_eq_of_lt (blockOffset_add_lt hN k i)

theorem blockBondDim_succ (A : VaryingBondChain d D N) {ℓ : Fin M → ℕ}
    (hN : ∑ j, ℓ j = N) (k : Fin M) (i : Fin (ℓ k)) :
    blockBondDim A ℓ k (i.val + 1) = A.bondDim (finRotate N (blockSite hN k i)) := by
  apply congrArg A.bondDim
  apply Fin.ext
  rw [coe_finRotate_mod]
  simp [blockSite, add_assoc]

@[simp] theorem blockBondDim_zero (A : VaryingBondChain d D N)
    (ℓ : Fin M → ℕ) (k : Fin M) : blockBondDim A ℓ k 0 = leftBond A ℓ k := rfl

theorem blockBondDim_length (A : VaryingBondChain d D N) {ℓ : Fin M → ℕ}
    (hN : ∑ j, ℓ j = N) (k : Fin M) : blockBondDim A ℓ k (ℓ k) = rightBond A ℓ k := by
  apply congrArg A.bondDim
  apply Fin.ext
  exact blockOffset_add_mod hN k

/-- Site matrices in a block, with the actual successive bond spaces as their types. -/
def rectangularBlockSites (A : VaryingBondChain d D N) {ℓ : Fin M → ℕ}
    (hN : ∑ j, ℓ j = N) (k : Fin M) (i : Fin (ℓ k)) (s : Fin d) :
    Matrix (Fin (blockBondDim A ℓ k i.val)) (Fin (blockBondDim A ℓ k (i.val + 1))) ℂ :=
  (A.tensor (blockSite hN k i) s).submatrix
    (Fin.cast (blockBondDim_site A hN k i)) (Fin.cast (blockBondDim_succ A hN k i))

/-- The actual rectangular product along a block, before any ambient-space padding. -/
noncomputable def rectangularBlockTensor (A : VaryingBondChain d D N) {ℓ : Fin M → ℕ}
    (hN : ∑ j, ℓ j = N) (k : Fin M) (s : Fin (blockPhysDim d (ℓ k))) :
    Matrix (Fin (blockBondDim A ℓ k 0)) (Fin (rightBond A ℓ k)) ℂ :=
  (MPSChainTensor.rectangularEval (blockBondDim A ℓ k) (rectangularBlockSites A hN k)
    (decodeBlockEquiv d (ℓ k) s)).submatrix id (Fin.cast (blockBondDim_length A hN k).symm)

/-- The rectangular blocked tensor pads to exactly the blocked padded tensor. -/
theorem zeroPad_rectangularBlockTensor (A : VaryingBondChain d D N) {ℓ : Fin M → ℕ}
    (hN : ∑ j, ℓ j = N) (k : Fin M) (hk : 0 < ℓ k) (s : Fin (blockPhysDim d (ℓ k))) :
    Matrix.zeroPad D (rectangularBlockTensor A hN k s) =
      chainBlockTensor (zeroPad A) hN k s := by
  have hcast {a b c : ℕ} (h : b = c) (X : Matrix (Fin a) (Fin b) ℂ) :
      Matrix.zeroPad D (X.submatrix id (Fin.cast h.symm)) = Matrix.zeroPad D X := by
    subst c
    rfl
  rw [rectangularBlockTensor, hcast (blockBondDim_length A hN k),
    MPSChainTensor.zeroPad_rectangularEval (blockBondDim A ℓ k)
      (fun _ => A.bondDim_le _) _ _ hk]
  congr 1
  funext i t a b
  simp only [rectangularBlockSites, zeroPad, Matrix.zeroPad, Matrix.submatrix_apply,
    blockBondDim_site A hN k i, blockBondDim_succ A hN k i]
  split_ifs <;> rfl

end VaryingBondChain
