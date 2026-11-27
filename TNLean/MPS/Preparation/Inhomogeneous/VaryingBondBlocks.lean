/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.Combinatorics.IndexInduction
import TNLean.MPS.Tensor.VaryingBond.VaryingBondChain
import TNLean.MPS.Transfer.RenormalizationFixedPoint.BlockIsometryState
import TNLean.MPS.Tensor.Physical.SupportedPolar
import TNLean.MPS.Preparation.Polar.BondEmbedding

/-!
# Blocks of a chain with bond dimensions at most `D`

Let `A` be a periodic chain with bond dimensions `D_0, …, D_{N-1}` at most `D`
(`VaryingBondChain`, in `TNLean.MPS.Chain.VaryingBondChain`), padded with zeros to the chain
`VaryingBondChain.zeroPad A` of bond dimension `D`. Cut the ring into blocks. For a block of
length at least one, the blocked tensor of block `k` of the padded chain vanishes outside the
rectangle `[0, D_{o_k}) × [0, D_{o_{k+1}})` of the bonds at the ends of the block
(`VaryingBondChain.chainBlockTensor_zeroPad_eq_zero`). Injectivity of the blocked tensors
(`VaryingBondChain.IsBlockInjective`) is stated for the padded chain: its blocked matrices span
every matrix unit in that rectangle. For blocks of length at least one the padded blocked tensor
is then injective on the rectangle (`VaryingBondChain.IsBlockInjective.isInjectiveOn`). Pairs
`ω^k` on `ℂ^{D_j} ⊗ ℂ^{D_j}`, for the bond `j` between blocks `k` and `k + 1`, are padded in the
same way (`VaryingBondChain.padPairs`), and their product is supported on the rectangles.

This is the setting of arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS",
for matrix product states "with bond dimension at most `D`".

## References

* arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS", and the footnote to the
  paragraph "Approximation through the fixed-point state".

## Density matrices and pairs on padded virtual bonds

Padding a virtual density matrix is its conjugation by the coordinate isometry. Its
fixed-point pair therefore equals the padding of the fixed-point pair on the actual bond.
This identifies the pairs used by the varying-bond preparation theorem.

### References

* arXiv:2307.01696v2, paragraph "Inhomogeneous short-range correlated MPS".
-/

section

open scoped BigOperators Matrix
open Kraus (blockPhysDim)

namespace VaryingBondChain

open MPSPreparation MPSTensor

variable {d D N M : ℕ}

/-- The dimension `D_{o_k}` of the bond at the left end of block `k`, for a ring of `N ≥ 1`
sites cut into blocks of lengths `ℓ`. -/
def leftBond [NeZero N] (A : VaryingBondChain d D N) (ℓ : Fin M → ℕ) (k : Fin M) : ℕ :=
  A.bondDim ⟨blockOffset ℓ k.val % N, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne N))⟩

/-- The dimension of the bond at the right end of block `k`, the left end of block `k + 1`,
cyclically. -/
def rightBond [NeZero N] (A : VaryingBondChain d D N) (ℓ : Fin M → ℕ) (k : Fin M) : ℕ :=
  leftBond A ℓ (finRotate M k)

theorem rightBond_le [NeZero N] (A : VaryingBondChain d D N) (ℓ : Fin M → ℕ) (k : Fin M) :
    rightBond A ℓ k ≤ D :=
  A.bondDim_le _

/-- The rectangle `[0, a) × [0, b)` of pairs of bond indices. -/
def corner (D a b : ℕ) : Set (Fin D × Fin D) :=
  {p | p.1.val < a ∧ p.2.val < b}

/-- The rectangle of block `k`: pairs `(α, β)` with `α < D_{o_k}` and `β < D_{o_{k+1}}`. -/
def blockCorner [NeZero N] (A : VaryingBondChain d D N) (ℓ : Fin M → ℕ) (k : Fin M) :
    Set (Fin D × Fin D) :=
  corner D (leftBond A ℓ k) (rightBond A ℓ k)

/-- **The blocked tensor of a padded chain is supported on the rectangle of the block**
`[0, D_{o_k}) × [0, D_{o_{k+1}})`, for a block of length at least one. -/
theorem chainBlockTensor_zeroPad_eq_zero [NeZero N] (A : VaryingBondChain d D N)
    {ℓ : Fin M → ℕ} (hN : ∑ k, ℓ k = N) {k : Fin M} (hk : 0 < ℓ k)
    (t : Fin (blockPhysDim d (ℓ k))) {p : Fin D × Fin D} (hp : p ∉ blockCorner A ℓ k) :
    chainBlockTensor (zeroPad A) hN k t p.1 p.2 = 0 := by
  have hNpos := Nat.pos_of_ne_zero (NeZero.ne N)
  let b : Fin (ℓ k + 1) → ℕ := fun j =>
    A.bondDim ⟨(blockOffset ℓ k.val + j.val) % N, Nat.mod_lt _ hNpos⟩
  refine MPSChainTensor.blockTensor_eq_zero_of_support _ hk b
    (fun j i α β h => zeroPad_eq_zero A ?_) t ?_
  · have h1 : A.bondDim (blockSite hN k j) = b j.castSucc := congrArg A.bondDim (Fin.ext (by
      simp [Nat.mod_eq_of_lt (blockOffset_add_lt hN k j)]))
    have h2 : A.bondDim (finRotate N (blockSite hN k j)) = b j.succ :=
      congrArg A.bondDim (Fin.ext (by rw [coe_finRotate_mod]; simp [add_assoc]))
    rwa [h1, h2]
  · have h0 : b 0 = leftBond A ℓ k := rfl
    have hl : b (Fin.last (ℓ k)) = rightBond A ℓ k :=
      congrArg A.bondDim (Fin.ext (by simpa using blockOffset_add_mod hN k))
    rw [h0, hl]
    exact hp

/-- **Injectivity of the blocked tensors** of a chain with bond dimensions at most `D`, stated
for the zero-padded chain: for every block `k`, the blocked matrices of the padded chain span
every matrix unit `|α⟩⟨β|` with `α < D_{o_k}` and `β < D_{o_{k+1}}`.

For a block of length at least one the padded blocked tensor vanishes outside that rectangle
(`VaryingBondChain.chainBlockTensor_zeroPad_eq_zero`), and its corner there is the product of
the rectangular matrices along the block, so the condition reads as injectivity of the
rectangular blocked tensor: its matrices, of size `D_{o_k} × D_{o_{k+1}}`, span all matrices of
that size. The exact product identification is
`VaryingBondChain.zeroPad_rectangularBlockTensor` in
`TNLean.MPS.Preparation.RectangularBlocks`. For a block
of length zero the two readings differ: the padded blocked tensor is the identity `1_D`.

arXiv:2307.01696, footnote to the paragraph "Approximation through the fixed-point state": the
blocked tensors are assumed injective. -/
def IsBlockInjective [NeZero N] (A : VaryingBondChain d D N) {ℓ : Fin M → ℕ}
    (hN : ∑ k, ℓ k = N) : Prop :=
  ∀ k, ∀ p ∈ blockCorner A ℓ k,
    Matrix.single p.1 p.2 (1 : ℂ) ∈ Submodule.span ℂ (Set.range (chainBlockTensor (zeroPad A) hN k))

/-- If every block has length at least one and the blocked tensors are injective, every padded
blocked tensor is injective on the rectangle of its block. -/
theorem IsBlockInjective.isInjectiveOn [NeZero N] {A : VaryingBondChain d D N}
    {ℓ : Fin M → ℕ} {hN : ∑ k, ℓ k = N} (hA : IsBlockInjective A hN) (hℓ : ∀ k, 0 < ℓ k)
    (k : Fin M) : IsInjectiveOn (chainBlockTensor (zeroPad A) hN k) (blockCorner A ℓ k) :=
  ⟨fun t _ hp => chainBlockTensor_zeroPad_eq_zero A hN (hℓ k) t hp, hA k⟩

/-- For blocks of positive length, block injectivity of a varying-bond chain is injectivity
of every padded blocked tensor on the rectangle of its block (arXiv:2307.01696, footnote to the
paragraph "Approximation through the fixed-point state": the blocked tensors are assumed
injective). Positive block lengths are part of that standing assumption. -/
theorem isBlockInjective_iff_forall_isInjectiveOn [NeZero N] {A : VaryingBondChain d D N}
    {ℓ : Fin M → ℕ} (hN : ∑ k, ℓ k = N) (hℓ : ∀ k, 0 < ℓ k) :
    IsBlockInjective A hN ↔
      ∀ k, IsInjectiveOn (chainBlockTensor (zeroPad A) hN k) (blockCorner A ℓ k) :=
  ⟨fun h => h.isInjectiveOn hℓ, fun h k => (h k).2⟩

/-! ### Pairs on the bonds between blocks -/

/-- A vector on `ℂ^r ⊗ ℂ^r`, padded with zeros to a vector on `ℂ^D ⊗ ℂ^D`. -/
def padPair {r : ℕ} (D : ℕ) (ω : Fin r × Fin r → ℂ) : Fin D × Fin D → ℂ :=
  fun p => Matrix.zeroPad D (Matrix.of fun a b => ω (a, b)) p.1 p.2

/-- Padding preserves inner products: `⟨pad ω, pad ω'⟩ = ⟨ω, ω'⟩` for `r ≤ D`. -/
theorem sum_star_padPair_mul {r : ℕ} (hr : r ≤ D) (ω ω' : Fin r × Fin r → ℂ) :
    ∑ p, star (padPair D ω p) * padPair D ω' p = ∑ p, star (ω p) * ω' p := by
  classical
  let e : Fin r × Fin r → Fin D × Fin D := fun p =>
    (⟨p.1.val, lt_of_lt_of_le p.1.isLt hr⟩, ⟨p.2.val, lt_of_lt_of_le p.2.isLt hr⟩)
  have he : Function.Injective e := fun p p' h => by
    simp only [e, Prod.mk.injEq, Fin.mk.injEq] at h
    exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)
  refine (Fintype.sum_of_injective e he (fun p => star (ω p) * ω' p) _ (fun q hq => ?_)
    fun p => ?_).symm
  · have : ¬(q.1.val < r ∧ q.2.val < r) := fun h =>
      hq ⟨(⟨q.1.val, h.1⟩, ⟨q.2.val, h.2⟩), Prod.ext (Fin.ext rfl) (Fin.ext rfl)⟩
    simp [padPair, Matrix.zeroPad_apply_eq_zero _ this]
  · simp [padPair, e, Matrix.zeroPad]

/-- The pairs `ω^k` on `ℂ^{D_j} ⊗ ℂ^{D_j}`, `j` the bond joining block `k` to block `k + 1`,
padded with zeros to vectors on `ℂ^D ⊗ ℂ^D`. -/
def padPairs [NeZero N] (A : VaryingBondChain d D N) (ℓ : Fin M → ℕ)
    (ω : ∀ k, Fin (rightBond A ℓ k) × Fin (rightBond A ℓ k) → ℂ) : Fin M → Fin D × Fin D → ℂ :=
  fun k => padPair D (ω k)

/-- Padded unit pairs are unit vectors. -/
theorem sum_star_padPairs_mul_self [NeZero N] (A : VaryingBondChain d D N) (ℓ : Fin M → ℕ)
    {ω : ∀ k, Fin (rightBond A ℓ k) × Fin (rightBond A ℓ k) → ℂ}
    (hω : ∀ k, ∑ p, star (ω k p) * ω k p = 1) (k : Fin M) :
    ∑ p, star (padPairs A ℓ ω k p) * padPairs A ℓ ω k p = 1 := by
  rw [padPairs, sum_star_padPair_mul (rightBond_le A ℓ k), hω k]

/-- **The product of padded pairs is supported on the rectangles of the blocks**: if
`Ω(c) ≠ 0`, then the pair `c_k` of bond indices of block `k` lies in its rectangle. -/
theorem mem_blockCorner_of_pairFamilyState_ne_zero [NeZero N] (A : VaryingBondChain d D N)
    (ℓ : Fin M → ℕ) (ω : ∀ k, Fin (rightBond A ℓ k) × Fin (rightBond A ℓ k) → ℂ)
    {c : Fin M → Fin D × Fin D} (hc : pairFamilyState (padPairs A ℓ ω) c ≠ 0) (k : Fin M) :
    c k ∈ blockCorner A ℓ k := by
  have hne : ∀ j, padPairs A ℓ ω j ((c j).2, (c (finRotate M j)).1) ≠ 0 := fun j h =>
    hc (Finset.prod_eq_zero (Finset.mem_univ j) h)
  have hsupp : ∀ j, (c j).2.val < rightBond A ℓ j ∧
      (c (finRotate M j)).1.val < rightBond A ℓ j := fun j => by
    by_contra h
    exact hne j (by rw [padPairs, padPair, Matrix.zeroPad_apply_eq_zero _ h])
  have h1 := (hsupp ((finRotate M).symm k)).2
  simp only [rightBond, Equiv.apply_symm_apply] at h1
  exact ⟨h1, (hsupp k).1⟩

end VaryingBondChain

end

section

open Matrix MPSTensor
open scoped ComplexOrder MatrixOrder

namespace MPSTensor

/-- Zero padding of a virtual-bond matrix is its coordinate-isometry embedding. -/
theorem zeroPad_eq_embeddedBlockState {D a : ℕ} (ha : a ≤ D)
    (X : Matrix (Fin a) (Fin a) ℂ) :
    Matrix.zeroPad D X = embeddedBlockState (Fin.castLE ha) X := by
  ext i j
  by_cases h : i.val < a ∧ j.val < a
  · let x : Fin a := ⟨i.val, h.1⟩
    let y : Fin a := ⟨j.val, h.2⟩
    have hi : i = Fin.castLE ha x := Fin.ext rfl
    have hj : j = Fin.castLE ha y := Fin.ext rfl
    rw [Matrix.zeroPad_apply_of_lt X h.1 h.2]
    conv_rhs => rw [hi, hj, embeddedBlockState,
      coordEmbedding_mul_mul_conjTranspose_apply_self (Fin.castLE_injective ha)]
  · rw [Matrix.zeroPad_apply_eq_zero X h, embeddedBlockState,
      coordEmbedding_mul_mul_conjTranspose_apply_eq_zero]
    rcases not_and_or.mp h with hi | hj
    · left
      rintro ⟨x, hx⟩
      exact hi (by simp [← hx])
    · right
      rintro ⟨y, hy⟩
      exact hj (by simp [← hy])

/-- The padded fixed-point pair is the fixed-point pair of the padded density matrix. -/
theorem padPair_fixedPointPair {D a : ℕ} (ha : a ≤ D)
    {σ : Matrix (Fin a) (Fin a) ℂ} (hσ : σ.PosSemidef) :
    VaryingBondChain.padPair D (fixedPointPair σ) = fixedPointPair (Matrix.zeroPad D σ) := by
  funext p
  change Matrix.zeroPad D (CFC.sqrt σ) p.1 p.2 = (CFC.sqrt (Matrix.zeroPad D σ)) p.1 p.2
  rw [zeroPad_eq_embeddedBlockState ha σ, embeddedBlockState,
    cfc_sqrt_coordEmbedding_mul_mul (Fin.castLE_injective ha) hσ,
    zeroPad_eq_embeddedBlockState ha (CFC.sqrt σ)]
  rfl

end MPSTensor

end
