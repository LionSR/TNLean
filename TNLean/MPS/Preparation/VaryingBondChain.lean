/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.BlockIsometryState
import TNLean.MPS.Preparation.IsometricChain
import TNLean.MPS.Preparation.SupportedPolar

/-!
# Periodic chains with bond dimensions at most `D`

A periodic chain on a ring of `N` sites whose bond dimensions `D_0, …, D_{N-1}` may vary along
the ring and are at most `D` (`MPSPreparation.VaryingBondChain`): site `k` carries rectangular
matrices `A_k^i` of size `D_k × D_{k+1}`, the bond `k` being the one to the left of site `k`, and
the state has coefficients `Tr(A_0^{s_0} ⋯ A_{N-1}^{s_{N-1}})`.

Padding every matrix with zeros to a `D × D` matrix (`MPSPreparation.VaryingBondChain.zeroPad`)
gives a chain with the common bond dimension `D` and, on a ring of `N ≥ 1` sites, the same state
(`MPSPreparation.VaryingBondChain.coeff_zeroPad`). Cut the ring into blocks; for a block of
length at least one, the blocked tensor of block `k` of the padded chain vanishes outside the
rectangle `[0, D_{o_k}) × [0, D_{o_{k+1}})` of the bonds at the ends of the block
(`MPSPreparation.VaryingBondChain.chainBlockTensor_zeroPad_eq_zero`). Injectivity of the blocked
tensors (`MPSPreparation.VaryingBondChain.IsBlockInjective`) says that the padded blocked
matrices span every matrix unit in that rectangle, which is injectivity of the rectangular
blocked tensor; the padded blocked tensor is then injective on the rectangle
(`MPSPreparation.VaryingBondChain.IsBlockInjective.isInjectiveOn`). Pairs `ω^k` on
`ℂ^{D_j} ⊗ ℂ^{D_j}`, for the bond `j` between blocks `k` and `k + 1`, are padded in the same way
(`MPSPreparation.VaryingBondChain.padPairs`), and their product is supported on the rectangles.

This is the setting of arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS",
for matrix product states "with bond dimension at most `D`".

## References

* arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS", and the footnote to the
  paragraph "Approximation through the fixed-point state".
-/

open scoped BigOperators Matrix

namespace MPSPreparation

open MPSTensor

/-- A periodic chain of tensors on a ring of `N` sites with **bond dimensions at most `D`**: the
bond `k`, to the left of site `k`, has dimension `D_k ≤ D`, and site `k` carries the rectangular
matrices `A_k^i` of size `D_k × D_{k+1}`, indices taken cyclically.

arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS": a sequence of matrix
product states "with bond dimension at most `D`", not translation invariant. -/
structure VaryingBondChain (d D N : ℕ) where
  /-- The dimension of the bond to the left of each site. -/
  bondDim : Fin N → ℕ
  bondDim_le : ∀ k, bondDim k ≤ D
  /-- The rectangular matrix of a site and a physical index. -/
  tensor : ∀ k : Fin N, Fin d → Matrix (Fin (bondDim k)) (Fin (bondDim (finRotate N k))) ℂ

namespace VaryingBondChain

variable {d D N M : ℕ}

/-- The coefficient `Tr(A_0^{s_0} ⋯ A_{N-1}^{s_{N-1}})` of the state of the chain, written as the
sum over the cyclic bond configurations `α` of `∏ₖ (A_k^{s_k})_{α_k α_{k+1}}`. -/
def coeff (A : VaryingBondChain d D N) (s : Fin N → Fin d) : ℂ :=
  ∑ α : (k : Fin N) → Fin (A.bondDim k), ∏ k, A.tensor k (s k) (α k) (α (finRotate N k))

/-- The state `|φ_N⟩ = ∑_s Tr(A_0^{s_0} ⋯ A_{N-1}^{s_{N-1}}) |s⟩` of the chain. -/
noncomputable def state (A : VaryingBondChain d D N) : MPVSpace d N :=
  (EuclideanSpace.equiv (ι := Cfg d N) (𝕜 := ℂ)).symm fun s => coeff A s

@[simp] theorem state_apply (A : VaryingBondChain d D N) (s : Cfg d N) :
    state A s = coeff A s := by
  simp [state, EuclideanSpace.equiv, PiLp.toLp_apply]

/-- **Zero padding**: every matrix `A_k^i` of size `D_k × D_{k+1}` is extended by zeros to a
`D × D` matrix, giving a chain with the common bond dimension `D`. -/
def zeroPad (A : VaryingBondChain d D N) : MPSChainTensor d D N :=
  fun k i a b =>
    if ha : a.val < A.bondDim k then
      if hb : b.val < A.bondDim (finRotate N k) then A.tensor k i ⟨a.val, ha⟩ ⟨b.val, hb⟩ else 0
    else 0

/-- An entry of a padded matrix outside the rectangle `[0, D_k) × [0, D_{k+1})` vanishes. -/
theorem zeroPad_eq_zero (A : VaryingBondChain d D N) {k : Fin N} {i : Fin d} {a b : Fin D}
    (h : ¬(a.val < A.bondDim k ∧ b.val < A.bondDim (finRotate N k))) : zeroPad A k i a b = 0 := by
  unfold zeroPad
  split_ifs with ha hb
  · exact absurd ⟨ha, hb⟩ h
  · rfl
  · rfl

/-- **Zero padding preserves the state**: on a ring of `N ≥ 1` sites the padded chain has the
coefficients `Tr(A_0^{s_0} ⋯ A_{N-1}^{s_{N-1}})` of the chain. -/
theorem coeff_zeroPad [NeZero N] (A : VaryingBondChain d D N) (s : Fin N → Fin d) :
    MPSChainTensor.coeff (zeroPad A) s = coeff A s := by
  classical
  rw [MPSChainTensor.coeff_eq_sum_cyclic]
  have hrot : ∀ k : Fin N, k + 1 = finRotate N k := fun k => by
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, (Nat.succ_pred_eq_of_ne_zero (NeZero.ne N)).symm⟩
    exact (finRotate_apply k).symm
  simp_rw [hrot]
  let e : ((k : Fin N) → Fin (A.bondDim k)) → Fin N → Fin D :=
    fun α k => ⟨(α k).val, lt_of_lt_of_le (α k).isLt (A.bondDim_le k)⟩
  have he : Function.Injective e := fun α α' h => funext fun k =>
    Fin.ext (by simpa [e] using congrArg Fin.val (congrFun h k))
  refine (Fintype.sum_of_injective e he _ _ (fun g hg => ?_) fun α => ?_).symm
  · have hk : ∃ k, ¬(g k).val < A.bondDim k := by
      by_contra hall
      push Not at hall
      exact hg ⟨fun k => ⟨(g k).val, hall k⟩, funext fun k => Fin.ext rfl⟩
    obtain ⟨k, hk⟩ := hk
    exact Finset.prod_eq_zero (Finset.mem_univ k) (zeroPad_eq_zero A fun h => hk h.1)
  · refine Finset.prod_congr rfl fun k _ => ?_
    simp only [zeroPad, e]
    rw [dite_eq_left (α k).isLt, dite_eq_left (α (finRotate N k)).isLt]

/-- The state of the chain is the state of the padded chain. -/
theorem state_eq_chainState_zeroPad [NeZero N] (A : VaryingBondChain d D N) (s : Cfg d N) :
    state A s = MPSChainTensor.coeff (zeroPad A) s := by
  rw [state_apply, coeff_zeroPad]

/-! ### Blocks -/

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

/-- A product of `n + 1` matrices whose factor `j` is supported on `[0, b_j) × [0, b_{j+1})` is
supported on `[0, b_0) × [0, b_{n+1})`. -/
theorem eval_eq_zero_of_support {n : ℕ} (C : MPSChainTensor d D (n + 1)) (b : Fin (n + 2) → ℕ)
    (hC : ∀ j i (α β : Fin D), ¬(α.val < b j.castSucc ∧ β.val < b j.succ) → C j i α β = 0)
    (σ : Fin (n + 1) → Fin d) {α β : Fin D} (h : ¬(α.val < b 0 ∧ β.val < b (Fin.last (n + 1)))) :
    MPSChainTensor.eval C σ α β = 0 := by
  rcases not_and_or.mp h with hα | hβ
  · rw [MPSChainTensor.eval_succ, Matrix.mul_apply]
    exact Finset.sum_eq_zero fun γ _ => by
      rw [hC 0 _ α γ fun h' => hα h'.1, zero_mul]
  · rw [MPSChainTensor.eval_succ', Matrix.mul_apply]
    refine Finset.sum_eq_zero fun γ _ => ?_
    rw [hC (Fin.last n) _ γ β fun h' => hβ (by simpa using h'.2), mul_zero]

/-- The cyclic successor of a site is its index plus one modulo `N`. -/
theorem finRotate_val_eq_mod (i : Fin N) : (finRotate N i).val = (i.val + 1) % N := by
  rw [finRotate_val]
  split_ifs with h
  · rw [h, Nat.mod_self]
  · exact (Nat.mod_eq_of_lt (by have := i.isLt; omega)).symm

/-- The site after the last site of block `k` starts block `k + 1`, cyclically:
`o_k + ℓ_k ≡ o_{k+1} (mod N)`. -/
theorem blockOffset_add_mod {ℓ : Fin M → ℕ} (hN : ∑ k, ℓ k = N) (k : Fin M) :
    (blockOffset ℓ k.val + ℓ k) % N = blockOffset ℓ (finRotate M k).val % N := by
  rw [← blockOffset_succ, finRotate_val]
  split_ifs with hkM
  · rw [hkM, blockOffset_of_le ℓ le_rfl, hN, Nat.mod_self, blockOffset_zero, Nat.zero_mod]
  · rfl

/-- A blocked tensor of a chain of `q ≥ 1` sites whose site `j` is supported on
`[0, b_j) × [0, b_{j+1})` is supported on `[0, b_0) × [0, b_q)`. -/
theorem blockTensor_eq_zero_of_support {q : ℕ} (C : MPSChainTensor d D q) (hq : 0 < q)
    (b : Fin (q + 1) → ℕ)
    (hC : ∀ j i (α β : Fin D), ¬(α.val < b j.castSucc ∧ β.val < b j.succ) → C j i α β = 0)
    (t : Fin (blockPhysDim d q)) {α β : Fin D} (h : ¬(α.val < b 0 ∧ β.val < b (Fin.last q))) :
    MPSChainTensor.blockTensor C t α β = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  exact eval_eq_zero_of_support C b hC _ h

/-- **The blocked tensor of a padded chain is supported on the rectangle of the block**
`[0, D_{o_k}) × [0, D_{o_{k+1}})`, for a block of length at least one. -/
theorem chainBlockTensor_zeroPad_eq_zero [NeZero N] (A : VaryingBondChain d D N)
    {ℓ : Fin M → ℕ} (hN : ∑ k, ℓ k = N) {k : Fin M} (hk : 0 < ℓ k)
    (t : Fin (blockPhysDim d (ℓ k))) {p : Fin D × Fin D} (hp : p ∉ blockCorner A ℓ k) :
    chainBlockTensor (zeroPad A) hN k t p.1 p.2 = 0 := by
  have hNpos := Nat.pos_of_ne_zero (NeZero.ne N)
  let b : Fin (ℓ k + 1) → ℕ := fun j =>
    A.bondDim ⟨(blockOffset ℓ k.val + j.val) % N, Nat.mod_lt _ hNpos⟩
  refine blockTensor_eq_zero_of_support _ hk b (fun j i α β h => zeroPad_eq_zero A ?_) t ?_
  · have h1 : A.bondDim (blockSite hN k j) = b j.castSucc := congrArg A.bondDim (Fin.ext (by
      simp [Nat.mod_eq_of_lt (blockOffset_add_lt hN k j)]))
    have h2 : A.bondDim (finRotate N (blockSite hN k j)) = b j.succ :=
      congrArg A.bondDim (Fin.ext (by rw [finRotate_val_eq_mod]; simp [add_assoc]))
    rwa [h1, h2]
  · have h0 : b 0 = leftBond A ℓ k := rfl
    have hl : b (Fin.last (ℓ k)) = rightBond A ℓ k :=
      congrArg A.bondDim (Fin.ext (by simpa using blockOffset_add_mod hN k))
    rw [h0, hl]
    exact hp

/-- **Injectivity of the blocked tensors** of a chain with bond dimensions at most `D`: for every
block `k`, the matrices of the blocked tensor, of size `D_{o_k} × D_{o_{k+1}}`, span all matrices
of that size. In terms of the padded chain, the padded blocked matrices span every matrix unit
`|α⟩⟨β|` with `α < D_{o_k}` and `β < D_{o_{k+1}}`.

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

/-! ### Pairs on the bonds between blocks -/

/-- A vector on `ℂ^r ⊗ ℂ^r`, padded with zeros to a vector on `ℂ^D ⊗ ℂ^D`. -/
def padPair {r : ℕ} (D : ℕ) (ω : Fin r × Fin r → ℂ) : Fin D × Fin D → ℂ :=
  fun p => if h : p.1.val < r ∧ p.2.val < r then ω (⟨p.1.val, h.1⟩, ⟨p.2.val, h.2⟩) else 0

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
    simp [padPair, this]
  · simp [padPair, e]

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
    exact hne j (by rw [padPairs, padPair, dite_eq_right h])
  have h1 := (hsupp ((finRotate M).symm k)).2
  simp only [rightBond, Equiv.apply_symm_apply] at h1
  exact ⟨h1, (hsupp k).1⟩

end VaryingBondChain

end MPSPreparation
