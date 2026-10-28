/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.Reduction.IrreducibleTensor
import TNLean.MPS.Symmetry.MPOSymmetry.ZipperUniqueness

/-!
# Uniqueness of split multi-block reductions

A multi-block reduction `P` of a tensor `B` onto blocks `C s`, `s ∈ S`, is *split* when its
transitions vanish: in the block coordinates every letter is block diagonal,
$$g B^i g^{-1} = \bigoplus_b \hat B^i_{bb},$$
with `C s` on the slot `s` and the `1 × 1` zero matrix on each zero slot. Equivalently the
remainder $B^i - \sum_s V_s C_s^i W_s$ vanishes, which is the zipper condition.

For two split reductions `P` and `Q` of the same tensor onto the same family, with coordinate
changes `g` and `g̃`, the relative gauge $h = \tilde g g^{-1}$ intertwines the two block diagonal
tensors, so its block $h_{b'b}$ intertwines the diagonal block at `b` with the diagonal block at
`b'`. For normal blocks this block vanishes unless the two blocks are gauge related, and it is a
scalar multiple of a fixed intertwiner when they are; it also vanishes between a block slot and a
zero slot. When no two blocks of the family are gauge related, the reading maps and injections of
the two reductions agree up to one nonzero scalar per block,
$$\widetilde W_s = \lambda_s W_s,\qquad \widetilde V_s = \lambda_s^{-1} V_s,$$
as matrices, with no words attached.

This is lecture note MultiBlockUniqueness, Proposition 5.11 (Uniqueness of split reductions),
in its bare form for the multi-block reductions of Section 1 of that note.

## Main definitions

* `MPSTensor.blockEntry`: the block $X_{b'b}$ of a matrix between two graded coordinate spaces.
* `MPSTensor.MultiBlockCompression.relativeGauge`: the relative gauge $h = \tilde g g^{-1}$ of
  two reductions.
* `MPSTensor.MultiBlockCompression.splitScalar`: the scalar $\lambda_s$ of a block slot.

## Main statements

* `MPSTensor.MultiBlockCompression.remainder_eq_zero_iff_conjMatrix_eq_blockDiagonal'`: a
  reduction is split exactly when every letter is block diagonal in its coordinates.
* `MPSTensor.MultiBlockCompression.blockEntry_intertwines`: the blocks of the relative gauge of
  two split reductions intertwine the diagonal blocks.
* `MPSTensor.MultiBlockCompression.blockEntry_eq_zero_of_not_isGaugeRelated`,
  `MPSTensor.MultiBlockCompression.blockEntry_inl_inr_eq_zero`,
  `MPSTensor.MultiBlockCompression.blockEntry_inr_inl_eq_zero`: the blocks vanish between blocks
  that are not gauge related and between a block slot and a zero slot.
* `MPSTensor.MultiBlockCompression.exists_blockEntry_eq_smul_of_intertwines`: between gauge
  related blocks the block is a scalar multiple of a fixed intertwiner.
* `MPSTensor.MultiBlockCompression.left_eq_smul_of_split_of_pairwise_not_isGaugeRelated`,
  `MPSTensor.MultiBlockCompression.right_eq_smul_of_split_of_pairwise_not_isGaugeRelated`:
  without repeated blocks, $\widetilde W_s = \lambda_s W_s$ and
  $\widetilde V_s = \lambda_s^{-1} V_s$.
* `MPSTensor.MultiBlockCompression.range_rightCol_le_iSup_range_rightCol`: with repeated blocks
  allowed, the range of `V_b` lies in the sum of the ranges of the `Ṽ_{b'}` over the slots `b'`
  gauge equivalent to `b` (lecture note AsymmetricFT, Proposition 6.12).
-/

open scoped Matrix

namespace Matrix

variable {o : Type*} [Fintype o] [DecidableEq o] {n : o → ℕ}

/-- The coordinate blocks resolve the identity: `∑ k, blockEmbed n k * blockProj n k = 1`. -/
theorem sum_blockEmbed_mul_blockProj : ∑ k, blockEmbed n k * blockProj n k = 1 := by
  have h := sum_blockEmbed_mul_mul_blockProj (n := n) fun _ => 1
  simp only [Matrix.mul_one] at h
  rw [h]
  exact blockDiagonal'_one

/-- A block diagonal matrix maps the `k`-th coordinate block into itself by its `k`-th block. -/
theorem blockDiagonal'_mul_blockEmbed (M : ∀ k, Matrix (Fin (n k)) (Fin (n k)) ℂ) (k : o) :
    blockDiagonal' M * blockEmbed n k = blockEmbed n k * M k := by
  rw [← sum_blockEmbed_mul_mul_blockProj, Matrix.sum_mul, Finset.sum_eq_single k]
  · rw [Matrix.mul_assoc, blockProj_mul_blockEmbed_self, Matrix.mul_one]
  · intro l _ hl
    rw [Matrix.mul_assoc, blockProj_mul_blockEmbed_of_ne hl, Matrix.mul_zero]
  · simp

/-- The `k`-th coordinate projection of a block diagonal matrix is its `k`-th block. -/
theorem blockProj_mul_blockDiagonal' (M : ∀ k, Matrix (Fin (n k)) (Fin (n k)) ℂ) (k : o) :
    blockProj n k * blockDiagonal' M = M k * blockProj n k := by
  rw [← sum_blockEmbed_mul_mul_blockProj, Matrix.mul_sum, Finset.sum_eq_single k]
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, blockProj_mul_blockEmbed_self, Matrix.one_mul]
  · intro l _ hl
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, blockProj_mul_blockEmbed_of_ne (Ne.symm hl),
      Matrix.zero_mul, Matrix.zero_mul]
  · simp

end Matrix

namespace MPSTensor

variable {d DB : ℕ}

/-! ### Intertwiners against a zero block -/

/-- A matrix annihilated on the left by every letter of a normal tensor is zero: the words of a
fixed positive length span the full matrix algebra, which contains the identity. -/
theorem eq_zero_of_isNormal_of_forall_letter_mul_eq_zero {D m : ℕ} {A : MPSTensor d D}
    (hA : Kraus.IsNormal A) {E : Matrix (Fin D) (Fin m) ℂ} (hE : ∀ i, A i * E = 0) : E = 0 := by
  obtain ⟨N, hN0, hN⟩ := hA
  let f : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin m) ℂ :=
    { toFun := fun M => M * E
      map_add' := fun M M' => Matrix.add_mul M M' E
      map_smul' := fun c M => by simp [Matrix.smul_mul] }
  have hle : Kraus.wordSpan A N ≤ LinearMap.ker f := by
    refine Submodule.span_le.2 (Set.range_subset_iff.2 fun σ => ?_)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hN0.ne'
    change Kraus.evalWord A (List.ofFn σ) * E = 0
    rw [Kraus.evalWord_intertwine A (fun _ => (0 : Matrix (Fin m) (Fin m) ℂ)) E
      (fun i => by rw [hE i, Matrix.mul_zero]), List.ofFn_succ, Kraus.evalWord_cons,
      Matrix.zero_mul, Matrix.mul_zero]
  rw [hN] at hle
  have h1 := LinearMap.mem_ker.1 (hle (Submodule.mem_top (x := 1)))
  change (1 : Matrix (Fin D) (Fin D) ℂ) * E = 0 at h1
  rwa [Matrix.one_mul] at h1

/-- A matrix annihilated on the right by every letter of a normal tensor is zero. -/
theorem eq_zero_of_isNormal_of_forall_mul_letter_eq_zero {D m : ℕ} {A : MPSTensor d D}
    (hA : Kraus.IsNormal A) {E : Matrix (Fin m) (Fin D) ℂ} (hE : ∀ i, E * A i = 0) : E = 0 := by
  obtain ⟨N, hN0, hN⟩ := hA
  let f : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin D) ℂ :=
    { toFun := fun M => E * M
      map_add' := fun M M' => Matrix.mul_add E M M'
      map_smul' := fun c M => by simp [Matrix.mul_smul] }
  have hle : Kraus.wordSpan A N ≤ LinearMap.ker f := by
    refine Submodule.span_le.2 (Set.range_subset_iff.2 fun σ => ?_)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hN0.ne'
    change E * Kraus.evalWord A (List.ofFn σ) = 0
    rw [List.ofFn_succ, Kraus.evalWord_cons, ← Matrix.mul_assoc, hE, Matrix.zero_mul]
  rw [hN] at hle
  have h1 := LinearMap.mem_ker.1 (hle (Submodule.mem_top (x := 1)))
  change E * (1 : Matrix (Fin D) (Fin D) ℂ) = 0 at h1
  rwa [Matrix.mul_one] at h1

/-! ### Blocks of a matrix between graded coordinate spaces -/

variable {ι : Type*} {D : ι → ℕ} [DecidableEq ι] {S : Finset ι} {C : ∀ s, MPSTensor d (D s)}

/-- The block $X_{b'b}$ of a matrix `X` from the graded coordinate space with `z` zero slots to
the one with `z'` zero slots: its rows at the coordinates of `b'` and its columns at those of
`b`. -/
def blockEntry {z z' : ℕ} (X : Matrix (BlockSpace D S z') (BlockSpace D S z) ℂ)
    (b' : BlockIndex S z') (b : BlockIndex S z) :
    Matrix (Fin (slotSize D b')) (Fin (slotSize D b)) ℂ :=
  Matrix.blockProj (slotSize D) b' * X * Matrix.blockEmbed (slotSize D) b

variable {z z' : ℕ}

/-- The rows of `X` at the slot `b'`, expanded over its blocks. -/
theorem blockProj_mul_eq_sum (X : Matrix (BlockSpace D S z') (BlockSpace D S z) ℂ)
    (b' : BlockIndex S z') :
    Matrix.blockProj (slotSize D) b' * X =
      ∑ b, blockEntry X b' b * Matrix.blockProj (slotSize D) b := by
  simp only [blockEntry, Matrix.mul_assoc, ← Matrix.mul_sum]
  rw [Matrix.sum_blockEmbed_mul_blockProj, Matrix.mul_one]

/-- The columns of `X` at the slot `b`, expanded over its blocks. -/
theorem mul_blockEmbed_eq_sum (X : Matrix (BlockSpace D S z') (BlockSpace D S z) ℂ)
    (b : BlockIndex S z) :
    X * Matrix.blockEmbed (slotSize D) b =
      ∑ b', Matrix.blockEmbed (slotSize D) b' * blockEntry X b' b := by
  simp only [blockEntry, ← Matrix.mul_assoc, ← Matrix.sum_mul]
  rw [Matrix.sum_blockEmbed_mul_blockProj, Matrix.one_mul]

/-- If the row of `X` at the block slot `s` has no nonzero block off the column of `s`, then its
rows at `s` are its diagonal block at `s` applied to the coordinates of `s`. -/
theorem blockProj_mul_eq_of_blockEntry_eq_zero
    (X : Matrix (BlockSpace D S z') (BlockSpace D S z) ℂ) (s : {s // s ∈ S})
    (h0 : ∀ b : BlockIndex S z, b ≠ Sum.inl s → blockEntry X (Sum.inl s) b = 0) :
    Matrix.blockProj (slotSize D) (Sum.inl s : BlockIndex S z') * X =
      blockEntry X (Sum.inl s) (Sum.inl s) *
        Matrix.blockProj (slotSize D) (Sum.inl s : BlockIndex S z) := by
  rw [blockProj_mul_eq_sum, Finset.sum_eq_single (Sum.inl s)]
  · intro b _ hb
    rw [h0 b hb, Matrix.zero_mul]
  · simp

/-- If the column of `X` at the block slot `s` has no nonzero block off the row of `s`, then its
columns at `s` are the coordinates of `s` composed with its diagonal block at `s`. -/
theorem mul_blockEmbed_eq_of_blockEntry_eq_zero
    (X : Matrix (BlockSpace D S z') (BlockSpace D S z) ℂ) (s : {s // s ∈ S})
    (h0 : ∀ b' : BlockIndex S z', b' ≠ Sum.inl s → blockEntry X b' (Sum.inl s) = 0) :
    X * Matrix.blockEmbed (slotSize D) (Sum.inl s : BlockIndex S z) =
      Matrix.blockEmbed (slotSize D) (Sum.inl s : BlockIndex S z') *
        blockEntry X (Sum.inl s) (Sum.inl s) := by
  rw [mul_blockEmbed_eq_sum, Finset.sum_eq_single (Sum.inl s)]
  · intro b' _ hb'
    rw [h0 b' hb', Matrix.mul_zero]
  · simp

/-- A matrix intertwining two block diagonal matrices has blocks intertwining their diagonal
blocks: if `X * blockDiagonal' M = blockDiagonal' M' * X`, then
`X_{b'b} * M b = M' b' * X_{b'b}`. -/
theorem blockEntry_mul_eq_of_mul_blockDiagonal'
    {X : Matrix (BlockSpace D S z') (BlockSpace D S z) ℂ}
    {M : ∀ b : BlockIndex S z, Matrix (Fin (slotSize D b)) (Fin (slotSize D b)) ℂ}
    {M' : ∀ b : BlockIndex S z', Matrix (Fin (slotSize D b)) (Fin (slotSize D b)) ℂ}
    (hX : X * Matrix.blockDiagonal' M = Matrix.blockDiagonal' M' * X)
    (b' : BlockIndex S z') (b : BlockIndex S z) :
    blockEntry X b' b * M b = M' b' * blockEntry X b' b := by
  calc blockEntry X b' b * M b
      = Matrix.blockProj (slotSize D) b' * (X * Matrix.blockDiagonal' M) *
          Matrix.blockEmbed (slotSize D) b := by
        simp only [blockEntry, Matrix.mul_assoc, Matrix.blockDiagonal'_mul_blockEmbed]
    _ = Matrix.blockProj (slotSize D) b' * Matrix.blockDiagonal' M' * X *
          Matrix.blockEmbed (slotSize D) b := by
        rw [hX]
        simp only [Matrix.mul_assoc]
    _ = M' b' * blockEntry X b' b := by
        rw [Matrix.blockProj_mul_blockDiagonal']
        simp only [blockEntry, Matrix.mul_assoc]

/-! ### Split reductions and their relative gauge -/

namespace MultiBlockCompression

variable {B : MPSTensor d DB} (P Q : MultiBlockCompression B S C)

/-- **Split reductions** (lecture note MultiBlockUniqueness, Section 5.2). The
remainder of a reduction vanishes exactly when, in its coordinates, every letter is the block
diagonal matrix of the prescribed blocks: `C s` on the slot `s` and `0` on each zero slot. -/
theorem remainder_eq_zero_iff_conjMatrix_eq_blockDiagonal' :
    P.remainder = 0 ↔ ∀ i,
      conjMatrix P.gauge (B i) = Matrix.blockDiagonal' (blockOf (S := S) (z := P.z) D C i) := by
  have key : ∀ i, Matrix.blockDiagonal' (conjMatrix P.gauge (B i)).blockDiag' =
      Matrix.blockDiagonal' (blockOf (S := S) (z := P.z) D C i) :=
    fun i => congrArg _ (funext (P.blockDiag'_conjMatrix i))
  constructor
  · intro h i
    have hr := P.conjMatrix_remainder i
    rw [h, Pi.zero_apply, conjMatrix_zero, key, eq_comm, sub_eq_zero] at hr
    exact hr
  · intro h
    funext i
    apply conjMatrix_injective P.gauge
    rw [P.conjMatrix_remainder i, key, h i, sub_self, Pi.zero_apply, conjMatrix_zero]

/-- The **relative gauge** $h = \tilde g g^{-1}$ of two reductions `P` (coordinates `g`) and `Q`
(coordinates `g̃`) of the same tensor (lecture note MultiBlockUniqueness, Proposition 5.11
(Uniqueness of split reductions)). -/
noncomputable def relativeGauge : Matrix (BlockSpace D S Q.z) (BlockSpace D S P.z) ℂ :=
  gaugeMatrix Q.gauge * gaugeMatrixInv P.gauge

/-- The relative gauge intertwines the letters in the two coordinate systems. -/
theorem relativeGauge_mul_conjMatrix (i : Fin d) :
    P.relativeGauge Q * conjMatrix P.gauge (B i) =
      conjMatrix Q.gauge (B i) * P.relativeGauge Q := by
  simp only [relativeGauge, conjMatrix_eq_gaugeMatrix_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (gaugeMatrixInv P.gauge) (gaugeMatrix P.gauge),
    gaugeMatrixInv_mul_gaugeMatrix, Matrix.one_mul,
    ← Matrix.mul_assoc (gaugeMatrixInv Q.gauge) (gaugeMatrix Q.gauge),
    gaugeMatrixInv_mul_gaugeMatrix, Matrix.one_mul]

/-- The coordinate change of `Q` is the relative gauge composed with that of `P`,
$\tilde g = h g$. -/
theorem gaugeMatrix_eq_relativeGauge_mul :
    gaugeMatrix Q.gauge = P.relativeGauge Q * gaugeMatrix P.gauge := by
  rw [relativeGauge, Matrix.mul_assoc, gaugeMatrixInv_mul_gaugeMatrix, Matrix.mul_one]

/-- The inverse coordinate change of `Q` is that of `P` composed with the relative gauge in the
reverse direction, $\tilde g^{-1} = g^{-1} h^{-1}$ with $h^{-1} = g \tilde g^{-1}$. -/
theorem gaugeMatrixInv_eq_mul_relativeGauge :
    gaugeMatrixInv Q.gauge = gaugeMatrixInv P.gauge * Q.relativeGauge P := by
  rw [relativeGauge, ← Matrix.mul_assoc, gaugeMatrixInv_mul_gaugeMatrix, Matrix.one_mul]

/-- The block of the relative gauge between two block slots is the product of the reading map of
`Q` and the injection of `P`, $h_{ts} = \widetilde W_t V_s$. -/
theorem blockEntry_relativeGauge_inl_inl (t s : {s // s ∈ S}) :
    blockEntry (P.relativeGauge Q) (Sum.inl t) (Sum.inl s) = Q.left t * P.right s := by
  simp only [blockEntry, relativeGauge, left, right, Matrix.mul_assoc]

variable {P Q}

/-- **The blocks of the relative gauge intertwine the diagonal blocks** (lecture note
MultiBlockUniqueness, Proposition 5.11 (Uniqueness of split reductions), first step of the
proof). For two split reductions the
block $h_{b'b}$ of $h = \tilde g g^{-1}$ intertwines the diagonal block at `b` with that at `b'`. -/
theorem blockEntry_intertwines (hP : P.remainder = 0) (hQ : Q.remainder = 0) (i : Fin d)
    (b' : BlockIndex S Q.z) (b : BlockIndex S P.z) :
    blockEntry (P.relativeGauge Q) b' b * blockOf D C i b =
      blockOf D C i b' * blockEntry (P.relativeGauge Q) b' b := by
  refine blockEntry_mul_eq_of_mul_blockDiagonal' ?_ b' b
  rw [← (P.remainder_eq_zero_iff_conjMatrix_eq_blockDiagonal').1 hP i,
    ← (Q.remainder_eq_zero_iff_conjMatrix_eq_blockDiagonal').1 hQ i,
    relativeGauge_mul_conjMatrix]

/-- **Blocks that are not gauge related do not mix** (lecture note MultiBlockUniqueness,
Proposition 5.11 (Uniqueness of split reductions), Schur
step). For two split reductions and normal blocks `C t`, `C s` that are
not gauge related, the block $h_{ts}$ of the relative gauge vanishes. -/
theorem blockEntry_eq_zero_of_not_isGaugeRelated (hP : P.remainder = 0) (hQ : Q.remainder = 0)
    {t s : {s // s ∈ S}} (ht : Kraus.IsNormal (C t.1)) (hs : Kraus.IsNormal (C s.1))
    (hts : ¬ IsGaugeRelated (C t.1) (C s.1)) :
    blockEntry (P.relativeGauge Q) (Sum.inl t) (Sum.inl s) = 0 :=
  (eq_zero_or_isGaugeRelated_of_intertwines ht hs
    fun i => (blockEntry_intertwines hP hQ i (Sum.inl t) (Sum.inl s)).symm).resolve_right hts

/-- **A block slot does not mix with a zero slot of the other reduction** (lecture note
MultiBlockUniqueness, Proposition 5.11 (Uniqueness of split
reductions)). The block of the relative gauge from a zero slot of `P`
to a normal block slot of `Q` vanishes: it is a column killed by every letter of the block. -/
theorem blockEntry_inl_inr_eq_zero (hP : P.remainder = 0) (hQ : Q.remainder = 0)
    {s : {s // s ∈ S}} (hs : Kraus.IsNormal (C s.1)) (t : Fin P.z) :
    blockEntry (P.relativeGauge Q) (Sum.inl s) (Sum.inr t) = 0 := by
  refine eq_zero_of_isNormal_of_forall_letter_mul_eq_zero hs fun i => ?_
  have h := blockEntry_intertwines hP hQ i (Sum.inl s) (Sum.inr t)
  change _ * 0 = C s.1 i * _ at h
  rw [Matrix.mul_zero] at h
  exact h.symm

/-- **A zero slot does not mix with a block slot of the other reduction** (lecture note
MultiBlockUniqueness, Proposition 5.11 (Uniqueness of split
reductions)). The block of the relative gauge from a normal block slot
of `P` to a zero slot of `Q` vanishes: it is a row killed by every letter of the block. -/
theorem blockEntry_inr_inl_eq_zero (hP : P.remainder = 0) (hQ : Q.remainder = 0)
    (t : Fin Q.z) {s : {s // s ∈ S}} (hs : Kraus.IsNormal (C s.1)) :
    blockEntry (P.relativeGauge Q) (Sum.inr t) (Sum.inl s) = 0 := by
  refine eq_zero_of_isNormal_of_forall_mul_letter_eq_zero hs fun i => ?_
  have h := blockEntry_intertwines hP hQ i (Sum.inr t) (Sum.inl s)
  change _ * C s.1 i = 0 * _ at h
  rw [Matrix.zero_mul] at h
  exact h

/-- **Between gauge related blocks the relative gauge is a scalar multiple of one intertwiner**
(lecture note MultiBlockUniqueness, Proposition 5.11 (Uniqueness of split reductions), the line of
intertwiners). If an invertible
`Y` intertwines the normal block `C s` with `C t`, `C t i * Y = Y * C s i`, then the block
$h_{ts}$ of the relative gauge of two split reductions is `μ • Y` for a scalar `μ`. -/
theorem exists_blockEntry_eq_smul_of_intertwines (hP : P.remainder = 0) (hQ : Q.remainder = 0)
    {t s : {s // s ∈ S}} (hs : Kraus.IsNormal (C s.1))
    {Y : Matrix (Fin (D t.1)) (Fin (D s.1)) ℂ} {Y' : Matrix (Fin (D s.1)) (Fin (D t.1)) ℂ}
    (hYY' : Y * Y' = 1) (hY'Y : Y' * Y = 1) (hY : ∀ i, C t.1 i * Y = Y * C s.1 i) :
    ∃ μ : ℂ, blockEntry (P.relativeGauge Q) (Sum.inl t) (Sum.inl s) = μ • Y := by
  set E : Matrix (Fin (D t.1)) (Fin (D s.1)) ℂ :=
    blockEntry (P.relativeGauge Q) (Sum.inl t) (Sum.inl s) with hEdef
  have hE : ∀ i, E * C s.1 i = C t.1 i * E := fun i =>
    blockEntry_intertwines hP hQ i (Sum.inl t) (Sum.inl s)
  have hY' : ∀ i, Y' * C t.1 i = C s.1 i * Y' := fun i => by
    calc Y' * C t.1 i = Y' * (C t.1 i * Y) * Y' := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hYY', Matrix.mul_one]
      _ = C s.1 i * Y' := by
          rw [hY, ← Matrix.mul_assoc, hY'Y, Matrix.one_mul]
  obtain ⟨μ, hμ⟩ := hs.eq_smul_one_of_commute (S := Y' * E) fun i => by
    rw [Matrix.mul_assoc, hE, ← Matrix.mul_assoc, hY', Matrix.mul_assoc]
  refine ⟨μ, ?_⟩
  calc E = Y * (Y' * E) := by rw [← Matrix.mul_assoc, hYY', Matrix.one_mul]
    _ = μ • Y := by rw [hμ, Matrix.mul_smul, Matrix.mul_one]

variable (P Q)

/-- The scalar $\lambda_s = \operatorname{tr}(\widetilde W_s V_s)/D_s$ of a block slot, for the
reductions `P` (maps $W$, $V$) and `Q` (maps $\widetilde W$, $\widetilde V$) (lecture note
MultiBlockUniqueness, Proposition 5.11 (Uniqueness of split reductions)). -/
noncomputable def splitScalar (s : {s // s ∈ S}) : ℂ :=
  (D s.1 : ℂ)⁻¹ * (Q.left s * P.right s).trace

variable {P Q}

/-- For split reductions and a normal block, the diagonal block of the relative gauge at a block
slot is the scalar $\lambda_s$: $\widetilde W_s V_s = \lambda_s 1$. -/
theorem left_mul_right_eq_splitScalar_smul (hP : P.remainder = 0) (hQ : Q.remainder = 0)
    {s : {s // s ∈ S}} (hs : Kraus.IsNormal (C s.1)) :
    Q.left s * P.right s = P.splitScalar Q s • 1 := by
  obtain ⟨y, hy⟩ := hs.eq_smul_one_of_commute (S := Q.left s * P.right s) fun i => by
    rw [← blockEntry_relativeGauge_inl_inl]
    exact blockEntry_intertwines hP hQ i (Sum.inl s) (Sum.inl s)
  rcases Nat.eq_zero_or_pos (D s.1) with hD | hD
  · ext a b
    exact absurd a.2 (by omega)
  rw [hy, splitScalar, hy, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul,
    ← mul_assoc, mul_comm _ y, mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hD.ne'), mul_one]

/-- Without repeated blocks, the row of the relative gauge at a block slot has no nonzero block
off its diagonal. -/
theorem blockEntry_relativeGauge_inl_eq_zero (hP : P.remainder = 0) (hQ : Q.remainder = 0)
    (hC : ∀ s ∈ S, Kraus.IsNormal (C s))
    (hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → ¬ IsGaugeRelated (C s) (C t)) (s : {s // s ∈ S}) :
    ∀ b : BlockIndex S P.z, b ≠ Sum.inl s →
      blockEntry (P.relativeGauge Q) (Sum.inl s) b = 0 := by
  rintro (t | t) hb
  · exact blockEntry_eq_zero_of_not_isGaugeRelated hP hQ (hC _ s.2) (hC _ t.2)
      (hsep _ s.2 _ t.2 fun h => hb (congrArg Sum.inl (Subtype.ext h).symm))
  · exact blockEntry_inl_inr_eq_zero hP hQ (hC _ s.2) t

/-- Without repeated blocks, the column of the relative gauge at a block slot has no nonzero
block off its diagonal. -/
theorem blockEntry_relativeGauge_eq_zero_inl (hP : P.remainder = 0) (hQ : Q.remainder = 0)
    (hC : ∀ s ∈ S, Kraus.IsNormal (C s))
    (hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → ¬ IsGaugeRelated (C s) (C t)) (s : {s // s ∈ S}) :
    ∀ b' : BlockIndex S Q.z, b' ≠ Sum.inl s →
      blockEntry (P.relativeGauge Q) b' (Sum.inl s) = 0 := by
  rintro (t | t) hb
  · exact blockEntry_eq_zero_of_not_isGaugeRelated hP hQ (hC _ t.2) (hC _ s.2)
      (hsep _ t.2 _ s.2 fun h => hb (congrArg Sum.inl (Subtype.ext h)))
  · exact blockEntry_inr_inl_eq_zero hP hQ t (hC _ s.2)

/-- **The reading maps of split reductions without repeated blocks** (lecture note
MultiBlockUniqueness, Proposition 5.11 (Uniqueness of split reductions), last
sentence). If no two blocks of the family are gauge
related, then $\widetilde W_s = \lambda_s W_s$ as matrices, with no words attached. -/
theorem left_eq_smul_of_split_of_pairwise_not_isGaugeRelated (hP : P.remainder = 0)
    (hQ : Q.remainder = 0) (hC : ∀ s ∈ S, Kraus.IsNormal (C s))
    (hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → ¬ IsGaugeRelated (C s) (C t)) (s : {s // s ∈ S}) :
    Q.left s = P.splitScalar Q s • P.left s := by
  calc Q.left s = Matrix.blockProj (slotSize D) (Sum.inl s : BlockIndex S Q.z) *
        P.relativeGauge Q * gaugeMatrix P.gauge := by
        rw [left, P.gaugeMatrix_eq_relativeGauge_mul Q, Matrix.mul_assoc]
    _ = (Q.left s * P.right s) * P.left s := by
        rw [blockProj_mul_eq_of_blockEntry_eq_zero _ s
          (blockEntry_relativeGauge_inl_eq_zero hP hQ hC hsep s),
          blockEntry_relativeGauge_inl_inl, Matrix.mul_assoc]
        rfl
    _ = P.splitScalar Q s • P.left s := by
        rw [left_mul_right_eq_splitScalar_smul hP hQ (hC _ s.2), Matrix.smul_mul, Matrix.one_mul]

/-- Without repeated blocks, the injections of two split reductions differ by the scalar of the
reverse comparison, $\widetilde V_s = \lambda'_s V_s$, where $W_s \widetilde V_s = \lambda'_s 1$. -/
theorem right_eq_splitScalar_smul (hP : P.remainder = 0) (hQ : Q.remainder = 0)
    (hC : ∀ s ∈ S, Kraus.IsNormal (C s))
    (hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → ¬ IsGaugeRelated (C s) (C t)) (s : {s // s ∈ S}) :
    Q.right s = Q.splitScalar P s • P.right s := by
  calc Q.right s = gaugeMatrixInv P.gauge * (Q.relativeGauge P *
        Matrix.blockEmbed (slotSize D) (Sum.inl s : BlockIndex S Q.z)) := by
        rw [right, P.gaugeMatrixInv_eq_mul_relativeGauge Q, Matrix.mul_assoc]
    _ = P.right s * (P.left s * Q.right s) := by
        rw [mul_blockEmbed_eq_of_blockEntry_eq_zero _ s
          (blockEntry_relativeGauge_eq_zero_inl hQ hP hC hsep s),
          blockEntry_relativeGauge_inl_inl, ← Matrix.mul_assoc]
        rfl
    _ = Q.splitScalar P s • P.right s := by
        rw [left_mul_right_eq_splitScalar_smul hQ hP (hC _ s.2), Matrix.mul_smul, Matrix.mul_one]

/-- The scalars of the two directions are mutually inverse, $\lambda_s\lambda'_s = 1$, by
biorthogonality of the reading map and the injection of `Q` at `s`. -/
theorem splitScalar_mul_splitScalar (hP : P.remainder = 0) (hQ : Q.remainder = 0)
    (hC : ∀ s ∈ S, Kraus.IsNormal (C s)) (hD : ∀ s ∈ S, 0 < D s)
    (hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → ¬ IsGaugeRelated (C s) (C t)) (s : {s // s ∈ S}) :
    P.splitScalar Q s * Q.splitScalar P s = 1 := by
  have : NeZero (D s.1) := ⟨(hD _ s.2).ne'⟩
  have h := Q.left_mul_right_self s
  rw [left_eq_smul_of_split_of_pairwise_not_isGaugeRelated hP hQ hC hsep s,
    right_eq_splitScalar_smul hP hQ hC hsep s, Matrix.smul_mul, Matrix.mul_smul,
    P.left_mul_right_self s, smul_smul] at h
  exact smul_left_injective ℂ one_ne_zero (h.trans (one_smul ℂ _).symm)

/-- The scalar $\lambda_s$ of a block slot is nonzero. -/
theorem splitScalar_ne_zero (hP : P.remainder = 0) (hQ : Q.remainder = 0)
    (hC : ∀ s ∈ S, Kraus.IsNormal (C s)) (hD : ∀ s ∈ S, 0 < D s)
    (hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → ¬ IsGaugeRelated (C s) (C t)) (s : {s // s ∈ S}) :
    P.splitScalar Q s ≠ 0 :=
  left_ne_zero_of_mul_eq_one (splitScalar_mul_splitScalar hP hQ hC hD hsep s)

/-- **The injections of split reductions without repeated blocks** (lecture note
MultiBlockUniqueness, Proposition 5.11 (Uniqueness of split reductions), last
sentence). If no two blocks of the family are gauge
related, then $\widetilde V_s = \lambda_s^{-1} V_s$ as matrices, with no words attached. -/
theorem right_eq_smul_of_split_of_pairwise_not_isGaugeRelated (hP : P.remainder = 0)
    (hQ : Q.remainder = 0) (hC : ∀ s ∈ S, Kraus.IsNormal (C s)) (hD : ∀ s ∈ S, 0 < D s)
    (hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → ¬ IsGaugeRelated (C s) (C t)) (s : {s // s ∈ S}) :
    Q.right s = (P.splitScalar Q s)⁻¹ • P.right s := by
  rw [right_eq_splitScalar_smul hP hQ hC hsep s,
    ← eq_inv_of_mul_eq_one_right (splitScalar_mul_splitScalar hP hQ hC hD hsep s)]

/-- **Uniqueness of split reductions without repeated blocks** (lecture note
MultiBlockUniqueness, Proposition 5.11 (Uniqueness of split
reductions)). Two split reductions of the same tensor onto the same
family of normal blocks of positive bond dimension, no two of which are gauge related, have
reading maps and injections that agree up to one nonzero scalar per block:
$\widetilde W_s = \lambda_s W_s$ and $\widetilde V_s = \lambda_s^{-1} V_s$. -/
theorem exists_left_eq_smul_and_right_eq_inv_smul_of_split (hP : P.remainder = 0)
    (hQ : Q.remainder = 0) (hC : ∀ s ∈ S, Kraus.IsNormal (C s)) (hD : ∀ s ∈ S, 0 < D s)
    (hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → ¬ IsGaugeRelated (C s) (C t)) :
    ∃ c : {s // s ∈ S} → ℂ, ∀ s, c s ≠ 0 ∧ Q.left s = c s • P.left s ∧
      Q.right s = (c s)⁻¹ • P.right s :=
  ⟨P.splitScalar Q, fun s => ⟨splitScalar_ne_zero hP hQ hC hD hsep s,
    left_eq_smul_of_split_of_pairwise_not_isGaugeRelated hP hQ hC hsep s,
    right_eq_smul_of_split_of_pairwise_not_isGaugeRelated hP hQ hC hD hsep s⟩⟩

/-- **Split reductions, subspace form** (lecture note AsymmetricFT, Proposition 6.12; milestone V,
V2.10). For two split reductions onto the same family of normal blocks of positive bond
dimension, repeated blocks allowed, the range of `V_b` lies in the sum of the ranges of the
`Ṽ_{b'}` over the slots `b'` whose diagonal block is gauge equivalent to that of `b` (zero slots
are gauge equivalent to each other). Indeed `V_b = ∑_{b'} Ṽ_{b'} h_{b'b}` with `h = g̃ g⁻¹`, and
by Schur's lemma `h_{b'b} = 0` unless the two diagonal blocks are gauge equivalent. -/
theorem range_rightCol_le_iSup_range_rightCol (hP : P.remainder = 0) (hQ : Q.remainder = 0)
    (hC : ∀ s ∈ S, Kraus.IsNormal (C s)) (hD : ∀ s ∈ S, 0 < D s) (b : BlockIndex S P.z) :
    LinearMap.range (P.rightCol b).mulVecLin ≤
      ⨆ (b' : BlockIndex S Q.z) (_ : IsGaugeRelated (slotTensor C b) (slotTensor C b')),
        LinearMap.range (Q.rightCol b').mulVecLin := by
  have hirr : ∀ {z : ℕ} (c : BlockIndex S z), Matrix.IsIrreducibleAction (slotTensor C c) :=
    fun c => ((isIrreducibleAction_and_pos_iff_isSimpleModule _).2
      (isSimpleModule_slotTensor hC hD c)).1
  have hV : P.rightCol b = ∑ b', Q.rightCol b' * blockEntry (P.relativeGauge Q) b' b := by
    rw [rightCol, MultiBlockCompression.gaugeMatrixInv_eq_mul_relativeGauge Q P, Matrix.mul_assoc,
      mul_blockEmbed_eq_sum, Matrix.mul_sum]
    simp only [rightCol, Matrix.mul_assoc]
  rintro _ ⟨u, rfl⟩
  rw [Matrix.mulVecLin_apply, hV, Matrix.sum_mulVec]
  refine Submodule.sum_mem _ fun b' _ => ?_
  by_cases hrel : IsGaugeRelated (slotTensor C b) (slotTensor C b')
  · refine Submodule.mem_iSup_of_mem b' (Submodule.mem_iSup_of_mem hrel ?_)
    exact ⟨blockEntry (P.relativeGauge Q) b' b *ᵥ u, by
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]⟩
  · have h0 := eq_zero_of_intertwines_of_not_isGaugeRelated (hirr b) (hirr b')
      (fun i => blockEntry_intertwines hP hQ i b' b) hrel
    rw [h0, Matrix.mul_zero, Matrix.zero_mulVec]
    exact zero_mem _

end MultiBlockCompression

end MPSTensor
