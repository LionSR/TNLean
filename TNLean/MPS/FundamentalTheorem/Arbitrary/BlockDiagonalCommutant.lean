/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixFamilyAction
import TNLean.MPS.FundamentalTheorem.Reduction.AdmissibleBlock
import TNLean.MPS.FundamentalTheorem.Reduction.SplitUniquenessGauge

/-!
# All gauges between completely reducible tensors

Let `Â^i = ⨁_c (1_{m_c} ⊗ C_c^i) ⊕ 0_z` with `C_c` admissible (irreducible, with a nonzero letter)
and pairwise not gauge equivalent. The invertible matrices commuting with every `Â^i` are exactly
`(⨁_c Y_c ⊗ 1_{D_c}) ⊕ Y_0` with `Y_c ∈ GL_{m_c}(ℂ)` and `Y_0 ∈ GL_z(ℂ)`; hence the gauges from a
tensor `B` to `Â` are `Z X₀` for one gauge `X₀` and `Z` in this group.

The statement is formalized for the block diagonal tensor of a family indexed by
`BlockIndex S z` (block slots and zero slots), with repeated gauge classes allowed, and for
rectangular intertwiners `X` between two such forms with `z` and `z'` zero slots. A matrix
intertwines the two block diagonal forms exactly when its block entries vanish between a block and
a zero slot and between blocks that are not gauge equivalent, and are, within a gauge class, the
class coefficients `classCoeff C X s₀` times the chosen intertwiners `Y_{t'} Y_t⁻¹`
(`classIntertwiner`); the entries among the zero slots are free. For `z = z'` such a matrix is
invertible exactly when every class coefficient matrix and the zero-slot block are, and every
choice of these occurs. For intertwiners `X`, `Y` in the two directions with `X Y = 1` the class
coefficient matrices satisfy `μ_X μ_Y = 1` on every gauge class.

## Main definitions

* `MPSTensor.classCoeff`: the class coefficient matrix of a matrix between two block diagonal forms;
  for the relative gauge of two split reductions it is `MultiBlockCompression.classMatrix`.

## Main results

* `MPSTensor.forall_mul_blockDiagonal'_eq_iff`: the intertwiners of the block diagonal form.
* `MPSTensor.isUnit_iff_of_forall_mul_blockDiagonal'_eq`,
  `MPSTensor.exists_forall_mul_blockDiagonal'_eq_and_classCoeff_eq`: invertibility, and every choice
  of class matrices and zero-slot block occurs.
* `MPSTensor.isUnit_and_forall_mul_eq_mul_iff_exists_eq_mul`: the gauges from `B` to `Â` are
  `Z X₀` with `Z` in the commutant of `Â`.
-/

open scoped Matrix

namespace MPSTensor

variable {d : ℕ} {ι : Type*} [DecidableEq ι] {D : ι → ℕ} {S : Finset ι}
  {C : ∀ s, MPSTensor d (D s)} {z z' : ℕ}

omit [DecidableEq ι] in
private theorem self_mem_gaugeClass (s₀ : {s // s ∈ S}) : s₀ ∈ gaugeClass C s₀ :=
  mem_gaugeClass.2 ⟨1, 1, Matrix.mul_one 1, Matrix.mul_one 1, fun i => by
    rw [Matrix.mul_one, Matrix.one_mul]⟩

variable (C) in
/-- **The class coefficients** of a matrix between two block diagonal forms: for `t, t'` in
the gauge class of `s₀`, `(D_{s₀})⁻¹ tr (Y_{t'}⁻¹ X_{t't} Y_t)`, where `Y_t` are the chosen
intertwiners `classIntertwiner`. For the relative gauge of two split reductions this is
`MultiBlockCompression.classMatrix`. -/
noncomputable def classCoeff (X : Matrix (BlockSpace D S z') (BlockSpace D S z) ℂ)
    (s₀ : {s // s ∈ S}) : Matrix (gaugeClass C s₀) (gaugeClass C s₀) ℂ :=
  Matrix.of fun t' t => (D s₀.1 : ℂ)⁻¹ *
    (classIntertwinerInv C s₀ t' * blockEntry X (Sum.inl t'.1) (Sum.inl t.1) *
      classIntertwiner C s₀ t).trace

omit [DecidableEq ι] in
/-- The fixed intertwiners `Y_{t'} Y_t⁻¹` of a gauge class intertwine `C t` with `C t'`. -/
private theorem classIntertwiner_mul_classIntertwinerInv_intertwines (s₀ : {s // s ∈ S})
    (t' t : gaugeClass C s₀) (i : Fin d) :
    classIntertwiner C s₀ t' * classIntertwinerInv C s₀ t * C t.1.1 i =
      C t'.1.1 i * (classIntertwiner C s₀ t' * classIntertwinerInv C s₀ t) := by
  rw [Matrix.mul_assoc, ← mul_classIntertwinerInv, ← Matrix.mul_assoc, ← mul_classIntertwiner,
    Matrix.mul_assoc]

/-- The rows of `N` at the coordinates of a slot. -/
private theorem blockProj_mul_apply {κ : Type*} (N : Matrix (BlockSpace D S z) κ ℂ)
    (b : BlockIndex S z) (p : Fin (slotSize D b)) (k : κ) :
    (Matrix.blockProj (slotSize D) b * N) p k = N ⟨b, p⟩ k := by
  simp [Matrix.mul_apply, Matrix.blockProj, Matrix.blockEmbed]

/-- **No entry from a zero slot to a block**: an intertwiner of the block diagonal forms has
zero block entry from a zero slot to an irreducible block with a nonzero letter. -/
theorem blockEntry_inl_inr_eq_zero_of_mul_blockDiagonal'_eq
    {X : Matrix (BlockSpace D S z') (BlockSpace D S z) ℂ}
    (hX : ∀ i, X * Matrix.blockDiagonal' (blockOf (z := z) D C i) =
      Matrix.blockDiagonal' (blockOf (z := z') D C i) * X)
    (s : {s // s ∈ S}) (hs : ∃ i, C s.1 i ≠ 0) (hirrs : Matrix.IsIrreducibleAction (C s.1))
    (u : Fin z) : blockEntry X (Sum.inl s) (Sum.inr u) = 0 := by
  refine eq_zero_of_forall_apply_mul_eq_zero hirrs hs fun i => ?_
  have h := blockEntry_mul_eq_of_mul_blockDiagonal' (hX i) (Sum.inl s) (Sum.inr u)
  change _ * 0 = C s.1 i * _ at h
  rw [Matrix.mul_zero] at h
  exact h.symm

/-- **No entry from a block to a zero slot**: an intertwiner of the block diagonal forms has
zero block entry from an irreducible block with a nonzero letter to a zero slot. -/
theorem blockEntry_inr_inl_eq_zero_of_mul_blockDiagonal'_eq
    {X : Matrix (BlockSpace D S z') (BlockSpace D S z) ℂ}
    (hX : ∀ i, X * Matrix.blockDiagonal' (blockOf (z := z) D C i) =
      Matrix.blockDiagonal' (blockOf (z := z') D C i) * X)
    (u : Fin z') (s : {s // s ∈ S}) (hs : ∃ i, C s.1 i ≠ 0)
    (hirrs : Matrix.IsIrreducibleAction (C s.1)) : blockEntry X (Sum.inr u) (Sum.inl s) = 0 := by
  refine eq_zero_of_forall_mul_apply_eq_zero hirrs hs fun i => ?_
  have h := blockEntry_mul_eq_of_mul_blockDiagonal' (hX i) (Sum.inr u) (Sum.inl s)
  change _ * C s.1 i = 0 * _ at h
  rw [Matrix.zero_mul] at h
  exact h

/-- **No entry between inequivalent blocks**: an intertwiner of the block diagonal forms has
zero block entry between two irreducible blocks that are not gauge equivalent. -/
theorem blockEntry_inl_inl_eq_zero_of_mul_blockDiagonal'_eq
    {X : Matrix (BlockSpace D S z') (BlockSpace D S z) ℂ}
    (hX : ∀ i, X * Matrix.blockDiagonal' (blockOf (z := z) D C i) =
      Matrix.blockDiagonal' (blockOf (z := z') D C i) * X)
    {t s : {s // s ∈ S}} (ht : Matrix.IsIrreducibleAction (C t.1))
    (hs : Matrix.IsIrreducibleAction (C s.1)) (hts : ¬ IsGaugeRelated (C t.1) (C s.1)) :
    blockEntry X (Sum.inl t) (Sum.inl s) = 0 :=
  eq_zero_of_intertwines_of_not_isGaugeRelated (C := C s.1) (C' := C t.1) hs ht
    (fun i => blockEntry_mul_eq_of_mul_blockDiagonal' (hX i) (Sum.inl t) (Sum.inl s))
    fun h => hts h.symm

/-- **Within a gauge class the entries are class coefficients**: an intertwiner of the block
diagonal forms has block entry `classCoeff C X s₀ t' t • Y_{t'} Y_t⁻¹` between two members of the
gauge class of `s₀`. No nonzero letter is needed (for `D s₀ = 0` both sides are empty matrices). -/
theorem blockEntry_inl_inl_eq_classCoeff_smul_of_mul_blockDiagonal'_eq
    (hirr : ∀ s ∈ S, Matrix.IsIrreducibleAction (C s))
    {X : Matrix (BlockSpace D S z') (BlockSpace D S z) ℂ}
    (hX : ∀ i, X * Matrix.blockDiagonal' (blockOf (z := z) D C i) =
      Matrix.blockDiagonal' (blockOf (z := z') D C i) * X)
    (s₀ : {s // s ∈ S}) (t' t : gaugeClass C s₀) :
    blockEntry X (Sum.inl t'.1) (Sum.inl t.1) =
      classCoeff C X s₀ t' t • (classIntertwiner C s₀ t' * classIntertwinerInv C s₀ t) := by
  set Y' := classIntertwiner C s₀ t'
  set X' := classIntertwinerInv C s₀ t'
  set Y := classIntertwiner C s₀ t
  set Xi := classIntertwinerInv C s₀ t
  set E := blockEntry X (Sum.inl t'.1) (Sum.inl t.1) with hEdef
  have hE : ∀ i, E * C t.1.1 i = C t'.1.1 i * E := fun i =>
    blockEntry_mul_eq_of_mul_blockDiagonal' (hX i) (Sum.inl t'.1) (Sum.inl t.1)
  obtain ⟨ν, hν⟩ := exists_eq_smul_one_of_intertwines (hirr _ s₀.2) (X := X' * E * Y)
    fun i => by
      calc X' * E * Y * C s₀.1 i = X' * (E * (Y * C s₀.1 i)) := by
            simp only [Matrix.mul_assoc]
        _ = X' * (E * C t.1.1 i) * Y := by
            rw [← mul_classIntertwiner]
            simp only [Matrix.mul_assoc, Y]
        _ = C s₀.1 i * X' * E * Y := by
            rw [hE, mul_classIntertwinerInv]
            simp only [Matrix.mul_assoc, X']
        _ = C s₀.1 i * (X' * E * Y) := by simp only [Matrix.mul_assoc]
  have hE' : E = ν • (Y' * Xi) := by
    calc E = Y' * (X' * E * Y) * Xi := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, classIntertwiner_mul_classIntertwinerInv,
            Matrix.one_mul, Matrix.mul_assoc, classIntertwiner_mul_classIntertwinerInv,
            Matrix.mul_one]
      _ = ν • (Y' * Xi) := by rw [hν, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  by_cases hD : D s₀.1 = 0
  · have : IsEmpty (Fin (D s₀.1)) := by rw [hD]; infer_instance
    have h0 : Y' * Xi = 0 := by
      ext a b
      simp [Matrix.mul_apply]
    rw [hE', h0, smul_zero, smul_zero]
  · have hD0 : (D s₀.1 : ℂ) ≠ 0 := by exact_mod_cast hD
    have hμ : classCoeff C X s₀ t' t = ν := by
      rw [classCoeff, Matrix.of_apply, hν, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
        smul_eq_mul, mul_comm, mul_assoc, mul_inv_cancel₀ hD0, mul_one]
    rw [hE', hμ]

/-- **Block entries that intertwine give an intertwiner** (converse direction; no hypothesis
on the blocks): if every block entry intertwines the diagonal blocks of its two slots, the matrix
intertwines the block diagonal forms. -/
theorem mul_blockDiagonal'_eq_of_forall_blockEntry
    {X : Matrix (BlockSpace D S z') (BlockSpace D S z) ℂ}
    (h : ∀ (i : Fin d) (b' : BlockIndex S z') (b : BlockIndex S z),
      blockEntry X b' b * blockOf D C i b = blockOf D C i b' * blockEntry X b' b) :
    ∀ i : Fin d,
      X * Matrix.blockDiagonal' (blockOf (z := z) D C i) =
        Matrix.blockDiagonal' (blockOf (z := z') D C i) * X := by
  intro i
  have key : ∀ b' : BlockIndex S z',
      Matrix.blockProj (slotSize D) b' * (X * Matrix.blockDiagonal' (blockOf (z := z) D C i)) =
        Matrix.blockProj (slotSize D) b' *
          (Matrix.blockDiagonal' (blockOf (z := z') D C i) * X) := by
    intro b'
    have hL : Matrix.blockProj (slotSize D) b' *
        (X * Matrix.blockDiagonal' (blockOf (z := z) D C i)) =
          ∑ b, blockEntry X b' b * blockOf D C i b * Matrix.blockProj (slotSize D) b := by
      rw [← Matrix.mul_assoc, blockProj_mul_eq_sum, Matrix.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Matrix.mul_assoc, Matrix.blockProj_mul_blockDiagonal', Matrix.mul_assoc]
    have hR : Matrix.blockProj (slotSize D) b' *
        (Matrix.blockDiagonal' (blockOf (z := z') D C i) * X) =
          ∑ b, blockOf D C i b' * blockEntry X b' b * Matrix.blockProj (slotSize D) b := by
      rw [← Matrix.mul_assoc, Matrix.blockProj_mul_blockDiagonal',
        Matrix.mul_assoc (blockOf D C i b'), blockProj_mul_eq_sum, Matrix.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Matrix.mul_assoc]
    rw [hL, hR]
    exact Finset.sum_congr rfl fun b _ => by rw [h i b' b]
  calc X * Matrix.blockDiagonal' (blockOf (z := z) D C i)
      = (∑ b', Matrix.blockEmbed (slotSize D) b' * Matrix.blockProj (slotSize D) b') *
          (X * Matrix.blockDiagonal' (blockOf (z := z) D C i)) := by
        rw [Matrix.sum_blockEmbed_mul_blockProj, Matrix.one_mul]
    _ = (∑ b', Matrix.blockEmbed (slotSize D) b' * Matrix.blockProj (slotSize D) b') *
          (Matrix.blockDiagonal' (blockOf (z := z') D C i) * X) := by
        simp only [Matrix.sum_mul, Matrix.mul_assoc, key]
    _ = _ := by rw [Matrix.sum_blockEmbed_mul_blockProj, Matrix.one_mul]

/-- **The intertwiners of the block diagonal form**: for admissible
blocks, a matrix intertwines the two block diagonal forms exactly when its block entries vanish
between a block and a zero slot and between inequivalent blocks, and are, within a gauge class, the
class coefficients times the fixed intertwiners `Y_{t'} Y_t⁻¹`. -/
theorem forall_mul_blockDiagonal'_eq_iff (hirr : ∀ s ∈ S, Matrix.IsIrreducibleAction (C s))
    (hlet : ∀ s ∈ S, ∃ i, C s i ≠ 0) {X : Matrix (BlockSpace D S z') (BlockSpace D S z) ℂ} :
    (∀ i : Fin d, X * Matrix.blockDiagonal' (blockOf (z := z) D C i) =
        Matrix.blockDiagonal' (blockOf (z := z') D C i) * X) ↔
      (∀ (s : {s // s ∈ S}) (u : Fin z), blockEntry X (Sum.inl s) (Sum.inr u) = 0) ∧
      (∀ (u : Fin z') (s : {s // s ∈ S}), blockEntry X (Sum.inr u) (Sum.inl s) = 0) ∧
      (∀ t s : {s // s ∈ S}, ¬ IsGaugeRelated (C t.1) (C s.1) →
        blockEntry X (Sum.inl t) (Sum.inl s) = 0) ∧
      ∀ (s₀ : {s // s ∈ S}) (t' t : gaugeClass C s₀),
        blockEntry X (Sum.inl t'.1) (Sum.inl t.1) =
          classCoeff C X s₀ t' t • (classIntertwiner C s₀ t' * classIntertwinerInv C s₀ t) := by
  constructor
  · intro hX
    exact ⟨fun s u => blockEntry_inl_inr_eq_zero_of_mul_blockDiagonal'_eq hX s (hlet _ s.2)
        (hirr _ s.2) u,
      fun u s => blockEntry_inr_inl_eq_zero_of_mul_blockDiagonal'_eq hX u s (hlet _ s.2)
        (hirr _ s.2),
      fun t s hts => blockEntry_inl_inl_eq_zero_of_mul_blockDiagonal'_eq hX (hirr _ t.2)
        (hirr _ s.2) hts,
      fun s₀ t' t => blockEntry_inl_inl_eq_classCoeff_smul_of_mul_blockDiagonal'_eq hirr hX s₀ t' t⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine mul_blockDiagonal'_eq_of_forall_blockEntry fun i b' b => ?_
    rcases b' with t' | u' <;> rcases b with t | u
    · by_cases hg : IsGaugeRelated (C t'.1) (C t.1)
      · have h4' : blockEntry X (Sum.inl t') (Sum.inl t) =
            classCoeff C X t' ⟨t', self_mem_gaugeClass t'⟩ ⟨t, mem_gaugeClass.2 hg⟩ •
              (classIntertwiner C t' ⟨t', self_mem_gaugeClass t'⟩ *
                classIntertwinerInv C t' ⟨t, mem_gaugeClass.2 hg⟩) :=
          h4 t' ⟨t', self_mem_gaugeClass t'⟩ ⟨t, mem_gaugeClass.2 hg⟩
        rw [h4', Matrix.smul_mul, Matrix.mul_smul]
        exact congrArg _ (classIntertwiner_mul_classIntertwinerInv_intertwines t' _ _ i)
      · rw [h3 t' t hg, Matrix.zero_mul, Matrix.mul_zero]
    · rw [h1 t' u, Matrix.zero_mul, Matrix.mul_zero]
    · rw [h2 u' t, Matrix.zero_mul, Matrix.mul_zero]
    · change _ * 0 = 0 * _
      rw [Matrix.mul_zero, Matrix.zero_mul]

/-- **Class coefficients multiply**: for intertwiners `X` and `Y` in the two directions with
`X Y = 1`, the class coefficient matrices satisfy `μ_X μ_Y = 1` on every gauge class. -/
theorem classCoeff_mul_classCoeff_of_mul_blockDiagonal'_eq
    (hirr : ∀ s ∈ S, Matrix.IsIrreducibleAction (C s)) (hlet : ∀ s ∈ S, ∃ i, C s i ≠ 0)
    {X : Matrix (BlockSpace D S z') (BlockSpace D S z) ℂ}
    (hX : ∀ i, X * Matrix.blockDiagonal' (blockOf (z := z) D C i) =
      Matrix.blockDiagonal' (blockOf (z := z') D C i) * X)
    {Y : Matrix (BlockSpace D S z) (BlockSpace D S z') ℂ}
    (hY : ∀ i : Fin d, Y * Matrix.blockDiagonal' (blockOf (z := z') D C i) =
      Matrix.blockDiagonal' (blockOf (z := z) D C i) * Y)
    (hXY : X * Y = 1) (s₀ : {s // s ∈ S}) : classCoeff C X s₀ * classCoeff C Y s₀ = 1 := by
  have : NeZero (D s₀.1) := ⟨(dim_pos_of_exists_ne_zero (hlet _ s₀.2)).ne'⟩
  ext t' t
  obtain ⟨c, hc⟩ : ∃ c, c = (classCoeff C X s₀ * classCoeff C Y s₀) t' t := ⟨_, rfl⟩
  rw [← hc]
  -- The block of `X Y` at `(t', t)` is `c • Y_{t'} Y_t⁻¹`.
  have key : blockEntry (X * Y) (Sum.inl t'.1) (Sum.inl t.1) =
      c • (classIntertwiner C s₀ t' * classIntertwinerInv C s₀ t) := by
    have hz : ∑ u : Fin z, blockEntry X (Sum.inl t'.1) (Sum.inr u) *
        blockEntry Y (Sum.inr u) (Sum.inl t.1) = 0 :=
      Finset.sum_eq_zero fun u _ => by
        rw [blockEntry_inl_inr_eq_zero_of_mul_blockDiagonal'_eq hX t'.1 (hlet _ t'.1.2)
          (hirr _ t'.1.2) u, Matrix.zero_mul]
    rw [blockEntry_mul, Fintype.sum_sum_type, hz, add_zero,
      ← Finset.sum_subset (Finset.subset_univ (gaugeClass C s₀)) (fun s _ hs => by
        rw [blockEntry_inl_inl_eq_zero_of_mul_blockDiagonal'_eq hX (hirr _ t'.1.2) (hirr _ s.2)
          (fun h => hs (mem_gaugeClass.2 ((mem_gaugeClass.1 t'.2).trans h))), Matrix.zero_mul]),
      ← Finset.sum_coe_sort, hc, Matrix.mul_apply, Finset.sum_smul]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [blockEntry_inl_inl_eq_classCoeff_smul_of_mul_blockDiagonal'_eq hirr hX s₀ t' s,
      blockEntry_inl_inl_eq_classCoeff_smul_of_mul_blockDiagonal'_eq hirr hY s₀ s t,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (classIntertwinerInv C s₀ s), classIntertwinerInv_mul_classIntertwiner,
      Matrix.one_mul]
  rw [hXY] at key
  have hconj : classIntertwinerInv C s₀ t' *
      blockEntry (1 : Matrix (BlockSpace D S z') (BlockSpace D S z') ℂ) (Sum.inl t'.1)
        (Sum.inl t.1) * classIntertwiner C s₀ t = c • 1 := by
    rw [key, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc,
      classIntertwinerInv_mul_classIntertwiner, Matrix.one_mul,
      classIntertwinerInv_mul_classIntertwiner]
  by_cases htt : t' = t
  · subst htt
    rw [blockEntry_one_self, Matrix.mul_one, classIntertwinerInv_mul_classIntertwiner] at hconj
    rw [Matrix.one_apply_eq]
    exact smul_left_injective ℂ one_ne_zero (hconj.symm.trans (one_smul ℂ _).symm)
  · have hne : (Sum.inl t'.1 : BlockIndex S z') ≠ Sum.inl t.1 := fun h =>
      htt (Subtype.ext (Sum.inl_injective h))
    rw [blockEntry_one_of_ne hne, Matrix.mul_zero, Matrix.zero_mul] at hconj
    rw [Matrix.one_apply_ne htt]
    exact (smul_eq_zero.1 hconj.symm).resolve_right one_ne_zero

/-- **Zero-slot blocks multiply**: for an intertwiner `X` and any `Y` with `X Y = 1`, the
zero-slot blocks satisfy `X₀ Y₀ = 1`. Only the blocks of positive size need a nonzero letter. -/
theorem zeroSlotBlock_mul_zeroSlotBlock_of_mul_blockDiagonal'_eq
    (hirr : ∀ s ∈ S, Matrix.IsIrreducibleAction (C s))
    (hlet₀ : ∀ s ∈ S, 0 < D s → ∃ i, C s i ≠ 0)
    {X : Matrix (BlockSpace D S z') (BlockSpace D S z) ℂ}
    (hX : ∀ i, X * Matrix.blockDiagonal' (blockOf (z := z) D C i) =
      Matrix.blockDiagonal' (blockOf (z := z') D C i) * X)
    {Y : Matrix (BlockSpace D S z) (BlockSpace D S z') ℂ}
    (hXY : X * Y = 1) : zeroSlotBlock X * zeroSlotBlock Y = 1 := by
  have h0 : ∀ (u : Fin z') (s : {s // s ∈ S}), blockEntry X (Sum.inr u) (Sum.inl s) = 0 := by
    intro u s
    rcases Nat.eq_zero_or_pos (D s.1) with hD | hD
    · ext a b
      exact absurd b.2 (by change ¬ (b : ℕ) < D s.1; omega)
    · exact blockEntry_inr_inl_eq_zero_of_mul_blockDiagonal'_eq hX u s (hlet₀ _ s.2 hD)
        (hirr _ s.2)
  rw [← zeroSlotBlock_mul _ _ h0, hXY, zeroSlotBlock_one]

/-- The kernel of an intertwiner of the block diagonal form is trivial when its zero-slot block is
invertible and every block slot lies in a gauge class with invertible class coefficients. -/
private theorem eq_zero_of_mul_eq_zero_of_isUnit_classCoeff
    (hirr : ∀ s ∈ S, Matrix.IsIrreducibleAction (C s)) (hlet : ∀ s ∈ S, ∃ i, C s i ≠ 0)
    {X : Matrix (BlockSpace D S z) (BlockSpace D S z) ℂ}
    (hX : ∀ i : Fin d, X * Matrix.blockDiagonal' (blockOf D C i) =
      Matrix.blockDiagonal' (blockOf D C i) * X)
    (hcl : ∀ t : {s // s ∈ S}, ∃ s₀, t ∈ gaugeClass C s₀ ∧ IsUnit (classCoeff C X s₀))
    (h0 : IsUnit (zeroSlotBlock X)) {κ : Type*} {N : Matrix (BlockSpace D S z) κ ℂ}
    (hXN : X * N = 0) : N = 0 := by
  have hrow : ∀ b' : BlockIndex S z,
      ∑ b, blockEntry X b' b * (Matrix.blockProj (slotSize D) b * N) = 0 := by
    intro b'
    calc ∑ b, blockEntry X b' b * (Matrix.blockProj (slotSize D) b * N)
        = Matrix.blockProj (slotSize D) b' * X * N := by
          rw [blockProj_mul_eq_sum, Matrix.sum_mul]
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [Matrix.mul_assoc, hXN, Matrix.mul_zero]
  -- the zero slots
  have hzero : ∀ (u : Fin z) (k : κ), N ⟨Sum.inr u, 0⟩ k = 0 := by
    intro u k
    have hw : (fun u : Fin z => N ⟨Sum.inr u, 0⟩ k) = 0 := by
      refine Matrix.mulVec_injective_iff_isUnit.2 h0 ?_
      rw [Matrix.mulVec_zero]
      funext u'
      have h00 : ∀ (s : {s // s ∈ S}) (p : Fin (D s.1)),
          X ⟨Sum.inr u', 0⟩ ⟨Sum.inl s, p⟩ = 0 := fun s p => by
        rw [← blockEntry_apply X (Sum.inr u') (Sum.inl s) 0 p,
          blockEntry_inr_inl_eq_zero_of_mul_blockDiagonal'_eq hX u' s (hlet _ s.2) (hirr _ s.2)]
        rfl
      have h := congrFun (congrFun hXN ⟨Sum.inr u', 0⟩) k
      simpa [zeroSlotBlock, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fintype.sum_sigma,
        Fintype.sum_sum_type, h00] using h
    exact congrFun hw u
  have hzero' : ∀ u : Fin z,
      Matrix.blockProj (slotSize D) (Sum.inr u : BlockIndex S z) * N = 0 := by
    intro u
    ext p k
    rw [blockProj_mul_apply]
    have hp : p = 0 := Fin.ext (by
      have := p.2; change (p : ℕ) < 1 at this; change (p : ℕ) = 0; omega)
    subst hp
    exact hzero u k
  -- the block slots
  have hblock : ∀ t : {s // s ∈ S},
      Matrix.blockProj (slotSize D) (Sum.inl t : BlockIndex S z) * N = 0 := by
    intro t
    obtain ⟨s₀, ht, hμ⟩ := hcl t
    have hsum : ∀ t' : gaugeClass C s₀, ∑ t : gaugeClass C s₀, classCoeff C X s₀ t' t •
        (classIntertwinerInv C s₀ t * (Matrix.blockProj (slotSize D) (Sum.inl t.1) * N)) = 0 := by
      intro t'
      have h := hrow (Sum.inl t'.1)
      have hz : ∑ u : Fin z, blockEntry X (Sum.inl t'.1) (Sum.inr u) *
          (Matrix.blockProj (slotSize D) (Sum.inr u) * N) = 0 :=
        Finset.sum_eq_zero fun u _ => by rw [hzero' u, Matrix.mul_zero]
      rw [Fintype.sum_sum_type, hz, add_zero,
        ← Finset.sum_subset (Finset.subset_univ (gaugeClass C s₀)) (fun s _ hs => by
          rw [blockEntry_inl_inl_eq_zero_of_mul_blockDiagonal'_eq hX (hirr _ t'.1.2) (hirr _ s.2)
            (fun h => hs (mem_gaugeClass.2 ((mem_gaugeClass.1 t'.2).trans h))),
            Matrix.zero_mul]),
        ← Finset.sum_coe_sort] at h
      have h' := congrArg (classIntertwinerInv C s₀ t' * ·) h
      simp only [Matrix.mul_zero, Matrix.mul_sum] at h'
      refine (Finset.sum_congr rfl fun t _ => ?_).trans h'
      rw [blockEntry_inl_inl_eq_classCoeff_smul_of_mul_blockDiagonal'_eq hirr hX s₀ t' t,
        Matrix.smul_mul, Matrix.mul_smul]
      simp only [← Matrix.mul_assoc, classIntertwinerInv_mul_classIntertwiner, Matrix.one_mul]
    obtain ⟨μi, hμi⟩ := hμ.exists_left_inv
    have hW : ∀ t'' : gaugeClass C s₀,
        classIntertwinerInv C s₀ t'' * (Matrix.blockProj (slotSize D) (Sum.inl t''.1) * N) =
          (0 : Matrix (Fin (D s₀.1)) κ ℂ) := by
      intro t''
      calc classIntertwinerInv C s₀ t'' * (Matrix.blockProj (slotSize D) (Sum.inl t''.1) * N)
          = ∑ t, (μi * classCoeff C X s₀) t'' t •
              (classIntertwinerInv C s₀ t * (Matrix.blockProj (slotSize D) (Sum.inl t.1) * N)) := by
            rw [hμi]
            simp [Matrix.one_apply, ite_smul]
        _ = ∑ t', μi t'' t' • ∑ t, classCoeff C X s₀ t' t •
              (classIntertwinerInv C s₀ t * (Matrix.blockProj (slotSize D) (Sum.inl t.1) * N)) := by
            simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
            exact Finset.sum_comm
        _ = 0 := by simp only [hsum, smul_zero, Finset.sum_const_zero]
    calc Matrix.blockProj (slotSize D) (Sum.inl t : BlockIndex S z) * N
        = classIntertwiner C s₀ ⟨t, ht⟩ * (classIntertwinerInv C s₀ ⟨t, ht⟩ *
            (Matrix.blockProj (slotSize D) (Sum.inl t : BlockIndex S z) * N)) := by
          rw [← Matrix.mul_assoc, classIntertwiner_mul_classIntertwinerInv, Matrix.one_mul]
      _ = 0 := by rw [hW ⟨t, ht⟩, Matrix.mul_zero]
  ext ⟨b, p⟩ k
  rcases b with t | u
  · simpa [Matrix.mul_apply, Matrix.blockProj, Matrix.blockEmbed]
      using congrFun (congrFun (hblock t) p) k
  · simpa [Matrix.mul_apply, Matrix.blockProj, Matrix.blockEmbed]
      using congrFun (congrFun (hzero' u) p) k

/-- An intertwiner of the block diagonal form is invertible when its zero-slot block is and every
block slot lies in a gauge class with invertible class coefficients. -/
private theorem isUnit_of_isUnit_classCoeff
    (hirr : ∀ s ∈ S, Matrix.IsIrreducibleAction (C s)) (hlet : ∀ s ∈ S, ∃ i, C s i ≠ 0)
    {X : Matrix (BlockSpace D S z) (BlockSpace D S z) ℂ}
    (hX : ∀ i : Fin d, X * Matrix.blockDiagonal' (blockOf D C i) =
      Matrix.blockDiagonal' (blockOf D C i) * X)
    (hcl : ∀ t : {s // s ∈ S}, ∃ s₀, t ∈ gaugeClass C s₀ ∧ IsUnit (classCoeff C X s₀))
    (h0 : IsUnit (zeroSlotBlock X)) : IsUnit X := by
  refine Matrix.mulVec_injective_iff_isUnit.1 fun v w hvw => ?_
  have hN := eq_zero_of_mul_eq_zero_of_isUnit_classCoeff hirr hlet hX hcl h0
    (N := Matrix.of fun x (_ : Unit) => v x - w x) (by
      ext x k
      have := congrFun hvw x
      simp only [Matrix.mulVec, dotProduct] at this
      simp [Matrix.mul_apply, mul_sub, Finset.sum_sub_distrib, this])
  funext x
  have := congrFun (congrFun hN x) ()
  simp only [Matrix.of_apply, Matrix.zero_apply] at this
  exact sub_eq_zero.1 this

/-- **Invertibility**: an intertwiner of the block diagonal form is invertible exactly when
every class coefficient matrix and the zero-slot block are invertible. -/
theorem isUnit_iff_of_forall_mul_blockDiagonal'_eq
    (hirr : ∀ s ∈ S, Matrix.IsIrreducibleAction (C s)) (hlet : ∀ s ∈ S, ∃ i, C s i ≠ 0)
    {X : Matrix (BlockSpace D S z) (BlockSpace D S z) ℂ}
    (hX : ∀ i : Fin d, X * Matrix.blockDiagonal' (blockOf D C i) =
      Matrix.blockDiagonal' (blockOf D C i) * X) :
    IsUnit X ↔ (∀ s₀ : {s // s ∈ S}, IsUnit (classCoeff C X s₀)) ∧ IsUnit (zeroSlotBlock X) := by
  constructor
  · intro hu
    obtain ⟨Y, hXY, hYX⟩ : ∃ Y, X * Y = 1 ∧ Y * X = 1 :=
      ⟨hu.unit⁻¹.1, hu.unit.mul_inv, hu.unit.inv_mul⟩
    have hY : ∀ i : Fin d, Y * Matrix.blockDiagonal' (blockOf D C i) =
        Matrix.blockDiagonal' (blockOf D C i) * Y := fun i => by
      calc Y * Matrix.blockDiagonal' (blockOf D C i)
          = Y * (Matrix.blockDiagonal' (blockOf D C i) * X) * Y := by
            rw [Matrix.mul_assoc Y, Matrix.mul_assoc, hXY, Matrix.mul_one]
        _ = (Y * X) * Matrix.blockDiagonal' (blockOf D C i) * Y := by
            rw [← hX, ← Matrix.mul_assoc Y]
        _ = _ := by rw [hYX, Matrix.one_mul]
    have hlet₀ : ∀ s ∈ S, 0 < D s → ∃ i, C s i ≠ 0 := fun s hs _ => hlet s hs
    exact ⟨fun s₀ => ⟨⟨_, _, classCoeff_mul_classCoeff_of_mul_blockDiagonal'_eq hirr hlet hX hY
        hXY s₀, classCoeff_mul_classCoeff_of_mul_blockDiagonal'_eq hirr hlet hY hX hYX s₀⟩, rfl⟩,
      ⟨⟨_, _, zeroSlotBlock_mul_zeroSlotBlock_of_mul_blockDiagonal'_eq hirr hlet₀ hX hXY,
        zeroSlotBlock_mul_zeroSlotBlock_of_mul_blockDiagonal'_eq hirr hlet₀ hY hYX⟩, rfl⟩⟩
  · rintro ⟨hcl, h0⟩
    exact isUnit_of_isUnit_classCoeff hirr hlet hX (fun t => ⟨t, self_mem_gaugeClass t, hcl t⟩) h0

open scoped Classical in
/-- The class block prescribed by the class matrices `μ` on the representatives `R`. -/
private noncomputable def prescribedEntry (R : Finset {s // s ∈ S})
    (μ : ∀ r : R, Matrix (gaugeClass C r.1) (gaugeClass C r.1) ℂ) (t' t : {s // s ∈ S}) :
    Matrix (Fin (D t'.1)) (Fin (D t.1)) ℂ :=
  if h : ∃ r : R, t' ∈ gaugeClass C r.1 ∧ t ∈ gaugeClass C r.1 then
    μ h.choose ⟨t', h.choose_spec.1⟩ ⟨t, h.choose_spec.2⟩ •
      (classIntertwiner C h.choose.1 ⟨t', h.choose_spec.1⟩ *
        classIntertwinerInv C h.choose.1 ⟨t, h.choose_spec.2⟩)
  else 0

/-- The matrix with prescribed class blocks and zero-slot block, zero elsewhere. -/
private noncomputable def prescribedMatrix (R : Finset {s // s ∈ S})
    (μ : ∀ r : R, Matrix (gaugeClass C r.1) (gaugeClass C r.1) ℂ)
    (Y₀ : Matrix (Fin z) (Fin z) ℂ) : Matrix (BlockSpace D S z) (BlockSpace D S z) ℂ :=
  Matrix.of fun x y => match x, y with
    | ⟨Sum.inl t', p⟩, ⟨Sum.inl t, q⟩ => prescribedEntry R μ t' t p q
    | ⟨Sum.inr u', _⟩, ⟨Sum.inr u, _⟩ => Y₀ u' u
    | _, _ => 0

/-- **Every choice occurs**: prescribed class matrices on a set `R` of class
representatives and a prescribed zero-slot block give an intertwiner of the block diagonal form,
invertible exactly when all prescribed blocks are. -/
theorem exists_forall_mul_blockDiagonal'_eq_and_classCoeff_eq
    (hirr : ∀ s ∈ S, Matrix.IsIrreducibleAction (C s)) (hlet : ∀ s ∈ S, ∃ i, C s i ≠ 0)
    (R : Finset {s // s ∈ S})
    (hR : ∀ s : {s // s ∈ S}, ∃! r, r ∈ R ∧ IsGaugeRelated (C r.1) (C s.1))
    (μ : ∀ r : R, Matrix (gaugeClass C r.1) (gaugeClass C r.1) ℂ)
    (Y₀ : Matrix (Fin z) (Fin z) ℂ) :
    ∃ X : Matrix (BlockSpace D S z) (BlockSpace D S z) ℂ,
      (∀ i : Fin d, X * Matrix.blockDiagonal' (blockOf D C i) =
        Matrix.blockDiagonal' (blockOf D C i) * X) ∧
      (∀ r : R, classCoeff C X r.1 = μ r) ∧ zeroSlotBlock X = Y₀ ∧
      (IsUnit X ↔ (∀ r : R, IsUnit (μ r)) ∧ IsUnit Y₀) := by
  set X := prescribedMatrix R μ Y₀ with hXdef
  have e11 : ∀ t' t : {s // s ∈ S},
      blockEntry X (Sum.inl t') (Sum.inl t) = prescribedEntry R μ t' t := fun t' t => by
    ext p q
    rw [blockEntry_apply]
    rfl
  have e12 : ∀ (t' : {s // s ∈ S}) (u : Fin z), blockEntry X (Sum.inl t') (Sum.inr u) = 0 :=
    fun t' u => by
      ext p q
      rw [blockEntry_apply]
      rfl
  have e21 : ∀ (u' : Fin z) (t : {s // s ∈ S}), blockEntry X (Sum.inr u') (Sum.inl t) = 0 :=
    fun u' t => by
      ext p q
      rw [blockEntry_apply]
      rfl
  have hzero : zeroSlotBlock X = Y₀ := by
    ext u' u
    rfl
  have hXint : ∀ i : Fin d, X * Matrix.blockDiagonal' (blockOf D C i) =
      Matrix.blockDiagonal' (blockOf D C i) * X := by
    refine mul_blockDiagonal'_eq_of_forall_blockEntry fun i b' b => ?_
    rcases b' with t' | u' <;> rcases b with t | u
    · rw [e11]
      by_cases h : ∃ r : R, t' ∈ gaugeClass C r.1 ∧ t ∈ gaugeClass C r.1
      · rw [prescribedEntry, dite_eq_left h, Matrix.smul_mul, Matrix.mul_smul]
        exact congrArg _ (classIntertwiner_mul_classIntertwinerInv_intertwines _ _ _ i)
      · rw [prescribedEntry, dite_eq_right h, Matrix.zero_mul, Matrix.mul_zero]
    · rw [e12, Matrix.zero_mul, Matrix.mul_zero]
    · rw [e21, Matrix.zero_mul, Matrix.mul_zero]
    · change _ * 0 = 0 * _
      rw [Matrix.mul_zero, Matrix.zero_mul]
  have hcoeff : ∀ r : R, classCoeff C X r.1 = μ r := by
    intro r
    have : NeZero (D r.1.1) := ⟨(dim_pos_of_exists_ne_zero (hlet _ r.1.2)).ne'⟩
    ext t' t
    have hex : ∃ r' : R, t'.1 ∈ gaugeClass C r'.1 ∧ t.1 ∈ gaugeClass C r'.1 := ⟨r, t'.2, t.2⟩
    have key : ∀ (r' : R) (h1 : t'.1 ∈ gaugeClass C r'.1) (h2 : t.1 ∈ gaugeClass C r'.1),
        r' = r → μ r' ⟨t'.1, h1⟩ ⟨t.1, h2⟩ • (classIntertwiner C r'.1 ⟨t'.1, h1⟩ *
          classIntertwinerInv C r'.1 ⟨t.1, h2⟩) =
          μ r t' t • (classIntertwiner C r.1 t' * classIntertwinerInv C r.1 t) := by
      rintro r' h1 h2 rfl
      rfl
    have hch : hex.choose = r := Subtype.ext ((hR t'.1).unique
      ⟨hex.choose.2, mem_gaugeClass.1 hex.choose_spec.1⟩ ⟨r.2, mem_gaugeClass.1 t'.2⟩)
    have hD0 : (D r.1.1 : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne (D r.1.1))
    rw [classCoeff, Matrix.of_apply, e11, prescribedEntry, dite_eq_left hex,
      key _ _ _ hch, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc,
      classIntertwinerInv_mul_classIntertwiner, Matrix.one_mul,
      classIntertwinerInv_mul_classIntertwiner, Matrix.trace_smul, Matrix.trace_one,
      Fintype.card_fin, smul_eq_mul, mul_comm, mul_assoc, mul_inv_cancel₀ hD0, mul_one]
  refine ⟨X, hXint, hcoeff, hzero, ?_⟩
  constructor
  · intro hu
    obtain ⟨h1, h2⟩ := (isUnit_iff_of_forall_mul_blockDiagonal'_eq hirr hlet hXint).1 hu
    exact ⟨fun r => hcoeff r ▸ h1 r.1, hzero ▸ h2⟩
  · rintro ⟨h1, h2⟩
    refine isUnit_of_isUnit_classCoeff hirr hlet hXint (fun t => ?_) (hzero ▸ h2)
    obtain ⟨r, ⟨hrR, hrt⟩, -⟩ := hR t
    refine ⟨r, mem_gaugeClass.2 hrt, ?_⟩
    rw [show classCoeff C X r = μ ⟨r, hrR⟩ from hcoeff ⟨r, hrR⟩]
    exact h1 ⟨r, hrR⟩

/-- **The gauges to a fixed tensor** (pure algebra, no hypothesis on the tensors): if `X₀` is
a gauge from `B` to `Â`, the gauges from `B` to `Â` are exactly `Z X₀` with `Z` invertible and
commuting with every `Â^i`. -/
theorem isUnit_and_forall_mul_eq_mul_iff_exists_eq_mul {n : ℕ} {B Â : MPSTensor d n}
    {X₀ : Matrix (Fin n) (Fin n) ℂ} (h₀ : IsUnit X₀) (hX₀ : ∀ i, X₀ * B i = Â i * X₀)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    (IsUnit X ∧ ∀ i, X * B i = Â i * X) ↔
      ∃ Z, IsUnit Z ∧ (∀ i, Z * Â i = Â i * Z) ∧ X = Z * X₀ := by
  obtain ⟨Ui, hUi1, hUi2⟩ : ∃ Ui : Matrix (Fin n) (Fin n) ℂ, X₀ * Ui = 1 ∧ Ui * X₀ = 1 :=
    ⟨h₀.unit⁻¹.1, h₀.unit.mul_inv, h₀.unit.inv_mul⟩
  have hinv : ∀ i, Ui * Â i = B i * Ui := fun i => by
    calc Ui * Â i = Ui * (Â i * X₀) * Ui := by
          rw [Matrix.mul_assoc Ui, Matrix.mul_assoc (Â i), hUi1, Matrix.mul_one]
      _ = B i * Ui := by rw [← hX₀, ← Matrix.mul_assoc Ui, hUi2, Matrix.one_mul]
  constructor
  · rintro ⟨hX, hXB⟩
    refine ⟨X * Ui, hX.mul ⟨⟨Ui, X₀, hUi2, hUi1⟩, rfl⟩, fun i => ?_, ?_⟩
    · rw [Matrix.mul_assoc, hinv, ← Matrix.mul_assoc X, hXB, Matrix.mul_assoc (Â i)]
    · rw [Matrix.mul_assoc, hUi2, Matrix.mul_one]
  · rintro ⟨Z, hZ, hZÂ, rfl⟩
    refine ⟨hZ.mul h₀, fun i => ?_⟩
    rw [Matrix.mul_assoc, hX₀, ← Matrix.mul_assoc Z, hZÂ, Matrix.mul_assoc (Â i)]

end MPSTensor
