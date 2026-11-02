/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.Reduction.SplitUniqueness
import TNLean.MPS.FundamentalTheorem.Reduction.UniquenessSameFlag

/-!
# The multiplicity gauge of split multi-block reductions

Let `P` and `Q` be two split reductions of the same tensor `B` onto the same family of normal blocks
`C s`, `s ∈ S`, of positive bond dimension, with coordinate changes `g` and `g_tilde`, and let
$h = \tilde g g^{-1}$ be their relative gauge. The block $h_{b'b}$ intertwines the diagonal block at
`b` with that at `b'`, so it vanishes between blocks that are not gauge related and between a block
slot and a zero slot. This module proves the remaining clause of the bare uniqueness of split
compressions (blueprint `prop:asym_uniq_split`, *Uniqueness of split compressions, bare form*): `h`
mixes the `m_c` copies of one gauge class `c` by an invertible `m_c × m_c` matrix composed with
intertwiners, and the zero slots by an invertible matrix.

**Gauge classes.** A gauge class is encoded by a representative block slot `s₀`: the class is the
set `gaugeClass C s₀` of block slots `t` with `C s₀` gauge related to `C t`. For every `t` in the
class an invertible intertwiner `Y_t` from `C s₀` to `C t`, with `C t i * Y_t = Y_t * C s₀ i`, is
chosen once (`classIntertwiner`, with inverse `classIntertwinerInv`). For `t, t'` in the class the
block of `h` is
$$h_{t't} = \mu_{t't}\, Y_{t'} Y_t^{-1},$$
and the coefficient matrix `μ = classMatrix P Q s₀` is invertible, with inverse the coefficient
matrix `classMatrix Q P s₀` of $h^{-1} = g \tilde g^{-1}$, for the same choice of intertwiners.

**Zero slots.** The zero-slot block `zeroSlotBlock h`, a `Q.z × P.z` matrix, has the two-sided
inverse `zeroSlotBlock h⁻¹`; this is the element of $\mathrm{GL}_z(\mathbb C)$ of the proposition.
The two numbers of zero slots agree by the uniqueness of the blocks (blueprint
`thm:asym_uniq_blocks`, *The blocks are unique*; `MPSTensor.MultiBlockCompression.z_eq`); the
statement is phrased with the two rectangular zero-slot blocks so that no transport along that
equality is needed.

## Main definitions

* `MPSTensor.gaugeClass`: the block slots gauge related to a representative.
* `MPSTensor.classIntertwiner`, `MPSTensor.classIntertwinerInv`: the chosen intertwiners `Y_t` and
  their inverses.
* `MPSTensor.zeroSlotBlock`: the block of a matrix between the zero slots.
* `MPSTensor.MultiBlockCompression.classMatrix`: the coefficient matrix `μ` of one gauge class.

## Main statements

* `MPSTensor.MultiBlockCompression.blockEntry_eq_zero_of_mem_gaugeClass_of_notMem`,
  `MPSTensor.MultiBlockCompression.blockEntry_eq_zero_of_notMem_gaugeClass_of_mem`: the relative
  gauge is block diagonal with respect to the partition into gauge classes.
* `MPSTensor.MultiBlockCompression.blockEntry_relativeGauge_eq_classMatrix_smul`:
  $h_{t't} = \mu_{t't} Y_{t'} Y_t^{-1}$.
* `MPSTensor.MultiBlockCompression.classMatrix_mul_classMatrix`,
  `MPSTensor.MultiBlockCompression.isUnit_classMatrix`: the coefficient matrix is invertible.
* `MPSTensor.MultiBlockCompression.zeroSlotBlock_relativeGauge_mul_zeroSlotBlock_relativeGauge`: the
  zero-slot block of `h` is invertible, with inverse the zero-slot block of $h^{-1}$.

## References

Blueprint `prop:asym_uniq_split`, *Uniqueness of split compressions, bare form*; *The asymmetric
fundamental theorem of matrix product states*, Proposition 6.12.
-/

open scoped Matrix

namespace MPSTensor

variable {d : ℕ}

variable {ι : Type*} {D : ι → ℕ} {S : Finset ι} {C : ∀ s, MPSTensor d (D s)}

/-! ### Gauge classes and their intertwiners -/

section Classes

variable (C) in
/-- The **gauge class** of a block slot `s₀`: the block slots `t` with `C s₀` gauge related to `C t`
(blueprint `prop:asym_uniq_split`, *Uniqueness of split compressions, bare form*). -/
noncomputable def gaugeClass (s₀ : {s // s ∈ S}) : Finset {s // s ∈ S} := by
  classical
  exact Finset.univ.filter fun t => IsGaugeRelated (C s₀.1) (C t.1)

theorem mem_gaugeClass {s₀ t : {s // s ∈ S}} :
    t ∈ gaugeClass C s₀ ↔ IsGaugeRelated (C s₀.1) (C t.1) := by
  unfold gaugeClass
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem self_mem_gaugeClass (s₀ : {s // s ∈ S}) : s₀ ∈ gaugeClass C s₀ :=
  mem_gaugeClass.2 ⟨1, 1, Matrix.mul_one 1, Matrix.mul_one 1, fun i => by
    rw [Matrix.mul_one, Matrix.one_mul]⟩

variable (C) in
/-- The chosen inverse `Y_t⁻¹` of the intertwiner of a member `t` of the gauge class of `s₀`: an
invertible matrix with `C s₀ i * Y_t⁻¹ = Y_t⁻¹ * C t i`. -/
noncomputable def classIntertwinerInv (s₀ : {s // s ∈ S}) (t : gaugeClass C s₀) :
    Matrix (Fin (D s₀.1)) (Fin (D t.1.1)) ℂ :=
  (mem_gaugeClass.1 t.2).choose

variable (C) in
/-- The chosen **intertwiner** `Y_t` from `C s₀` to a member `t` of its gauge class:
`C t i * Y_t = Y_t * C s₀ i`. -/
noncomputable def classIntertwiner (s₀ : {s // s ∈ S}) (t : gaugeClass C s₀) :
    Matrix (Fin (D t.1.1)) (Fin (D s₀.1)) ℂ :=
  (mem_gaugeClass.1 t.2).choose_spec.choose

theorem classIntertwinerInv_mul_classIntertwiner (s₀ : {s // s ∈ S}) (t : gaugeClass C s₀) :
    classIntertwinerInv C s₀ t * classIntertwiner C s₀ t = 1 :=
  (mem_gaugeClass.1 t.2).choose_spec.choose_spec.1

theorem classIntertwiner_mul_classIntertwinerInv (s₀ : {s // s ∈ S}) (t : gaugeClass C s₀) :
    classIntertwiner C s₀ t * classIntertwinerInv C s₀ t = 1 :=
  (mem_gaugeClass.1 t.2).choose_spec.choose_spec.2.1

theorem mul_classIntertwinerInv (s₀ : {s // s ∈ S}) (t : gaugeClass C s₀) (i : Fin d) :
    C s₀.1 i * classIntertwinerInv C s₀ t = classIntertwinerInv C s₀ t * C t.1.1 i :=
  (mem_gaugeClass.1 t.2).choose_spec.choose_spec.2.2 i

/-- The chosen intertwiner intertwines: `C t i * Y_t = Y_t * C s₀ i`. -/
theorem mul_classIntertwiner (s₀ : {s // s ∈ S}) (t : gaugeClass C s₀) (i : Fin d) :
    C t.1.1 i * classIntertwiner C s₀ t = classIntertwiner C s₀ t * C s₀.1 i := by
  set X := classIntertwinerInv C s₀ t
  set Y := classIntertwiner C s₀ t
  calc C t.1.1 i * Y = Y * (X * C t.1.1 i) * Y := by
        rw [← Matrix.mul_assoc, classIntertwiner_mul_classIntertwinerInv, Matrix.one_mul]
    _ = Y * C s₀.1 i := by
        rw [← mul_classIntertwinerInv, Matrix.mul_assoc, Matrix.mul_assoc,
          classIntertwinerInv_mul_classIntertwiner, Matrix.mul_one]

end Classes

variable [DecidableEq ι]

/-! ### Block multiplication -/

section Blocks

variable {z z' z'' : ℕ}

/-- The entries of a block are the entries of the matrix at the coordinates of the two slots. -/
theorem blockEntry_apply (X : Matrix (BlockSpace D S z') (BlockSpace D S z) ℂ)
    (b' : BlockIndex S z') (b : BlockIndex S z) (i : Fin (slotSize D b'))
    (j : Fin (slotSize D b)) : blockEntry X b' b i j = X ⟨b', i⟩ ⟨b, j⟩ := by
  simp [blockEntry, Matrix.mul_apply, Matrix.blockProj, Matrix.blockEmbed]

/-- **Block multiplication**: the block of a product is the sum over the intermediate slots of
the products of blocks. -/
theorem blockEntry_mul (X : Matrix (BlockSpace D S z'') (BlockSpace D S z') ℂ)
    (Y : Matrix (BlockSpace D S z') (BlockSpace D S z) ℂ) (b'' : BlockIndex S z'')
    (b : BlockIndex S z) :
    blockEntry (X * Y) b'' b = ∑ b', blockEntry X b'' b' * blockEntry Y b' b := by
  calc blockEntry (X * Y) b'' b =
        Matrix.blockProj (slotSize D) b'' * X * Y * Matrix.blockEmbed (slotSize D) b := by
        simp only [blockEntry, Matrix.mul_assoc]
    _ = _ := by
        rw [blockProj_mul_eq_sum, Matrix.sum_mul, Matrix.sum_mul]
        simp only [blockEntry, Matrix.mul_assoc]

/-- The diagonal blocks of the identity are identities. -/
theorem blockEntry_one_self (b : BlockIndex S z) :
    blockEntry (1 : Matrix (BlockSpace D S z) (BlockSpace D S z) ℂ) b b = 1 := by
  rw [blockEntry, Matrix.mul_one, Matrix.blockProj_mul_blockEmbed_self]

/-- The off-diagonal blocks of the identity vanish. -/
theorem blockEntry_one_of_ne {b' b : BlockIndex S z} (h : b' ≠ b) :
    blockEntry (1 : Matrix (BlockSpace D S z) (BlockSpace D S z) ℂ) b' b = 0 := by
  rw [blockEntry, Matrix.mul_one, Matrix.blockProj_mul_blockEmbed_of_ne h]

/-- The block of a matrix between the zero slots: its entries at the coordinates of the zero
slots, a `z' × z` matrix. -/
def zeroSlotBlock (X : Matrix (BlockSpace D S z') (BlockSpace D S z) ℂ) :
    Matrix (Fin z') (Fin z) ℂ :=
  Matrix.of fun t' t => X ⟨Sum.inr t', 0⟩ ⟨Sum.inr t, 0⟩

/-- The zero-slot block of the identity is the identity. -/
theorem zeroSlotBlock_one :
    zeroSlotBlock (1 : Matrix (BlockSpace D S z) (BlockSpace D S z) ℂ) = 1 := by
  ext t' t
  by_cases h : t' = t
  · subst h
    simp [zeroSlotBlock]
  · rw [zeroSlotBlock, Matrix.of_apply, Matrix.one_apply_ne, Matrix.one_apply_ne h]
    intro he
    exact h (Sum.inr_injective (congrArg Sigma.fst he))

/-- If the rows of `X` at the zero slots have no nonzero block at a block slot, the zero-slot
block of `X * Y` is the product of the zero-slot blocks. -/
theorem zeroSlotBlock_mul (X : Matrix (BlockSpace D S z'') (BlockSpace D S z') ℂ)
    (Y : Matrix (BlockSpace D S z') (BlockSpace D S z) ℂ)
    (hX : ∀ (t : Fin z'') (s : {s // s ∈ S}), blockEntry X (Sum.inr t) (Sum.inl s) = 0) :
    zeroSlotBlock (X * Y) = zeroSlotBlock X * zeroSlotBlock Y := by
  ext t' t
  have h0 : ∀ (s : {s // s ∈ S}) (p : Fin (D s.1)),
      X ⟨Sum.inr t', 0⟩ ⟨Sum.inl s, p⟩ = 0 := fun s p => by
    rw [← blockEntry_apply X (Sum.inr t') (Sum.inl s) 0 p, hX]
    rfl
  simp [zeroSlotBlock, Matrix.mul_apply, Fintype.sum_sigma, Fintype.sum_sum_type, h0]

end Blocks


/-! ### The relative gauge of two split reductions -/

namespace MultiBlockCompression

variable {DB : ℕ} {B : MPSTensor d DB} (P Q : MultiBlockCompression B S C)

/-- The relative gauges in the two directions are mutually inverse, $h h^{-1} = 1$ with
$h^{-1} = g \tilde g^{-1}$. -/
theorem relativeGauge_mul_relativeGauge : P.relativeGauge Q * Q.relativeGauge P = 1 := by
  rw [relativeGauge, relativeGauge, Matrix.mul_assoc, ← Matrix.mul_assoc (gaugeMatrixInv P.gauge),
    gaugeMatrixInv_mul_gaugeMatrix, Matrix.one_mul, gaugeMatrix_mul_gaugeMatrixInv]

/-- The **coefficient matrix** `μ` of the gauge class of `s₀` (blueprint `prop:asym_uniq_split`,
*Uniqueness of split compressions, bare form*):
$\mu_{t't} = \operatorname{tr}(Y_{t'}^{-1} h_{t't} Y_t)/D_{s_0}$ for `t, t'` in the class, where `h`
is the relative gauge of `P` and `Q` and `Y_t` are the chosen intertwiners. For split reductions
$h_{t't} = \mu_{t't} Y_{t'} Y_t^{-1}$ (`blockEntry_relativeGauge_eq_classMatrix_smul`). -/
noncomputable def classMatrix (s₀ : {s // s ∈ S}) :
    Matrix (gaugeClass C s₀) (gaugeClass C s₀) ℂ :=
  Matrix.of fun t' t => (D s₀.1 : ℂ)⁻¹ *
    (classIntertwinerInv C s₀ t' * blockEntry (P.relativeGauge Q) (Sum.inl t'.1) (Sum.inl t.1) *
      classIntertwiner C s₀ t).trace

variable {P Q}

/-- **The relative gauge does not mix a gauge class with its complement** (blueprint
`prop:asym_uniq_split`, *Uniqueness of split compressions, bare form*): the block from a block slot
outside the class of `s₀` to a member of the class vanishes. -/
theorem blockEntry_eq_zero_of_mem_gaugeClass_of_notMem (hP : P.remainder = 0)
    (hQ : Q.remainder = 0) (hC : ∀ s ∈ S, Kraus.IsNormal (C s)) {s₀ t' s : {s // s ∈ S}}
    (ht' : t' ∈ gaugeClass C s₀) (hs : s ∉ gaugeClass C s₀) :
    blockEntry (P.relativeGauge Q) (Sum.inl t') (Sum.inl s) = 0 :=
  blockEntry_eq_zero_of_not_isGaugeRelated hP hQ (hC _ t'.2) (hC _ s.2) fun h =>
    hs (mem_gaugeClass.2 ((mem_gaugeClass.1 ht').trans h))

/-- The block from a member of the class of `s₀` to a block slot outside the class vanishes. -/
theorem blockEntry_eq_zero_of_notMem_gaugeClass_of_mem (hP : P.remainder = 0)
    (hQ : Q.remainder = 0) (hC : ∀ s ∈ S, Kraus.IsNormal (C s)) {s₀ s t : {s // s ∈ S}}
    (hs : s ∉ gaugeClass C s₀) (ht : t ∈ gaugeClass C s₀) :
    blockEntry (P.relativeGauge Q) (Sum.inl s) (Sum.inl t) = 0 :=
  blockEntry_eq_zero_of_not_isGaugeRelated hP hQ (hC _ s.2) (hC _ t.2) fun h =>
    hs (mem_gaugeClass.2 ((mem_gaugeClass.1 ht).trans h.symm))

/-- **Within a gauge class the relative gauge is the coefficient matrix composed with intertwiners**
(blueprint `prop:asym_uniq_split`, *Uniqueness of split compressions, bare form*): for two split
reductions and `t, t'` in the class of `s₀`, $h_{t't} = \mu_{t't}\, Y_{t'} Y_t^{-1}$. -/
theorem blockEntry_relativeGauge_eq_classMatrix_smul (hP : P.remainder = 0)
    (hQ : Q.remainder = 0) (hC : ∀ s ∈ S, Kraus.IsNormal (C s)) (hD : ∀ s ∈ S, 0 < D s)
    (s₀ : {s // s ∈ S}) (t' t : gaugeClass C s₀) :
    blockEntry (P.relativeGauge Q) (Sum.inl t'.1) (Sum.inl t.1) =
      P.classMatrix Q s₀ t' t • (classIntertwiner C s₀ t' * classIntertwinerInv C s₀ t) := by
  set Y' := classIntertwiner C s₀ t'
  set X' := classIntertwinerInv C s₀ t'
  set Y := classIntertwiner C s₀ t
  set X := classIntertwinerInv C s₀ t
  obtain ⟨ν, hν⟩ := exists_blockEntry_eq_smul_of_intertwines hP hQ (t := t'.1) (s := t.1)
    (hC _ t.1.2) (Y := Y' * X) (Y' := Y * X')
    (by rw [Matrix.mul_assoc, ← Matrix.mul_assoc X, classIntertwinerInv_mul_classIntertwiner,
      Matrix.one_mul, classIntertwiner_mul_classIntertwinerInv])
    (by rw [Matrix.mul_assoc, ← Matrix.mul_assoc X', classIntertwinerInv_mul_classIntertwiner,
      Matrix.one_mul, classIntertwiner_mul_classIntertwinerInv])
    fun i => by
      rw [← Matrix.mul_assoc, mul_classIntertwiner, Matrix.mul_assoc, mul_classIntertwinerInv,
        Matrix.mul_assoc]
  have hμ : P.classMatrix Q s₀ t' t = ν := by
    have hD0 : (D s₀.1 : ℂ) ≠ 0 := by exact_mod_cast (hD _ s₀.2).ne'
    have h1 : X' * (ν • (Y' * X)) * Y = ν • 1 := by
      rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc,
        classIntertwinerInv_mul_classIntertwiner, Matrix.one_mul,
        classIntertwinerInv_mul_classIntertwiner]
    rw [classMatrix, Matrix.of_apply, hν, h1, Matrix.trace_smul, Matrix.trace_one,
      Fintype.card_fin, smul_eq_mul, mul_comm, mul_assoc, mul_inv_cancel₀ hD0, mul_one]
  rw [hν, hμ]

/-- **The coefficient matrices of the two directions are mutually inverse** (blueprint
`prop:asym_uniq_split`, *Uniqueness of split compressions, bare form*): for two split reductions,
the coefficient matrix of `h = g_tilde g⁻¹` on the gauge class of `s₀` times that of
`h⁻¹ = g g_tilde⁻¹` is the identity. -/
theorem classMatrix_mul_classMatrix (hP : P.remainder = 0) (hQ : Q.remainder = 0)
    (hC : ∀ s ∈ S, Kraus.IsNormal (C s)) (hD : ∀ s ∈ S, 0 < D s) (s₀ : {s // s ∈ S}) :
    P.classMatrix Q s₀ * Q.classMatrix P s₀ = 1 := by
  have : NeZero (D s₀.1) := ⟨(hD _ s₀.2).ne'⟩
  ext t' t
  obtain ⟨c, hc⟩ : ∃ c, c = (P.classMatrix Q s₀ * Q.classMatrix P s₀) t' t := ⟨_, rfl⟩
  rw [← hc]
  -- The block of `h h⁻¹` at `(t', t)` is `c • Y_{t'} Y_t⁻¹`.
  have key : blockEntry (P.relativeGauge Q * Q.relativeGauge P) (Sum.inl t'.1) (Sum.inl t.1) =
      c • (classIntertwiner C s₀ t' * classIntertwinerInv C s₀ t) := by
    have hz : ∑ u : Fin P.z, blockEntry (P.relativeGauge Q) (Sum.inl t'.1) (Sum.inr u) *
        blockEntry (Q.relativeGauge P) (Sum.inr u) (Sum.inl t.1) = 0 :=
      Finset.sum_eq_zero fun u _ => by
        rw [blockEntry_inl_inr_eq_zero hP hQ (hC _ t'.1.2) u, Matrix.zero_mul]
    rw [blockEntry_mul, Fintype.sum_sum_type, hz, add_zero,
      ← Finset.sum_subset (Finset.subset_univ (gaugeClass C s₀)) (fun s _ hs => by
        rw [blockEntry_eq_zero_of_mem_gaugeClass_of_notMem hP hQ hC t'.2 hs, Matrix.zero_mul]),
      ← Finset.sum_coe_sort, hc, Matrix.mul_apply, Finset.sum_smul]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [blockEntry_relativeGauge_eq_classMatrix_smul hP hQ hC hD s₀ t' s,
      blockEntry_relativeGauge_eq_classMatrix_smul hQ hP hC hD s₀ s t, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, Matrix.mul_assoc, ← Matrix.mul_assoc (classIntertwinerInv C s₀ s),
      classIntertwinerInv_mul_classIntertwiner, Matrix.one_mul]
  rw [relativeGauge_mul_relativeGauge] at key
  have hconj : classIntertwinerInv C s₀ t' *
      blockEntry (1 : Matrix (BlockSpace D S Q.z) (BlockSpace D S Q.z) ℂ) (Sum.inl t'.1)
        (Sum.inl t.1) * classIntertwiner C s₀ t = c • 1 := by
    rw [key, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc,
      classIntertwinerInv_mul_classIntertwiner, Matrix.one_mul,
      classIntertwinerInv_mul_classIntertwiner]
  by_cases htt : t' = t
  · subst htt
    rw [blockEntry_one_self, Matrix.mul_one, classIntertwinerInv_mul_classIntertwiner] at hconj
    rw [Matrix.one_apply_eq]
    exact smul_left_injective ℂ one_ne_zero (hconj.symm.trans (one_smul ℂ _).symm)
  · have hne : (Sum.inl t'.1 : BlockIndex S Q.z) ≠ Sum.inl t.1 := fun h =>
      htt (Subtype.ext (Sum.inl_injective h))
    rw [blockEntry_one_of_ne hne, Matrix.mul_zero, Matrix.zero_mul] at hconj
    rw [Matrix.one_apply_ne htt]
    exact (smul_eq_zero.1 hconj.symm).resolve_right one_ne_zero

/-- **The multiplicity gauge of one gauge class is invertible** (blueprint `prop:asym_uniq_split`,
*Uniqueness of split compressions, bare form*, the $\mathrm{GL}_{m_c}$ clause): for two split
reductions onto normal blocks of positive bond dimension, the coefficient matrix of every gauge
class is invertible. -/
theorem isUnit_classMatrix (hP : P.remainder = 0) (hQ : Q.remainder = 0)
    (hC : ∀ s ∈ S, Kraus.IsNormal (C s)) (hD : ∀ s ∈ S, 0 < D s) (s₀ : {s // s ∈ S}) :
    IsUnit (P.classMatrix Q s₀) :=
  ⟨⟨P.classMatrix Q s₀, Q.classMatrix P s₀, classMatrix_mul_classMatrix hP hQ hC hD s₀,
    classMatrix_mul_classMatrix hQ hP hC hD s₀⟩, rfl⟩

/-- **The zero slots are mixed by an invertible matrix** (blueprint `prop:asym_uniq_split`,
*Uniqueness of split compressions, bare form*, the $\mathrm{GL}_z$ clause): for two split reductions
onto normal blocks, the zero-slot block of `h = g_tilde g⁻¹` times that of `h⁻¹ = g g_tilde⁻¹` is
the identity. -/
theorem zeroSlotBlock_relativeGauge_mul_zeroSlotBlock_relativeGauge (hP : P.remainder = 0)
    (hQ : Q.remainder = 0) (hC : ∀ s ∈ S, Kraus.IsNormal (C s)) :
    zeroSlotBlock (P.relativeGauge Q) * zeroSlotBlock (Q.relativeGauge P) = 1 := by
  rw [← zeroSlotBlock_mul _ _ fun t s => blockEntry_inr_inl_eq_zero hP hQ t (hC _ s.2),
    relativeGauge_mul_relativeGauge, zeroSlotBlock_one]

/-- **The zero-slot block of the relative gauge has a two-sided inverse** (blueprint
`prop:asym_uniq_split`, *Uniqueness of split compressions, bare form*, the $\mathrm{GL}_z$ clause):
the zero-slot block of `h⁻¹` is a left and a right inverse of that of `h`. -/
theorem zeroSlotBlock_relativeGauge_mul_eq_one_and_mul_eq_one (hP : P.remainder = 0)
    (hQ : Q.remainder = 0) (hC : ∀ s ∈ S, Kraus.IsNormal (C s)) :
    zeroSlotBlock (P.relativeGauge Q) * zeroSlotBlock (Q.relativeGauge P) = 1 ∧
      zeroSlotBlock (Q.relativeGauge P) * zeroSlotBlock (P.relativeGauge Q) = 1 :=
  ⟨zeroSlotBlock_relativeGauge_mul_zeroSlotBlock_relativeGauge hP hQ hC,
    zeroSlotBlock_relativeGauge_mul_zeroSlotBlock_relativeGauge hQ hP hC⟩

/-- For two reductions with the same number of zero slots and the same order, the second written
as `P.withGauge g` (blueprint `thm:asym_uniq_same_flag`, *Two compressions with the same flag*),
the relative gauge is the coordinate change $h = \tilde g g^{-1}$ of that theorem. -/
theorem relativeGauge_withGauge (P : MultiBlockCompression B S C)
    (g : (Fin DB → ℂ) ≃ₗ[ℂ] (BlockSpace D S P.z → ℂ))
    (htri : ∀ i, (conjMatrix g (B i)).BlockTriangular fun x => P.ord x.1)
    (hdiag : ∀ i b, (conjMatrix g (B i)).blockDiag' b = blockOf D C i b) :
    P.relativeGauge (P.withGauge g htri hdiag) = coordChange P.gauge g :=
  rfl

end MultiBlockCompression

end MPSTensor
