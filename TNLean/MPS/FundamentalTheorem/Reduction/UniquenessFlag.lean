/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.Reduction.MultiBlock
import TNLean.MPS.FundamentalTheorem.Reduction.StarSemisimple

/-!
# Multi-block compressions are labelled invariant flags

A multi-block compression of a tensor `B` onto blocks `C s`, `s ∈ S`, with `z` zero slots is a
change of bond coordinates `g` in which every `B^i` is block upper triangular with the prescribed
diagonal blocks. Writing `E_k` for the span of the coordinate vectors of the first `k` slots, the
subspaces `M_k = g⁻¹ E_k` form an invariant flag of `B` whose `k`-th step carries the block of the
slot at position `k`; conversely a labelled invariant flag gives a compression whose flag it is
(lecture note MultiBlockUniqueness, Proposition 2.3 (Reductions are labelled flags with an adapted
basis)). The reading map `W_b` of a slot `b` at
position `k` vanishes on `M_{k-1}`, maps `M_k` onto the coordinates of the slot and intertwines
the action of `B` on `M_k` with the diagonal block; the injection `V_b` takes values in `M_k`
(lecture note MultiBlockUniqueness, Lemma 5.1 (The maps in terms of the flag)).

## Main definitions

* `WordAlgebra.linearMapOfLetter`: a complex-linear map commuting with every one-letter word, as
  a map of word-algebra modules.
* `MPSTensor.slotTensor`: the diagonal block of a slot as a tensor, `C s` on a block slot and the
  one-dimensional zero tensor on a zero slot.
* `MPSTensor.MultiBlockCompression.flag`: the flag `M_k = g⁻¹ E_k` of a compression.
* `MPSTensor.MultiBlockCompression.leftRow`, `MPSTensor.MultiBlockCompression.rightCol`: the
  reading map and the injection of a block or zero slot.
* `MPSTensor.MultiBlockCompression.stepEquiv`: the step of the flag at the position of a slot is
  the word module of the diagonal block of that slot.
* `MPSTensor.MultiBlockCompression.toFlagData`: the labelled invariant flag of a compression.

## Main results

* `MPSTensor.MultiBlockCompression.leftRow_mulVec_eq_zero_of_mem`,
  `MPSTensor.MultiBlockCompression.leftRow_surjOn`,
  `MPSTensor.MultiBlockCompression.leftRow_mulVec_mulVec_of_mem`: Lemma 5.1 (The maps in terms of
  the flag), part (a).
* `MPSTensor.MultiBlockCompression.rightCol_mulVec_mem_flag`,
  `MPSTensor.MultiBlockCompression.leftRow_mul_rightCol_self`: Lemma 5.1 (The maps in terms of the
  flag), part (b).
* `MPSTensor.MultiBlockCompression.leftRow_mul_rightCol_of_ne`: `W_b V_{b'} = 0` for distinct
  slots (lecture note AsymmetricFT, (1.2)).
* `MPSTensor.FlagData.mem_H_iff`: a member of a labelled invariant flag is the set of vectors
  whose adapted coordinates vanish at the later steps.
* `MPSTensor.FlagData.toMultiBlockCompression_flag`: the flag of the compression built from a
  labelled invariant flag is that flag.
-/

open scoped Matrix

namespace WordAlgebra

variable {d : ℕ} {M N : Type*} [AddCommGroup M] [Module ℂ M] [Module (WordAlgebra d) M]
  [IsScalarTower ℂ (WordAlgebra d) M] [AddCommGroup N] [Module ℂ N] [Module (WordAlgebra d) N]
  [IsScalarTower ℂ (WordAlgebra d) N]

/-- A complex-linear map between word-algebra modules that commutes with the action of every
one-letter word commutes with the action of the whole word algebra. -/
def linearMapOfLetter (f : M →ₗ[ℂ] N)
    (hf : ∀ (i : Fin d) (x : M), f ((ofWord [i] : WordAlgebra d) • x) =
      (ofWord [i] : WordAlgebra d) • f x) : M →ₗ[WordAlgebra d] N where
  toFun := f
  map_add' := f.map_add
  map_smul' p x := by
    have hword : ∀ (w : List (Fin d)) (y : M),
        f ((ofWord w : WordAlgebra d) • y) = (ofWord w : WordAlgebra d) • f y := by
      intro w
      induction w with
      | nil => intro y; rw [ofWord_nil, one_smul, one_smul]
      | cons i w ih => intro y; rw [ofWord_cons, mul_smul, mul_smul, hf, ih]
    change f (p • x) = p • f x
    induction p using MonoidAlgebra.induction_on with
    | of g => exact hword (FreeMonoid.toList g) x
    | add p q hp hq => rw [add_smul, add_smul, f.map_add, hp, hq]
    | smul r p hp => rw [smul_assoc, f.map_smul, hp, smul_assoc]

@[simp] theorem linearMapOfLetter_apply (f : M →ₗ[ℂ] N)
    (hf : ∀ (i : Fin d) (x : M), f ((ofWord [i] : WordAlgebra d) • x) =
      (ofWord [i] : WordAlgebra d) • f x) (x : M) : linearMapOfLetter f hf x = f x := rfl

end WordAlgebra

namespace MPSTensor

open WordAlgebra

variable {d DB : ℕ} {ι : Type*} {D : ι → ℕ}

/-- The diagonal block of a slot as a tensor: the block `C s` on a block slot `s`, and the
one-dimensional tensor with zero letters on a zero slot (lecture note MultiBlockUniqueness,
notation `C_b`). -/
def slotTensor {S : Finset ι} {z : ℕ} (C : ∀ s, MPSTensor d (D s)) (b : BlockIndex S z) :
    MPSTensor d (slotSize D b) :=
  fun i => blockOf D C i b

variable [DecidableEq ι]

/-- A coordinate vector supported on one block vanishes off that block. -/
theorem blockEmbed_mulVec_apply_of_fst_ne {S : Finset ι} {z : ℕ} {b : BlockIndex S z}
    (v : Fin (slotSize D b) → ℂ) {y : BlockSpace D S z} (hy : y.1 ≠ b) :
    (Matrix.blockEmbed (slotSize D) b *ᵥ v) y = 0 := by
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_eq_zero fun j _ => by rw [Matrix.blockEmbed_apply_of_fst_ne hy, zero_mul]

/-- Projecting onto a block reads off the coordinates of that block. -/
theorem blockProj_mulVec {S : Finset ι} {z : ℕ} (b : BlockIndex S z)
    (u : BlockSpace D S z → ℂ) :
    Matrix.blockProj (slotSize D) b *ᵥ u = fun j => u ⟨b, j⟩ := by
  funext j
  simp [Matrix.mulVec, dotProduct, Matrix.blockProj, Matrix.blockEmbed, Matrix.transpose_apply,
    Matrix.of_apply]

namespace MultiBlockCompression

variable {B : MPSTensor d DB} {S : Finset ι} {C : ∀ s, MPSTensor d (D s)}
  (P : MultiBlockCompression B S C)

/-- The block coordinates of a vector of the bond space. -/
noncomputable def coord : B.WordModule ≃ₗ[ℂ] (BlockSpace D S P.z → ℂ) :=
  (WordModule.toVec B).trans P.gauge

theorem coord_apply (x : B.WordModule) : P.coord x = P.gauge (WordModule.toVec B x) := rfl

/-- In block coordinates a one-letter word acts by the matrix of the letter in those
coordinates. -/
theorem coord_ofWord_smul (i : Fin d) (x : B.WordModule) :
    P.coord ((ofWord [i] : WordAlgebra d) • x) = conjMatrix P.gauge (B i) *ᵥ P.coord x := by
  rw [coord_apply, coord_apply, asModuleEquiv_letter_smul, conjMatrix_apply,
    LinearMap.toMatrix'_mulVec, LinearEquiv.conj_apply_apply, Matrix.toLin'_apply,
    LinearEquiv.symm_apply_apply]

/-- The diagonal block of every one-site matrix at a slot is the prescribed one. -/
theorem blockDiag'_conjMatrix (i : Fin d) (b : BlockIndex S P.z) :
    (conjMatrix P.gauge (B i)).blockDiag' b = blockOf D C i b := by
  rcases b with s | t
  · exact P.matched i s
  · exact P.unmatched i t

/-- The leading coordinate subspace `E_k`: the vectors supported on the slots at positions
`< k`. -/
def leadingSpace (k : Fin (S.card + P.z + 1)) : Submodule ℂ (BlockSpace D S P.z → ℂ) where
  carrier := {u | ∀ y : BlockSpace D S P.z, k ≤ (P.ord y.1).castSucc → u y = 0}
  add_mem' hu hv y hy := by simp [hu y hy, hv y hy]
  zero_mem' _ _ := rfl
  smul_mem' c u hu y hy := by simp [hu y hy]

theorem mem_leadingSpace {k : Fin (S.card + P.z + 1)} {u : BlockSpace D S P.z → ℂ} :
    u ∈ P.leadingSpace k ↔ ∀ y : BlockSpace D S P.z, k ≤ (P.ord y.1).castSucc → u y = 0 :=
  Iff.rfl

/-- Block upper triangular matrices preserve the leading coordinate subspaces. -/
theorem mulVec_mem_leadingSpace (i : Fin d) {k : Fin (S.card + P.z + 1)}
    {u : BlockSpace D S P.z → ℂ} (hu : u ∈ P.leadingSpace k) :
    conjMatrix P.gauge (B i) *ᵥ u ∈ P.leadingSpace k := by
  rw [mem_leadingSpace] at hu ⊢
  intro y hy
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun y' _ => ?_
  by_cases hlt : P.ord y'.1 < P.ord y.1
  · rw [P.triangular i hlt, zero_mul]
  · rw [hu y' (le_trans hy (Fin.castSucc_le_castSucc_iff.2 (not_lt.1 hlt))), mul_zero]

/-- **The flag of a multi-block compression** (lecture note MultiBlockUniqueness,
Proposition 2.3 (Reductions are labelled flags with an adapted
basis)): `M_k = g⁻¹ E_k`, the vectors of the bond space whose block coordinates vanish
on every slot at a position `≥ k`. It is invariant because the one-site matrices are block upper
triangular in the block coordinates. -/
noncomputable def flag (k : Fin (S.card + P.z + 1)) : Submodule (WordAlgebra d) B.WordModule :=
  WordAlgebra.submoduleOfLetterInvariant
    ((P.leadingSpace k).comap (P.coord : B.WordModule →ₗ[ℂ] (BlockSpace D S P.z → ℂ)))
    fun i x hx => by
      rw [Submodule.mem_comap, LinearEquiv.coe_coe] at hx ⊢
      rw [P.coord_ofWord_smul]
      exact P.mulVec_mem_leadingSpace i hx

theorem mem_flag_iff {k : Fin (S.card + P.z + 1)} {x : B.WordModule} :
    x ∈ P.flag k ↔ ∀ y : BlockSpace D S P.z, k ≤ (P.ord y.1).castSucc → P.coord x y = 0 :=
  Iff.rfl

theorem flag_zero : P.flag 0 = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
  have h : P.coord x = 0 := funext fun y => P.mem_flag_iff.1 hx y (Fin.zero_le _)
  exact P.coord.map_eq_zero_iff.1 h

theorem flag_last : P.flag (Fin.last _) = ⊤ :=
  eq_top_iff.2 fun _ _ => P.mem_flag_iff.2 fun _ hy =>
    absurd hy (not_le.2 (Fin.castSucc_lt_last _))

theorem flag_mono : Monotone P.flag :=
  fun _ _ hkl _ hx => P.mem_flag_iff.2 fun y hy => P.mem_flag_iff.1 hx y (hkl.trans hy)

/-! ### The reading maps and injections -/

/-- The reading map of a slot, block or zero (the note's `W_b`): the row block of the change
of coordinates at that slot. On a block slot it is `MultiBlockCompression.left`. -/
noncomputable def leftRow (b : BlockIndex S P.z) : Matrix (Fin (slotSize D b)) (Fin DB) ℂ :=
  Matrix.blockProj (slotSize D) b * gaugeMatrix P.gauge

/-- The injection of a slot, block or zero (the note's `V_b`): the column block of the inverse
change of coordinates at that slot. On a block slot it is `MultiBlockCompression.right`. -/
noncomputable def rightCol (b : BlockIndex S P.z) : Matrix (Fin DB) (Fin (slotSize D b)) ℂ :=
  gaugeMatrixInv P.gauge * Matrix.blockEmbed (slotSize D) b

theorem leftRow_inl (s : {s // s ∈ S}) : P.leftRow (Sum.inl s) = P.left s := rfl

theorem rightCol_inl (s : {s // s ∈ S}) : P.rightCol (Sum.inl s) = P.right s := rfl

/-- **Biorthogonality of the maps of a slot** (lecture note MultiBlockUniqueness, Lemma 5.1 (The
maps in terms of the flag), part (b),
`W_b V_b = 1`). -/
theorem leftRow_mul_rightCol_self (b : BlockIndex S P.z) : P.leftRow b * P.rightCol b = 1 := by
  simp only [leftRow, rightCol, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (gaugeMatrix P.gauge), gaugeMatrix_mul_gaugeMatrixInv, Matrix.one_mul,
    Matrix.blockProj_mul_blockEmbed_self]

/-- **Biorthogonality across slots** (lecture note AsymmetricFT, (1.2); milestone V, V2.1):
`W_b V_{b'} = 0` for distinct slots `b ≠ b'`, zero slots included; it is the block at `(b, b')`
of `g g⁻¹ = 1`. -/
theorem leftRow_mul_rightCol_of_ne {b b' : BlockIndex S P.z} (h : b ≠ b') :
    P.leftRow b * P.rightCol b' = 0 := by
  simp only [leftRow, rightCol, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (gaugeMatrix P.gauge), gaugeMatrix_mul_gaugeMatrixInv, Matrix.one_mul,
    Matrix.blockProj_mul_blockEmbed_of_ne h]

theorem leftRow_mulVec (b : BlockIndex S P.z) (v : Fin DB → ℂ) :
    P.leftRow b *ᵥ v = fun j => P.gauge v ⟨b, j⟩ := by
  rw [leftRow, ← Matrix.mulVec_mulVec, gaugeMatrix, LinearMap.toMatrix'_mulVec,
    LinearEquiv.coe_coe, blockProj_mulVec]

theorem gauge_rightCol_mulVec (b : BlockIndex S P.z) (v : Fin (slotSize D b) → ℂ) :
    P.gauge (P.rightCol b *ᵥ v) = Matrix.blockEmbed (slotSize D) b *ᵥ v := by
  rw [rightCol, ← Matrix.mulVec_mulVec, gaugeMatrixInv, LinearMap.toMatrix'_mulVec,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

/-- **The reading map vanishes on the previous step** (lecture note MultiBlockUniqueness,
Lemma 5.1 (The maps in terms of the flag), part
(a)): `W_b` vanishes on `M_{k-1}`, where `k` is the position of `b`. -/
theorem leftRow_mulVec_eq_zero_of_mem {b : BlockIndex S P.z} {x : B.WordModule}
    (hx : x ∈ P.flag (P.ord b).castSucc) : P.leftRow b *ᵥ WordModule.toVec B x = 0 := by
  rw [leftRow_mulVec]
  funext j
  exact P.mem_flag_iff.1 hx ⟨b, j⟩ le_rfl

/-- **The injection lands in the step of its slot** (lecture note MultiBlockUniqueness,
Lemma 5.1 (The maps in terms of the flag), part
(b)): `V_b` maps into `M_k`, where `k` is the position of `b`. -/
theorem rightCol_mulVec_mem_flag (b : BlockIndex S P.z) (v : Fin (slotSize D b) → ℂ) :
    (WordModule.toVec B).symm (P.rightCol b *ᵥ v) ∈ P.flag (P.ord b).succ := by
  refine P.mem_flag_iff.2 fun y hy => ?_
  rw [coord_apply, LinearEquiv.apply_symm_apply, gauge_rightCol_mulVec]
  refine blockEmbed_mulVec_apply_of_fst_ne v fun hyb => ?_
  rw [hyb] at hy
  exact absurd hy (not_le.2 Fin.castSucc_lt_succ)

/-- **The reading map is onto on the step of its slot** (lecture note MultiBlockUniqueness,
Lemma 5.1 (The maps in terms of the flag), part
(a)): `W_b` maps `M_k` onto the coordinates of `b`, where `k` is the position
of `b`. -/
theorem leftRow_surjOn (b : BlockIndex S P.z) :
    Set.SurjOn (fun x : B.WordModule => P.leftRow b *ᵥ WordModule.toVec B x)
      (P.flag (P.ord b).succ) Set.univ := by
  intro u _
  refine ⟨(WordModule.toVec B).symm (P.rightCol b *ᵥ u), P.rightCol_mulVec_mem_flag b u, ?_⟩
  simp only [LinearEquiv.apply_symm_apply, Matrix.mulVec_mulVec, leftRow_mul_rightCol_self,
    Matrix.one_mulVec]

/-- **The reading map intertwines on the step of its slot** (lecture note MultiBlockUniqueness,
Lemma 5.1 (The maps in terms of the flag), part
(a)): for `x ∈ M_k`, where `k` is the position of `b`, `W_b B^i x = C_b^i W_b x`. -/
theorem leftRow_mulVec_mulVec_of_mem {b : BlockIndex S P.z} (i : Fin d) {x : B.WordModule}
    (hx : x ∈ P.flag (P.ord b).succ) :
    P.leftRow b *ᵥ (B i *ᵥ WordModule.toVec B x) =
      blockOf D C i b *ᵥ (P.leftRow b *ᵥ WordModule.toVec B x) := by
  rw [← asModuleEquiv_letter_smul, P.leftRow_mulVec, P.leftRow_mulVec, ← coord_apply,
    ← coord_apply, P.coord_ofWord_smul, ← P.blockDiag'_conjMatrix i b]
  funext j
  simp only [Matrix.mulVec, dotProduct, Matrix.blockDiag'_apply]
  rw [Fintype.sum_sigma, Finset.sum_eq_single b]
  · intro b' _ hb'
    refine Finset.sum_eq_zero fun j' _ => ?_
    rcases lt_trichotomy (P.ord b') (P.ord b) with hlt | heq | hgt
    · rw [P.triangular i (show P.ord (⟨b', j'⟩ : BlockSpace D S P.z).1 <
          P.ord (⟨b, j⟩ : BlockSpace D S P.z).1 from hlt), zero_mul]
    · exact absurd (P.ord.injective heq) hb'
    · rw [P.mem_flag_iff.1 hx ⟨b', j'⟩ (Fin.succ_le_castSucc_iff.2 hgt), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ b) h

/-! ### The labelled invariant flag of a compression -/

/-- The reading map of a slot on the step of its slot, as a map of word-algebra modules into
the word module of the diagonal block of the slot. -/
noncomputable def readStep (b : BlockIndex S P.z) :
    P.flag (P.ord b).succ →ₗ[WordAlgebra d] (slotTensor C b).WordModule :=
  WordAlgebra.linearMapOfLetter
    { toFun := fun x : P.flag (P.ord b).succ => (WordModule.toVec (slotTensor C b)).symm
        (P.leftRow b *ᵥ WordModule.toVec B (x : B.WordModule))
      map_add' := fun x y => by simp [Matrix.mulVec_add]
      map_smul' := fun c x => by simp [Matrix.mulVec_smul] }
    fun i x => by
      apply (WordModule.toVec (slotTensor C b)).injective
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_smul_of_tower]
      rw [asModuleEquiv_letter_smul (slotTensor C b), LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply, asModuleEquiv_letter_smul B,
        P.leftRow_mulVec_mulVec_of_mem i x.2]
      rfl

theorem toVec_readStep (b : BlockIndex S P.z) (x : P.flag (P.ord b).succ) :
    WordModule.toVec (slotTensor C b) (P.readStep b x) =
      P.leftRow b *ᵥ WordModule.toVec B (x : B.WordModule) := by
  simp [readStep]

theorem readStep_surjective (b : BlockIndex S P.z) : Function.Surjective (P.readStep b) := by
  intro w
  refine ⟨⟨(WordModule.toVec B).symm (P.rightCol b *ᵥ WordModule.toVec (slotTensor C b) w),
    P.rightCol_mulVec_mem_flag b _⟩, ?_⟩
  apply (WordModule.toVec (slotTensor C b)).injective
  rw [toVec_readStep]
  simp only [LinearEquiv.apply_symm_apply, Matrix.mulVec_mulVec, leftRow_mul_rightCol_self,
    Matrix.one_mulVec]

theorem ker_readStep (b : BlockIndex S P.z) :
    LinearMap.ker (P.readStep b) =
      (P.flag (P.ord b).castSucc).comap (P.flag (P.ord b).succ).subtype := by
  ext x
  rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply,
    ← (WordModule.toVec (slotTensor C b)).map_eq_zero_iff, toVec_readStep]
  constructor
  · intro h
    refine P.mem_flag_iff.2 fun ⟨b', j'⟩ hy => ?_
    by_cases hb : b' = b
    · subst hb
      exact congrFun (P.leftRow_mulVec b' _ ▸ h) j'
    · have hlt : P.ord b < P.ord b' :=
        lt_of_le_of_ne (Fin.castSucc_le_castSucc_iff.1 hy) fun h' => hb (P.ord.injective h').symm
      exact P.mem_flag_iff.1 x.2 ⟨b', j'⟩ (Fin.succ_le_castSucc_iff.2 hlt)
  · exact P.leftRow_mulVec_eq_zero_of_mem

/-- **The step of the flag at the position of a slot** (lecture note MultiBlockUniqueness,
Proposition 2.3 (Reductions are labelled flags with an adapted
basis)): `M_k / M_{k-1}` is isomorphic, as a word-algebra module, to the word module
of the diagonal block of the slot at position `k`, through the reading map of that slot. -/
noncomputable def stepEquiv (b : BlockIndex S P.z) :
    Submodule.subquot (P.flag (P.ord b).castSucc) (P.flag (P.ord b).succ) ≃ₗ[WordAlgebra d]
      (slotTensor C b).WordModule :=
  (Submodule.quotEquivOfEq _ _ (P.ker_readStep b).symm).trans
    ((P.readStep b).quotKerEquivOfSurjective (P.readStep_surjective b))

/-- **The labelled invariant flag of a multi-block compression** (lecture note
MultiBlockUniqueness, Proposition 2.3 (Reductions are labelled flags with an adapted basis), forward
direction): the flag `M_k = g⁻¹ E_k`, with the
step at position `k` labelled by the slot at position `k`. -/
noncomputable def toFlagData : FlagData B.WordModule S C where
  r := S.card + P.z
  z := P.z
  H := P.flag
  H_zero := P.flag_zero
  H_last := P.flag_last
  H_mono := P.flag_mono
  label := P.ord.symm
  label_bijective := P.ord.symm.bijective
  matched k s hk := by
    obtain rfl : k = P.ord (Sum.inl s) := P.ord.symm_apply_eq.1 hk
    exact ⟨P.stepEquiv (Sum.inl s)⟩
  unmatched_finrank k t hk := by
    obtain rfl : k = P.ord (Sum.inr t) := P.ord.symm_apply_eq.1 hk
    rw [((P.stepEquiv (Sum.inr t)).restrictScalars ℂ).finrank_eq,
      (WordModule.toVec (slotTensor C (Sum.inr t : BlockIndex S P.z))).finrank_eq]
    simp
  unmatched_smul k t hk i x := by
    obtain rfl : k = P.ord (Sum.inr t) := P.ord.symm_apply_eq.1 hk
    apply (P.stepEquiv (Sum.inr t)).injective
    rw [map_smul, map_zero]
    apply (WordModule.toVec (slotTensor C (Sum.inr t : BlockIndex S P.z))).injective
    rw [asModuleEquiv_letter_smul, map_zero]
    simp [slotTensor, blockOf]

end MultiBlockCompression

/-! ### The flag of the compression of a labelled invariant flag -/

namespace FlagData

variable {M : Type*} [AddCommGroup M] [Module ℂ M] [Module (WordAlgebra d) M]
  [IsScalarTower ℂ (WordAlgebra d) M] [FiniteDimensional ℂ M] {S : Finset ι}
  {C : ∀ s, MPSTensor d (D s)}

omit [DecidableEq ι] in
/-- A member of a labelled invariant flag consists of the vectors whose flag-adapted
coordinates vanish at every step from its index on (lecture note MultiBlockUniqueness,
Proposition 2.3 (Reductions are labelled flags with an adapted basis)). -/
theorem mem_H_iff (F : FlagData M S C) (k : Fin (F.r + 1)) (x : M) :
    x ∈ F.H k ↔ ∀ (l : Fin F.r) (j : Fin (slotSize D (F.label l))), (k : ℕ) ≤ l →
      F.adaptedCoord x ⟨l, j⟩ = 0 := by
  obtain ⟨-, -, hstep, hlater⟩ := F.adaptedCoord_spec
  have hfwd : ∀ (k : Fin (F.r + 1)) (x : M), x ∈ F.H k → ∀ (l : Fin F.r)
      (j : Fin (slotSize D (F.label l))), (k : ℕ) ≤ l → F.adaptedCoord x ⟨l, j⟩ = 0 := by
    intro k x hx l j hkl
    obtain ⟨k', rfl⟩ : ∃ k' : Fin F.r, k = k'.castSucc := ⟨⟨k, by omega⟩, Fin.ext rfl⟩
    exact hlater k' x hx l (Fin.le_def.2 hkl) j
  refine ⟨hfwd k x, fun h => ?_⟩
  induction k using Fin.induction generalizing x with
  | zero =>
    have hx : F.adaptedCoord x = 0 := funext fun ⟨l, j⟩ => h l j (Nat.zero_le _)
    rw [F.adaptedCoord.map_eq_zero_iff.1 hx]
    exact zero_mem _
  | succ k ih =>
    obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _
      ((F.stepCoord k).symm fun j => F.adaptedCoord x ⟨k, j⟩)
    have hvk : ∀ j, F.adaptedCoord (v : M) ⟨k, j⟩ = F.adaptedCoord x ⟨k, j⟩ := by
      intro j
      rw [hstep k v j, hv, LinearEquiv.apply_symm_apply]
    have hsub : x - v ∈ F.H k.castSucc := by
      refine ih (x - v) fun l j hkl => ?_
      rw [map_sub, Pi.sub_apply, sub_eq_zero]
      rcases eq_or_lt_of_le (show (k : ℕ) ≤ l by simpa using hkl) with hkl' | hkl'
      · obtain rfl : l = k := Fin.ext hkl'.symm
        exact (hvk j).symm
      · rw [h l j (by simpa using hkl'), hfwd k.succ v v.2 l j (by simpa using hkl')]
    have := (F.H k.succ).add_mem (F.H_mono (Fin.castSucc_le_succ k) hsub) v.2
    rwa [sub_add_cancel] at this

end FlagData

namespace FlagData

variable {M : Type*} {S : Finset ι} {C : ∀ s, MPSTensor d (D s)} {B : MPSTensor d DB}

/-- **The flag of the compression of a labelled invariant flag is that flag** (lecture note
MultiBlockUniqueness, Proposition 2.3 (Reductions are labelled flags with an adapted basis),
converse direction), up to the identification of the
number of steps with the number of slots. -/
theorem toMultiBlockCompression_flag (F : FlagData B.WordModule S C) (k : Fin (F.r + 1)) :
    F.toMultiBlockCompression.flag (Fin.cast (congrArg (· + 1) F.r_eq) k) = F.H k := by
  ext x
  rw [MultiBlockCompression.mem_flag_iff, F.mem_H_iff]
  have hcoord : ∀ y, F.toMultiBlockCompression.coord x y =
      F.adaptedCoord x (F.blockSpaceEquiv.symm y) := by
    intro y
    change F.gauge (WordModule.toVec B x) y = _
    simp only [FlagData.gauge, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
      LinearEquiv.funCongrLeft_apply]
    rfl
  have hord : ∀ y : BlockSpace D S F.z,
      ((F.toMultiBlockCompression.ord y.1 : Fin (S.card + F.z)) : ℕ) =
        ((F.blockSpaceEquiv.symm y).1 : ℕ) := fun _ => rfl
  constructor
  · intro h l j hkl
    have h1 := h (F.blockSpaceEquiv ⟨l, j⟩) (by
      rw [Fin.le_def, Fin.val_castSucc, hord, Equiv.symm_apply_apply]
      simpa using hkl)
    have h2 := hcoord (F.blockSpaceEquiv ⟨l, j⟩)
    rw [Equiv.symm_apply_apply] at h2
    exact h2.symm.trans h1
  · intro h y hy
    rw [hcoord]
    rw [Fin.le_def, Fin.val_castSucc] at hy
    exact h (F.blockSpaceEquiv.symm y).1 (F.blockSpaceEquiv.symm y).2 hy

end FlagData

end MPSTensor
