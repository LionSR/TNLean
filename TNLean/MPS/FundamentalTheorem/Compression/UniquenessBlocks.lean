/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.SimpleModule.Rank
import QICLean.Algebra.Module.CoveringMatching
import QICLean.Algebra.Module.Subquotient
import TNLean.MPS.FundamentalTheorem.WordModule.GaugeWordModule
import TNLean.MPS.FundamentalTheorem.Compression.IrreducibleTensor
import TNLean.MPS.FundamentalTheorem.Compression.LabelledFlag
import TNLean.MPS.Operator.Fusion.ZipperUniqueness

/-!
# The blocks of a multi-block reduction are unique

Let `P` and `Q` be two multi-block compressions of the same tensor `B`, onto nonzero irreducible
blocks `C s`, `s ∈ S`, with `z` zero slots, and onto nonzero irreducible blocks `C' t`, `t ∈ S'`,
with `z'` zero slots. The flags `M_k` of `P` and `M'_{k'}` of `Q` are covering chains of invariant
subspaces: the step `M_k / M_{k-1}` is the word module of the diagonal block at position `k`, which
is simple. The matching (blueprint `prop:asym_uniq_matching`, *The matching*) matches the steps of
the two chains: the step `k` goes to the least `k'` with `M_k ∩ M'_{k'} ⊄ M_{k-1}`, and with
`U = M_k ∩ M'_{k'}`, `K = M_{k-1} ∩ M'_{k'} = M_k ∩ M'_{k'-1}`, the inclusions of `U` induce
isomorphisms `U / K ≅ M_k / M_{k-1}` and `U / K ≅ M'_{k'} / M'_{k'-1}` of word-algebra modules.
Isomorphic word modules come from gauge related tensors. A zero slot has all letters zero and a
nonzero irreducible block has a nonzero letter, so the matching sends zero slots to zero slots and
block slots to block slots; this is the uniqueness of the blocks (blueprint `thm:asym_uniq_blocks`,
*The blocks are unique*): `z = z'` and the blocks agree up to a bijection of the labels and gauge.

## Main definitions

* `Submodule.subquotInfEquivOfLt`, `Submodule.subquotInfEquivOfLt'`: for two steps `P ⋖ Q`,
  `P' ⋖ Q'` of submodules satisfying the matching condition, the isomorphisms `U / K ≅ Q / P` and
  `U / K ≅ Q' / P'` induced by the inclusions (blueprint `lem:asym_uniq_step`, *One step against
  another*).
* `MPSTensor.MultiBlockCompression.coveringChain`: the flag of a compression onto nonzero
  irreducible blocks as a covering chain.
* `MPSTensor.MultiBlockCompression.matching`: the matching of the positions of two compressions.
* `MPSTensor.MultiBlockCompression.stepEquivMatching`: the matched diagonal blocks have isomorphic
  word modules.
* `MPSTensor.MultiBlockCompression.slotMatching`, `MPSTensor.MultiBlockCompression.labelMatching`:
  the matching read on the slot labels and on the block labels.

## Main results

* `Submodule.exists_subquotEquiv_of_covBy_of_lt`,
  `CoveringMatching.CoveringChain.nonempty_subquotEquiv_jumpEquiv`: one step against another, and
  matched steps of any two covering chains are isomorphic (blueprint `lem:asym_uniq_step`, *One step
  against another*; blueprint `prop:asym_uniq_matching`, *The matching*).
* `MPSTensor.MultiBlockCompression.matching_symm`, `MPSTensor.MultiBlockCompression.flag_sup_inf_eq`
  and its four companion identities: the matching (blueprint `prop:asym_uniq_matching`, *The
  matching*).
* `MPSTensor.isGaugeRelated_of_linearEquiv`: isomorphic word modules come from gauge related
  tensors.
* `MPSTensor.MultiBlockCompression.matching_inl_iff`, `MPSTensor.MultiBlockCompression.z_eq`,
  `MPSTensor.MultiBlockCompression.z_eq_and_exists_equiv_isGaugeRelated`: the uniqueness of the
  blocks (blueprint `thm:asym_uniq_blocks`, *The blocks are unique*).

## References

Blueprint chapter *The Multi-Block Asymmetric Fundamental Theorem* (`ch:asymmetric_ft`):
`lem:asym_uniq_step`, *One step against another*, `prop:asym_uniq_matching`, *The matching*, and
`thm:asym_uniq_blocks`, *The blocks are unique*.

## Gauge equivalence is isomorphism of word modules

Two tensors `A`, `A'` with `d` letters are gauge equivalent, `A i * X = X * A' i` for an invertible
`X`, exactly when their word modules are isomorphic modules over the free algebra on the letters.
One direction is `nonempty_linearEquiv_wordModule_of_isGaugeRelated`, the other
`isGaugeRelated_of_linearEquiv`; reflexivity, symmetry and transitivity of gauge equivalence are
`IsGaugeRelated.refl`, `IsGaugeRelated.symm` and `IsGaugeRelated.trans`.

### Main results

* `MPSTensor.isGaugeRelated_iff_nonempty_linearEquiv_wordModule`.
-/

section

open scoped Matrix

/-! ### One step against another: the step isomorphisms -/

namespace MPSTensor

open WordAlgebra

section Letters

variable {d D : ℕ}

/-- A one-dimensional module over the word algebra is simple. -/
theorem isSimpleModule_of_finrank_eq_one {M : Type*} [AddCommGroup M] [Module ℂ M]
    [Module (WordAlgebra d) M] [IsScalarTower ℂ (WordAlgebra d) M]
    (h : Module.finrank ℂ M = 1) : IsSimpleModule (WordAlgebra d) M := by
  have : IsSimpleModule ℂ M := isSimpleModule_iff_finrank_eq_one.2 h
  have : Nontrivial M := Module.nontrivial_of_finrank_eq_succ h
  refine (isSimpleModule_iff (WordAlgebra d) M).2 ⟨fun K => ?_⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top (K.restrictScalars ℂ) with hK | hK
  · exact Or.inl (Submodule.restrictScalars_injective ℂ _ _ (by simpa using hK))
  · exact Or.inr (Submodule.restrictScalars_injective ℂ _ _ (by simpa using hK))

end Letters

namespace MultiBlockCompression

variable {d DB : ℕ} {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {D : ι → ℕ} {D' : κ → ℕ}
  {B : MPSTensor d DB} {S : Finset ι} {S' : Finset κ} {C : ∀ s, MPSTensor d (D s)}
  {C' : ∀ t, MPSTensor d (D' t)}

omit [DecidableEq ι] in
/-- The diagonal block of a slot of a compression onto nonzero irreducible blocks has a simple word
module: a nonzero irreducible block, or a one-dimensional zero slot. -/
theorem isSimpleModule_slotTensor {z : ℕ} (hirr : ∀ s ∈ S, Matrix.IsIrreducibleAction (C s))
    (hlet : ∀ s ∈ S, ∃ i, C s i ≠ 0) (b : BlockIndex S z) :
    IsSimpleModule (WordAlgebra d) (slotTensor C b).WordModule := by
  rcases b with s | t
  · exact (isIrreducibleAction_and_pos_iff_isSimpleModule (C s.1)).1
      ⟨hirr s.1 s.2, dim_pos_of_exists_ne_zero (hlet s.1 s.2)⟩
  · refine isSimpleModule_of_finrank_eq_one ?_
    rw [(WordModule.toVec (slotTensor C (Sum.inr t : BlockIndex S z))).finrank_eq]
    simp

omit [DecidableEq ι] in
/-- On a zero slot every letter of the diagonal block vanishes; on a block slot of a compression
onto nonzero irreducible blocks some letter does not (proof of blueprint `thm:asym_uniq_blocks`,
*The blocks are unique*). -/
theorem forall_slotTensor_eq_zero_iff {z : ℕ} (hlet : ∀ s ∈ S, ∃ i, C s i ≠ 0)
    (b : BlockIndex S z) :
    (∀ i, slotTensor C b i = 0) ↔ b.isRight := by
  rcases b with s | t
  · simp only [Sum.isRight_inl, Bool.false_eq_true, iff_false, not_forall]
    exact hlet s.1 s.2
  · simp only [Sum.isRight_inr, iff_true]
    intro i
    rfl

variable (P : MultiBlockCompression B S C) (Q : MultiBlockCompression B S' C')

/-- The step of the flag at position `k` is the word module of the diagonal block of the slot at
position `k` (blueprint `prop:asym_uniq_dictionary`, *A compression is a labelled flag with an
adapted basis*), indexed by the position. -/
noncomputable def stepEquivAt (k : Fin (S.card + P.z)) :
    Submodule.subquot (P.flag k.castSucc) (P.flag k.succ) ≃ₗ[WordAlgebra d]
      (slotTensor C (P.ord.symm k)).WordModule :=
  (Submodule.subquotCongr (by rw [P.ord.apply_symm_apply]) (by rw [P.ord.apply_symm_apply])).trans
    (P.stepEquiv (P.ord.symm k))

/-- The steps of the flag of a compression onto nonzero irreducible blocks are covering pairs:
nothing invariant lies strictly between `M_{k-1}` and `M_k`, because the step is a simple module
(blueprint `prop:asym_uniq_matching`, *The matching*). -/
theorem flag_covBy (hirr : ∀ s ∈ S, Matrix.IsIrreducibleAction (C s)) (hlet : ∀ s ∈ S, ∃ i,
    C s i ≠ 0)
    (k : Fin (S.card + P.z)) : P.flag k.castSucc ⋖ P.flag k.succ := by
  have := isSimpleModule_slotTensor hirr hlet (P.ord.symm k)
  exact (covBy_iff_quot_is_simple (P.flag_mono (Fin.castSucc_le_succ k))).2
    (IsSimpleModule.congr (P.stepEquivAt k))

/-- **The flag of a compression onto nonzero irreducible blocks is a covering chain** (blueprint
`prop:asym_uniq_matching`, *The matching*): `⊥ = M_0 ⋖ M_1 ⋖ ⋯ ⋖ M_r = ⊤` in the lattice of
invariant subspaces of the bond space. -/
noncomputable def coveringChain (hirr : ∀ s ∈ S, Matrix.IsIrreducibleAction (C s))
    (hlet : ∀ s ∈ S, ∃ i, C s i ≠ 0) :
    CoveringMatching.CoveringChain (Submodule (WordAlgebra d) B.WordModule) (S.card + P.z) where
  toFun := P.flag
  toFun_zero := P.flag_zero
  toFun_last := P.flag_last
  covBy := P.flag_covBy hirr hlet

variable (hirr : ∀ s ∈ S, Matrix.IsIrreducibleAction (C s)) (hlet : ∀ s ∈ S, ∃ i, C s i ≠ 0)
  (hirr' : ∀ t ∈ S', Matrix.IsIrreducibleAction (C' t)) (hlet' : ∀ t ∈ S', ∃ i, C' t i ≠ 0)

/-- **The matching of two compressions** (blueprint `prop:asym_uniq_matching`, *The matching*): the
position `k` of `P` goes to the least position `k'` of `Q` with `M_k ∩ M'_{k'} ⊄ M_{k-1}`. -/
noncomputable def matching : Fin (S.card + P.z) ≃ Fin (S'.card + Q.z) :=
  (P.coveringChain hirr hlet).jumpEquiv (Q.coveringChain hirr' hlet')

theorem matching_apply (k : Fin (S.card + P.z)) :
    P.matching Q hirr hlet hirr' hlet' k =
      CoveringMatching.CoveringChain.jump (P.coveringChain hirr hlet)
      (Q.coveringChain hirr' hlet') k :=
  rfl

/-- The inverse of the matching is the matching with the two compressions exchanged (blueprint
`prop:asym_uniq_matching`, *The matching*). -/
theorem matching_symm :
    (P.matching Q hirr hlet hirr' hlet').symm = Q.matching P hirr' hlet' hirr hlet :=
  rfl

/-- The matching (blueprint `prop:asym_uniq_matching`, *The matching*) with the step lemma
(blueprint `lem:asym_uniq_step`, *One step against another*): for matched positions `k ↦ k'`,
`M_{k-1} + (M_k ∩ M'_{k'}) = M_k`. -/
theorem flag_sup_inf_eq (k : Fin (S.card + P.z)) :
    P.flag k.castSucc ⊔ (P.flag k.succ ⊓ Q.flag (P.matching Q hirr hlet hirr' hlet' k).succ) =
      P.flag k.succ :=
  (CoveringMatching.CoveringChain.jump_sup_eq (P.coveringChain hirr hlet)
    (Q.coveringChain hirr' hlet') k).1

/-- The matching (blueprint `prop:asym_uniq_matching`, *The matching*) with the step lemma
(blueprint `lem:asym_uniq_step`, *One step against another*): for matched positions `k ↦ k'`,
`M'_{k'-1} + (M_k ∩ M'_{k'}) = M'_{k'}`. -/
theorem flag_sup_inf_eq' (k : Fin (S.card + P.z)) :
    Q.flag (P.matching Q hirr hlet hirr' hlet' k).castSucc ⊔
        (P.flag k.succ ⊓ Q.flag (P.matching Q hirr hlet hirr' hlet' k).succ) =
      Q.flag (P.matching Q hirr hlet hirr' hlet' k).succ :=
  (CoveringMatching.CoveringChain.jump_sup_eq (P.coveringChain hirr hlet)
    (Q.coveringChain hirr' hlet') k).2.1

/-- The matching (blueprint `prop:asym_uniq_matching`, *The matching*) with the step lemma
(blueprint `lem:asym_uniq_step`, *One step against another*): for matched positions `k ↦ k'`,
`U ∩ M_{k-1} = K`, where `U = M_k ∩ M'_{k'}` and `K = M_{k-1} ∩ M'_{k'}`. -/
theorem flag_inf_inf_eq (k : Fin (S.card + P.z)) :
    P.flag k.succ ⊓ Q.flag (P.matching Q hirr hlet hirr' hlet' k).succ ⊓ P.flag k.castSucc =
      P.flag k.castSucc ⊓ Q.flag (P.matching Q hirr hlet hirr' hlet' k).succ :=
  (CoveringMatching.CoveringChain.jump_sup_eq (P.coveringChain hirr hlet)
    (Q.coveringChain hirr' hlet') k).2.2.1

/-- The matching (blueprint `prop:asym_uniq_matching`, *The matching*) with the step lemma
(blueprint `lem:asym_uniq_step`, *One step against another*): for matched positions `k ↦ k'`,
`U ∩ M'_{k'-1} = K`, where `U = M_k ∩ M'_{k'}` and `K = M_{k-1} ∩ M'_{k'}`. -/
theorem flag_inf_inf_eq' (k : Fin (S.card + P.z)) :
    P.flag k.succ ⊓ Q.flag (P.matching Q hirr hlet hirr' hlet' k).succ ⊓
        Q.flag (P.matching Q hirr hlet hirr' hlet' k).castSucc =
      P.flag k.castSucc ⊓ Q.flag (P.matching Q hirr hlet hirr' hlet' k).succ :=
  (CoveringMatching.CoveringChain.jump_sup_eq (P.coveringChain hirr hlet)
    (Q.coveringChain hirr' hlet') k).2.2.2.1

/-- The matching (blueprint `prop:asym_uniq_matching`, *The matching*) with the step lemma
(blueprint `lem:asym_uniq_step`, *One step against another*): for matched positions `k ↦ k'`,
`M_{k-1} ∩ M'_{k'} = M_k ∩ M'_{k'-1}`. -/
theorem flag_inf_eq (k : Fin (S.card + P.z)) :
    P.flag k.castSucc ⊓ Q.flag (P.matching Q hirr hlet hirr' hlet' k).succ =
      P.flag k.succ ⊓ Q.flag (P.matching Q hirr hlet hirr' hlet' k).castSucc :=
  (CoveringMatching.CoveringChain.jump_sup_eq (P.coveringChain hirr hlet)
    (Q.coveringChain hirr' hlet') k).2.2.2.2

/-- **The matched steps are isomorphic** (blueprint `lem:asym_uniq_step`, *One step against
another*; blueprint `prop:asym_uniq_matching`, *The matching*): with `U = M_k ∩ M'_{k'}` and
`K = U ∩ M_{k-1} = U ∩ M'_{k'-1}`, the second isomorphism theorem gives
`U / K ≅ (U + M_{k-1}) / M_{k-1} = M_k / M_{k-1}` and likewise `U / K ≅ M'_{k'} / M'_{k'-1}`. -/
noncomputable def subquotEquivMatching (k : Fin (S.card + P.z)) :
    Submodule.subquot (P.flag k.castSucc) (P.flag k.succ) ≃ₗ[WordAlgebra d]
      Submodule.subquot (Q.flag (P.matching Q hirr hlet hirr' hlet' k).castSucc)
        (Q.flag (P.matching Q hirr hlet hirr' hlet' k).succ) :=
  (Submodule.subquotInfEquivOfLt (P.flag_covBy hirr hlet k)
      ((P.coveringChain hirr hlet).jump_spec (Q.coveringChain hirr' hlet') k)).symm.trans
    (Submodule.subquotInfEquivOfLt' (P.flag_covBy hirr hlet k) (Q.flag_covBy hirr' hlet' _)
      ((P.coveringChain hirr hlet).jump_spec (Q.coveringChain hirr' hlet') k))

/-- **The matched diagonal blocks have isomorphic word modules** (blueprint
`prop:asym_uniq_matching`, *The matching*): the step isomorphism of the matching composed with the
identifications of the two steps with the diagonal blocks at those positions. -/
noncomputable def stepEquivMatching (k : Fin (S.card + P.z)) :
    (slotTensor C (P.ord.symm k)).WordModule ≃ₗ[WordAlgebra d]
      (slotTensor C' (Q.ord.symm (P.matching Q hirr hlet hirr' hlet' k))).WordModule :=
  ((P.stepEquivAt k).symm.trans (P.subquotEquivMatching Q hirr hlet hirr' hlet' k)).trans
    (Q.stepEquivAt (P.matching Q hirr hlet hirr' hlet' k))

/-- **The matched diagonal blocks are gauge related** (blueprint `prop:asym_uniq_matching`, *The
matching*). -/
theorem isGaugeRelated_matching (k : Fin (S.card + P.z)) :
    IsGaugeRelated (slotTensor C (P.ord.symm k))
      (slotTensor C' (Q.ord.symm (P.matching Q hirr hlet hirr' hlet' k))) :=
  isGaugeRelated_of_linearEquiv (P.stepEquivMatching Q hirr hlet hirr' hlet' k)

/-- The matching read on the slot labels: the slot at position `k` of `P` goes to the slot at
the matched position of `Q`. -/
noncomputable def slotMatching : BlockIndex S P.z ≃ BlockIndex S' Q.z :=
  P.ord.trans ((P.matching Q hirr hlet hirr' hlet').trans Q.ord.symm)

theorem slotMatching_apply (b : BlockIndex S P.z) :
    P.slotMatching Q hirr hlet hirr' hlet' b = Q.ord.symm (P.matching Q hirr hlet hirr' hlet'
    (P.ord b)) :=
  rfl

/-- **The slots matched with each other carry gauge related diagonal blocks** (blueprint
`prop:asym_uniq_matching`, *The matching*). -/
theorem isGaugeRelated_slotMatching (b : BlockIndex S P.z) :
    IsGaugeRelated (slotTensor C b) (slotTensor C' (P.slotMatching Q hirr hlet hirr' hlet' b)) := by
  have h := P.isGaugeRelated_matching Q hirr hlet hirr' hlet' (P.ord b)
  rw [P.ord.symm_apply_apply] at h
  exact h

/-- **The matching sends zero slots to zero slots** (proof of blueprint `thm:asym_uniq_blocks`, *The
blocks are unique*): a zero slot has all letters zero, a nonzero irreducible block has a nonzero
letter, and gauge related tensors have all letters zero together. -/
theorem isRight_slotMatching_iff (b : BlockIndex S P.z) :
    (P.slotMatching Q hirr hlet hirr' hlet' b).isRight ↔ b.isRight := by
  rw [← forall_slotTensor_eq_zero_iff hlet, ← forall_slotTensor_eq_zero_iff hlet',
    (P.isGaugeRelated_slotMatching Q hirr hlet hirr' hlet' b).forall_eq_zero_iff]

/-- **The matching sends block slots to block slots** (proof of blueprint `thm:asym_uniq_blocks`,
*The blocks are unique*). -/
theorem isLeft_slotMatching_iff (b : BlockIndex S P.z) :
    (P.slotMatching Q hirr hlet hirr' hlet' b).isLeft ↔ b.isLeft := by
  rw [← Sum.not_isRight, ← Sum.not_isRight, P.isRight_slotMatching_iff Q hirr hlet hirr' hlet']

/-- **The matching sends block positions to block positions** (proof of blueprint
`thm:asym_uniq_blocks`, *The blocks are unique*): the position `k` of `P` carries a block of `C`
exactly when the matched position of `Q` carries a block of `C'`. -/
theorem matching_inl_iff (k : Fin (S.card + P.z)) :
    (∃ t, Q.ord.symm (P.matching Q hirr hlet hirr' hlet' k) = Sum.inl t) ↔
      ∃ s, P.ord.symm k = Sum.inl s := by
  have h := P.isLeft_slotMatching_iff Q hirr hlet hirr' hlet' (P.ord.symm k)
  rw [slotMatching_apply, P.ord.apply_symm_apply] at h
  rw [← Sum.isLeft_iff, ← Sum.isLeft_iff, h]

include hirr hlet hirr' hlet' in
/-- **The numbers of zero slots agree** (blueprint `thm:asym_uniq_blocks`, *The blocks are unique*).
-/
theorem z_eq : P.z = Q.z :=
  Fin.equiv_iff_eq.mp ⟨Equiv.sumIsRight.symm.trans
    (((P.slotMatching Q hirr hlet hirr' hlet').subtypeEquiv fun b =>
      (P.isRight_slotMatching_iff Q hirr hlet hirr' hlet' b).symm).trans Equiv.sumIsRight)⟩

/-- The bijection of the block labels induced by the matching. -/
noncomputable def labelMatching : {s // s ∈ S} ≃ {t // t ∈ S'} :=
  Equiv.sumIsLeft.symm.trans
    (((P.slotMatching Q hirr hlet hirr' hlet').subtypeEquiv fun b =>
      (P.isLeft_slotMatching_iff Q hirr hlet hirr' hlet' b).symm).trans Equiv.sumIsLeft)

theorem slotMatching_inl (s : {s // s ∈ S}) :
    P.slotMatching Q hirr hlet hirr' hlet' (Sum.inl s) = Sum.inl
    (P.labelMatching Q hirr hlet hirr' hlet' s) := by
  simp [labelMatching]

include hirr hlet hirr' hlet' in
/-- **The blocks are unique** (blueprint `thm:asym_uniq_blocks`, *The blocks are unique*). Two
compressions of the same tensor onto nonzero irreducible blocks have the
same number of zero slots, and a bijection of the block labels pairs gauge related blocks. -/
theorem z_eq_and_exists_equiv_isGaugeRelated :
    P.z = Q.z ∧ ∃ τ : {s // s ∈ S} ≃ {t // t ∈ S'},
      ∀ s, IsGaugeRelated (C s.1) (C' (τ s).1) := by
  refine ⟨P.z_eq Q hirr hlet hirr' hlet', P.labelMatching Q hirr hlet hirr' hlet', fun s => ?_⟩
  have h := P.isGaugeRelated_slotMatching Q hirr hlet hirr' hlet' (Sum.inl s)
  rw [slotMatching_inl] at h
  exact h

/-- The paired blocks have equal bond dimensions (blueprint `thm:asym_uniq_blocks`, *The blocks are
unique*). -/
theorem dim_labelMatching (s : {s // s ∈ S}) :
    D s.1 = D' (P.labelMatching Q hirr hlet hirr' hlet' s).1 := by
  have h := P.isGaugeRelated_slotMatching Q hirr hlet hirr' hlet' (Sum.inl s)
  rw [slotMatching_inl] at h
  exact h.dim_eq

end MultiBlockCompression

end MPSTensor

end

section

namespace MPSTensor

variable {d : ℕ}

/-- **Word modules and gauges**. Two tensors are gauge equivalent if and only
if their word modules are isomorphic modules over the free algebra on the letters. -/
theorem isGaugeRelated_iff_nonempty_linearEquiv_wordModule {D₁ D₂ : ℕ} {A : MPSTensor d D₁}
    {A' : MPSTensor d D₂} :
    IsGaugeRelated A A' ↔ Nonempty (A.WordModule ≃ₗ[WordAlgebra d] A'.WordModule) :=
  ⟨nonempty_linearEquiv_wordModule_of_isGaugeRelated, fun ⟨e⟩ => isGaugeRelated_of_linearEquiv e⟩

end MPSTensor

end
