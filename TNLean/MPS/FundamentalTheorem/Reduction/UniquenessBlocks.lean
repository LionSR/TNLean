/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.SimpleModule.Rank
import TNLean.Algebra.CoveringMatching
import TNLean.Algebra.Subquotient
import TNLean.MPS.FundamentalTheorem.Reduction.UniquenessFlag
import TNLean.MPS.Symmetry.MPOSymmetry.ZipperUniqueness

/-!
# The blocks of a multi-block reduction are unique

Let `P` and `Q` be two multi-block compressions of the same tensor `B`, onto normal blocks `C s`,
`s ∈ S`, with `z` zero slots, and onto normal blocks `C' t`, `t ∈ S'`, with `z'` zero slots. The
flags `M_k` of `P` and `M'_{k'}` of `Q` are covering chains of invariant subspaces: the step
`M_k / M_{k-1}` is the word module of the diagonal block at position `k`, which is simple. The
matching (blueprint `prop:asym_uniq_matching`, *The matching*) matches the steps of the two chains:
the step `k` goes to the least `k'` with `M_k ∩ M'_{k'} ⊄ M_{k-1}`, and with `U = M_k ∩ M'_{k'}`,
`K = M_{k-1} ∩ M'_{k'} = M_k ∩ M'_{k'-1}`, the inclusions of `U` induce isomorphisms
`U / K ≅ M_k / M_{k-1}` and `U / K ≅ M'_{k'} / M'_{k'-1}` of word-algebra modules. Isomorphic word
modules come from gauge related tensors. A zero slot has all letters zero and a normal block has a
nonzero letter, so the matching sends zero slots to zero slots and block slots to block slots; this
is the uniqueness of the blocks (blueprint `thm:asym_uniq_blocks`, *The blocks are unique*):
`z = z'` and the blocks agree up to a bijection of the labels and gauge.

## Main definitions

* `Submodule.subquotInfEquivOfLt`, `Submodule.subquotInfEquivOfLt'`: for two steps `P ⋖ Q`,
  `P' ⋖ Q'` of submodules satisfying the matching condition, the isomorphisms `U / K ≅ Q / P` and
  `U / K ≅ Q' / P'` induced by the inclusions (blueprint `lem:asym_uniq_step`, *One step against
  another*).
* `MPSTensor.MultiBlockCompression.coveringChain`: the flag of a compression onto normal blocks as a
  covering chain.
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
-/

open scoped Matrix

/-! ### One step against another: the step isomorphisms -/

namespace Submodule

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- The second isomorphism theorem for a step: if `U ≤ Q`, `P ⊔ U = Q` and `U ⊓ P = K`, the
inclusion `U → Q` induces an isomorphism `U / K ≅ Q / P`. -/
noncomputable def subquotEquivOfSupEq {K U P Q : Submodule R M} (hUQ : U ≤ Q) (hsup : P ⊔ U = Q)
    (hinf : U ⊓ P = K) : subquot K U ≃ₗ[R] subquot P Q :=
  let f : U →ₗ[R] subquot P Q := (P.comap Q.subtype).mkQ ∘ₗ Submodule.inclusion hUQ
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨p, hp, u, hu, hpu⟩ := Submodule.mem_sup.1 (hsup.symm ▸ y.2 : (y : M) ∈ P ⊔ U)
    refine ⟨⟨u, hu⟩, (Submodule.Quotient.eq _).2 ?_⟩
    rw [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub,
      Submodule.coe_inclusion, ← hpu, sub_add_cancel_right]
    exact P.neg_mem hp
  have hker : LinearMap.ker f = K.comap U.subtype := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.mem_comap,
      Submodule.subtype_apply, Submodule.subtype_apply, Submodule.coe_inclusion, ← hinf]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  (Submodule.quotEquivOfEq _ _ hker.symm).trans (f.quotKerEquivOfSurjective hf)

/-- The isomorphism `U / K ≅ Q / P` is induced by the inclusion. -/
theorem subquotEquivOfSupEq_mk {K U P Q : Submodule R M} (hUQ : U ≤ Q) (hsup : P ⊔ U = Q)
    (hinf : U ⊓ P = K) (x : U) :
    subquotEquivOfSupEq hUQ hsup hinf (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨x, hUQ x.2⟩ := rfl

/-- The isomorphism `U / K ≅ Q / P` of the step lemma (blueprint `lem:asym_uniq_step`, *One step
against another*) for a step `P ⋖ Q` against `P'`, `Q'` with `P ⊔ (Q ⊓ P') < P ⊔ (Q ⊓ Q')`, where
`U = Q ⊓ Q'` and `K = P ⊓ Q'`. -/
noncomputable def subquotInfEquivOfLt {P₁ Q₁ P₂ Q₂ : Submodule R M} (h₁ : P₁ ⋖ Q₁)
    (h : P₁ ⊔ Q₁ ⊓ P₂ < P₁ ⊔ Q₁ ⊓ Q₂) :
    subquot (P₁ ⊓ Q₂) (Q₁ ⊓ Q₂) ≃ₗ[R] subquot P₁ Q₁ :=
  subquotEquivOfSupEq inf_le_left (CoveringMatching.step_sup_eq_of_lt h₁ h).1 <|
    le_antisymm (le_inf inf_le_right (inf_le_left.trans inf_le_right))
      (le_inf (le_inf (inf_le_left.trans h₁.le) inf_le_right) inf_le_left)

/-- The isomorphism `U / K ≅ Q' / P'` of the step lemma (blueprint `lem:asym_uniq_step`, *One step
against another*) for two steps `P ⋖ Q`, `P' ⋖ Q'` with `P ⊔ (Q ⊓ P') < P ⊔ (Q ⊓ Q')`, where
`U = Q ⊓ Q'` and `K = P ⊓ Q'`. -/
noncomputable def subquotInfEquivOfLt' {P₁ Q₁ P₂ Q₂ : Submodule R M} (h₁ : P₁ ⋖ Q₁)
    (h₂ : P₂ ⋖ Q₂) (h : P₁ ⊔ Q₁ ⊓ P₂ < P₁ ⊔ Q₁ ⊓ Q₂) :
    subquot (P₁ ⊓ Q₂) (Q₁ ⊓ Q₂) ≃ₗ[R] subquot P₂ Q₂ :=
  subquotEquivOfSupEq inf_le_right (CoveringMatching.step_sup_eq_of_lt' h₁ h₂ h).1 <| by
    rw [inf_assoc, inf_eq_right.2 h₂.le]
    exact (CoveringMatching.step_inf_eq_of_lt h₁ h₂ h).symm

/-- **One step against another** (blueprint `lem:asym_uniq_step`, *One step against another*): for
steps `P ⋖ Q` and `P' ⋖ Q'` of invariant subspaces with `P ⊔ (Q ⊓ P') < P ⊔ (Q ⊓ Q')` (the matching
condition), and `U = Q ⊓ Q'`, `K = P ⊓ Q'`, the inclusions induce isomorphisms `U / K ≅ Q / P` and
`U / K ≅ Q' / P'`. Stated for modules over any ring; for the word module of a tensor these are
isomorphisms commuting with the letters. No hypothesis on blocks. -/
theorem exists_subquotEquiv_of_covBy_of_lt {P₁ Q₁ P₂ Q₂ : Submodule R M} (h₁ : P₁ ⋖ Q₁)
    (h₂ : P₂ ⋖ Q₂) (h : P₁ ⊔ Q₁ ⊓ P₂ < P₁ ⊔ Q₁ ⊓ Q₂) :
    (∃ e : subquot (P₁ ⊓ Q₂) (Q₁ ⊓ Q₂) ≃ₗ[R] subquot P₁ Q₁,
      ∀ x : ↥(Q₁ ⊓ Q₂), e (Submodule.Quotient.mk x) =
        Submodule.Quotient.mk ⟨x.1, (Submodule.mem_inf.1 x.2).1⟩) ∧
    (∃ e : subquot (P₁ ⊓ Q₂) (Q₁ ⊓ Q₂) ≃ₗ[R] subquot P₂ Q₂,
      ∀ x : ↥(Q₁ ⊓ Q₂), e (Submodule.Quotient.mk x) =
        Submodule.Quotient.mk ⟨x.1, (Submodule.mem_inf.1 x.2).2⟩) :=
  ⟨⟨subquotInfEquivOfLt h₁ h, fun _ => rfl⟩, ⟨subquotInfEquivOfLt' h₁ h₂ h, fun _ => rfl⟩⟩

end Submodule

namespace CoveringMatching.CoveringChain

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- **Matched steps of two covering chains are isomorphic** (blueprint `prop:asym_uniq_matching`,
*The matching*): for any two chains of submodules with covering steps, not only the flags of two
reductions, the step `k` of the first and the matched step of the second are isomorphic modules. For
invariant flags of a tensor this is the coordinate-free form of "the induced letters are gauge
equivalent". -/
theorem nonempty_subquotEquiv_jumpEquiv {r r' : ℕ} (c : CoveringChain (Submodule R M) r)
    (c' : CoveringChain (Submodule R M) r') (k : Fin r) :
    Nonempty (Submodule.subquot (c.toFun k.castSucc) (c.toFun k.succ) ≃ₗ[R]
      Submodule.subquot (c'.toFun (c.jumpEquiv c' k).castSucc)
        (c'.toFun (c.jumpEquiv c' k).succ)) :=
  ⟨(Submodule.subquotInfEquivOfLt (c.covBy k) (c.jump_spec c' k)).symm.trans
    (Submodule.subquotInfEquivOfLt' (c.covBy k) (c'.covBy _) (c.jump_spec c' k))⟩

end CoveringMatching.CoveringChain

namespace MPSTensor

open WordAlgebra

section GaugeRelatedOfLinearEquiv

variable {d D₁ D₂ : ℕ}

/-- Isomorphic word modules come from gauge related tensors: a word-algebra isomorphism
`A.WordModule ≃ A'.WordModule` is, in coordinates, an invertible matrix intertwining the letters
(blueprint `prop:asym_uniq_matching`, *The matching*, last assertion). -/
theorem isGaugeRelated_of_linearEquiv {A : MPSTensor d D₁} {A' : MPSTensor d D₂}
    (e : A.WordModule ≃ₗ[WordAlgebra d] A'.WordModule) : IsGaugeRelated A A' := by
  let g : (Fin D₂ → ℂ) ≃ₗ[ℂ] (Fin D₁ → ℂ) :=
    ((WordModule.toVec A').symm.trans (e.symm.restrictScalars ℂ)).trans (WordModule.toVec A)
  have hg : ∀ (i : Fin d) (w : Fin D₂ → ℂ), g (A' i *ᵥ w) = A i *ᵥ g w := by
    intro i w
    obtain ⟨v, rfl⟩ := (WordModule.toVec A').surjective w
    simp only [g, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
      LinearEquiv.symm_apply_apply]
    rw [← asModuleEquiv_letter_smul, LinearEquiv.symm_apply_apply, map_smul,
      asModuleEquiv_letter_smul]
  refine ⟨LinearMap.toMatrix' (g : (Fin D₂ → ℂ) →ₗ[ℂ] (Fin D₁ → ℂ)),
    LinearMap.toMatrix' (g.symm : (Fin D₁ → ℂ) →ₗ[ℂ] (Fin D₂ → ℂ)), ?_, ?_, fun i => ?_⟩
  · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    ext w
    simp
  · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    ext w
    simp
  · refine Matrix.toLin'.injective (LinearMap.ext fun w => ?_)
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec,
      LinearEquiv.coe_coe, hg]

/-- Gauge related tensors have all letters zero together. -/
theorem IsGaugeRelated.forall_eq_zero_iff {A : MPSTensor d D₁} {A' : MPSTensor d D₂}
    (h : IsGaugeRelated A A') : (∀ i, A i = 0) ↔ ∀ i, A' i = 0 := by
  obtain ⟨X, Y, hXY, hYX, hint⟩ := h
  refine ⟨fun h0 i => ?_, fun h0 i => ?_⟩
  · calc A' i = Y * (A i * X) := by rw [hint, ← Matrix.mul_assoc, hYX, Matrix.one_mul]
      _ = 0 := by rw [h0, Matrix.zero_mul, Matrix.mul_zero]
  · calc A i = X * A' i * Y := by rw [← hint, Matrix.mul_assoc, hXY, Matrix.mul_one]
      _ = 0 := by rw [h0, Matrix.mul_zero, Matrix.zero_mul]

/-- Gauge related tensors have equal bond dimensions. -/
theorem IsGaugeRelated.dim_eq {A : MPSTensor d D₁} {A' : MPSTensor d D₂}
    (h : IsGaugeRelated A A') : D₁ = D₂ := by
  obtain ⟨X, Y, hXY, hYX, -⟩ := h
  let e : (Fin D₂ → ℂ) ≃ₗ[ℂ] (Fin D₁ → ℂ) :=
    LinearEquiv.ofLinearMap (Matrix.toLin' X) (Matrix.toLin' Y)
      (by rw [← Matrix.toLin'_mul, hXY, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, hYX, Matrix.toLin'_one])
  simpa using e.finrank_eq.symm

end GaugeRelatedOfLinearEquiv

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
/-- The diagonal block of a slot of a compression onto normal blocks has a simple word module:
a normal block of positive bond dimension, or a one-dimensional zero slot. -/
theorem isSimpleModule_slotTensor {z : ℕ} (hC : ∀ s ∈ S, Kraus.IsNormal (C s))
    (hD : ∀ s ∈ S, 0 < D s) (b : BlockIndex S z) :
    IsSimpleModule (WordAlgebra d) (slotTensor C b).WordModule := by
  rcases b with s | t
  · exact isSimpleModule_wordModule_of_isNormal (C s.1) (hC s.1 s.2) (hD s.1 s.2)
  · refine isSimpleModule_of_finrank_eq_one ?_
    rw [(WordModule.toVec (slotTensor C (Sum.inr t : BlockIndex S z))).finrank_eq]
    simp

omit [DecidableEq ι] in
/-- On a zero slot every letter of the diagonal block vanishes; on a block slot of a compression
onto normal blocks some letter does not (proof of blueprint `thm:asym_uniq_blocks`, *The blocks are
unique*). -/
theorem forall_slotTensor_eq_zero_iff {z : ℕ} (hC : ∀ s ∈ S, Kraus.IsNormal (C s))
    (hD : ∀ s ∈ S, 0 < D s) (b : BlockIndex S z) :
    (∀ i, slotTensor C b i = 0) ↔ b.isRight := by
  rcases b with s | t
  · simp only [Sum.isRight_inl, Bool.false_eq_true, iff_false, not_forall]
    have : NeZero (D s.1) := ⟨(hD s.1 s.2).ne'⟩
    exact exists_ne_zero_of_isNormal (hC s.1 s.2)
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

/-- The steps of the flag of a compression onto normal blocks are covering pairs: nothing invariant
lies strictly between `M_{k-1}` and `M_k`, because the step is a simple module (blueprint
`prop:asym_uniq_matching`, *The matching*). -/
theorem flag_covBy (hC : ∀ s ∈ S, Kraus.IsNormal (C s)) (hD : ∀ s ∈ S, 0 < D s)
    (k : Fin (S.card + P.z)) : P.flag k.castSucc ⋖ P.flag k.succ := by
  have := isSimpleModule_slotTensor hC hD (P.ord.symm k)
  exact (covBy_iff_quot_is_simple (P.flag_mono (Fin.castSucc_le_succ k))).2
    (IsSimpleModule.congr (P.stepEquivAt k))

/-- **The flag of a compression onto normal blocks is a covering chain** (blueprint
`prop:asym_uniq_matching`, *The matching*): `⊥ = M_0 ⋖ M_1 ⋖ ⋯ ⋖ M_r = ⊤` in the lattice of
invariant subspaces of the bond space. -/
noncomputable def coveringChain (hC : ∀ s ∈ S, Kraus.IsNormal (C s)) (hD : ∀ s ∈ S, 0 < D s) :
    CoveringMatching.CoveringChain (Submodule (WordAlgebra d) B.WordModule) (S.card + P.z) where
  toFun := P.flag
  toFun_zero := P.flag_zero
  toFun_last := P.flag_last
  covBy := P.flag_covBy hC hD

variable (hC : ∀ s ∈ S, Kraus.IsNormal (C s)) (hD : ∀ s ∈ S, 0 < D s)
  (hC' : ∀ t ∈ S', Kraus.IsNormal (C' t)) (hD' : ∀ t ∈ S', 0 < D' t)

/-- **The matching of two compressions** (blueprint `prop:asym_uniq_matching`, *The matching*): the
position `k` of `P` goes to the least position `k'` of `Q` with `M_k ∩ M'_{k'} ⊄ M_{k-1}`. -/
noncomputable def matching : Fin (S.card + P.z) ≃ Fin (S'.card + Q.z) :=
  (P.coveringChain hC hD).jumpEquiv (Q.coveringChain hC' hD')

theorem matching_apply (k : Fin (S.card + P.z)) :
    P.matching Q hC hD hC' hD' k =
      CoveringMatching.CoveringChain.jump (P.coveringChain hC hD) (Q.coveringChain hC' hD') k :=
  rfl

/-- The inverse of the matching is the matching with the two compressions exchanged (blueprint
`prop:asym_uniq_matching`, *The matching*). -/
theorem matching_symm : (P.matching Q hC hD hC' hD').symm = Q.matching P hC' hD' hC hD :=
  rfl

/-- The matching (blueprint `prop:asym_uniq_matching`, *The matching*) with the step lemma
(blueprint `lem:asym_uniq_step`, *One step against another*): for matched positions `k ↦ k'`,
`M_{k-1} + (M_k ∩ M'_{k'}) = M_k`. -/
theorem flag_sup_inf_eq (k : Fin (S.card + P.z)) :
    P.flag k.castSucc ⊔ (P.flag k.succ ⊓ Q.flag (P.matching Q hC hD hC' hD' k).succ) =
      P.flag k.succ :=
  (CoveringMatching.CoveringChain.jump_sup_eq (P.coveringChain hC hD)
    (Q.coveringChain hC' hD') k).1

/-- The matching (blueprint `prop:asym_uniq_matching`, *The matching*) with the step lemma
(blueprint `lem:asym_uniq_step`, *One step against another*): for matched positions `k ↦ k'`,
`M'_{k'-1} + (M_k ∩ M'_{k'}) = M'_{k'}`. -/
theorem flag_sup_inf_eq' (k : Fin (S.card + P.z)) :
    Q.flag (P.matching Q hC hD hC' hD' k).castSucc ⊔
        (P.flag k.succ ⊓ Q.flag (P.matching Q hC hD hC' hD' k).succ) =
      Q.flag (P.matching Q hC hD hC' hD' k).succ :=
  (CoveringMatching.CoveringChain.jump_sup_eq (P.coveringChain hC hD)
    (Q.coveringChain hC' hD') k).2.1

/-- The matching (blueprint `prop:asym_uniq_matching`, *The matching*) with the step lemma
(blueprint `lem:asym_uniq_step`, *One step against another*): for matched positions `k ↦ k'`,
`U ∩ M_{k-1} = K`, where `U = M_k ∩ M'_{k'}` and `K = M_{k-1} ∩ M'_{k'}`. -/
theorem flag_inf_inf_eq (k : Fin (S.card + P.z)) :
    P.flag k.succ ⊓ Q.flag (P.matching Q hC hD hC' hD' k).succ ⊓ P.flag k.castSucc =
      P.flag k.castSucc ⊓ Q.flag (P.matching Q hC hD hC' hD' k).succ :=
  (CoveringMatching.CoveringChain.jump_sup_eq (P.coveringChain hC hD)
    (Q.coveringChain hC' hD') k).2.2.1

/-- The matching (blueprint `prop:asym_uniq_matching`, *The matching*) with the step lemma
(blueprint `lem:asym_uniq_step`, *One step against another*): for matched positions `k ↦ k'`,
`U ∩ M'_{k'-1} = K`, where `U = M_k ∩ M'_{k'}` and `K = M_{k-1} ∩ M'_{k'}`. -/
theorem flag_inf_inf_eq' (k : Fin (S.card + P.z)) :
    P.flag k.succ ⊓ Q.flag (P.matching Q hC hD hC' hD' k).succ ⊓
        Q.flag (P.matching Q hC hD hC' hD' k).castSucc =
      P.flag k.castSucc ⊓ Q.flag (P.matching Q hC hD hC' hD' k).succ :=
  (CoveringMatching.CoveringChain.jump_sup_eq (P.coveringChain hC hD)
    (Q.coveringChain hC' hD') k).2.2.2.1

/-- The matching (blueprint `prop:asym_uniq_matching`, *The matching*) with the step lemma
(blueprint `lem:asym_uniq_step`, *One step against another*): for matched positions `k ↦ k'`,
`M_{k-1} ∩ M'_{k'} = M_k ∩ M'_{k'-1}`. -/
theorem flag_inf_eq (k : Fin (S.card + P.z)) :
    P.flag k.castSucc ⊓ Q.flag (P.matching Q hC hD hC' hD' k).succ =
      P.flag k.succ ⊓ Q.flag (P.matching Q hC hD hC' hD' k).castSucc :=
  (CoveringMatching.CoveringChain.jump_sup_eq (P.coveringChain hC hD)
    (Q.coveringChain hC' hD') k).2.2.2.2

/-- **The matched steps are isomorphic** (blueprint `lem:asym_uniq_step`, *One step against
another*; blueprint `prop:asym_uniq_matching`, *The matching*): with `U = M_k ∩ M'_{k'}` and
`K = U ∩ M_{k-1} = U ∩ M'_{k'-1}`, the second isomorphism theorem gives
`U / K ≅ (U + M_{k-1}) / M_{k-1} = M_k / M_{k-1}` and likewise `U / K ≅ M'_{k'} / M'_{k'-1}`. -/
noncomputable def subquotEquivMatching (k : Fin (S.card + P.z)) :
    Submodule.subquot (P.flag k.castSucc) (P.flag k.succ) ≃ₗ[WordAlgebra d]
      Submodule.subquot (Q.flag (P.matching Q hC hD hC' hD' k).castSucc)
        (Q.flag (P.matching Q hC hD hC' hD' k).succ) :=
  (Submodule.subquotInfEquivOfLt (P.flag_covBy hC hD k)
      ((P.coveringChain hC hD).jump_spec (Q.coveringChain hC' hD') k)).symm.trans
    (Submodule.subquotInfEquivOfLt' (P.flag_covBy hC hD k) (Q.flag_covBy hC' hD' _)
      ((P.coveringChain hC hD).jump_spec (Q.coveringChain hC' hD') k))

/-- **The matched diagonal blocks have isomorphic word modules** (blueprint
`prop:asym_uniq_matching`, *The matching*): the step isomorphism of the matching composed with the
identifications of the two steps with the diagonal blocks at those positions. -/
noncomputable def stepEquivMatching (k : Fin (S.card + P.z)) :
    (slotTensor C (P.ord.symm k)).WordModule ≃ₗ[WordAlgebra d]
      (slotTensor C' (Q.ord.symm (P.matching Q hC hD hC' hD' k))).WordModule :=
  ((P.stepEquivAt k).symm.trans (P.subquotEquivMatching Q hC hD hC' hD' k)).trans
    (Q.stepEquivAt (P.matching Q hC hD hC' hD' k))

/-- **The matched diagonal blocks are gauge related** (blueprint `prop:asym_uniq_matching`, *The
matching*). -/
theorem isGaugeRelated_matching (k : Fin (S.card + P.z)) :
    IsGaugeRelated (slotTensor C (P.ord.symm k))
      (slotTensor C' (Q.ord.symm (P.matching Q hC hD hC' hD' k))) :=
  isGaugeRelated_of_linearEquiv (P.stepEquivMatching Q hC hD hC' hD' k)

/-- The matching read on the slot labels: the slot at position `k` of `P` goes to the slot at
the matched position of `Q`. -/
noncomputable def slotMatching : BlockIndex S P.z ≃ BlockIndex S' Q.z :=
  P.ord.trans ((P.matching Q hC hD hC' hD').trans Q.ord.symm)

theorem slotMatching_apply (b : BlockIndex S P.z) :
    P.slotMatching Q hC hD hC' hD' b = Q.ord.symm (P.matching Q hC hD hC' hD' (P.ord b)) :=
  rfl

/-- **The slots matched with each other carry gauge related diagonal blocks** (blueprint
`prop:asym_uniq_matching`, *The matching*). -/
theorem isGaugeRelated_slotMatching (b : BlockIndex S P.z) :
    IsGaugeRelated (slotTensor C b) (slotTensor C' (P.slotMatching Q hC hD hC' hD' b)) := by
  have h := P.isGaugeRelated_matching Q hC hD hC' hD' (P.ord b)
  rw [P.ord.symm_apply_apply] at h
  exact h

/-- **The matching sends zero slots to zero slots** (proof of blueprint `thm:asym_uniq_blocks`, *The
blocks are unique*): a zero slot has all letters zero, a normal block has a nonzero letter, and
gauge related tensors have all letters zero together. -/
theorem isRight_slotMatching_iff (b : BlockIndex S P.z) :
    (P.slotMatching Q hC hD hC' hD' b).isRight ↔ b.isRight := by
  rw [← forall_slotTensor_eq_zero_iff hC hD, ← forall_slotTensor_eq_zero_iff hC' hD',
    (P.isGaugeRelated_slotMatching Q hC hD hC' hD' b).forall_eq_zero_iff]

/-- **The matching sends block slots to block slots** (proof of blueprint `thm:asym_uniq_blocks`,
*The blocks are unique*). -/
theorem isLeft_slotMatching_iff (b : BlockIndex S P.z) :
    (P.slotMatching Q hC hD hC' hD' b).isLeft ↔ b.isLeft := by
  rw [← Sum.not_isRight, ← Sum.not_isRight, P.isRight_slotMatching_iff Q hC hD hC' hD']

/-- **The matching sends block positions to block positions** (proof of blueprint
`thm:asym_uniq_blocks`, *The blocks are unique*): the position `k` of `P` carries a block of `C`
exactly when the matched position of `Q` carries a block of `C'`. -/
theorem matching_inl_iff (k : Fin (S.card + P.z)) :
    (∃ t, Q.ord.symm (P.matching Q hC hD hC' hD' k) = Sum.inl t) ↔
      ∃ s, P.ord.symm k = Sum.inl s := by
  have h := P.isLeft_slotMatching_iff Q hC hD hC' hD' (P.ord.symm k)
  rw [slotMatching_apply, P.ord.apply_symm_apply] at h
  rw [← Sum.isLeft_iff, ← Sum.isLeft_iff, h]

include hC hD hC' hD' in
/-- **The numbers of zero slots agree** (blueprint `thm:asym_uniq_blocks`, *The blocks are unique*).
-/
theorem z_eq : P.z = Q.z :=
  Fin.equiv_iff_eq.mp ⟨Equiv.sumIsRight.symm.trans
    (((P.slotMatching Q hC hD hC' hD').subtypeEquiv fun b =>
      (P.isRight_slotMatching_iff Q hC hD hC' hD' b).symm).trans Equiv.sumIsRight)⟩

/-- The bijection of the block labels induced by the matching. -/
noncomputable def labelMatching : {s // s ∈ S} ≃ {t // t ∈ S'} :=
  Equiv.sumIsLeft.symm.trans
    (((P.slotMatching Q hC hD hC' hD').subtypeEquiv fun b =>
      (P.isLeft_slotMatching_iff Q hC hD hC' hD' b).symm).trans Equiv.sumIsLeft)

theorem slotMatching_inl (s : {s // s ∈ S}) :
    P.slotMatching Q hC hD hC' hD' (Sum.inl s) = Sum.inl (P.labelMatching Q hC hD hC' hD' s) := by
  simp [labelMatching]

include hC hD hC' hD' in
/-- **The blocks are unique** (blueprint `thm:asym_uniq_blocks`, *The blocks are unique*). Two
compressions of the same tensor onto normal blocks of positive bond dimension have the same number
of zero slots, and a bijection of the block labels pairs gauge related blocks. -/
theorem z_eq_and_exists_equiv_isGaugeRelated :
    P.z = Q.z ∧ ∃ τ : {s // s ∈ S} ≃ {t // t ∈ S'},
      ∀ s, IsGaugeRelated (C s.1) (C' (τ s).1) := by
  refine ⟨P.z_eq Q hC hD hC' hD', P.labelMatching Q hC hD hC' hD', fun s => ?_⟩
  have h := P.isGaugeRelated_slotMatching Q hC hD hC' hD' (Sum.inl s)
  rw [slotMatching_inl] at h
  exact h

/-- The paired blocks have equal bond dimensions (blueprint `thm:asym_uniq_blocks`, *The blocks are
unique*). -/
theorem dim_labelMatching (s : {s // s ∈ S}) :
    D s.1 = D' (P.labelMatching Q hC hD hC' hD' s).1 := by
  have h := P.isGaugeRelated_slotMatching Q hC hD hC' hD' (Sum.inl s)
  rw [slotMatching_inl] at h
  exact h.dim_eq

end MultiBlockCompression

end MPSTensor
