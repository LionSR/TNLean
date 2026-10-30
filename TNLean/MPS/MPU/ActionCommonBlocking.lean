/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.ReductionBlocking
import TNLean.MPS.MPU.GroupRepresentation
import TNLean.MPS.Symmetry.MPOSymmetry.PermutedBlocks

/-!
# Common blocking of action reductions

For a finite family of selected action reductions, one positive blocking length
makes one exterior site suffice for every pair `(g, x)`. The source action law
is retained explicitly as `CarriesMPV`: it supplies positive-length equality,
which certifies the residual nilpotency bounds. A selected reduction alone does
not supply that action law.

In arXiv:2502.20257, `main.tex` lines 1782--1873, the action tensors are
`V = A^Γ` and `W = A^{ref Γ}`. The interior identity holds for every word,
including the empty word; the exterior identity requires a nonempty central
word. See `docs/paper-gaps/fbc25_mpu_action_stabilizer_source_audit.tex`.

**Local fix (arXiv:2502.20257, `main.tex` line 1870):** the source assumes
blocking until all nilpotency lengths of the action tensors are one.  The
one-site exterior buffer proved below is the content of that sentence used
here.  The blocked residual letters need not vanish, and the blocked
nilpotency length of MGSC18 Definition 8 need not equal one; see
`docs/paper-gaps/mgsc18_nilpotency_length_one_terminology.tex`.
-/

open scoped Matrix Kronecker

namespace MPOTensor

variable {d D₁ D₂ : ℕ}

/-- Blocking commutes with the action tensor. The contracted input word is
reindexed by `decodeBlockEquiv`; the output uses the same blocked alphabet
on both sides.

Source: arXiv:2502.20257, `main.tex` lines 1789--1870. -/
theorem blockTensor_actTensor (T : MPOTensor d D₁) (A : MPSTensor d D₂) (L : ℕ) :
    MPSTensor.blockTensor (actTensor T A) L =
      actTensor (blockTensor T L) (MPSTensor.blockTensor A L) := by
  funext I
  change Kraus.evalWord (actTensor T A) (List.ofFn (Kraus.decodeBlock d L I)) = _
  rw [evalWord_actTensor, actTensor_apply]
  rw [← (Kraus.decodeBlockEquiv d L).sum_comp]
  rfl

namespace GroupFamily

universe u v

variable {G : Type u} [Group G] {F : GroupFamily G d}
  {X : Type v} [MulAction G X] {D : X → ℕ} {A : (x : X) → MPSTensor d (D x)}

omit [Group G] [MulAction G X] in
/-- Positive blocking preserves the periodic action law.
Source: arXiv:2502.20257, `main.tex` lines 1782--1870, with the explicit
periodic action hypothesis of arXiv:2203.12563, line 1064. -/
theorem CarriesMPV.blockTensor {D₃ : ℕ} {T : MPOTensor d D₁}
    {B : MPSTensor d D₂} {C : MPSTensor d D₃} (h : CarriesMPV T B C)
    {L : ℕ} (hL : 0 < L) :
    CarriesMPV (blockTensor T L) (MPSTensor.blockTensor B L) (MPSTensor.blockTensor C L) := by
  intro N hN
  rw [mpo_mulVec_mpv]
  funext σ
  rw [← blockTensor_actTensor]
  have hSame := h.sameMPV₂Pos_actTensor (MPSTensor.SameMPV₂Pos.refl B)
    (N * L) (Nat.mul_pos hN hL) (MPSTensor.blockedConfigEquiv d N L σ)
  simpa only [MPSTensor.mpv, MPSTensor.coeff, MPSTensor.evalWord_blockTensor,
    MPSTensor.ofFn_blockedConfigEquiv] using hSame

namespace BlockActionData

/-- The MGSC18 residual nilpotency length of the selected action reduction.
Source: arXiv:1706.07329v2, Definition 8; arXiv:2502.20257, line 1870. -/
noncomputable def nilpotencyLength (ad : BlockActionData F A) (g : G) (x : X) : ℕ :=
  MPSTensor.reductionResidualNilpotencyLength (actTensor (F.tensor g) (A x))
    (A (g • x)) (ad.V g x) (ad.W g x)

/-- Exterior action identity with buffers of at least `m` sites and a nonempty
central word. Source: arXiv:2502.20257, `eq:action_exterior`, lines 1789--1838. -/
def HasExteriorBufferLength (ad : BlockActionData F A) (m : ℕ) : Prop :=
  ∀ g x, MPSTensor.IsReductionExteriorBufferLength (actTensor (F.tensor g) (A x))
    (A (g • x)) (ad.V g x) (ad.W g x) m

/-- Blocking preserves the selected action reductions, with unchanged matrices
and block-dependent source and target bonds.
Source: arXiv:2502.20257, `eq:action_interior`, lines 1840--1870. -/
noncomputable def block (ad : BlockActionData F A) (L : ℕ) :
    BlockActionData (F.block L) (fun x ↦ MPSTensor.blockTensor (A x) L) where
  V := ad.V
  W := ad.W
  isReduction g x := by
    change MPSTensor.IsReduction
      (actTensor (blockTensor (F.tensor g) L) (MPSTensor.blockTensor (A x) L))
      (MPSTensor.blockTensor (A (g • x)) L) (ad.V g x) (ad.W g x)
    rw [← blockTensor_actTensor]
    exact (ad.isReduction g x).blockTensor L

/-- The interior action identity, including the empty word.
Source: arXiv:2502.20257, `eq:action_interior`, lines 1840--1870 (`n ≥ 0`). -/
theorem interior (ad : BlockActionData F A) (g : G) (x : X) (w : List (Fin d)) :
    ad.V g x * Kraus.evalWord (actTensor (F.tensor g) (A x)) w * ad.W g x =
      Kraus.evalWord (A (g • x)) w :=
  (ad.isReduction g x).evalWord w

/-- Source-form exterior identity, with a nonempty center and independently
sized buffers. Source: arXiv:2502.20257, `eq:action_exterior`, lines 1789--1870. -/
theorem exterior (ad : BlockActionData F A) {m : ℕ} (h : ad.HasExteriorBufferLength m)
    (g : G) (x : X) (p c q : List (Fin d)) (hc : c ≠ [])
    (hp : m ≤ p.length) (hq : m ≤ q.length) :
    Kraus.evalWord (actTensor (F.tensor g) (A x)) p * ad.W g x *
        Kraus.evalWord (A (g • x)) c * ad.V g x *
        Kraus.evalWord (actTensor (F.tensor g) (A x)) q =
      Kraus.evalWord (actTensor (F.tensor g) (A x)) (p ++ c ++ q) :=
  h g x p c q hc hp hq

/-- A single positive length bounding all residual buffer lengths gives every
blocked action reduction a one-site exterior buffer. The action law is an
explicit hypothesis, as required by the equality case of MGSC18.
Source: arXiv:2502.20257, `main.tex` line 1870. -/
theorem block_hasExteriorBufferLength_one (ad : BlockActionData F A)
    (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x)))
    {L : ℕ} (hL : 0 < L) (hN : ∀ g x, ad.nilpotencyLength g x ≤ L + 1) :
    (ad.block L).HasExteriorBufferLength 1 := by
  intro g x
  change MPSTensor.IsReductionExteriorBufferLength
    (actTensor (blockTensor (F.tensor g) L) (MPSTensor.blockTensor (A x) L))
    (MPSTensor.blockTensor (A (g • x)) L) (ad.V g x) (ad.W g x) 1
  rw [← blockTensor_actTensor]
  exact ((ad.isReduction g x).isReductionExteriorBufferLength_nilpotencyLength
    ((hperm g x).sameMPV₂Pos_actTensor (MPSTensor.SameMPV₂Pos.refl _))).blockTensor hL
      (by have := hN g x; change ad.nilpotencyLength g x - 1 ≤ 1 * L; omega)

section Finite

variable [Fintype G] [Fintype X]

/-- One common length for all action pairs, including the empty label family:
`max 1 (sup (N₀(g,x) - 1))`.
Source: arXiv:2502.20257, `main.tex` line 1870, interpreted as exterior blocking. -/
noncomputable def commonBufferLength (ad : BlockActionData F A) : ℕ :=
  _root_.commonBufferLength fun p : G × X ↦ ad.nilpotencyLength p.1 p.2

/-- The common action blocking length is positive. -/
theorem commonBufferLength_pos (ad : BlockActionData F A) : 0 < ad.commonBufferLength :=
  _root_.commonBufferLength_pos _

/-- Every action reduction's nilpotency length is at most the common length plus one. -/
theorem nilpotencyLength_le_commonBufferLength_add_one (ad : BlockActionData F A)
    (g : G) (x : X) : ad.nilpotencyLength g x ≤ ad.commonBufferLength + 1 :=
  le_commonBufferLength_add_one (fun p : G × X ↦ ad.nilpotencyLength p.1 p.2) (g, x)

/-- For an empty label family the common length is one, without choosing a label. -/
theorem commonBufferLength_of_isEmpty [IsEmpty X] (ad : BlockActionData F A) :
    ad.commonBufferLength = 1 := by
  simp [commonBufferLength, _root_.commonBufferLength, Finset.univ_eq_empty]

/-- One common blocking makes one exterior site suffice for every action pair.
Source: arXiv:2502.20257, `main.tex` line 1870. -/
theorem block_commonBufferLength_hasExteriorBufferLength_one (ad : BlockActionData F A)
    (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x))) :
    (ad.block ad.commonBufferLength).HasExteriorBufferLength 1 :=
  ad.block_hasExteriorBufferLength_one hperm ad.commonBufferLength_pos
    ad.nilpotencyLength_le_commonBufferLength_add_one

end Finite

/-- Reciprocal scalar action gauge: `W ↦ γ W` and `V ↦ γ⁻¹ V`.
Source: arXiv:2502.20257, `eq:scalar_act_ten`, lines 1871--1873.
This preserves the actual interior equations, including the empty word; it
does not claim that all bare reductions differ only by scalars. -/
noncomputable def smul (ad : BlockActionData F A) (γ : G → X → ℂ)
    (hγ : ∀ g x, γ g x ≠ 0) : BlockActionData F A where
  V g x := (γ g x)⁻¹ • ad.V g x
  W g x := γ g x • ad.W g x
  isReduction g x := (ad.isReduction g x).reciprocal_smul (hγ g x)

/-- Reciprocal action gauge preserves the actual exterior identities for the
same buffer length, in both directions.
Source: arXiv:2502.20257, `eq:scalar_act_ten`, lines 1871--1873. -/
theorem hasExteriorBufferLength_smul (ad : BlockActionData F A) (γ : G → X → ℂ)
    (hγ : ∀ g x, γ g x ≠ 0) (m : ℕ) :
    (ad.smul γ hγ).HasExteriorBufferLength m ↔ ad.HasExteriorBufferLength m := by
  unfold HasExteriorBufferLength
  exact forall_congr' fun g ↦ forall_congr' fun x ↦
    MPSTensor.IsReductionExteriorBufferLength.reciprocal_smul_iff (hγ g x)

/-- Physical blocking commutes with reciprocal scalar action gauge. -/
theorem block_smul (ad : BlockActionData F A) (γ : G → X → ℂ)
    (hγ : ∀ g x, γ g x ≠ 0) (L : ℕ) :
    (ad.smul γ hγ).block L = (ad.block L).smul γ hγ := rfl

end BlockActionData

/-- Common blocking of action reductions for finite families of normal blocks
of positive dimension. The action law is retained explicitly. The resulting
reductions satisfy the all-word interior identity and the one-site-buffer
exterior identity with nonempty center.

Source: arXiv:2502.20257, `main.tex` lines 1782--1870, with the explicit
periodic action hypothesis of arXiv:2203.12563, line 1064. -/
theorem exists_block_blockActionData_one [Finite G] [Finite X]
    (hA : ∀ x, Kraus.IsNormal (A x)) (hD : ∀ x, 0 < D x)
    (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x))) :
    ∃ L : ℕ, 0 < L ∧ ∃ ad :
      BlockActionData (F.block L) (fun x ↦ MPSTensor.blockTensor (A x) L),
      ad.HasExteriorBufferLength 1 := by
  classical
  let := Fintype.ofFinite G
  let := Fintype.ofFinite X
  obtain ⟨ad⟩ := nonempty_blockActionData hA hD hperm
  exact ⟨ad.commonBufferLength, ad.commonBufferLength_pos,
    ad.block ad.commonBufferLength, ad.block_commonBufferLength_hasExteriorBufferLength_one hperm⟩

/-- In the transitive setting of arXiv:2502.20257, `main.tex` lines 1782--1873,
a finite group gives a finite label family, including when the label set is
empty. A single common block preserves the MPU representation, injectivity of
the state tensors, and the explicit periodic action law, and supplies action
reductions with the one-site exterior identity. No scalar gauge is supplied
as an existence premise.

The periodic action hypothesis is left implicit in the printed passage; it
is stated explicitly here as in arXiv:2203.12563, line 1064. -/
theorem exists_block_blockActionData_one_of_isPretransitive [Finite G]
    [MulAction.IsPretransitive G X] (hF : F.IsRepresentation)
    (hA : ∀ x, Kraus.IsInjective (A x)) (hD : ∀ x, 0 < D x)
    (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x))) :
    ∃ L : ℕ, 0 < L ∧ (F.block L).IsRepresentation ∧
      (∀ x, Kraus.IsInjective (MPSTensor.blockTensor (A x) L)) ∧
      (∀ g x, CarriesMPV ((F.block L).tensor g) (MPSTensor.blockTensor (A x) L)
        (MPSTensor.blockTensor (A (g • x)) L)) ∧
      ∃ ad : BlockActionData (F.block L) (fun x ↦ MPSTensor.blockTensor (A x) L),
        ad.HasExteriorBufferLength 1 := by
  classical
  have : Finite X := by
    rcases isEmpty_or_nonempty X with hX | hX
    · let := hX
      infer_instance
    · exact Finite.of_surjective (fun g : G ↦ g • Classical.choice hX)
        (fun x ↦ MulAction.exists_smul_eq G (Classical.choice hX) x)
  obtain ⟨L, hL, ad, had⟩ :=
    exists_block_blockActionData_one (fun x ↦ (hA x).isNormal) hD hperm
  refine ⟨L, hL, hF.block F L hL, ?_, fun g x ↦ (hperm g x).blockTensor hL, ad, had⟩
  intro x
  apply (MPSTensor.isNBlkInjective_iff_blockTensor_isInjective (A x) L).1
  simpa using MPSTensor.isNBlkInjective_mul_of_isNBlkInjective (A x) hL
    (Kraus.isNBlkInjective_one_of_isInjective (hA x))

end GroupFamily

end MPOTensor
