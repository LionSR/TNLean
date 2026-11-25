/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PatchRewrite.PatchRewriteTruncation
import TNLean.PEPS.Approximation.Frames.FrameRegisters
import TNLean.PEPS.Approximation.PatchRewrite.SiteChainMonomials

/-!
# The small-patch rewrite as a sum of allowed monomials

The last step of the proof of the second assertion of Lemma 6.3 `lem:small-rewrite` of the
polynomial-PEPS manuscript reads every product term of the truncated branch expansion as a
monomial allowed by Theorem 5.2, on the registers of the two frames: at every party, the tags it
holds and the raw configurations of the sites it owns
(`TNLean.PEPS.Approximation.Frames.FrameRegisters`).

For a branch `(a, s, b)` and a choice of one vector on every open-leg group of its network, the
product term, placed in the tag block `|a⟩⟨b|`, is a scalar of modulus at most one times the
operator of the following monomial from the registers of `F_old` to the output of the gate
`SmallPatchRewrite.gateSystem` (`SmallPatchRewrite.exists_termChain`):

1. on the open input legs of each patch bra, the normalized covector of the term, contracted at
   the at most two old owners of these legs (a pair effect or a private map), the legs then being
   reset to `|0⟩`;
2. on every site touched by the branch, `|0⟩⟨0|`, contracted at the old owner and prepared at the
   new owner; this imposes the zero bras of the old-hole decoders and transfers the reset raw
   sites;
3. on the open output legs of each patch ket, the normalized vector of the term, prepared at the
   at most two new owners (a pair source or a private map) after contracting the zeros;
4. on the tags, `⟨b|` on the affected old tags and `|a⟩` on the affected new tags, each at its
   tag owner.

The first three steps are a monomial on the sheets (`SiteChain.termOp_eq_smul_prod`,
`EncodedFrame.exists_monomial_listProd`, `EncodedFrame.exists_zeroChain`), run beside the tags;
the last is one local operation at every party (`SmallPatchRewrite.tagChange`). The output of the
gate has the registers of `F_new` at the specified parties and those of `F_old` elsewhere, where
the two frames differ only by one-point tag factors of the affected holes: the gate then uses
only the specified parties.

Every site in no selected square is untouched and keeps its owner. The monomial uses only the
specified parties, with at most `2m` normalized pair sources and at most `2m` normalized pair
effects. Combined with the approximation by product terms (`exists_contractive_approx`), this
gives the contraction `M_δ` with `‖M_δ - M‖ ≤ δ` as a sum of at most `N k^{2m}` allowed
monomials with coefficients of modulus at most one (`exists_allowed_monomial_approx`), where `N`
is the number of branches and `k` the truncation rank; if every hole and every patch has at most
`D` cylinder terms, `N ≤ D^{r_new + m + r_old}` (`exists_allowed_monomial_approx_of_card_le`).

The frame construction fixes projectors whose numbers `∑_j d_j` of cylinder terms are bounded by
one fixed power of `L` (`05-frames.tex`, lines 34–46), and Lemma 6.3 has boundedly many patches
and affected holes and a bounded specified list of parties. Under these bounds, `D ≤ C L^c` and
`m`, `r_old`, `r_new` and the number of specified parties at most `b`, the choice `δ = L^{-a}`
gives at most `K L^e` monomials, with `K` and `e` explicit in `C`, `c`, `b` and `a`, whose
participating parties lie in one fixed list of at most `b` parties
(`exists_allowed_monomial_approx_polynomial`). This is the second assertion of Lemma 6.3.

The bound `D ≤ C L^c` is a property of the projectors that the source's setting fixes by
Proposition 4.1 `prop:patch` (`03-patches.tex`), so it enters these theorems as a hypothesis on
the cylinder data rather than being derived here; Proposition 4.1 is a separate result, and
composing it with these theorems discharges the hypothesis. This reading is recorded in
`docs/paper-gaps/polypeps_small_rewrite_monomials.tex`.

The expansion is stated in the canonical coordinates of the two frames, the tags of the untouched
holes first; the source compares frames after the canonical identification of tag orderings
(`05-frames.tex`, lines 74–75 and 84–85). Each monomial has at most `2m` pair sources and `2m`
pair effects, one of each per patch vertex with open legs, rather than one per open-leg group;
the source requires only a bounded number.

## Main definitions

* `EncodedFrame.SmallPatchRewrite.gateSystem`, `EncodedFrame.SmallPatchRewrite.gateConfigEquiv`:
  the output of the gate and its canonical coordinates.
* `EncodedFrame.SmallPatchRewrite.tagStep`, `EncodedFrame.SmallPatchRewrite.tagChange`,
  `EncodedFrame.SmallPatchRewrite.termMonomial`: the tag maps and the product term of a branch.

## Main results

* `EncodedFrame.SmallPatchRewrite.liftBranch_apply`: the tag block of a branch.
* `EncodedFrame.SmallPatchRewrite.op_termMonomial`: the operator of the product term of a branch.
* `EncodedFrame.SmallPatchRewrite.exists_termChain`: a product term as an allowed monomial.
* `EncodedFrame.SmallPatchRewrite.exists_allowed_monomial_approx`: the second assertion of
  Lemma 6.3, with the count `N k^{2m}`.
* `EncodedFrame.SmallPatchRewrite.exists_allowed_monomial_approx_of_card_le`: the same, with the
  number of cylinder terms as an explicit parameter.
* `EncodedFrame.SmallPatchRewrite.exists_allowed_monomial_approx_polynomial`: the second assertion
  of Lemma 6.3, with a count polynomial in `L`.
* `EncodedFrame.SmallPatchRewrite.exists_allowed_monomial_approx_refVec`: the same for `a = 30`,
  with reference-vector error at most `(2b + 1) L^{-20}`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Lemma 6.3 `lem:small-rewrite`,
  `05-frames.tex`, lines 188–217; proof lines 254–342, in particular lines 262–273 and 306–316;
  the bound on the cylinder terms, lines 34–46; allowed monomials, `04-compression.tex`,
  lines 32–35.

Source text: `openai/math` at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, file
`preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/`
`build/sections/05-frames.tex`. The statements and proofs here are formalized independently from
the manuscript; no upstream Lean proof text was reused.
-/

noncomputable section

open Matrix
open scoped Kronecker Matrix.Norms.L2Operator

namespace TNLean.PEPS.EncodedFrame

open ManyBody QuantumCircuit.Party SiteChain

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} {pos : ι → ℝ × ℝ} {Party : Type}

/-! ### Branches of the rewrite -/

namespace SmallPatchRewrite

variable (R : SmallPatchRewrite pos q Party)

/-- The entries of a matrix placed in the tag block of a branch. -/
theorem liftBranch_apply (β : R.Branch) (Y : Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (τ' : TagSpace (R.untouched ++ R.newAffected)) (c' : ι → Fin q)
    (τ : TagSpace (R.untouched ++ R.oldAffected)) (c : ι → Fin q) :
    R.liftBranch β Y (τ', c') (τ, c) =
      if (tagAppendEquiv R.untouched R.newAffected τ').2 = β.1 ∧
          (tagAppendEquiv R.untouched R.oldAffected τ).2 = β.2.2 ∧
          (tagAppendEquiv R.untouched R.newAffected τ').1 =
            (tagAppendEquiv R.untouched R.oldAffected τ).1 then Y c' c else 0 := by
  simp only [liftBranch, layoutEquiv, reindex_apply, submatrix_apply, Equiv.coe_fn_symm_mk,
    kroneckerMap_apply, tagLift, of_apply, Matrix.one_apply]
  by_cases h₁ : (tagAppendEquiv R.untouched R.newAffected τ').2 = β.1 <;>
    by_cases h₂ : (tagAppendEquiv R.untouched R.oldAffected τ).2 = β.2.2 <;>
    by_cases h₃ : (tagAppendEquiv R.untouched R.newAffected τ').1 =
      (tagAppendEquiv R.untouched R.oldAffected τ).1 <;> simp [h₁, h₂, h₃]

/-! ### The output of the gate and the tag maps of a branch -/

section Gate

variable [Fintype Party] [DecidableEq Party]

omit [Fintype Party] in
/-- A list of holes none of whose tags is held by `p` has one basis vector at `p`. -/
def tagSystemEquivUnit {p : Party} : (l : List (Hole pos q Party)) →
    (∀ h ∈ l, h.tagOwner ≠ p) → tagSystem l p ≃ Unit
  | [], _ => Equiv.refl Unit
  | h :: l, hl =>
    ((Equiv.cast (updateOn_of_notMem (Finset.notMem_singleton.mpr
        (Ne.symm (hl h List.mem_cons_self))))).prodCongr
      (tagSystemEquivUnit l fun h' hh' ↦ hl h' (List.mem_cons_of_mem _ hh'))).trans
      (Equiv.prodPUnit Unit)

omit [Fintype Party] [DecidableEq Party] in
theorem tagOwner_ne_of_mem_oldAffected (hR : R.Conditions) {p : Party} (hp : p ∉ R.parties) :
    ∀ h ∈ R.oldAffected, h.tagOwner ≠ p := fun h hh e ↦
  hp (e ▸ hR.tag_owners_mem h (List.mem_append_left _ hh))

omit [Fintype Party] [DecidableEq Party] in
theorem tagOwner_ne_of_mem_newAffected (hR : R.Conditions) {p : Party} (hp : p ∉ R.parties) :
    ∀ h ∈ R.newAffected, h.tagOwner ≠ p := fun h hh e ↦
  hp (e ▸ hR.tag_owners_mem h (List.mem_append_right _ hh))

omit [Fintype Party] in
/-- **The tags of the two frames at an unspecified party.** Such a party holds no affected tag
(condition (iv)), so its tags in both frames are those of the untouched holes. -/
def tagSwap (hR : R.Conditions) {p : Party} (hp : p ∉ R.parties) :
    tagSystem (R.untouched ++ R.newAffected) p ≃ tagSystem (R.untouched ++ R.oldAffected) p :=
  (tagSystemAppendEquiv _ _ p).trans
    (((Equiv.refl _).prodCongr
      ((tagSystemEquivUnit _ (R.tagOwner_ne_of_mem_newAffected hR hp)).trans
        (tagSystemEquivUnit _ (R.tagOwner_ne_of_mem_oldAffected hR hp)).symm)).trans
      (tagSystemAppendEquiv _ _ p).symm)

omit [Fintype Party] in
theorem tagSwap_fst (hR : R.Conditions) {p : Party} (hp : p ∉ R.parties)
    (y : tagSystem (R.untouched ++ R.newAffected) p) :
    (tagSystemAppendEquiv _ _ p (R.tagSwap hR hp y)).1 = (tagSystemAppendEquiv _ _ p y).1 := by
  simp [tagSwap]

omit [Fintype Party] in
/-- The tag basis at a party of the output of the gate: the tags of the new frame at the
specified parties and those of the old frame elsewhere. -/
def gateTag (p : Party) : Type :=
  if p ∈ R.parties then tagSystem (R.untouched ++ R.newAffected) p
  else tagSystem (R.untouched ++ R.oldAffected) p

omit [Fintype Party] in
theorem gateTag_of_mem {p : Party} (hp : p ∈ R.parties) :
    R.gateTag p = tagSystem (R.untouched ++ R.newAffected) p := by
  simp [gateTag, hp]

omit [Fintype Party] in
theorem gateTag_of_notMem {p : Party} (hp : p ∉ R.parties) :
    R.gateTag p = tagSystem (R.untouched ++ R.oldAffected) p := by
  simp [gateTag, hp]

instance (p : Party) : Fintype (R.gateTag p) := by
  unfold gateTag
  split_ifs <;> infer_instance

instance (p : Party) : DecidableEq (R.gateTag p) := by
  unfold gateTag
  split_ifs <;> infer_instance

variable (q) in
/-- **The output of the gate of the rewrite.** At every party, the tags of `gateTag` and the raw
configurations of the sites it owns in the new frame. It agrees with the registers of the new
frame at the specified parties and with those of the old frame elsewhere. -/
abbrev gateSystem (p : Party) : Type := R.gateTag p × Sheet.system q ⟨R.ownerNew⟩ p

omit [Fintype Party] in
/-- The tags of the new frame read as those of the output of the gate. -/
def gateTagEquiv (hR : R.Conditions) (p : Party) :
    tagSystem (R.untouched ++ R.newAffected) p ≃ R.gateTag p :=
  if hp : p ∈ R.parties then Equiv.cast (R.gateTag_of_mem hp).symm
  else (R.tagSwap hR hp).trans (Equiv.cast (R.gateTag_of_notMem hp).symm)

/-- The configurations of a system read on the parties of `Finset.univ`. -/
def univConfigEquiv (X : Party → Type) :
    Config X ≃ Config (fun s : ↥(Finset.univ : Finset Party) ↦ X s.1) where
  toFun x s := x s.1
  invFun z p := z ⟨p, Finset.mem_univ p⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The registers of the old frame, on the parties of `Finset.univ`, in canonical
coordinates. -/
def oldConfigEquiv : Config (fun s : ↥(Finset.univ : Finset Party) ↦ R.oldFrame.system s.1) ≃
    R.oldFrame.Layout :=
  (univConfigEquiv R.oldFrame.system).symm.trans R.oldFrame.configEquiv

/-- The output of the gate, on the parties of `Finset.univ`, in the canonical coordinates of
the new frame. -/
def gateConfigEquiv (hR : R.Conditions) :
    Config (fun s : ↥(Finset.univ : Finset Party) ↦ R.gateSystem q s.1) ≃ R.newFrame.Layout :=
  (Equiv.piCongrRight fun s : ↥(Finset.univ : Finset Party) ↦
      ((R.gateTagEquiv hR s.1).prodCongr (Equiv.refl _)).symm).trans
    ((univConfigEquiv R.newFrame.system).symm.trans R.newFrame.configEquiv)

/-- The tag map of a branch `(a, s, b)` at one party: `⟨b|` on its old affected tags and `|a⟩`
on its new affected tags, the identity on its untouched tags. -/
def tagStep (a : TagSpace R.newAffected) (b : TagSpace R.oldAffected) (p : Party) :
    Matrix (tagSystem (R.untouched ++ R.newAffected) p)
      (tagSystem (R.untouched ++ R.oldAffected) p) ℂ :=
  reindex (tagSystemAppendEquiv _ _ p).symm (tagSystemAppendEquiv _ _ p).symm
    ((1 : Matrix (tagSystem R.untouched p) (tagSystem R.untouched p) ℂ) ⊗ₖ
      (prepMatrix (Equiv.prodPUnit.{0, 0} _).symm
          (EuclideanSpace.single ((tagConfigEquiv R.newAffected).symm a p) (1 : ℂ)) *
        (prepMatrix (Equiv.prodPUnit.{0, 0} _).symm
          (EuclideanSpace.single ((tagConfigEquiv R.oldAffected).symm b p) (1 : ℂ)))ᴴ))

omit [Fintype Party] in
theorem tagStep_apply (a : TagSpace R.newAffected) (b : TagSpace R.oldAffected) (p : Party)
    (y : tagSystem (R.untouched ++ R.newAffected) p)
    (x : tagSystem (R.untouched ++ R.oldAffected) p) :
    R.tagStep a b p y x =
      if (tagSystemAppendEquiv _ _ p y).1 = (tagSystemAppendEquiv _ _ p x).1 ∧
          (tagSystemAppendEquiv _ _ p y).2 = (tagConfigEquiv R.newAffected).symm a p ∧
          (tagSystemAppendEquiv _ _ p x).2 = (tagConfigEquiv R.oldAffected).symm b p
      then 1 else 0 := by
  simp only [tagStep, reindex_apply, submatrix_apply, Equiv.symm_symm, kroneckerMap_apply,
    one_apply, mul_apply, prepMatrix_apply, conjTranspose_apply, Equiv.prodPUnit_symm_apply,
    PiLp.single_apply, Finset.univ_unique, Finset.sum_singleton, ite_true]
  split_ifs <;> simp_all

omit [Fintype Party] in
theorem norm_tagStep_le (a : TagSpace R.newAffected) (b : TagSpace R.oldAffected) (p : Party) :
    ‖R.tagStep a b p‖ ≤ 1 := by
  refine (l2_opNorm_reindex_le _ _ _).trans ((l2_opNorm_one_kronecker_le _).trans ?_)
  refine l2_opNorm_mul_le_one _ _ ((norm_prepMatrix_le _ _).trans (by simp)) ?_
  rw [l2_opNorm_conjTranspose]
  exact (norm_prepMatrix_le _ _).trans (by simp)

/-- The tag maps of a branch at every party of `Finset.univ`, beside the raw configurations of
the new frame. -/
def tagChange (hR : R.Conditions) (a : TagSpace R.newAffected) (b : TagSpace R.oldAffected)
    (s : ↥(Finset.univ : Finset Party)) :
    Matrix (R.gateSystem q s.1) (layoutSystem q (R.untouched ++ R.oldAffected) R.ownerNew s.1) ℂ :=
  reindex ((R.gateTagEquiv hR s.1).prodCongr (Equiv.refl _)) (Equiv.refl _)
    (R.tagStep a b s.1 ⊗ₖ (1 : Matrix (Sheet.system q ⟨R.ownerNew⟩ s.1)
      (Sheet.system q ⟨R.ownerNew⟩ s.1) ℂ))

theorem tagChange_apply (hR : R.Conditions) (a : TagSpace R.newAffected)
    (b : TagSpace R.oldAffected) (s : ↥(Finset.univ : Finset Party)) (y x) :
    R.tagChange hR a b s y x =
      R.tagStep a b s.1 ((R.gateTagEquiv hR s.1).symm y.1) x.1 * if y.2 = x.2 then 1 else 0 := by
  simp [tagChange, reindex_apply, kroneckerMap_apply, one_apply]

theorem norm_tagChange_le (hR : R.Conditions) (a : TagSpace R.newAffected)
    (b : TagSpace R.oldAffected) (s : ↥(Finset.univ : Finset Party)) :
    ‖R.tagChange hR a b s‖ ≤ 1 :=
  (l2_opNorm_reindex_le _ _ _).trans ((l2_opNorm_kronecker_one_le _).trans
    (R.norm_tagStep_le a b s.1))

omit [Fintype ι] [DecidableEq ι] [Fintype Party] [DecidableEq Party] in
private theorem cast_prod_left {A B C : Type} (h : A = B) (y : A × C) :
    cast (congrArg (· × C) h) y = (cast h y.1, y.2) := by
  subst h
  rfl

/-- **The tag maps act at the specified parties only.** At a party outside the specified list
the tag map of a branch is the identification of equal bases. -/
theorem tagChange_of_notMem (hR : R.Conditions) (a : TagSpace R.newAffected)
    (b : TagSpace R.oldAffected) {s : ↥(Finset.univ : Finset Party)} (hs : s.1 ∉ R.parties) :
    ∃ h : R.gateSystem q s.1 = layoutSystem q (R.untouched ++ R.oldAffected) R.ownerNew s.1,
      ∀ y x, R.tagChange hR a b s y x = if cast h y = x then 1 else 0 := by
  refine ⟨congrArg (· × _) (R.gateTag_of_notMem hs), fun y x ↦ ?_⟩
  have hsym : (R.gateTagEquiv hR s.1).symm y.1 =
      (R.tagSwap hR hs).symm (cast (R.gateTag_of_notMem hs) y.1) := by
    simp only [gateTagEquiv, hs, dite_false, Equiv.symm_trans_apply]
    rfl
  have hcast : cast (congrArg (· × _) (R.gateTag_of_notMem hs)) y =
      (cast (R.gateTag_of_notMem hs) y.1, y.2) :=
    cast_prod_left _ y
  set w := cast (R.gateTag_of_notMem hs) y.1
  have hu₁ : ∀ z z' : tagSystem R.oldAffected s.1, z = z' := fun z z' ↦
    (tagSystemEquivUnit _ (R.tagOwner_ne_of_mem_oldAffected hR hs)).injective rfl
  have hu₂ : ∀ z z' : tagSystem R.newAffected s.1, z = z' := fun z z' ↦
    (tagSystemEquivUnit _ (R.tagOwner_ne_of_mem_newAffected hR hs)).injective rfl
  rw [tagChange_apply, hsym, tagStep_apply, hcast]
  have hfst : (tagSystemAppendEquiv _ _ s.1 ((R.tagSwap hR hs).symm w)).1 =
      (tagSystemAppendEquiv _ _ s.1 w).1 := by
    rw [← R.tagSwap_fst hR hs, Equiv.apply_symm_apply]
  rw [hfst]
  have hw : (tagSystemAppendEquiv _ _ s.1 w).1 = (tagSystemAppendEquiv _ _ s.1 x.1).1 ↔
      w = x.1 := by
    refine ⟨fun h ↦ (tagSystemAppendEquiv _ _ s.1).injective (Prod.ext h (hu₁ _ _)),
      fun h ↦ h ▸ rfl⟩
  by_cases h₁ : w = x.1 <;> by_cases h₂ : y.2 = x.2 <;>
    simp [hw, h₁, h₂, hu₂ _ ((tagConfigEquiv R.newAffected).symm a s.1),
      hu₁ _ ((tagConfigEquiv R.oldAffected).symm b s.1), Prod.ext_iff]

/-- The tag maps of a branch at all parties, in canonical coordinates: the tag block `|a⟩⟨b|`
beside the identity on the untouched tags. -/
theorem prod_tagStep (a : TagSpace R.newAffected) (b : TagSpace R.oldAffected)
    (y : Config (tagSystem (R.untouched ++ R.newAffected)))
    (x : Config (tagSystem (R.untouched ++ R.oldAffected))) :
    (∏ s : ↥(Finset.univ : Finset Party), R.tagStep a b s.1 (y s.1) (x s.1)) =
      if (tagAppendEquiv R.untouched R.newAffected (tagConfigEquiv _ y)).2 = a ∧
          (tagAppendEquiv R.untouched R.oldAffected (tagConfigEquiv _ x)).2 = b ∧
          (tagAppendEquiv R.untouched R.newAffected (tagConfigEquiv _ y)).1 =
            (tagAppendEquiv R.untouched R.oldAffected (tagConfigEquiv _ x)).1
      then 1 else 0 := by
  simp only [tagStep_apply, Finset.prod_boole, Finset.mem_univ, true_implies]
  refine if_congr ?_ rfl rfl
  rw [tagAppendEquiv_tagConfigEquiv, tagAppendEquiv_tagConfigEquiv]
  simp only [← Equiv.eq_symm_apply, (tagConfigEquiv R.untouched).apply_eq_iff_eq,
    funext_iff]
  exact ⟨fun h ↦ ⟨fun p ↦ (h ⟨p, Finset.mem_univ p⟩).2.1, fun p ↦ (h ⟨p, Finset.mem_univ p⟩).2.2,
    fun p ↦ (h ⟨p, Finset.mem_univ p⟩).1⟩, fun h s ↦ ⟨h.2.2 s.1, h.1 s.1, h.2.1 s.1⟩⟩

/-- The product term of a branch on the registers of the frames: a monomial `M` on the sheets,
beside the tags of the old frame, followed by the tag maps of the branch. -/
def termMonomial (hR : R.Conditions) (β : R.Branch)
    (M : Monomial (Finset.univ : Finset Party) (univSheet q R.ownerOld) (univSheet q R.ownerNew)) :
    Monomial (Finset.univ : Finset Party) (fun s ↦ R.oldFrame.system s.1)
      (fun s ↦ R.gateSystem q s.1) :=
  PartyCircuit.comp (M.frame fun s ↦ tagSystem (R.untouched ++ R.oldAffected) s.1)
    (PartyCircuit.localOps (R.tagChange hR β.1 β.2.2))

/-- **The operator of the product term of a branch.** If the monomial on the sheets has the
operator `Y` in canonical site coordinates, the product term has the operator of `Y` placed in
the tag block of the branch, in the canonical coordinates of the two frames. -/
theorem op_termMonomial (hR : R.Conditions) (β : R.Branch)
    (M : Monomial (Finset.univ : Finset Party) (univSheet q R.ownerOld) (univSheet q R.ownerNew))
    (Y : Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (hM : M.op chainEv = reindex (univSheetEquiv R.ownerNew).symm
      (univSheetEquiv R.ownerOld).symm Y) :
    (R.termMonomial hR β M).op chainEv =
      reindex (R.gateConfigEquiv hR).symm R.oldConfigEquiv.symm (R.liftBranch β Y) := by
  rw [termMonomial, PartyCircuit.op_comp (P := ↥(Finset.univ : Finset Party)) (G := ChainGate),
    PartyCircuit.op_localOps,
    PartyCircuit.op_frame (fun s ↦ tagSystem (R.untouched ++ R.oldAffected) s.1) chainEv
      chainEv_isCompatible_frame M, hM]
  ext y x
  rw [mul_apply, Finset.sum_eq_single (fun s ↦ ((x s).1, (y s).2)) (fun m _ hm ↦ ?_)
    (fun h ↦ absurd (Finset.mem_univ _) h)]
  · simp only [piKronecker_apply, R.tagChange_apply, reindex_apply, submatrix_apply,
      Equiv.symm_symm, kroneckerMap_apply, Equiv.arrowProdEquivProdArrow_apply, one_apply_eq,
      one_mul, ite_true, mul_one]
    rw [R.prod_tagStep β.1 β.2.2 (fun p ↦ (R.gateTagEquiv hR p).symm (y ⟨p, Finset.mem_univ p⟩).1)
      (fun p ↦ (x ⟨p, Finset.mem_univ p⟩).1), liftBranch_apply, boole_mul]
    rfl
  · simp only [piKronecker_apply, R.tagChange_apply, reindex_apply, submatrix_apply,
      Equiv.symm_symm, kroneckerMap_apply, Equiv.arrowProdEquivProdArrow_apply, one_apply]
    by_cases h₁ : (fun s ↦ (m s).1) = fun s ↦ (x s).1
    · have h₂ : ∃ s, (y s).2 ≠ (m s).2 := by
        by_contra h
        push Not at h
        exact hm (funext fun s ↦ Prod.ext (congrFun h₁ s) (h s).symm)
      obtain ⟨s, hs⟩ := h₂
      rw [Finset.prod_eq_zero (Finset.mem_univ s) (by simp [hs]), zero_mul]
    · simp [h₁]

end Gate

end SmallPatchRewrite

/-! ### Product terms as allowed monomials -/

section Terms

variable [NeZero q]

theorem exists_of_mem_encSteps {s : Step ι q} : (l : List (Hole pos q Party)) →
    (t : TagSpace l) → s ∈ encSteps l t → ∃ h ∈ l, ∃ j, s.sites = h.patch.tagSample j
  | [], _, hs => absurd hs List.not_mem_nil
  | h :: l, t, hs => by
    rcases List.mem_cons.mp hs with rfl | hs
    · exact ⟨h, List.mem_cons_self, t.1, rfl⟩
    · obtain ⟨h', hh', j, hj⟩ := exists_of_mem_encSteps l t.2 hs
      exact ⟨h', List.mem_cons_of_mem _ hh', j, hj⟩

theorem exists_of_mem_decSteps {s : Step ι q} : (l : List (Hole pos q Party)) →
    (t : TagSpace l) → s ∈ decSteps l t → ∃ h ∈ l, ∃ j, s.sites = h.patch.tagSample j
  | [], _, hs => absurd hs List.not_mem_nil
  | h :: l, t, hs => by
    rcases List.mem_append.mp hs with hs | hs
    · obtain ⟨h', hh', j, hj⟩ := exists_of_mem_decSteps l t.2 hs
      exact ⟨h', List.mem_cons_of_mem _ hh', j, hj⟩
    · rw [List.mem_singleton.mp hs]
      exact ⟨h, List.mem_cons_self, t.1, rfl⟩

namespace SmallPatchRewrite

variable (R : SmallPatchRewrite pos q Party)

/-- Every site of a step of a branch lies in the physical sample of a patch or of an affected
hole, so by condition (iv) its old and new owners belong to the specified list. -/
theorem owners_mem_parties_of_mem_branchSteps (hR : R.Conditions) (β : R.Branch)
    {s : Step ι q} (hs : s ∈ R.branchSteps β) {x : ι} (hx : x ∈ s.sites) :
    R.ownerOld x ∈ R.parties ∧ R.ownerNew x ∈ R.parties := by
  rcases List.mem_append.mp hs with hs | hs
  · rcases List.mem_append.mp hs with hs | hs
    · obtain ⟨h, hh, j, hj⟩ := exists_of_mem_encSteps _ _ hs
      obtain ⟨j', hj'⟩ := h.patch.exists_mem_sample_of_mem_tagSample (hj ▸ hx)
      exact R.owners_mem_parties_of_mem_sample hR
        (Or.inr ⟨h, List.mem_append_right _ hh, j', hj'⟩)
    · obtain ⟨P, hP, j, hj, -, -⟩ := exists_of_mem_patchSteps _ _ hs
      obtain ⟨j', hj'⟩ := P.exists_mem_sample_of_mem_tagSample (hj ▸ hx)
      exact R.owners_mem_parties_of_mem_sample hR (Or.inl ⟨P, hP, j', hj'⟩)
  · obtain ⟨h, hh, j, hj⟩ := exists_of_mem_decSteps _ _ hs
    obtain ⟨j', hj'⟩ := h.patch.exists_mem_sample_of_mem_tagSample (hj ▸ hx)
    exact R.owners_mem_parties_of_mem_sample hR
      (Or.inr ⟨h, List.mem_append_left _ hh, j', hj'⟩)

theorem owners_mem_parties_of_not_untouched (hR : R.Conditions) (β : R.Branch) {x : ι}
    (hx : ¬Untouched (R.branchChain β) x) :
    R.ownerOld x ∈ R.parties ∧ R.ownerNew x ∈ R.parties := by
  simp only [Untouched, not_forall, not_not] at hx
  obtain ⟨k, hk⟩ := hx
  exact R.owners_mem_parties_of_mem_branchSteps hR β (List.getElem_mem (l := R.branchSteps β) k.2)
    hk

/-- **A site touched by no step of a branch keeps its owner**, by condition (ii). -/
theorem ownerOld_eq_ownerNew_of_untouched (hR : R.Conditions) (β : R.Branch) {x : ι}
    (hx : Untouched (R.branchChain β) x) : R.ownerOld x = R.ownerNew x := by
  refine R.ownerOld_eq_ownerNew_of_direct hR β.2.1 fun hxP => ?_
  obtain ⟨s, hs, hxs⟩ := (mem_patchSquares_iff _ _).mp hxP
  obtain ⟨k, -, -, hk⟩ := exists_get_append₃_eq_mid (encSteps R.newAffected β.1)
    (patchSteps R.patches β.2.1) (decSteps R.oldAffected β.2.2) hs
  exact hx k (by
    change x ∈ ((encSteps R.newAffected β.1 ++ patchSteps R.patches β.2.1 ++
      decSteps R.oldAffected β.2.2).get k).sites
    rw [hk]
    exact hxs)

/-- The vertices of a branch network with open legs are at most `2m`. -/
theorem card_open_vertices_le (hR : R.Conditions) (β : R.Branch) :
    (∑ j, if ∃ x, IsOpen (R.branchChain β) (.inl j) x then 1 else 0) +
      (∑ j, if ∃ x, IsOpen (R.branchChain β) (.inr j) x then 1 else 0) ≤
        2 * R.patches.length := by
  classical
  rw [← Fintype.sum_sum_type (f := fun v => if ∃ x, IsOpen (R.branchChain β) v x then 1 else 0),
    Finset.sum_boole, Nat.cast_id]
  refine (Finset.card_le_card fun v hv => ?_).trans (R.card_patchVertices_le β)
  obtain ⟨x, hx⟩ := (Finset.mem_filter.mp hv).2
  exact R.mem_patchVertices_of_isOpen hR β hx

variable [Fintype Party] [DecidableEq Party]

/-- **A product term of a branch as an allowed monomial.** Under the four conditions of
Lemma 6.3, let `(a, s, b)` be a branch and let a unit vector be chosen on every open-leg group of
its network (one of the orthonormal families of the whole-group truncation). Then the product
term placed in the tag block, `|a⟩⟨b| ⊗ T ⊗ 1`, is `σ` times the operator of an allowed monomial
from the registers of `F_old` to the output of the gate (the registers of `F_new` at the
specified parties), in canonical coordinates, with `|σ| ≤ 1`. The monomial uses only the
specified parties and has at most `2m` normalized pair sources and at most `2m` normalized pair
effects. It consumes the open inputs of each patch bra by its normalized covector at their at
most two old owners, contracts every touched raw site with `⟨0|` at its old owner and prepares
`|0⟩` at its new owner, prepares the open outputs of each patch ket by its normalized vector at
their at most two new owners, and replaces the affected tags by `⟨b|` and `|a⟩` at their tag
owners; every other register is untouched.

Polynomial-PEPS manuscript, proof of Lemma 6.3, `05-frames.tex`, lines 262–273 and 306–316:
after restoring the factored private maps and direct identities, each product term is precisely
a monomial allowed by Theorem 5.2, with boundedly many pair states and effects and a coefficient
of absolute value at most one. -/
theorem exists_termChain (hR : R.Conditions) (β : R.Branch)
    {r : Fin (R.branchSteps β).length ⊕ Fin (R.branchSteps β).length → ℕ}
    (e : (v : Fin (R.branchSteps β).length ⊕ Fin (R.branchSteps β).length) → Fin (r v) →
      EuclideanSpace ℂ (Group (R.branchChain β) v))
    (he : ∀ v, Orthonormal ℂ (e v))
    (i : (v : Fin (R.branchSteps β).length ⊕ Fin (R.branchSteps β).length) → Fin (r v)) :
    ∃ (σ : ℂ) (M : Monomial (Finset.univ : Finset Party) (fun s ↦ R.oldFrame.system s.1)
        (fun s ↦ R.gateSystem q s.1)),
      ‖σ‖ ≤ 1 ∧ M.IsAllowed chainEv ChainGate.IsAllowed ∧ M.UsesOnly R.parties ∧
      M.sourceCount ≤ 2 * R.patches.length ∧ M.effectCount ≤ 2 * R.patches.length ∧
      σ • M.op chainEv = reindex (R.gateConfigEquiv hR).symm R.oldConfigEquiv.symm
        (R.liftBranch β (termOp (R.branchChain β) e i)) := by
  set S := R.parties
  have hbra := fun j : Fin (R.branchSteps β).length =>
    exists_braVertexBlock (q := q) R.ownerOld S (IsOpen (R.branchChain β) (.inl j))
      (fun _ => by
        obtain ⟨P, hP, hPx⟩ := R.exists_owners_of_isOpen_inl hR β j
        exact ⟨P, hP, fun x hx => ⟨(hPx x hx).1, (hPx x hx).2.1⟩⟩)
      (e (.inl j) (i (.inl j))) ((he _).1 _)
  choose B sB hsB hBE hBK hBB MB hMB₁ hMB₂ hMB₃ hMB₄ hMB₅ using hbra
  have hket := fun j : Fin (R.branchSteps β).length =>
    exists_ketVertexBlock (q := q) R.ownerNew S (IsOpen (R.branchChain β) (.inr j))
      (fun _ => by
        obtain ⟨P, hP, hPx⟩ := R.exists_owners_of_isOpen_inr hR β j
        exact ⟨P, hP, fun x hx => ⟨(hPx x hx).1, (hPx x hx).2.2⟩⟩)
      (e (.inr j) (i (.inr j))) ((he _).1 _)
  choose K sK hsK hKE hKB hKK MK hMK₁ hMK₂ hMK₃ hMK₄ hMK₅ using hket
  set W := (Finset.univ : Finset ι).toList.filter fun x => decide (¬Untouched (R.branchChain β) x)
    with hWdef
  have hWn : W.Nodup := (Finset.nodup_toList _).filter _
  have hW : ∀ x, x ∈ W ↔ ¬Untouched (R.branchChain β) x := fun x => by simp [hWdef]
  obtain ⟨M₁, a₁, a₂, a₃, a₄, a₅⟩ := exists_monomial_listProd (univSheetEquiv R.ownerOld) S
    (fun j => (B j).op)
    (fun j => if ∃ x, IsOpen (R.branchChain β) (.inl j) x then 1 else 0)
    (fun j => if ∃ x, IsOpen (R.branchChain β) (.inl j) x then 1 else 0)
    (List.finRange _) fun j _ => ⟨MB j, hMB₁ j, hMB₂ j, hMB₃ j, hMB₄ j, hMB₅ j⟩
  obtain ⟨M₂, b₁, b₂, b₃, b₄, b₅⟩ := exists_zeroChain (q := q) S W hWn R.ownerOld R.ownerNew
    (fun x hx => R.owners_mem_parties_of_not_untouched hR β ((hW x).mp hx))
    (fun x hx => R.ownerOld_eq_ownerNew_of_untouched hR β (by simpa [hW] using hx))
  obtain ⟨M₃, c₁, c₂, c₃, c₄, c₅⟩ := exists_monomial_listProd (univSheetEquiv R.ownerNew) S
    (fun j => (K j).op)
    (fun j => if ∃ x, IsOpen (R.branchChain β) (.inr j) x then 1 else 0)
    (fun j => if ∃ x, IsOpen (R.branchChain β) (.inr j) x then 1 else 0)
    (List.finRange _) fun j _ => ⟨MK j, hMK₁ j, hMK₂ j, hMK₃ j, hMK₄ j, hMK₅ j⟩
  have hsum : ∀ g : Fin (R.branchSteps β).length → ℕ,
      ((List.finRange _).map g).sum = ∑ j, g j := fun g => by
    rw [← List.ofFn_eq_map, List.sum_ofFn]
  have hcount := R.card_open_vertices_le hR β
  rw [hsum] at a₃ a₄ c₃ c₄
  have hprod : ∀ A : Fin (R.branchSteps β).length → RankOneBlock ι q,
      ((List.finRange _).map fun j => (A j).op) = (List.ofFn A).map RankOneBlock.op := fun A => by
    rw [List.ofFn_eq_map, List.map_map]
    rfl
  set Msh := (M₁.comp M₂).comp M₃
  have hMsh : Msh.op chainEv = reindex (univSheetEquiv R.ownerNew).symm
      (univSheetEquiv R.ownerOld).symm (((List.ofFn K).map RankOneBlock.op).prod *
        ((W.map (zeroBlock (q := q))).map RankOneBlock.op).prod *
        ((List.ofFn B).map RankOneBlock.op).prod) := by
    rw [PartyCircuit.op_comp (P := ↥(Finset.univ : Finset Party)) (G := ChainGate),
      PartyCircuit.op_comp (P := ↥(Finset.univ : Finset Party)) (G := ChainGate), c₅, b₅, a₅,
      hprod, hprod, reindex_apply, reindex_apply, reindex_apply, reindex_apply,
      submatrix_mul_equiv, submatrix_mul_equiv, Matrix.mul_assoc]
  have hframe : ∀ ⦃D : Finset ↥(Finset.univ : Finset Party)⦄
      ⦃X Y : ↥(Finset.univ : Finset Party) → Type⦄
      [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
      [∀ s, DecidableEq (Y s)] (g : ChainGate D X Y), ChainGate.IsAllowed g →
        ChainGate.IsAllowed (GateFrame.frame
          (fun s : ↥(Finset.univ : Finset Party) ↦ tagSystem (R.untouched ++ R.oldAffected) s.1)
          g) := by
    intro _ _ _ _ _ _ _ g h
    cases g <;> exact h
  refine ⟨(∏ j, sB j) * ∏ j, sK j, R.termMonomial hR β Msh, ?_,
    ⟨PartyCircuit.isAllowed_frame _ chainEv chainEv_isCompatible_frame hframe (c := Msh)
      ⟨⟨a₁, b₁⟩, c₁⟩, fun s ↦ R.norm_tagChange_le hR _ _ s⟩,
    ⟨PartyCircuit.UsesOnly.frame _ (c := Msh) ⟨⟨a₂, b₂⟩, c₂⟩, fun s hs ↦ by
      obtain ⟨h, h'⟩ := R.tagChange_of_notMem hR β.1 β.2.2 hs
      exact ⟨h, fun y x ↦ (h' y x).trans (by congr)⟩⟩, ?_, ?_, ?_⟩
  · rw [norm_mul, norm_prod, norm_prod]
    calc _ ≤ (1 : ℝ) * 1 := mul_le_mul
          (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun j _ => hsB j)
          (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun j _ => hsK j)
          (Finset.prod_nonneg fun _ _ => norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · change Monomial.sourceCount (PartyCircuit.comp _ _) ≤ _
    rw [Monomial.sourceCount_comp, Monomial.sourceCount_frame, Monomial.sourceCount_comp,
      Monomial.sourceCount_comp, b₃]
    change _ + 0 ≤ _
    change _ ≤ _ at hcount
    omega
  · change Monomial.effectCount (PartyCircuit.comp _ _) ≤ _
    rw [Monomial.effectCount_comp, Monomial.effectCount_frame, Monomial.effectCount_comp,
      Monomial.effectCount_comp, b₄]
    change _ + 0 ≤ _
    change _ ≤ _ at hcount
    omega
  · rw [termOp_eq_smul_prod (R.branchChain β) e i B K sB sK hBE hBK hBB hKE hKB hKK hWn hW,
      liftBranch_smul, R.op_termMonomial hR β Msh _ hMsh]
    ext y x
    simp [reindex_apply]

/-- **Lemma 6.3, the rewrite as a sum of allowed monomials.** Under the four conditions of
Lemma 6.3, for every `δ > 0` (for instance `δ = L^{-a}`) let `N` be the number of branches, `m`
the number of additional patches and `k = ⌈(4 N m / δ)²⌉ + 1`. There are a contraction `M_δ` with
`‖M_δ - M‖ ≤ δ` and a gate `∑_t c_t M_t` of at most `N k^{2m}` monomials `M_t` from the
registers of `F_old` to the output of the gate, each allowed in the sense of Theorem 5.2, using
only the specified parties, with at most `2m` normalized pair sources and at most `2m`
normalized pair effects, and with coefficients `|c_t| ≤ 1`, whose operator is `M_δ` in canonical
coordinates.

With `norm_toEuclideanLin_refVec_sub_le_of_approx` and `rewrite_error_le_inv_pow_twenty`, the
choice `δ = L^{-30}` gives the reference-vector error `O(L^{-20})` of the final assertion of
Lemma 6.3. For `δ = L^{-a}`, the count `N k^{2m}` is polynomial in `L` once `N` is and `m` is
bounded; see `exists_allowed_monomial_approx_polynomial`.

Polynomial-PEPS manuscript, Lemma 6.3 `lem:small-rewrite`, `05-frames.tex`, lines 214–217;
proof lines 254–341. -/
theorem exists_allowed_monomial_approx (hR : R.Conditions) {δ : ℝ} (hδ : 0 < δ) :
    ∃ g : WeightedGate (Finset.univ : Finset Party) R.oldFrame.system (R.gateSystem q),
      g.terms.length ≤ Fintype.card R.Branch *
        truncationRank (Fintype.card R.Branch) ((2 * R.patches.length : ℕ) : ℝ) δ ^
          (2 * R.patches.length) ∧
      (∀ t ∈ g.terms, ‖t.1‖ ≤ 1 ∧ t.2.IsAllowed chainEv ChainGate.IsAllowed ∧
        t.2.UsesOnly R.parties ∧ t.2.sourceCount ≤ 2 * R.patches.length ∧
        t.2.effectCount ≤ 2 * R.patches.length) ∧
      ∃ Ma : Matrix R.newFrame.Layout R.oldFrame.Layout ℂ, ‖Ma‖ ≤ 1 ∧ ‖Ma - R.rewrite‖ ≤ δ ∧
        WeightedGate.ev g () = reindex (R.gateConfigEquiv hR).symm R.oldConfigEquiv.symm Ma := by
  obtain ⟨r, e, c, -, he, hc, hcard, h1, h2⟩ := R.exists_contractive_approx hR hδ
  choose σ M hσ hM₁ hM₂ hM₃ hM₄ hM₅ using fun (β : R.Branch)
    (ii : (v : Fin (R.branchSteps β).length ⊕ Fin (R.branchSteps β).length) → Fin (r β v)) =>
      R.exists_termChain hR β (e β) (he β) ii
  set a : ℂ := (((1 + δ / 2)⁻¹ : ℝ) : ℂ) with ha
  have hna : ‖a‖ ≤ 1 := by
    rw [ha, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact inv_le_one_of_one_le₀ (by linarith)
  let κ := Σ β : R.Branch, ((v : Fin (R.branchSteps β).length ⊕ Fin (R.branchSteps β).length) →
    Fin (r β v))
  refine ⟨⟨(Finset.univ : Finset κ).toList.map fun t => (a * c t.1 t.2 * σ t.1 t.2, M t.1 t.2)⟩,
    ?_, ?_, _, h1, h2, ?_⟩
  · rw [List.length_map, Finset.length_toList, Finset.card_univ, Fintype.card_sigma]
    calc _ ≤ ∑ _β : R.Branch, truncationRank (Fintype.card R.Branch)
          ((2 * R.patches.length : ℕ) : ℝ) δ ^ (2 * R.patches.length) :=
          Finset.sum_le_sum fun β _ => hcard β
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  · intro t ht
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp ht
    refine ⟨?_, hM₁ _ _, hM₂ _ _, hM₃ _ _, hM₄ _ _⟩
    rw [norm_mul, norm_mul]
    calc _ ≤ (1 : ℝ) * 1 * 1 := mul_le_mul (mul_le_mul hna (hc _ _) (norm_nonneg _) zero_le_one)
          (hσ _ _) (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  · have hterm : ∀ t : κ, (a * c t.1 t.2 * σ t.1 t.2) • (M t.1 t.2).op chainEv =
        reindexLinearEquiv ℂ ℂ (R.gateConfigEquiv hR).symm R.oldConfigEquiv.symm
          ((a * c t.1 t.2) • R.liftBranch t.1 (termOp (R.branchChain t.1) (e t.1) t.2)) := by
      intro t
      rw [mul_smul, hM₅, map_smul]
      rfl
    rw [WeightedGate.ev, List.map_map, Function.comp_def]
    simp only [hterm]
    rw [Finset.sum_map_toList, ← map_sum, Fintype.sum_sigma]
    rw [← coe_reindexLinearEquiv ℂ ℂ]
    congr 1
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [liftBranch_sum_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun ii _ => ?_
    rw [mul_smul]

/-- **Lemma 6.3, the count with the number of cylinder terms as a parameter.** If every affected
hole and every additional patch has at most `D` cylinder terms, the expansion of
`exists_allowed_monomial_approx` has at most `D^E k'^{2m}` allowed monomials, with
`E = r_new + m + r_old` and `k' = ⌈(4 D^E m / δ)²⌉ + 1`. For `δ = L^{-a}`, this count is polynomial
in `L` when `D ≤ C L^c` (the bound on `∑_j d_j` of the frame construction) and `m`, `r_old`,
`r_new` are bounded; see `exists_allowed_monomial_approx_polynomial`.

Polynomial-PEPS manuscript, Lemma 6.3 `lem:small-rewrite`, `05-frames.tex`, lines 214–217;
proof lines 254–257 and 331–342; the bound on `∑_j d_j`, lines 34–46. -/
theorem exists_allowed_monomial_approx_of_card_le (hR : R.Conditions) {δ : ℝ} (hδ : 0 < δ)
    {D : ℕ} (hnew : ∀ h ∈ R.newAffected, Fintype.card h.patch.Tag ≤ D)
    (hpatch : ∀ P ∈ R.patches, Fintype.card P.Tag ≤ D)
    (hold : ∀ h ∈ R.oldAffected, Fintype.card h.patch.Tag ≤ D) :
    ∃ g : WeightedGate (Finset.univ : Finset Party) R.oldFrame.system (R.gateSystem q),
      g.terms.length ≤ D ^ (R.newAffected.length + R.patches.length + R.oldAffected.length) *
        truncationRank ((D ^ (R.newAffected.length + R.patches.length +
          R.oldAffected.length) : ℕ) : ℝ) ((2 * R.patches.length : ℕ) : ℝ) δ ^
          (2 * R.patches.length) ∧
      (∀ t ∈ g.terms, ‖t.1‖ ≤ 1 ∧ t.2.IsAllowed chainEv ChainGate.IsAllowed ∧
        t.2.UsesOnly R.parties ∧ t.2.sourceCount ≤ 2 * R.patches.length ∧
        t.2.effectCount ≤ 2 * R.patches.length) ∧
      ∃ Ma : Matrix R.newFrame.Layout R.oldFrame.Layout ℂ, ‖Ma‖ ≤ 1 ∧ ‖Ma - R.rewrite‖ ≤ δ ∧
        WeightedGate.ev g () = reindex (R.gateConfigEquiv hR).symm R.oldConfigEquiv.symm Ma := by
  obtain ⟨G, hG, rest⟩ := R.exists_allowed_monomial_approx hR hδ
  have hN := R.card_branch_le hnew hpatch hold
  refine ⟨G, hG.trans (Nat.mul_le_mul hN (Nat.pow_le_pow_left ?_ _)), rest⟩
  exact truncationRank_mono (Nat.cast_nonneg _) (by exact_mod_cast hN) (Nat.cast_nonneg _) le_rfl hδ

/-- **Lemma 6.3, second assertion: the polynomial count.** Let `L ≥ 1`, and suppose that every
affected hole and every additional patch has at most `C L^c` cylinder terms (the standing bound
`∑_j d_j ≤ C L^c` on the projectors chosen in the frame construction) and that there are at most
`b` additional patches, at most `b` affected old holes, at most `b` affected new holes and at
most `b` parties in the specified list of condition (iv). For every real `a`, the canonical
contraction `M` admits a contraction `M_a` with `‖M_a - M‖ ≤ L^{-a}` and an expansion
`M_a = ∑_t c_t M_t` into at most `K L^e` monomials allowed by Theorem 5.2, all participating
parties lying in the specified list of condition (iv), of at most `b` parties, each
monomial moving a register of that list at every exchange of tensor factors and having at most
`2b` normalized pair sources and at most `2b` normalized pair effects, and with `|c_t| ≤ 1`. Here
`K = (C + 1)^{3b} (16 b² (C + 1)^{6b} + 1)^{2b}` and `e = 3bc + 4b(3bc + ⌈a⌉)` depend only on
`C`, `c`, `b` and `a`. The expansion is read in canonical coordinates, the tags of the untouched
holes first, as in the canonical identification of tag orderings of the source.

The bound on the participating parties is the boundedness of the specified list in condition
(iv), not a consequence of conditions (i)–(iii): the touched sites include whole selected hole
squares, whose raw owners inside the inner holes condition (iii) does not restrict, and each of
them receives `⟨0|` at its old owner and `|0⟩` at its new owner.

Polynomial-PEPS manuscript, Lemma 6.3 `lem:small-rewrite`, `05-frames.tex`, lines 188–217, in
particular the specified bounded list of parties of condition (iv), line 204; the bound on the
cylinder terms, lines 34–46; proof lines 331–343. -/
theorem exists_allowed_monomial_approx_polynomial (hR : R.Conditions) {C c b L : ℕ}
    (hL : 1 ≤ L) (hnew : ∀ h ∈ R.newAffected, Fintype.card h.patch.Tag ≤ C * L ^ c)
    (hpatch : ∀ P ∈ R.patches, Fintype.card P.Tag ≤ C * L ^ c)
    (hold : ∀ h ∈ R.oldAffected, Fintype.card h.patch.Tag ≤ C * L ^ c)
    (hm : R.patches.length ≤ b) (hrold : R.oldAffected.length ≤ b)
    (hrnew : R.newAffected.length ≤ b) (hparties : R.parties.card ≤ b) (a : ℝ) :
    R.parties.card ≤ b ∧
      ∃ g : WeightedGate (Finset.univ : Finset Party) R.oldFrame.system (R.gateSystem q),
      g.terms.length ≤ (C + 1) ^ (3 * b) * (16 * b ^ 2 * (C + 1) ^ (6 * b) + 1) ^ (2 * b) *
        L ^ (3 * b * c + 4 * b * (3 * b * c + ⌈a⌉₊)) ∧
      (∀ t ∈ g.terms, ‖t.1‖ ≤ 1 ∧ t.2.IsAllowed chainEv ChainGate.IsAllowed ∧
        t.2.UsesOnly R.parties ∧ t.2.sourceCount ≤ 2 * b ∧
        t.2.effectCount ≤ 2 * b) ∧
      ∃ Ma : Matrix R.newFrame.Layout R.oldFrame.Layout ℂ, ‖Ma‖ ≤ 1 ∧
        ‖Ma - R.rewrite‖ ≤ (L : ℝ) ^ (-a) ∧
        WeightedGate.ev g () = reindex (R.gateConfigEquiv hR).symm R.oldConfigEquiv.symm Ma := by
  set B := (C + 1) * L ^ c with hBdef
  have hL0 : 0 < L := hL
  have hB1 : 1 ≤ B := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hCB : C * L ^ c ≤ B := Nat.mul_le_mul_right _ (Nat.le_succ C)
  have hδ : (0 : ℝ) < (L : ℝ) ^ (-a) := Real.rpow_pos_of_pos (by exact_mod_cast hL0) _
  obtain ⟨G, hG, hGp, rest⟩ := R.exists_allowed_monomial_approx_of_card_le hR hδ (D := B)
    (fun h hh => (hnew h hh).trans hCB) (fun P hP => (hpatch P hP).trans hCB)
    (fun h hh => (hold h hh).trans hCB)
  have hN : B ^ (R.newAffected.length + R.patches.length + R.oldAffected.length) ≤
      B ^ (3 * b) := Nat.pow_le_pow_right hB1 (by omega)
  set X := 4 * b * B ^ (3 * b) * L ^ ⌈a⌉₊ with hX
  have hk : truncationRank ((B ^ (R.newAffected.length + R.patches.length +
      R.oldAffected.length) : ℕ) : ℝ) ((2 * R.patches.length : ℕ) : ℝ) ((L : ℝ) ^ (-a)) ≤
      X ^ 2 + 1 := by
    refine (truncationRank_mono (Nat.cast_nonneg _) (Nat.cast_le.mpr hN) (Nat.cast_nonneg _)
      (Nat.cast_le.mpr (Nat.mul_le_mul_left 2 hm)) hδ).trans ?_
    refine Nat.add_le_add_right (Nat.ceil_le.mpr ?_) 1
    have hLa : (L : ℝ) ^ a ≤ (L : ℝ) ^ ⌈a⌉₊ := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hL) (Nat.le_ceil a)
    have hdiv : 2 * ((B ^ (3 * b) : ℕ) : ℝ) * ((2 * b : ℕ) : ℝ) / (L : ℝ) ^ (-a) =
        4 * b * (B : ℝ) ^ (3 * b) * (L : ℝ) ^ a := by
      rw [Real.rpow_neg (Nat.cast_nonneg _), div_inv_eq_mul]
      push_cast
      ring
    rw [hdiv, hX]
    push_cast
    gcongr
  have hP : 1 ≤ L ^ (2 * (3 * b * c + ⌈a⌉₊)) := Nat.one_le_pow _ _ hL0
  have hX2 : X ^ 2 + 1 ≤ (16 * b ^ 2 * (C + 1) ^ (6 * b) + 1) * L ^ (2 * (3 * b * c + ⌈a⌉₊)) := by
    have : X ^ 2 = 16 * b ^ 2 * (C + 1) ^ (6 * b) * L ^ (2 * (3 * b * c + ⌈a⌉₊)) := by
      rw [hX, hBdef, mul_pow (C + 1) (L ^ c)]
      ring
    rw [this, add_mul, one_mul]
    exact Nat.add_le_add_left hP _
  refine ⟨hparties, G, ?_, fun t ht => ?_, rest⟩
  · refine hG.trans ((Nat.mul_le_mul hN ((Nat.pow_le_pow_left hk _).trans
      (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.mul_le_mul_left 2 hm)))).trans ?_)
    calc B ^ (3 * b) * (X ^ 2 + 1) ^ (2 * b)
        ≤ B ^ (3 * b) * ((16 * b ^ 2 * (C + 1) ^ (6 * b) + 1) *
            L ^ (2 * (3 * b * c + ⌈a⌉₊))) ^ (2 * b) := by gcongr
      _ = _ := by rw [hBdef, mul_pow (C + 1) (L ^ c), mul_pow _ (L ^ _)]; ring
  · obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hGp t ht
    exact ⟨h₁, h₂, h₃, h₄.trans (by omega), h₅.trans (by omega)⟩

/-- **Lemma 6.3, the bounded change with reference-vector error `O(L^{-20})`.** In the setting of
`exists_allowed_monomial_approx_polynomial`, let `Ω` be a vector with `‖Ω‖ ≤ 1` on which every
additional patch projector and every affected old-hole projector has error at most `L^{-60}`, the
accuracy fixed for all applications of Proposition 4.1 in the frame construction. The choice
`a = 30` gives a contraction `M_30` with `‖M_30 - M‖ ≤ L^{-30}`, expanded into at most
`K L^e` allowed monomials whose participating parties lie in the specified list of
condition (iv), of at most `b` parties, and with `‖M_30 Ω_{F_old} - Ω_{F_new}‖ ≤ (2b + 1) L^{-20}`.

Polynomial-PEPS manuscript, Lemma 6.3 `lem:small-rewrite`, `05-frames.tex`, lines 188–218; the
accuracy `ε = L^{-60}`, lines 21–25 (`eq:frame-epsilon`); proof lines 343–344. -/
theorem exists_allowed_monomial_approx_refVec (hR : R.Conditions) {C c b L : ℕ}
    (hL : 1 ≤ L) (hnew : ∀ h ∈ R.newAffected, Fintype.card h.patch.Tag ≤ C * L ^ c)
    (hpatch : ∀ P ∈ R.patches, Fintype.card P.Tag ≤ C * L ^ c)
    (hold : ∀ h ∈ R.oldAffected, Fintype.card h.patch.Tag ≤ C * L ^ c)
    (hm : R.patches.length ≤ b) (hrold : R.oldAffected.length ≤ b)
    (hrnew : R.newAffected.length ≤ b) (hparties : R.parties.card ≤ b)
    {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ ≤ 1)
    (hεpatch : ∀ P ∈ R.patches, ‖toEuclideanLin P.proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹)
    (hεold : ∀ h ∈ R.oldAffected, ‖toEuclideanLin h.patch.proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹) :
    R.parties.card ≤ b ∧
      ∃ g : WeightedGate (Finset.univ : Finset Party) R.oldFrame.system (R.gateSystem q),
      g.terms.length ≤ (C + 1) ^ (3 * b) * (16 * b ^ 2 * (C + 1) ^ (6 * b) + 1) ^ (2 * b) *
        L ^ (3 * b * c + 4 * b * (3 * b * c + 30)) ∧
      (∀ t ∈ g.terms, ‖t.1‖ ≤ 1 ∧ t.2.IsAllowed chainEv ChainGate.IsAllowed ∧
        t.2.UsesOnly R.parties ∧ t.2.sourceCount ≤ 2 * b ∧
        t.2.effectCount ≤ 2 * b) ∧
      ∃ Ma : Matrix R.newFrame.Layout R.oldFrame.Layout ℂ, ‖Ma‖ ≤ 1 ∧
        ‖Ma - R.rewrite‖ ≤ ((L : ℝ) ^ 30)⁻¹ ∧
        ‖toEuclideanLin Ma (R.oldFrame.refVec Ω) - R.newFrame.refVec Ω‖ ≤
          (2 * b + 1) * ((L : ℝ) ^ 20)⁻¹ ∧
        WeightedGate.ev g () = reindex (R.gateConfigEquiv hR).symm R.oldConfigEquiv.symm Ma := by
  have h30 : ⌈(30 : ℝ)⌉₊ = 30 := by exact_mod_cast Nat.ceil_natCast 30
  have hrpow : (L : ℝ) ^ (-(30 : ℝ)) = ((L : ℝ) ^ 30)⁻¹ := by
    rw [Real.rpow_neg (Nat.cast_nonneg _)]
    exact_mod_cast congrArg Inv.inv (Real.rpow_natCast (L : ℝ) 30)
  obtain ⟨-, G, hG, hGp, Ma, hMa1, hMa, hz⟩ := R.exists_allowed_monomial_approx_polynomial
    hR hL hnew hpatch hold hm hrold hrnew hparties 30
  rw [h30] at hG
  rw [hrpow] at hMa
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  have href := R.norm_toEuclideanLin_refVec_sub_le_of_approx hR.avoidsUntouched hΩ hεpatch hεold hMa
  refine ⟨hparties, G, hG, hGp, Ma, hMa1, hMa, href.trans ?_, hz⟩
  have h60 : ((L : ℝ) ^ 60)⁻¹ ≤ ((L : ℝ) ^ 20)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_right₀ hLr (by norm_num))
  have h30' : ((L : ℝ) ^ 30)⁻¹ ≤ ((L : ℝ) ^ 20)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_right₀ hLr (by norm_num))
  have hcount : ((R.patches.length + R.oldAffected.length : ℕ) : ℝ) ≤ 2 * b := by
    exact_mod_cast (by omega : R.patches.length + R.oldAffected.length ≤ 2 * b)
  push_cast at hcount
  calc ((L : ℝ) ^ 30)⁻¹ + (R.patches.length + R.oldAffected.length) * ((L : ℝ) ^ 60)⁻¹
      ≤ ((L : ℝ) ^ 20)⁻¹ + 2 * b * ((L : ℝ) ^ 20)⁻¹ := by
        gcongr
    _ = (2 * b + 1) * ((L : ℝ) ^ 20)⁻¹ := by ring


end SmallPatchRewrite

end Terms

end TNLean.PEPS.EncodedFrame
