/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.PartyCircuit.ApproximateCircuitError
import TNLean.Lattice.PartyCircuit.OriginalProducerResources
import TNLean.PEPS.Approximation.SampledOriginalCircuit
import TNLean.PEPS.Approximation.SheetStackReadoutCircuit
import TNLean.PEPS.Approximation.TwoSheetRegisters

/-!
# Bounded changes of the sheet stack

In the protocol of Proposition 7.1 of the polynomial-PEPS manuscript every change of the memory
is a bounded number of gates: each change of the schedule has at most one nonprivate gate, whose
participants are parties its event uses, whose monomial expansion has polynomially many
monomials with polynomially bounded coefficients and a bounded number of pair effects, and which
takes the reference vector of the sheets within `C L⁻²⁰` of the next reference vector
(`06-geometry.tex`, lines 25–41 and 572–583).

This file packages these properties into one predicate and proves that the operations of the
schedule preserve it.

* `PairEffect.OriginalCircuit.IsBoundedChange` : an original circuit with at most one
  nonprivate gate, participants in a set `S`, expansion and monomial bounds, and an error at
  most `ε` from a vector `x` to a vector `y`.
* `EncodedFrame.HasBoundedChange` : a bounded change between two lists of encoded frames, followed
  by the same idle registers, from the reference vector of the first list to that of the second.

The closure properties are:

* reorderings of the sheets, before or after a change, and identity changes
  (`EncodedFrame.hasBoundedChange_of_perm`, `EncodedFrame.HasBoundedChange.perm_left`,
  `EncodedFrame.HasBoundedChange.perm_right`, `PairEffect.OriginalCircuit.isBoundedChange_id`);
* a change of one sheet or of two adjacent sheets, lifted to the whole stack
  (`EncodedFrame.hasBoundedChange_liftOne`, `EncodedFrame.hasBoundedChange_liftTwo`);
* the activation of an auxiliary sheet: a reordering that brings an idle copy next to the main
  sheet, followed by a lifted change of the two sheets
  (`EncodedFrame.hasBoundedChange_activate`);
* the bounded words of the births and exchanges, and the bounded chains of the deaths
  (`PairEffect.Word.isBoundedChange_toOriginalCircuit`,
  `PairEffect.PartyChain.isBoundedChange_toOriginalCircuit`), with the reference vector of two
  sheets in the coordinates of the exchange (`EncodedFrame.pairRef_eq_twoLayoutIso_symm`).

## References

* Polynomial-PEPS manuscript (September 24, 2026), Proposition 7.1 `prop:protocol`,
  `06-geometry.tex`, lines 25–41 (statement) and 572–583 (bounded gates and the precision of
  each change); original circuits, `04-compression.tex`, lines 21–43 and 199–208.
-/

noncomputable section

open scoped TensorProduct
open ContinuousLinearMap

namespace TNLean.PEPS

namespace PairEffect

variable {P : Type}

namespace OriginalCircuit

/-- An original circuit does not increase the norm of a vector. -/
theorem norm_eval_le_norm {a b : Layout P} (w : OriginalCircuit a b) (v : Mem a) :
    ‖w.eval v‖ ≤ ‖v‖ := by
  simpa only [one_mul] using w.eval.le_of_opNorm_le w.norm_eval_le_one v

/-- **A bounded change.** The original circuit `c` has at most one nonprivate gate, all its
participants lie in `S`, every monomial of its expansion has at most `r` pair effects, its
coefficient sum and its number of monomials are at most `K`, and it takes `x` within `ε` of `y`.

Polynomial-PEPS manuscript, Proposition 7.1 `prop:protocol`, item 2 and the reference vectors,
`06-geometry.tex`, lines 25–41, and the gate count of each change, lines 572–583; original
circuits, `04-compression.tex`, lines 199–208. -/
structure IsBoundedChange {a b : Layout P} (c : OriginalCircuit a b) (S : Set P) (r K : ℕ)
    (ε : ℝ) (x : Mem a) (y : Mem b) : Prop where
  /-- At most one nonprivate gate. -/
  nonprivateCount_le : c.nonprivateCount ≤ 1
  /-- The participants of the gate lie in `S`. -/
  participants_subset : ∀ g, (↑(c.participants g) : Set P) ⊆ S
  /-- At most `r` pair effects per monomial and coefficient sum at most `K`. -/
  isExpansionBounded : c.IsExpansionBounded r K
  /-- At most `K` monomials. -/
  isMonomialBounded : c.IsMonomialBounded K
  /-- The error on the reference vector. -/
  norm_eval_sub_le : ‖c.eval x - y‖ ≤ ε

namespace IsBoundedChange

variable {a b d : Layout P} {c : OriginalCircuit a b} {S S' : Set P} {r r' K K' : ℕ}
  {ε ε' : ℝ} {x : Mem a} {y : Mem b}

/-- A bounded change stays bounded under weaker bounds. -/
theorem mono (h : c.IsBoundedChange S r K ε x y) (hS : S ⊆ S') (hr : r ≤ r') (hK : K ≤ K')
    (hε : ε ≤ ε') : c.IsBoundedChange S' r' K' ε' x y where
  nonprivateCount_le := h.nonprivateCount_le
  participants_subset g := (h.participants_subset g).trans hS
  isExpansionBounded := c.isExpansionBounded_mono h.isExpansionBounded hr (by exact_mod_cast hK)
  isMonomialBounded := c.isMonomialBounded_mono h.isMonomialBounded hK
  norm_eval_sub_le := h.norm_eval_sub_le.trans hε

/-- A bounded change followed by a circuit without nonprivate gates is a bounded change to the
image of the target. -/
theorem comp_right (h : c.IsBoundedChange S r K ε x y) (e : OriginalCircuit b d)
    (he0 : e.nonprivateCount = 0) (heE : e.IsExpansionBounded r K)
    (heM : e.IsMonomialBounded K) : (c.comp e).IsBoundedChange S r K ε x (e.eval y) where
  nonprivateCount_le := by
    change c.nonprivateCount + e.nonprivateCount ≤ 1
    rw [he0, add_zero]; exact h.nonprivateCount_le
  participants_subset g := by
    rcases g with g | g
    · exact h.participants_subset g
    · exact e.participants_subset_of_nonprivateCount_eq_zero he0 S g
  isExpansionBounded := ⟨h.isExpansionBounded, heE⟩
  isMonomialBounded := ⟨h.isMonomialBounded, heM⟩
  norm_eval_sub_le := by
    change ‖e.eval (c.eval x) - e.eval y‖ ≤ ε
    rw [← map_sub]
    exact (e.norm_eval_le_norm _).trans h.norm_eval_sub_le

/-- A circuit without nonprivate gates followed by a bounded change is a bounded change from any
preimage of the source. -/
theorem comp_left {x' : Mem d} (e : OriginalCircuit d a) (he0 : e.nonprivateCount = 0)
    (heE : e.IsExpansionBounded r K) (heM : e.IsMonomialBounded K) (hx : e.eval x' = x)
    (h : c.IsBoundedChange S r K ε x y) : (e.comp c).IsBoundedChange S r K ε x' y where
  nonprivateCount_le := by
    change e.nonprivateCount + c.nonprivateCount ≤ 1
    rw [he0, zero_add]; exact h.nonprivateCount_le
  participants_subset g := by
    rcases g with g | g
    · exact e.participants_subset_of_nonprivateCount_eq_zero he0 S g
    · exact h.participants_subset g
  isExpansionBounded := ⟨heE, h.isExpansionBounded⟩
  isMonomialBounded := ⟨heM, h.isMonomialBounded⟩
  norm_eval_sub_le := by
    change ‖c.eval (e.eval x') - y‖ ≤ ε
    rw [hx]; exact h.norm_eval_sub_le

end IsBoundedChange

/-- **The identity change.** The circuit without operations is a bounded change from a vector to
itself, for every set of participants and all bounds. -/
theorem isBoundedChange_id {a : Layout P} (S : Set P) (r K : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (x : Mem a) : (OriginalCircuit.id a).IsBoundedChange S r K ε x x where
  nonprivateCount_le := zero_le_one
  participants_subset g := nomatch g
  isExpansionBounded := trivial
  isMonomialBounded := trivial
  norm_eval_sub_le := by
    change ‖x - x‖ ≤ ε
    rw [sub_self, norm_zero]
    exact hε

end OriginalCircuit

/-! ### Words and chains of pair resources -/

/-- **A word with at most one pair source.** An allowed word using only the parties of `S`, with
at most one pair source, is a bounded change for every `r` and every `K ≥ 1`, with its own error.
These are the words of the births of Lemma 6.5 and of the lens exchange of Lemma 6.6.

Polynomial-PEPS manuscript, `05-frames.tex`, Lemmas 6.5 and 6.6, and `06-geometry.tex`,
lines 357–445 and 572–583. -/
theorem Word.isBoundedChange_toOriginalCircuit {S : Set P} {r K : ℕ} {ε : ℝ} {a b : Layout P}
    {w : Word a b} (hw : w.IsAllowed) (hS : w.UsesOnly S) (hsrc : w.sourceCount ≤ 1)
    (hK : 1 ≤ K) {x : Mem a} {y : Mem b} (herr : ‖w.eval x - y‖ ≤ ε) :
    (w.toOriginalCircuit hw).IsBoundedChange S r K ε x y where
  nonprivateCount_le := (w.nonprivateCount_toOriginalCircuit hw).trans_le hsrc
  participants_subset := w.participants_toOriginalCircuit_subset hw hS
  isExpansionBounded := w.isExpansionBounded_toOriginalCircuit hw r (by exact_mod_cast hK)
  isMonomialBounded := w.isMonomialBounded_toOriginalCircuit hw hK
  norm_eval_sub_le := by rwa [w.eval_toOriginalCircuit]

/-- **A chain with one pair effect.** An allowed chain using only the parties of `S`, without
pair sources and with at most one pair effect, is a bounded change for every `r ≥ 1` and every
`K ≥ 1`, with its own error. These are the chains of the deaths of Lemma 6.5.

Polynomial-PEPS manuscript, `05-frames.tex`, Lemma 6.5, and `06-geometry.tex`, lines 357–387 and
572–583. -/
theorem PartyChain.isBoundedChange_toOriginalCircuit {S : Set P} {r K : ℕ} {ε : ℝ}
    {a b : Layout P} {M : PartyChain a b} (hM : M.IsAllowed) (hS : M.UsesOnly S)
    (hsrc : M.sourceCount = 0) (heff : M.toEffectChain.effectCount ≤ 1) (hr : 1 ≤ r)
    (hK : 1 ≤ K) {x : Mem a} {y : Mem b} (herr : ‖M.toEffectChain.eval x - y‖ ≤ ε) :
    (M.toOriginalCircuit hM).IsBoundedChange S r K ε x y where
  nonprivateCount_le := by
    rw [M.nonprivateCount_toOriginalCircuit hM, hsrc, zero_add]; exact heff
  participants_subset := M.participants_toOriginalCircuit_subset hM hS
  isExpansionBounded := M.isExpansionBounded_toOriginalCircuit hM hr (by exact_mod_cast hK)
  isMonomialBounded := M.isMonomialBounded_toOriginalCircuit hM hK
  norm_eval_sub_le := by rwa [M.eval_toOriginalCircuit]

end PairEffect

namespace EncodedFrame

open PairEffect

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} [NeZero q] {Party : Type}
  {pos : ι → ℝ × ℝ}

/-- **The reference vector of two sheets in the coordinates of the exchange.** The reference
vector of two frames on their concatenated registers is the product `Ω_{F₁} ⊗ Ω_{F₂}` read through
the coordinates of the two layouts. -/
theorem pairRef_eq_twoLayoutIso_symm (F₁ F₂ : Frame pos q Party)
    (Ω : EuclideanSpace ℂ (ι → Fin q)) :
    pairRef F₁ F₂ Ω = (twoLayoutIso F₁.holes F₂.holes F₁.owner F₂.owner).symm
      (EuclideanSpace.vecKron (F₁.refVec Ω) (F₂.refVec Ω)) := by
  rw [LinearIsometryEquiv.eq_symm_apply]
  change EuclideanSpace.pairIso _ _ ((layoutIso F₂.holes F₂.owner).lTensor _
      ((layoutIso F₁.holes F₁.owner).rTensor _ (appendIso _ _ ((appendIso _ _).symm
        (F₁.regRef Ω ⊗ₜ F₂.regRef Ω))))) = _
  rw [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.rTensor_tmul,
    LinearIsometryEquiv.lTensor_tmul]
  ext i
  simp [Frame.regRef, EuclideanSpace.vecKron]

/-! ### Bounded changes of the sheet stack -/

/-- **A bounded change of the sheets.** There is an original circuit from the registers of the
frames `Fs`, followed by the idle registers `ℓ`, to those of `Fs'`, followed by `ℓ`, that is a
bounded change, in the sense of `PairEffect.OriginalCircuit.IsBoundedChange`, from the reference
vector of `Fs` with idle vector `ξ` to that of `Fs'`.

Polynomial-PEPS manuscript, Proposition 7.1 `prop:protocol`, items 2 and 4,
`06-geometry.tex`, lines 25–41, and lines 572–583. -/
def HasBoundedChange (Ω : EuclideanSpace ℂ (ι → Fin q)) (Fs Fs' : List (Frame pos q Party))
    {ℓ : Layout Party} (ξ : Mem ℓ) (S : Set Party) (r K : ℕ) (ε : ℝ) : Prop :=
  ∃ c : OriginalCircuit (stackRegs Fs ℓ) (stackRegs Fs' ℓ),
    c.IsBoundedChange S r K ε (stackVec Ω Fs ξ) (stackVec Ω Fs' ξ)

variable {Ω : EuclideanSpace ℂ (ι → Fin q)} {Fs Fs' Gs : List (Frame pos q Party)}
  {ℓ : Layout Party} {ξ : Mem ℓ} {S S' : Set Party} {r r' K K' : ℕ} {ε ε' : ℝ}

/-- A bounded change of the sheets stays bounded under weaker bounds. -/
theorem HasBoundedChange.mono (h : HasBoundedChange Ω Fs Fs' ξ S r K ε) (hS : S ⊆ S')
    (hr : r ≤ r') (hK : K ≤ K') (hε : ε ≤ ε') : HasBoundedChange Ω Fs Fs' ξ S' r' K' ε' :=
  let ⟨c, hc⟩ := h
  ⟨c, hc.mono hS hr hK hε⟩

/-- **Reordering the sheets is a bounded change.** A permutation of the frames is a bounded change
without nonprivate gates and without error. -/
theorem hasBoundedChange_of_perm (h : Fs.Perm Fs') (ξ : Mem ℓ) (S : Set Party) (r K : ℕ)
    (hε : 0 ≤ ε) : HasBoundedChange Ω Fs Fs' ξ S r K ε := by
  obtain ⟨c, h0, -, hE, hM, he⟩ := exists_originalCircuit_stackVec_of_perm Ω h ℓ
  refine ⟨(OriginalCircuit.id _).comp c, ?_⟩
  simpa [he] using (OriginalCircuit.isBoundedChange_id S r K hε (stackVec Ω Fs ξ)).comp_right c
    h0 (hE r K) (hM K)

/-- The identity change of the sheets. -/
theorem hasBoundedChange_refl (Fs : List (Frame pos q Party)) (ξ : Mem ℓ) (S : Set Party)
    (r K : ℕ) (hε : 0 ≤ ε) : HasBoundedChange Ω Fs Fs ξ S r K ε :=
  hasBoundedChange_of_perm (List.Perm.refl Fs) ξ S r K hε

/-- A reordering of the sheets followed by a bounded change is a bounded change. -/
theorem HasBoundedChange.perm_left (hp : Fs.Perm Gs) (h : HasBoundedChange Ω Gs Fs' ξ S r K ε) :
    HasBoundedChange Ω Fs Fs' ξ S r K ε := by
  obtain ⟨e, h0, -, hE, hM, he⟩ := exists_originalCircuit_stackVec_of_perm Ω hp ℓ
  obtain ⟨c, hc⟩ := h
  exact ⟨e.comp c, hc.comp_left e h0 (hE r K) (hM K) (he ξ)⟩

/-- A bounded change followed by a reordering of the sheets is a bounded change. -/
theorem HasBoundedChange.perm_right (h : HasBoundedChange Ω Fs Gs ξ S r K ε) (hp : Gs.Perm Fs') :
    HasBoundedChange Ω Fs Fs' ξ S r K ε := by
  obtain ⟨e, h0, -, hE, hM, he⟩ := exists_originalCircuit_stackVec_of_perm Ω hp ℓ
  obtain ⟨c, hc⟩ := h
  exact ⟨c.comp e, by simpa [he] using hc.comp_right e h0 (hE r K) (hM K)⟩

/-- The lift of a bounded change of one sheet to the stack. -/
theorem isBoundedChange_liftOne {F F' : Frame pos q Party} (pre post : List (Frame pos q Party))
    {c : OriginalCircuit F.regs F'.regs} (hc : c.IsBoundedChange S r K ε (F.regRef Ω) (F'.regRef Ω))
    (hΩ : ‖Ω‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1) :
    (liftOne post ℓ c pre).IsBoundedChange S r K ε (stackVec Ω (pre ++ F :: post) ξ)
      (stackVec Ω (pre ++ F' :: post) ξ) where
  nonprivateCount_le := (nonprivateCount_liftOne post ℓ c pre).trans_le hc.nonprivateCount_le
  participants_subset := participants_liftOne_subset post ℓ c hc.participants_subset pre
  isExpansionBounded := isExpansionBounded_liftOne post ℓ c hc.isExpansionBounded pre
  isMonomialBounded := isMonomialBounded_liftOne post ℓ c hc.isMonomialBounded pre
  norm_eval_sub_le := (norm_eval_liftOne_stackVec_sub_le post c hΩ hξ pre).trans
    hc.norm_eval_sub_le

/-- **A change of one sheet, on the whole stack.** A bounded change of the frame `F` into `F'`,
from `Ω_F` to `Ω_{F'}`, is a bounded change of the stack `pre ++ F :: post` into
`pre ++ F' :: post`, with the same participants, bounds and error, when `‖Ω‖ ≤ 1` and the idle
vector has norm at most one.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 39–41 and 574–583. -/
theorem hasBoundedChange_liftOne {F F' : Frame pos q Party} (pre post : List (Frame pos q Party))
    {c : OriginalCircuit F.regs F'.regs} (hc : c.IsBoundedChange S r K ε (F.regRef Ω) (F'.regRef Ω))
    (hΩ : ‖Ω‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1) :
    HasBoundedChange Ω (pre ++ F :: post) (pre ++ F' :: post) ξ S r K ε :=
  ⟨liftOne post ℓ c pre, isBoundedChange_liftOne pre post hc hΩ hξ⟩

/-- The lift of a bounded change of two adjacent sheets to the stack. -/
theorem isBoundedChange_liftTwo {F₁ F₂ F₁' F₂' : Frame pos q Party}
    (pre post : List (Frame pos q Party))
    {c : OriginalCircuit (F₁.regs ++ F₂.regs) (F₁'.regs ++ F₂'.regs)}
    (hc : c.IsBoundedChange S r K ε (pairRef F₁ F₂ Ω) (pairRef F₁' F₂' Ω)) (hΩ : ‖Ω‖ ≤ 1)
    (hξ : ‖ξ‖ ≤ 1) :
    (liftTwo post ℓ c pre).IsBoundedChange S r K ε (stackVec Ω (pre ++ F₁ :: F₂ :: post) ξ)
      (stackVec Ω (pre ++ F₁' :: F₂' :: post) ξ) where
  nonprivateCount_le := (nonprivateCount_liftTwo post ℓ c pre).trans_le hc.nonprivateCount_le
  participants_subset := participants_liftTwo_subset post ℓ c hc.participants_subset pre
  isExpansionBounded := isExpansionBounded_liftTwo post ℓ c hc.isExpansionBounded pre
  isMonomialBounded := isMonomialBounded_liftTwo post ℓ c hc.isMonomialBounded pre
  norm_eval_sub_le := (norm_eval_liftTwo_stackVec_sub_le post c hΩ hξ pre).trans
    hc.norm_eval_sub_le

/-- **A change of two adjacent sheets, on the whole stack.** A bounded change of the frames
`F₁, F₂` into `F₁', F₂'`, from `Ω_{F₁} ⊗ Ω_{F₂}` to `Ω_{F₁'} ⊗ Ω_{F₂'}`, is a bounded change of
the stack `pre ++ F₁ :: F₂ :: post` into `pre ++ F₁' :: F₂' :: post`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 39–41, 389–430 and 574–583. -/
theorem hasBoundedChange_liftTwo {F₁ F₂ F₁' F₂' : Frame pos q Party}
    (pre post : List (Frame pos q Party))
    {c : OriginalCircuit (F₁.regs ++ F₂.regs) (F₁'.regs ++ F₂'.regs)}
    (hc : c.IsBoundedChange S r K ε (pairRef F₁ F₂ Ω) (pairRef F₁' F₂' Ω)) (hΩ : ‖Ω‖ ≤ 1)
    (hξ : ‖ξ‖ ≤ 1) :
    HasBoundedChange Ω (pre ++ F₁ :: F₂ :: post) (pre ++ F₁' :: F₂' :: post) ξ S r K ε :=
  ⟨liftTwo post ℓ c pre, isBoundedChange_liftTwo pre post hc hΩ hξ⟩

/-- **Activating an auxiliary sheet.** If the frames `Fs` are a reordering of
`pre ++ F₁ :: F₂ :: post`, for instance with an idle auxiliary copy `F₂` moved next to the main
sheet `F₁`, then a bounded change of the two adjacent sheets is a bounded change of `Fs`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 183–186, 389–430 and 658–667. -/
theorem hasBoundedChange_activate {F₁ F₂ F₁' F₂' : Frame pos q Party}
    {pre post : List (Frame pos q Party)} (hp : Fs.Perm (pre ++ F₁ :: F₂ :: post))
    {c : OriginalCircuit (F₁.regs ++ F₂.regs) (F₁'.regs ++ F₂'.regs)}
    (hc : c.IsBoundedChange S r K ε (pairRef F₁ F₂ Ω) (pairRef F₁' F₂' Ω)) (hΩ : ‖Ω‖ ≤ 1)
    (hξ : ‖ξ‖ ≤ 1) : HasBoundedChange Ω Fs (pre ++ F₁' :: F₂' :: post) ξ S r K ε :=
  (hasBoundedChange_liftTwo pre post hc hΩ hξ).perm_left hp

/-- **A one-sheet change after a reordering.** If the frames `Fs` are a reordering of
`pre ++ F :: post`, a bounded change of `F` is a bounded change of `Fs`. -/
theorem hasBoundedChange_perm_liftOne {F F' : Frame pos q Party}
    {pre post : List (Frame pos q Party)} (hp : Fs.Perm (pre ++ F :: post))
    {c : OriginalCircuit F.regs F'.regs} (hc : c.IsBoundedChange S r K ε (F.regRef Ω) (F'.regRef Ω))
    (hΩ : ‖Ω‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1) : HasBoundedChange Ω Fs (pre ++ F' :: post) ξ S r K ε :=
  (hasBoundedChange_liftOne pre post hc hΩ hξ).perm_left hp

/-- **An unchanged sheet.** If the frame does not change, as for a birth or death with empty
target or the resize of a hole whose radius does not change, the identity change of the frame is a
bounded change for every set of participants and all bounds.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 432–438 and 529–541. -/
theorem exists_isBoundedChange_of_frame_eq {F F' : Frame pos q Party} (h : F = F') (S : Set Party)
    (r K : ℕ) (hε : 0 ≤ ε) :
    ∃ c : OriginalCircuit F.regs F'.regs, c.IsBoundedChange S r K ε (F.regRef Ω) (F'.regRef Ω) := by
  subst h
  exact ⟨.id _, OriginalCircuit.isBoundedChange_id S r K hε _⟩

end EncodedFrame

end TNLean.PEPS
