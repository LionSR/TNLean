/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.LayoutEqualityCoordinates
import TNLean.PEPS.Approximation.SheetStack

/-!
# Initialization and reordering of the sheets

In the protocol of Proposition 7.1 of the polynomial-PEPS manuscript the memory holds the main
sheet, the active auxiliary sheets, the frozen auxiliary sheets and the auxiliary copies of `Ω`
not yet in use. Every copy of `Ω`, including the main copy at the root, is initialized privately
at its future owner, so the initial vector is a pure product across parties
(`06-geometry.tex`, lines 658–667). This file supplies three pieces of that bookkeeping for the
memory of a list of encoded frames (`EncodedFrame.stackRegs`, `EncodedFrame.stackVec`).

* **Reordering the sheets.** A permutation of the frames is implemented by a word of exchanges
  of tensor factors that carries the reference vector of the frames, in the old order, to the
  reference vector in the new order (`EncodedFrame.exists_reordering_stackVec`). In particular
  an auxiliary sheet can be moved next to the main sheet before a lens exchange, which acts on
  two adjacent sheets (`EncodedFrame.liftTwo`). As an original circuit the reordering has no
  nonprivate gate (`EncodedFrame.exists_originalCircuit_stackVec_of_perm`).
* **The initial private maps.** If each frame of a list is held entirely by one party, the
  whole private memory of a party can be taken to be the memory of its frames. One private map
  per party then splits these whole memories into the registers of the frames, and carries the
  product of the frame reference vectors of the parties to the reference vector of all frames
  (`EncodedFrame.exists_originalCircuit_initial`).
* **The norm of the reference vector.** If every frame satisfies the frame constraint at
  accuracy `ε`, the reference vector has norm at least one minus `ε` times the total number of
  holes (`EncodedFrame.one_sub_mul_le_norm_stackVec`). With at most `C L³` holes in total and
  `ε = L⁻⁶⁰` this is the bound `1 - C L⁻⁵⁷ ≤ ‖Ξ‖ ≤ 1` for the product `Ξ` of the frozen
  auxiliary frames (`06-geometry.tex`, lines 674–678).

## Main results

* `EncodedFrame.exists_reordering_stackVec`,
  `EncodedFrame.exists_originalCircuit_stackVec_of_perm`.
* `EncodedFrame.stackVec_append`.
* `EncodedFrame.exists_originalCircuit_initial`.
* `EncodedFrame.one_sub_mul_le_norm_stackVec`,
  `EncodedFrame.one_sub_div_pow_le_norm_stackVec`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Proposition 7.1 `prop:protocol`,
  `06-geometry.tex`, lines 21–23 and 39–41 (statement), 653–667 (initialization and the
  reference vectors) and 669–681 (the final reference vector); `eq:frame-norm`,
  `05-frames.tex`, lines 84–94; private maps, `04-compression.tex`, lines 21–36 and 137–139.
-/

noncomputable section

open scoped TensorProduct
open ContinuousLinearMap

namespace TNLean.PEPS.EncodedFrame

open PairEffect

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} {Party : Type} {pos : ι → ℝ × ℝ}

/-! ### Registers of concatenated lists of frames -/

/-- The registers of a concatenated list of frames. -/
theorem stackRegs_append (A B : List (Frame pos q Party)) (ℓ : Layout Party) :
    stackRegs A [] ++ stackRegs B ℓ = stackRegs (A ++ B) ℓ := by
  induction A with
  | nil => rfl
  | cons F A ih => exact (List.append_assoc _ _ _).trans (congrArg (F.regs ++ ·) ih)

section Reference

variable [NeZero q]

/-- The reference vector of a list of frames, with no idle registers. -/
abbrev framesVec (Ω : EuclideanSpace ℂ (ι → Fin q)) (Fs : List (Frame pos q Party)) :
    Mem (stackRegs Fs []) :=
  stackVec Ω Fs (ℓ := []) (1 : ℂ)

private theorem appendIso_symm_memCongr_heq (a : Layout Party) {b c : Layout Party} (h : b = c)
    (x : Mem a) (y : Mem b) :
    HEq ((appendIso a b).symm (x ⊗ₜ y)) ((appendIso a c).symm (x ⊗ₜ Layout.memCongr h y)) := by
  cases h
  rfl

/-- The reference vector of a concatenated list of frames is the product of the reference
vectors of the two lists. -/
theorem stackVec_append (Ω : EuclideanSpace ℂ (ι → Fin q)) (A B : List (Frame pos q Party))
    {ℓ : Layout Party} (ξ : Mem ℓ) :
    Layout.memCongr (stackRegs_append A B ℓ)
        ((appendIso (stackRegs A []) (stackRegs B ℓ)).symm
          (framesVec Ω A ⊗ₜ stackVec Ω B ξ)) =
      stackVec Ω (A ++ B) ξ := by
  induction A with
  | nil =>
      change (appendIso ([] : Layout Party) (stackRegs B ℓ)).symm
        ((1 : ℂ) ⊗ₜ stackVec Ω B ξ) = _
      rw [appendIso_nil_symm_tmul, one_smul]
      rfl
  | cons F A ih =>
      apply eq_of_heq
      refine (Layout.memCongr_apply_heq _ _).trans ?_
      refine (appendIso_assoc_symm_heq F.regs (stackRegs A []) (stackRegs B ℓ)
        (F.regRef Ω) (framesVec Ω A) (stackVec Ω B ξ)).symm.trans ?_
      change HEq _ ((appendIso F.regs (stackRegs (A ++ B) ℓ)).symm
        (F.regRef Ω ⊗ₜ stackVec Ω (A ++ B) ξ))
      rw [← ih]
      exact appendIso_symm_memCongr_heq F.regs _ _ _

/-! ### Reordering the sheets -/

/-- **Reordering the sheets.** A permutation of a list of frames is implemented on their
registers, followed by untouched registers `ℓ`, by a word of exchanges of tensor factors that
carries the reference vector of the frames in the old order to the reference vector in the new
order. Polynomial-PEPS manuscript, `06-geometry.tex`, lines 662–667, and allowed monomials,
`04-compression.tex`, lines 32–35. -/
theorem exists_reordering_stackVec (Ω : EuclideanSpace ℂ (ι → Fin q))
    {Fs Fs' : List (Frame pos q Party)} (h : Fs.Perm Fs') (ℓ : Layout Party) :
    ∃ w : Word (stackRegs Fs ℓ) (stackRegs Fs' ℓ), w.IsReordering ∧
      ∀ ξ : Mem ℓ, w.eval (stackVec Ω Fs ξ) = stackVec Ω Fs' ξ := by
  induction h with
  | nil => exact ⟨.id _, Word.isReordering_id _, fun _ => rfl⟩
  | cons F _ ih =>
      obtain ⟨w, hw, he⟩ := ih
      exact ⟨Word.frameList F.regs w, hw.frameList _, fun ξ => by
        change (Word.frameList F.regs w).eval ((appendIso _ _).symm (F.regRef Ω ⊗ₜ _)) = _
        rw [Word.eval_frameList_appendIso_symm, he]
        rfl⟩
  | swap F G Fs =>
      exact ⟨Word.exchangeBlocks G.regs F.regs (stackRegs Fs ℓ),
        Word.isReordering_exchangeBlocks _ _ _,
        fun ξ => Word.eval_exchangeBlocks_appendIso_symm _ _ _ _ _ _⟩
  | trans _ _ ih ih' =>
      obtain ⟨w, hw, he⟩ := ih
      obtain ⟨w', hw', he'⟩ := ih'
      exact ⟨.comp w w', hw.comp hw', fun ξ => by
        rw [Word.eval_comp, comp_apply, he, he']⟩

/-- **Reordering the sheets, as an original circuit.** The reordering of
`exists_reordering_stackVec` has no nonprivate gate, so every participant condition holds
vacuously, and it carries the reference vector of the frames to the reference vector in the
new order. Polynomial-PEPS manuscript, `06-geometry.tex`, lines 662–667, and original circuits,
`04-compression.tex`, lines 199–208. -/
theorem exists_originalCircuit_stackVec_of_perm (Ω : EuclideanSpace ℂ (ι → Fin q))
    {Fs Fs' : List (Frame pos q Party)} (h : Fs.Perm Fs') (ℓ : Layout Party) :
    ∃ c : OriginalCircuit (stackRegs Fs ℓ) (stackRegs Fs' ℓ), c.nonprivateCount = 0 ∧
      (∀ (S : Set Party) g, (↑(c.participants g) : Set Party) ⊆ S) ∧
      (∀ r s, c.IsExpansionBounded r s) ∧ (∀ K, c.IsMonomialBounded K) ∧
      ∀ ξ : Mem ℓ, c.eval (stackVec Ω Fs ξ) = stackVec Ω Fs' ξ := by
  obtain ⟨w, hw, he⟩ := exists_reordering_stackVec Ω h ℓ
  refine ⟨w.toOriginalCircuit hw.isAllowed, Word.nonprivateCount_toOriginalCircuit_of_isReordering
    hw, fun S g => Word.participants_toOriginalCircuit_subset _ _ (hw.usesOnly S) g,
    fun r s => Word.isExpansionBounded_toOriginalCircuit_of_sourceCount_eq_zero _ _
      hw.sourceCount_eq r s,
    fun K => Word.isMonomialBounded_toOriginalCircuit_of_sourceCount_eq_zero _ _
      hw.sourceCount_eq K, fun ξ => ?_⟩
  rw [Word.eval_toOriginalCircuit, he]

/-! ### Identity changes -/

/-- **The identity change.** A change that leaves the frame unchanged, such as a birth or death
with empty target or the resize of a hole whose radius does not change, is the original circuit
without operations: it has no nonprivate gate and no reference error. It is kept as a change so
that the counts of changes per event do not depend on the geometry. Polynomial-PEPS manuscript,
`06-geometry.tex`, lines 432–438 and 529–541. -/
theorem exists_originalCircuit_of_frame_eq (Ω : EuclideanSpace ℂ (ι → Fin q))
    {F F' : Frame pos q Party} (h : F = F') :
    ∃ c : OriginalCircuit F.regs F'.regs, c.nonprivateCount = 0 ∧
      (∀ (S : Set Party) g, (↑(c.participants g) : Set Party) ⊆ S) ∧
      (∀ r s, c.IsExpansionBounded r s) ∧ (∀ K, c.IsMonomialBounded K) ∧
      c.eval (F.regRef Ω) = F'.regRef Ω := by
  subst h
  exact ⟨.id _, rfl, fun _ g => (nomatch g), fun _ _ => trivial, fun _ => trivial, rfl⟩

/-! ### The initial private maps -/

omit [Fintype ι] [DecidableEq ι] in
private theorem memCongr_self_symm_apply {a : Layout Party} (h : a = a) (x : Mem a) :
    (Layout.memCongr h).symm x = x :=
  rfl

/-- The whole initial private memory of a party that holds the list of frames `Fs`: the memory
of the registers of these frames. -/
abbrev framesSpace (Fs : List (Frame pos q Party)) : HSpace := Mem (stackRegs Fs [])

/-- The private map of a party that splits its whole memory `ℂ ⊗ M` into the registers of its
frames. -/
def splitMap (Fs : List (Frame pos q Party)) (p : Party) :
    Mem [(⟨p, framesSpace Fs⟩ : Reg Party)] →L[ℂ] Mem (stackRegs Fs []) :=
  (TensorProduct.ridIsometry ℂ (framesSpace Fs)).toLinearIsometry.toContinuousLinearMap

omit [NeZero q] in
theorem splitMap_tmul_one (Fs : List (Frame pos q Party)) (p : Party)
    (x : framesSpace Fs) : splitMap Fs p (x ⊗ₜ (1 : ℂ)) = x := by
  simp [splitMap]

omit [NeZero q] in
theorem norm_splitMap_le (Fs : List (Frame pos q Party)) (p : Party) :
    ‖splitMap Fs p‖ ≤ 1 :=
  LinearIsometry.norm_toContinuousLinearMap_le _

/-- The initial private maps: every party `p` of the list `ps`, holding the frames `blk p`,
splits its whole memory into the registers of these frames, by one private map each. -/
def splitCircuit (blk : Party → List (Frame pos q Party))
    (hblk : ∀ p, ∀ r ∈ stackRegs (blk p) [], r.owner = p) :
    (ps : List Party) →
      OriginalCircuit (ps.map fun p => (⟨p, framesSpace (blk p)⟩ : Reg Party))
        (stackRegs (ps.flatMap blk) [])
  | [] => .id []
  | p :: ps =>
      .comp (.privateMap p (a := [⟨p, framesSpace (blk p)⟩]) (by simp) (hblk p)
          (splitMap (blk p) p) (norm_splitMap_le _ _)
          (ps.map fun p => (⟨p, framesSpace (blk p)⟩ : Reg Party)))
        ((OriginalCircuit.frameList (stackRegs (blk p) []) (splitCircuit blk hblk ps)).castLayouts
          rfl ((stackRegs_append _ _ _).trans (by rw [List.flatMap_cons])))

omit [NeZero q] in
theorem nonprivateCount_splitCircuit (blk : Party → List (Frame pos q Party))
    (hblk : ∀ p, ∀ r ∈ stackRegs (blk p) [], r.owner = p) :
    (ps : List Party) → (splitCircuit blk hblk ps).nonprivateCount = 0
  | [] => rfl
  | _ :: ps => by
      simp only [splitCircuit, OriginalCircuit.nonprivateCount,
        OriginalCircuit.nonprivateCount_castLayouts, OriginalCircuit.nonprivateCount_frameList,
        nonprivateCount_splitCircuit blk hblk ps]

omit [NeZero q] in
theorem isExpansionBounded_splitCircuit (blk : Party → List (Frame pos q Party))
    (hblk : ∀ p, ∀ r ∈ stackRegs (blk p) [], r.owner = p) (r : ℕ) (s : ℝ) :
    (ps : List Party) → (splitCircuit blk hblk ps).IsExpansionBounded r s
  | [] => trivial
  | _ :: ps => ⟨trivial, OriginalCircuit.isExpansionBounded_castLayouts _ _ _
      (OriginalCircuit.isExpansionBounded_frameList _
        (isExpansionBounded_splitCircuit blk hblk r s ps) _)⟩

omit [NeZero q] in
theorem isMonomialBounded_splitCircuit (blk : Party → List (Frame pos q Party))
    (hblk : ∀ p, ∀ r ∈ stackRegs (blk p) [], r.owner = p) (K : ℕ) :
    (ps : List Party) → (splitCircuit blk hblk ps).IsMonomialBounded K
  | [] => trivial
  | _ :: ps => ⟨trivial, OriginalCircuit.isMonomialBounded_castLayouts _ _ _
      (OriginalCircuit.isMonomialBounded_frameList _
        (isMonomialBounded_splitCircuit blk hblk K ps) _)⟩

omit [NeZero q] in
theorem participants_splitCircuit_subset (blk : Party → List (Frame pos q Party))
    (hblk : ∀ p, ∀ r ∈ stackRegs (blk p) [], r.owner = p) (S : Set Party) :
    (ps : List Party) → (g : (splitCircuit blk hblk ps).nonprivateLocations) →
      (↑((splitCircuit blk hblk ps).participants g) : Set Party) ⊆ S
  | [], g => nomatch g
  | _ :: ps, g => by
      rcases g with g | g
      · exact nomatch g
      · exact OriginalCircuit.participants_castLayouts_subset _ _ _
          (OriginalCircuit.participants_frameList_subset _
            (participants_splitCircuit_subset blk hblk S ps) _) g

/-- The initial private maps carry the product of the frame reference vectors of the parties to
the reference vector of all frames. -/
theorem eval_splitCircuit (Ω : EuclideanSpace ℂ (ι → Fin q))
    (blk : Party → List (Frame pos q Party))
    (hblk : ∀ p, ∀ r ∈ stackRegs (blk p) [], r.owner = p)
    (hx : ∀ p, ‖framesVec Ω (blk p)‖ = 1) :
    (ps : List Party) →
      (splitCircuit blk hblk ps).eval
          (ProductInput.ofParties (fun p => framesSpace (blk p))
            (fun p => framesVec Ω (blk p)) hx ps).vector =
        framesVec Ω (ps.flatMap blk)
  | [] => rfl
  | p :: ps => by
      have ih := eval_splitCircuit Ω blk hblk hx ps
      simp only [splitCircuit, OriginalCircuit.eval, OriginalCircuit.eval_castLayouts,
        comp_apply, isoL_apply, ProductInput.ofParties, ProductInput.vector]
      erw [appendIso_one_tmul]
      rw [rTensor_tmul, splitMap_tmul_one, memCongr_self_symm_apply]
      rw [OriginalCircuit.eval_frameList_appendIso_symm, ih]
      apply eq_of_heq
      refine (Layout.memCongr_apply_heq _ _).trans ?_
      refine HEq.trans ?_ (heq_of_eq (stackVec_append Ω (blk p) (ps.flatMap blk) (ℓ := []) (1 : ℂ)))
      refine HEq.trans ?_ (Layout.memCongr_apply_heq _ _).symm
      congr 1

/-- **The initial private maps.** Let every frame `F` of the list `Fs` be held entirely by the
party `holder F`. Take as the whole initial memory of each party the memory of its frames, in
their order in `Fs`, and as its initial vector the product of their reference vectors, of norm
one. One private map per party splits the whole memories into the registers of the frames, and
a reordering puts the frames in the order of `Fs`. The resulting original circuit has no
nonprivate gate and carries the initial product vector exactly to the reference vector of `Fs`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 21–23 and 658–667 (“Initialize all
required copies of `Ω` privately at their future owners, including the main copy at the root.
This is a pure product initialization across parties”), and the product inputs of Theorem 5.2,
`04-compression.tex`, lines 137–139. -/
theorem exists_originalCircuit_initial [Fintype Party] [DecidableEq Party]
    (Ω : EuclideanSpace ℂ (ι → Fin q)) (Fs : List (Frame pos q Party))
    (holder : Frame pos q Party → Party) (hown : ∀ F ∈ Fs, ∀ r ∈ F.regs, r.owner = holder F)
    (hx : ∀ p, ‖framesVec Ω (Fs.filter fun F => holder F = p)‖ = 1) :
    ∃ c : OriginalCircuit
        (ProductInput.wholePartyLayout fun p => framesSpace (Fs.filter fun F => holder F = p))
        (stackRegs Fs []),
      c.nonprivateCount = 0 ∧ (∀ (S : Set Party) g, (↑(c.participants g) : Set Party) ⊆ S) ∧
      (∀ r s, c.IsExpansionBounded r s) ∧ (∀ K, c.IsMonomialBounded K) ∧
      c.eval (ProductInput.ofAllParties _ _ hx).vector = framesVec Ω Fs := by
  set blk : Party → List (Frame pos q Party) := fun p => Fs.filter fun F => holder F = p
  have hblk : ∀ p, ∀ r ∈ stackRegs (blk p) [], r.owner = p := by
    intro p
    suffices ∀ G : List (Frame pos q Party), (∀ F ∈ G, holder F = p ∧ F ∈ Fs) →
        ∀ r ∈ stackRegs G [], r.owner = p from
      this _ fun F hF => by
        obtain ⟨h1, h2⟩ := List.mem_filter.1 hF
        exact ⟨by simpa using h2, h1⟩
    intro G hG
    induction G with
    | nil => simp
    | cons F G ih =>
        intro r hr
        rcases List.mem_append.1 hr with hr | hr
        · obtain ⟨h1, h2⟩ := hG F List.mem_cons_self
          exact (hown F h2 r hr).trans h1
        · exact ih (fun F hF => hG F (List.mem_cons_of_mem _ hF)) r hr
  have hperm : ((Finset.univ : Finset Party).toList.flatMap blk).Perm Fs := by
    classical
    rw [List.perm_iff_count]
    intro F
    have key : ∀ p, (blk p).count F = if holder F = p then Fs.count F else 0 := by
      intro p
      split_ifs with hp
      · exact List.count_filter (by simpa using hp)
      · exact List.count_eq_zero.2 fun h => hp (by simpa using (List.mem_filter.1 h).2)
    rw [List.count_flatMap, Function.comp_def, Finset.sum_map_toList]
    simp only [key, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  obtain ⟨c, h0, hP, hE, hM, he⟩ := exists_originalCircuit_stackVec_of_perm Ω hperm []
  refine ⟨.comp (splitCircuit blk hblk _) c, ?_, fun S g => ?_, fun r s =>
    ⟨isExpansionBounded_splitCircuit blk hblk r s _, hE r s⟩,
    fun K => ⟨isMonomialBounded_splitCircuit blk hblk K _, hM K⟩, ?_⟩
  · change (splitCircuit blk hblk _).nonprivateCount + c.nonprivateCount = 0
    rw [nonprivateCount_splitCircuit, h0]
  · rcases g with g | g
    · exact participants_splitCircuit_subset blk hblk S _ g
    · exact hP S g
  · change c.eval ((splitCircuit blk hblk _).eval _) = _
    exact (congrArg c.eval (eval_splitCircuit Ω blk hblk hx _)).trans (he (1 : ℂ))

/-! ### The norm of the reference vector -/

/-- **The norm of the reference vector of several sheets.** If `‖Ω‖ = 1` and every hole of
every frame satisfies the frame constraint `‖P Ω - Ω‖ ≤ ε`, then the reference vector of the
frames has norm at least `1 - (number of holes) ε` times the norm of the idle vector.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 674–678, from `eq:frame-norm`,
`05-frames.tex`, lines 84–94. -/
theorem one_sub_mul_le_norm_stackVec {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1)
    {ε : ℝ} : (Fs : List (Frame pos q Party)) →
      (∀ F ∈ Fs, ∀ h ∈ F.holes, ‖act h.patch.proj Ω - Ω‖ ≤ ε) → {ℓ : Layout Party} →
      (ξ : Mem ℓ) →
        (1 - (Fs.map fun F => (F.holes.length : ℝ)).sum * ε) * ‖ξ‖ ≤ ‖stackVec Ω Fs ξ‖
  | [], _, _, ξ => by simp only [List.map_nil, List.sum_nil, zero_mul, sub_zero, one_mul]; rfl
  | F :: Fs, hε, ℓ, ξ => by
      obtain ⟨h1, h2⟩ := F.one_sub_mul_le_norm_refVec hΩ (hε F List.mem_cons_self)
      have ih := one_sub_mul_le_norm_stackVec hΩ Fs
        (fun G hG => hε G (List.mem_cons_of_mem _ hG)) ξ
      have hle : ‖stackVec Ω Fs ξ‖ ≤ ‖ξ‖ := norm_stackVec_le hΩ.le Fs ξ
      change _ ≤ ‖(appendIso F.regs (stackRegs Fs ℓ)).symm (F.regRef Ω ⊗ₜ stackVec Ω Fs ξ)‖
      rw [LinearIsometryEquiv.norm_map, TensorProduct.norm_tmul, F.norm_regRef, List.map_cons,
        List.sum_cons]
      have hy := mul_le_mul_of_nonneg_left hle (sub_nonneg.2 h2)
      have hz := mul_le_mul_of_nonneg_right (show 1 - ‖F.refVec Ω‖ ≤ F.holes.length * ε by
        linarith) (norm_nonneg ξ)
      nlinarith

/-- **The bound `1 - C L⁻⁵⁷ ≤ ‖Ξ‖ ≤ 1`.** If `‖Ω‖ = 1`, every hole of every frame satisfies the
frame constraint at accuracy `L⁻⁶⁰`, and the frames have at most `C L³` holes in total, then the
reference vector of the frames, with an idle vector of norm one, has norm between
`1 - C L⁻⁵⁷` and `1`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 653–656 (“Even the weaker total bound
`C L³` on frozen auxiliary holes will suffice”) and 674–678. -/
theorem one_sub_div_pow_le_norm_stackVec {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1)
    {L : ℕ} (hL : 0 < L) {C : ℝ} (Fs : List (Frame pos q Party))
    (hε : ∀ F ∈ Fs, ∀ h ∈ F.holes, ‖act h.patch.proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹)
    (hholes : (Fs.map fun F => (F.holes.length : ℝ)).sum ≤ C * (L : ℝ) ^ 3)
    {ℓ : Layout Party} {ξ : Mem ℓ} (hξ : ‖ξ‖ = 1) :
    1 - C / (L : ℝ) ^ 57 ≤ ‖stackVec Ω Fs ξ‖ ∧ ‖stackVec Ω Fs ξ‖ ≤ 1 := by
  refine ⟨?_, hξ ▸ norm_stackVec_le hΩ.le Fs ξ⟩
  have h := one_sub_mul_le_norm_stackVec hΩ Fs hε ξ
  rw [hξ, mul_one] at h
  refine le_trans ?_ h
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hpow : C / (L : ℝ) ^ 57 = C * (L : ℝ) ^ 3 * ((L : ℝ) ^ 60)⁻¹ := by
    field_simp
  rw [hpow]
  have := mul_le_mul_of_nonneg_right hholes (inv_nonneg.2 (pow_nonneg hL'.le 60))
  linarith

end Reference

end TNLean.PEPS.EncodedFrame
