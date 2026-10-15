/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.GuideFrameRewrite
import TNLean.PEPS.Approximation.PatchRewriteCircuit

/-!
# A small-patch rewrite between frames of guides as one gate

Under the plane conditions of Lemma 6.3 (`GuideFrameRewrite.PlaneConditions`), a rewrite between
the frames of two guides is an original circuit from the registers of the old frame to those of
the new frame with at most one nonprivate gate, whose participants are specified parties, and
which maps the reference vector of the old frame to that of the new frame up to
`(2b + 1) L^{-20}` (`GuideFrameRewrite.exists_originalCircuit`). The frames of guides list their
holes in the order of their centers, while Lemma 6.3 lists the untouched holes first; the two
orders are identified by exchanges of tag registers, which move the reference vector of one
listing to that of the other (`EncodedFrame.Frame.exists_permWord`), as in the canonical
identification of tag orderings of the source.

## Main results

* `EncodedFrame.Frame.exists_permWord`: frames with the same owners whose holes are listed in two
  orders are identified by a word of exchanges, which preserves norms and reference vectors.
* `Approximation.GuideFrameRewrite.exists_originalCircuit`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Lemma 6.3 `lem:small-rewrite`,
  `05-frames.tex`, lines 188–218; the canonical identification of tag orderings, lines 74–75 and
  84–85; the gates of Proposition 7.1, `06-geometry.tex`, lines 574–583.
-/

open Set Metric

noncomputable section

namespace TNLean.PEPS

open PairEffect

namespace EncodedFrame

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} {pos : ι → ℝ × ℝ} {Party : Type}

theorem nonempty_tagSpace : (l : List (Hole pos q Party)) → (∀ h ∈ l, Nonempty h.patch.Tag) →
    Nonempty (TagSpace l)
  | [], _ => ⟨()⟩
  | h :: l, hl =>
      have := hl h List.mem_cons_self
      have := nonempty_tagSpace l fun h' hh' => hl h' (List.mem_cons_of_mem _ hh')
      inferInstanceAs (Nonempty (h.patch.Tag × TagSpace l))

theorem Frame.nontrivial_mem_regs [NeZero q] (F : Frame pos q Party)
    (h : ∀ h ∈ F.holes, Nonempty h.patch.Tag) : Nontrivial (Mem F.regs) := by
  have := nonempty_tagSpace F.holes h
  exact F.regIso.toLinearEquiv.toEquiv.nontrivial

/-- **Two listings of the holes of a frame.** If two frames have the same owners and list the
same holes in two orders, there is a word of exchanges of tensor factors from the registers of the
first to those of the second, using no party, preserving norms and mapping the reference vector
of the first frame to that of the second.

Polynomial-PEPS manuscript, `05-frames.tex`, lines 74–75 and 84–85. -/
theorem Frame.exists_permWord [NeZero q] (F F' : Frame pos q Party) (ho : F.owner = F'.owner)
    (hp : F.holes.Perm F'.holes) :
    ∃ w : Word F.regs F'.regs, w.IsReordering ∧ (∀ z, ‖w.eval z‖ = ‖z‖) ∧
      ∀ Ω, w.eval (F.regIso.symm (F.refVec Ω)) = F'.regIso.symm (F'.refVec Ω) := by
  obtain ⟨own, l, hl⟩ := F
  obtain ⟨own', l', hl'⟩ := F'
  dsimp only at ho hp
  subst ho
  obtain ⟨e, he, w, hw, hw'⟩ := exists_tagWord_of_perm hl hp (siteRegs q own (sites ι))
  set E := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (e.prodCongr (Equiv.refl (ι → Fin q)))
  have key : ∀ y, layoutIso l' own (w.eval ((layoutIso l own).symm y)) = E y := by
    intro y
    conv_lhs => rw [← (EuclideanSpace.basisFun _ ℂ).sum_repr y]
    conv_rhs => rw [← (EuclideanSpace.basisFun _ ℂ).sum_repr y]
    simp only [map_sum, map_smul]
    refine Finset.sum_congr rfl fun ⟨τ, c⟩ _ => ?_
    rw [EuclideanSpace.basisFun_apply, layoutIso_symm_single]
    congr 1
    rw [layoutVec, hw', ← layoutVec, layoutIso_layoutVec]
    exact (LinearIsometryEquiv.piLpCongrLeft_single (p := 2) (𝕜 := ℂ) (E := ℂ)
      (e.prodCongr (Equiv.refl _)) (τ, c) (1 : ℂ)).symm
  refine ⟨w, hw, fun z => ?_, fun Ω => ?_⟩
  · have := key (layoutIso l own z)
    rw [LinearIsometryEquiv.symm_apply_apply] at this
    rw [← (layoutIso l' own).norm_map, this, E.norm_map, (layoutIso l own).norm_map]
  · apply (layoutIso l' own).injective
    change layoutIso l' own (w.eval ((layoutIso l own).symm _)) = _
    rw [key, LinearIsometryEquiv.apply_symm_apply]
    ext ⟨τ', c⟩
    have h := he (e.symm τ')
    rw [Equiv.apply_symm_apply] at h
    simp only [E, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply,
      Equiv.prodCongr_symm, Equiv.prodCongr_apply, Equiv.refl_symm, Prod.map_apply,
      Equiv.refl_apply]
    simp only [Frame.refVec, Frame.encoder, frameEncoder, act_apply_apply, Matrix.mulVec,
      dotProduct, stack, Matrix.of_apply, h]

end EncodedFrame

namespace Approximation

open EncodedFrame

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} {pos : ι → ℝ × ℝ} {κ Party : Type}

namespace GuideFrameRewrite

variable {G : GuideFrameRewrite pos q κ Party} [NeZero q]

/-- **A small-patch rewrite between frames of guides as one gate.** Under the plane conditions
of Lemma 6.3, suppose that every affected hole and every additional patch has at most `C L^c`
cylinder terms, that there are at most `b` additional patches, `b` old and `b` new affected holes
and `b` specified parties,
that `‖Ω‖ ≤ 1` and every additional patch and every old affected hole has error at most
`L^{-60}` on `Ω`, that the specified list of parties is nonempty and that every hole of the old
frame has a tag. Then there is an original circuit from the registers of the old frame to those
of the new frame with at most one nonprivate gate, every participant of a gate a specified party,
gate expansion into at most `K L^e` allowed monomials with at most `2b` normalized pair effects
each and coefficients of total modulus at most `K L^e`, mapping the reference vector of the old
frame to that of the new frame up to `(2b + 1) L^{-20}`. Here
`K = (C + 1)^{3b} (16 b² (C + 1)^{6b} + 1)^{2b}` and `e = 3bc + 4b(3bc + 30)`.

Polynomial-PEPS manuscript, Lemma 6.3 `lem:small-rewrite`, `05-frames.tex`, lines 188–218; the
canonical identification of tag orderings, lines 74–75 and 84–85; the gates of Proposition 7.1,
`06-geometry.tex`, lines 574–583. -/
theorem PlaneConditions.exists_originalCircuit (h : G.PlaneConditions) {C c b L : ℕ}
    (hL : 1 ≤ L) (hnew : ∀ a ∈ G.newAffected, Fintype.card (G.holeNew a).Tag ≤ C * L ^ c)
    (hpatch : ∀ z ∈ G.centers, Fintype.card (G.patch z).Tag ≤ C * L ^ c)
    (hold : ∀ a ∈ G.oldAffected, Fintype.card (G.holeOld a).Tag ≤ C * L ^ c)
    (hm : G.centers.card ≤ b) (hrold : G.oldAffected.card ≤ b) (hrnew : G.newAffected.card ≤ b)
    (hparties : G.parties.card ≤ b)
    {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ ≤ 1)
    (hεpatch : ∀ z ∈ G.centers, ‖act (G.patch z).proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹)
    (hεold : ∀ a ∈ G.oldAffected, ‖act (G.holeOld a).proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹)
    (hS₀ : G.parties.Nonempty)
    (htag : ∀ z ∈ G.untouched ∪ G.oldAffected, Nonempty (G.holeOld z).Tag) :
    ∃ w : OriginalCircuit G.oldFrame.regs G.newFrame.regs, w.nonprivateCount ≤ 1 ∧
      (∀ g, (↑(w.participants g) : Set Party) ⊆ ↑G.parties) ∧
      w.IsExpansionBounded (2 * b) ((C + 1) ^ (3 * b) * (16 * b ^ 2 * (C + 1) ^ (6 * b) + 1) ^
        (2 * b) * L ^ (3 * b * c + 4 * b * (3 * b * c + 30)) : ℕ) ∧
      w.IsMonomialBounded ((C + 1) ^ (3 * b) * (16 * b ^ 2 * (C + 1) ^ (6 * b) + 1) ^ (2 * b) *
        L ^ (3 * b * c + 4 * b * (3 * b * c + 30))) ∧
      ‖w.eval (G.oldFrame.regIso.symm (G.oldFrame.refVec Ω)) -
          G.newFrame.regIso.symm (G.newFrame.refVec Ω)‖ ≤ (2 * b + 1) * ((L : ℝ) ^ 20)⁻¹ := by
  set R := G.toSmallPatchRewrite h.untouched_agree
  have hR := h.conditions
  have hne : Nontrivial (Mem R.oldFrame.regs) := R.oldFrame.nontrivial_mem_regs fun h' hh' => by
    rcases List.mem_append.1 hh' with hh' | hh' <;> obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hh'
    · exact htag z (Finset.mem_union_left _ (Finset.mem_toList.1 hz))
    · exact htag z (Finset.mem_union_right _ (Finset.mem_toList.1 hz))
  obtain ⟨c₀, Ma, -, -, href, hc₀, hcount, hpart, hexp, hmono⟩ :=
    R.exists_originalCircuit_refVec hR hL
      (fun h' hh' => by obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hh'
                        exact hnew a (Finset.mem_toList.1 ha))
      (fun P hP => by obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hP
                      exact hpatch z (Finset.mem_toList.1 hz))
      (fun h' hh' => by obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hh'
                        exact hold a (Finset.mem_toList.1 ha))
      (by simpa [R, toSmallPatchRewrite] using hm) (by simpa [R, toSmallPatchRewrite] using hrold)
      (by simpa [R, toSmallPatchRewrite] using hrnew) hparties hΩ
      (fun P hP => by obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hP
                      exact hεpatch z (Finset.mem_toList.1 hz))
      (fun h' hh' => by obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hh'
                        exact hεold a (Finset.mem_toList.1 ha)) hS₀ hne
  obtain ⟨w₁, hw₁, -, hr₁⟩ := Frame.exists_permWord G.oldFrame R.oldFrame rfl
    G.perm_oldFrame_holes
  have hp₃ : R.newFrame.holes.Perm G.newFrame.holes := by
    change (G.untouched.toList.map (G.holeAt G.old G.holeOld) ++ _).Perm _
    rw [G.map_holeAt_untouched h.untouched_agree]
    exact G.perm_newFrame_holes.symm
  obtain ⟨w₃, hw₃, hn₃, hr₃⟩ := Frame.exists_permWord R.newFrame G.newFrame rfl hp₃
  refine ⟨(w₁.toOriginalCircuit hw₁.isAllowed).comp (c₀.comp (w₃.toOriginalCircuit
    hw₃.isAllowed)), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [OriginalCircuit.nonprivateCount,
      Word.nonprivateCount_toOriginalCircuit_of_isReordering hw₁,
      Word.nonprivateCount_toOriginalCircuit_of_isReordering hw₃, zero_add, add_zero]
    exact hcount
  · rintro (g | g | g)
    · exact Word.participants_toOriginalCircuit_subset _ _ (hw₁.usesOnly _) g
    · exact hpart g
    · exact Word.participants_toOriginalCircuit_subset _ _ (hw₃.usesOnly _) g
  · exact ⟨Word.isExpansionBounded_toOriginalCircuit_of_sourceCount_eq_zero _ _
      hw₁.sourceCount_eq _ _, hexp,
      Word.isExpansionBounded_toOriginalCircuit_of_sourceCount_eq_zero _ _ hw₃.sourceCount_eq _ _⟩
  · exact ⟨Word.isMonomialBounded_toOriginalCircuit_of_sourceCount_eq_zero _ _
      hw₁.sourceCount_eq _, hmono,
      Word.isMonomialBounded_toOriginalCircuit_of_sourceCount_eq_zero _ _ hw₃.sourceCount_eq _⟩
  · simp only [OriginalCircuit.eval, ContinuousLinearMap.comp_apply,
      Word.eval_toOriginalCircuit, hr₁]
    rw [← hr₃, ← map_sub, hn₃, ← R.newFrame.regIso.norm_map, map_sub,
      LinearIsometryEquiv.apply_symm_apply, hc₀, LinearIsometryEquiv.apply_symm_apply]
    exact href

end GuideFrameRewrite

end Approximation

end TNLean.PEPS
