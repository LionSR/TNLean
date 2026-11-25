/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.FrameChanges.GuideFrameRewrite
import TNLean.PEPS.Approximation.PatchRewrite.PatchRewriteCircuit
import TNLean.PEPS.Approximation.Frames.FrameBoundedChanges

/-!
# A small-patch rewrite between frames of guides as one gate

Under the plane conditions of Lemma 6.3 (`GuideFrameRewrite.PlaneConditions`), a rewrite between
the frames of two guides is an original circuit from the registers of the old frame to those of
the new frame with at most one nonprivate gate, whose participants are specified parties, and
which maps the reference vector of the old frame to that of the new frame up to
`(2b + 1) L^{-20}` (`GuideFrameRewrite.exists_originalCircuit`). The frames of guides list their
holes in the order of their centers, while Lemma 6.3 lists the untouched holes first; the two
orders are identified by a relabelling of the tags at every party, which moves the reference
vector of one listing to that of the other (`EncodedFrame.Frame.exists_relabel_of_perm`), as in
the canonical identification of tag orderings of the source.

## Main results

* `EncodedFrame.Frame.exists_relabel_of_perm`: frames with the same owners whose holes are listed
  in two orders are identified by a relabelling of the bases of the parties, which maps reference
  vectors to reference vectors.
* `Approximation.GuideFrameRewrite.PlaneConditions.exists_originalCircuit_isSourceBounded`,
  `Approximation.GuideFrameRewrite.PlaneConditions.exists_originalCircuit`: with and without the
  bound of `2b` pair sources in every monomial.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Lemma 6.3 `lem:small-rewrite`,
  `05-frames.tex`, lines 188–218; the canonical identification of tag orderings, lines 74–75 and
  84–85; the gates of Proposition 7.1, `06-geometry.tex`, lines 574–583.
-/

open Set Metric

noncomputable section

namespace TNLean.PEPS

open Matrix ManyBody QuantumCircuit.Party

namespace EncodedFrame

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} {pos : ι → ℝ × ℝ} {Party : Type}
  [Fintype Party] [DecidableEq Party]

/-- **Two listings of the holes of a frame.** If two frames have the same owners and list the
same holes in two orders, the registers of the first are those of the second at every party, the
tag of every hole moved to its new position: the relabelling of the bases of the parties along
this identification, a circuit without nonprivate gates, maps the reference vector of the first
frame to that of the second.

Polynomial-PEPS manuscript, `05-frames.tex`, lines 74–75 and 84–85. -/
theorem Frame.exists_relabel_of_perm [NeZero q] (F F' : Frame pos q Party)
    (ho : F.owner = F'.owner) (hp : F.holes.Perm F'.holes) :
    ∃ e : ∀ p, F'.system p ≃ F.system p, ∀ Ω : EuclideanSpace ℂ (ι → Fin q),
      toEuclideanLin (OriginalCircuit.relabel e).op (F.regRef Ω) = F'.regRef Ω := by
  obtain ⟨own, l, hl⟩ := F
  obtain ⟨own', l', hl'⟩ := F'
  dsimp only at ho hp
  subst ho
  obtain ⟨f, hf⟩ := exists_tagSystemEquiv_of_perm hl hp
  refine ⟨fun p ↦ (f p).prodCongr (Equiv.refl _), fun Ω ↦ ?_⟩
  ext z
  rw [OriginalCircuit.toEuclideanLin_op_relabel]
  simp only [LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply, Equiv.symm_symm,
    Frame.regRef_apply, Frame.configEquiv, layoutConfigEquiv_apply]
  change (stack (rawProd l) *ᵥ Ω.ofLp) _ = (stack (rawProd l') *ᵥ Ω.ofLp) _
  simp only [mulVec, dotProduct, stack_apply, ← hf]
  rfl

end EncodedFrame

namespace Approximation

open EncodedFrame

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} {pos : ι → ℝ × ℝ} {κ Party : Type}
  [Fintype Party] [DecidableEq Party]

namespace GuideFrameRewrite

variable {G : GuideFrameRewrite pos q κ Party} [NeZero q]

/-- **A small-patch rewrite between frames of guides as one gate, with its pair sources.** The
conclusion of `PlaneConditions.exists_originalCircuit`, together with the bound of `2b` pair
sources in every monomial of the gate.

Polynomial-PEPS manuscript, Lemma 6.3 `lem:small-rewrite`, `05-frames.tex`, lines 188–218;
Theorem 5.2, item 3, `04-compression.tex`, lines 143–147. -/
theorem PlaneConditions.exists_originalCircuit_isSourceBounded (h : G.PlaneConditions)
    {C c b L : ℕ} (hL : 1 ≤ L)
    (hnew : ∀ a ∈ G.newAffected, Fintype.card (G.holeNew a).Tag ≤ C * L ^ c)
    (hpatch : ∀ z ∈ G.centers, Fintype.card (G.patch z).Tag ≤ C * L ^ c)
    (hold : ∀ a ∈ G.oldAffected, Fintype.card (G.holeOld a).Tag ≤ C * L ^ c)
    (hm : G.centers.card ≤ b) (hrold : G.oldAffected.card ≤ b) (hrnew : G.newAffected.card ≤ b)
    (hparties : G.parties.card ≤ b)
    {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ ≤ 1)
    (hεpatch : ∀ z ∈ G.centers, ‖toEuclideanLin (G.patch z).proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹)
    (hεold : ∀ a ∈ G.oldAffected, ‖toEuclideanLin (G.holeOld a).proj Ω - Ω‖ ≤
      ((L : ℝ) ^ 60)⁻¹) :
    ∃ w : OriginalCircuit G.oldFrame.system G.newFrame.system, w.nonprivateCount ≤ 1 ∧
      (∀ g, (↑(w.participants g) : Set Party) ⊆ ↑G.parties) ∧
      w.IsExpansionBounded (2 * b) ((C + 1) ^ (3 * b) * (16 * b ^ 2 * (C + 1) ^ (6 * b) + 1) ^
        (2 * b) * L ^ (3 * b * c + 4 * b * (3 * b * c + 30)) : ℕ) ∧
      w.IsMonomialBounded ((C + 1) ^ (3 * b) * (16 * b ^ 2 * (C + 1) ^ (6 * b) + 1) ^ (2 * b) *
        L ^ (3 * b * c + 4 * b * (3 * b * c + 30))) ∧
      ‖toEuclideanLin w.op (G.oldFrame.regRef Ω) - G.newFrame.regRef Ω‖ ≤
        (2 * b + 1) * ((L : ℝ) ^ 20)⁻¹ ∧
      w.IsSourceBounded (2 * b) := by
  set R := G.toSmallPatchRewrite h.untouched_agree
  have hR := h.conditions
  obtain ⟨c₀, Ma, -, -, href, hop, hcount, hpart, hexp, hmono, hsrc⟩ :=
    R.exists_originalCircuit_refVec_isSourceBounded hR hL
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
                        exact hεold a (Finset.mem_toList.1 ha))
  obtain ⟨e₁, hr₁⟩ := Frame.exists_relabel_of_perm G.oldFrame R.oldFrame rfl
    G.perm_oldFrame_holes
  have hp₃ : R.newFrame.holes.Perm G.newFrame.holes := by
    change (G.untouched.toList.map (G.holeAt G.old G.holeOld) ++ _).Perm _
    rw [G.map_holeAt_untouched h.untouched_agree]
    exact G.perm_newFrame_holes.symm
  obtain ⟨e₃, hr₃⟩ := Frame.exists_relabel_of_perm R.newFrame G.newFrame rfl hp₃
  have h₁ := OriginalCircuit.nonprivateCount_relabel e₁
  have h₃ := OriginalCircuit.nonprivateCount_relabel e₃
  refine ⟨(OriginalCircuit.relabel e₁).comp (c₀.comp (OriginalCircuit.relabel e₃)), ?_, ?_,
    ⟨OriginalCircuit.isExpansionBounded_of_nonprivateCount_eq_zero h₁ _ _, hexp,
      OriginalCircuit.isExpansionBounded_of_nonprivateCount_eq_zero h₃ _ _⟩,
    ⟨OriginalCircuit.isMonomialBounded_of_nonprivateCount_eq_zero h₁ _, hmono,
      OriginalCircuit.isMonomialBounded_of_nonprivateCount_eq_zero h₃ _⟩, ?_,
    ⟨OriginalCircuit.isSourceBounded_of_nonprivateCount_eq_zero h₁ _, hsrc,
      OriginalCircuit.isSourceBounded_of_nonprivateCount_eq_zero h₃ _⟩⟩
  · simp only [OriginalCircuit.nonprivateCount_comp, h₁, h₃, zero_add, add_zero]
    exact hcount
  · rintro (g | g | g)
    · exact OriginalCircuit.forall_participants_of_nonprivateCount_eq_zero
        (Q := fun D ↦ (↑D : Set Party) ⊆ ↑G.parties) h₁ g
    · exact hpart g
    · exact OriginalCircuit.forall_participants_of_nonprivateCount_eq_zero
        (Q := fun D ↦ (↑D : Set Party) ⊆ ↑G.parties) h₃ g
  · simp only [OriginalCircuit.op_comp, toEuclideanLin_mul_apply, hr₁]
    rw [← hr₃, ← map_sub, OriginalCircuit.toEuclideanLin_op_relabel,
      LinearIsometryEquiv.norm_map, hop, Frame.regRef, toEuclideanLin_reindex_piLpCongrLeft₂,
      Frame.regRef, ← map_sub, LinearIsometryEquiv.norm_map]
    exact href

/-- **A small-patch rewrite between frames of guides as one gate.** Under the plane conditions
of Lemma 6.3, suppose that every affected hole and every additional patch has at most `C L^c`
cylinder terms, that there are at most `b` additional patches, `b` old and `b` new affected holes
and `b` specified parties, and that `‖Ω‖ ≤ 1` and every additional patch and every old affected
hole has error at most `L^{-60}` on `Ω`. Then there is an original circuit from the registers of
the old frame to those of the new frame with at most one nonprivate gate, every participant of a
gate a specified party, gate expansion into at most `K L^e` allowed monomials with at most `2b`
normalized pair effects each and coefficients of total modulus at most `K L^e`, mapping the
reference vector of the old frame to that of the new frame up to `(2b + 1) L^{-20}`. Here
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
    (hεpatch : ∀ z ∈ G.centers, ‖toEuclideanLin (G.patch z).proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹)
    (hεold : ∀ a ∈ G.oldAffected, ‖toEuclideanLin (G.holeOld a).proj Ω - Ω‖ ≤
      ((L : ℝ) ^ 60)⁻¹) :
    ∃ w : OriginalCircuit G.oldFrame.system G.newFrame.system, w.nonprivateCount ≤ 1 ∧
      (∀ g, (↑(w.participants g) : Set Party) ⊆ ↑G.parties) ∧
      w.IsExpansionBounded (2 * b) ((C + 1) ^ (3 * b) * (16 * b ^ 2 * (C + 1) ^ (6 * b) + 1) ^
        (2 * b) * L ^ (3 * b * c + 4 * b * (3 * b * c + 30)) : ℕ) ∧
      w.IsMonomialBounded ((C + 1) ^ (3 * b) * (16 * b ^ 2 * (C + 1) ^ (6 * b) + 1) ^ (2 * b) *
        L ^ (3 * b * c + 4 * b * (3 * b * c + 30))) ∧
      ‖toEuclideanLin w.op (G.oldFrame.regRef Ω) - G.newFrame.regRef Ω‖ ≤
        (2 * b + 1) * ((L : ℝ) ^ 20)⁻¹ := by
  obtain ⟨w, h₁, h₂, h₃, h₄, h₅, -⟩ := h.exists_originalCircuit_isSourceBounded hL hnew hpatch hold
    hm hrold hrnew hparties hΩ hεpatch hεold
  exact ⟨w, h₁, h₂, h₃, h₄, h₅⟩

end GuideFrameRewrite

end Approximation

end TNLean.PEPS
