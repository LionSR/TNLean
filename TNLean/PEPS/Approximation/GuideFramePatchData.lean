/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.GuideFrameRewriteCircuit

/-!
# Patch data of small-patch rewrites from the adaptive patch constraint

The small-patch rewrites between frames of guides of Proposition 7.1
(`GuideFrameRewrite.PlaneConditions.exists_originalCircuit`) take three kinds of patch data as
hypotheses: polynomial bounds on the numbers of tags, errors at most `L^{-60}` of the patch
projectors on the ground vector, and a tag for every hole of the old frame. In the dyadic protocol
every hole and every additional patch is the patch chosen from Proposition 4.1 at test exponent
`60` (`EncodedFrame.patchAt`), and this file derives all three from that supply.

The tags of a supplied patch are nonempty without any convention: with an empty outer sample there
is the identity tag, and with a nonempty outer sample and no tag the cylinder sum vanishes, so its
error on a unit vector is `1 > L^{-p}`.

## Main definitions

* `EncodedFrame.IsSuppliedPatch`: a patch chosen from the supply of Proposition 4.1 at some center
  and admissible scale.
* `Approximation.GuideFrameRewrite.IsSupplied`: every additional patch and every hole patch of a
  rewrite between frames of guides is supplied.

## Main results

* `EncodedFrame.IsSuppliedPatch.norm_act_proj_sub_le`, `EncodedFrame.IsSuppliedPatch.card_tag_le`,
  `EncodedFrame.IsSuppliedPatch.nonempty_tag`: the error, the tag count and the nonemptiness of
  the tags of a supplied patch.
* `Approximation.GuideFrameRewrite.IsSupplied.patchData`: the patch hypotheses of
  `GuideFrameRewrite.PlaneConditions.exists_originalCircuit` for a supplied rewrite.
* `Approximation.GuideFrameRewrite.PlaneConditions.exists_originalCircuit_of_isSupplied`: a
  supplied small-patch rewrite between frames of guides is one gate, with the supply of
  Proposition 4.1 as the only source of patch data.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Proposition 4.1 `prop:patch`,
  `03-patches.tex`, lines 26–49; the holes with test exponent `60` and one adaptive choice on
  every sheet, `06-geometry.tex`, lines 109–118; the trivial one-branch encoding of an empty
  outer square, `06-geometry.tex`, lines 123–124, and `05-frames.tex`, lines 67–69; the
  `L^{-60}` patch tests of the protocol gates, `06-geometry.tex`, lines 574–583.
-/

noncomputable section

namespace TNLean.PEPS

open PairEffect

namespace EncodedFrame

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ} {pos : ι → ℝ × ℝ}
  {Ω : EuclideanSpace ℂ (ι → Fin q)} {B₀ C c p : ℝ} {L : ℕ}

/-- **A supplied patch.** The patch chosen from the supply of Proposition 4.1 at some center `z`
and some scale `0 < u ≤ B₀ log L`.

Polynomial-PEPS manuscript, Proposition 4.1 `prop:patch`, `03-patches.tex`, lines 26–49, and
`06-geometry.tex`, lines 109–118. -/
def IsSuppliedPatch (S : AdaptivePatchSupply pos Ω B₀ C c p L) (P : SquarePatch pos q) : Prop :=
  ∃ z u, ∃ hu : 0 < u ∧ u ≤ B₀ * Real.log L, patchAt S z hu = P

namespace IsSuppliedPatch

variable {S : AdaptivePatchSupply pos Ω B₀ C c p L} {P : SquarePatch pos q}

/-- The projector of a supplied patch has error at most `L^{-p}` on `Ω`.

Polynomial-PEPS manuscript, `03-patches.tex`, lines 26–33. -/
theorem norm_act_proj_sub_le (h : IsSuppliedPatch S P) :
    ‖act P.proj Ω - Ω‖ ≤ (L : ℝ) ^ (-p) := by
  obtain ⟨z, u, hu, rfl⟩ := h
  exact norm_act_proj_patchAt_sub_le S z hu

/-- **Tag count of a supplied patch.** For natural constants `C' ≥ max 1 C` and `c' ≥ c`, a
supplied patch has at most `C' L^{c'}` tags.

Polynomial-PEPS manuscript, `03-patches.tex`, lines 34–45, and `05-frames.tex`, lines 50–69. -/
theorem card_tag_le (h : IsSuppliedPatch S P) (hL : 1 ≤ L) {C' c' : ℕ} (hC : C ≤ C')
    (hC' : 1 ≤ C') (hc : c ≤ c') : Fintype.card P.Tag ≤ C' * L ^ c' := by
  obtain ⟨z, u, hu, rfl⟩ := h
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hC'' : (1 : ℝ) ≤ C' := by exact_mod_cast hC'
  have hpow : (L : ℝ) ^ c ≤ (L : ℝ) ^ (c' : ℝ) := Real.rpow_le_rpow_of_exponent_le hL' hc
  have hone : (1 : ℝ) ≤ (L : ℝ) ^ (c' : ℝ) := Real.one_le_rpow hL' (Nat.cast_nonneg _)
  have hpos : 0 < (L : ℝ) ^ c := Real.rpow_pos_of_pos (by linarith) c
  have key : max 1 (C * (L : ℝ) ^ c) ≤ (C' : ℝ) * (L : ℝ) ^ (c' : ℝ) := by
    refine max_le (by nlinarith) ?_
    rcases le_or_gt 0 C with hC0 | hC0
    · calc C * (L : ℝ) ^ c ≤ C * (L : ℝ) ^ (c' : ℝ) := mul_le_mul_of_nonneg_left hpow hC0
        _ ≤ C' * (L : ℝ) ^ (c' : ℝ) := mul_le_mul_of_nonneg_right hC (by linarith)
    · nlinarith
  rw [Real.rpow_natCast] at key
  exact_mod_cast (card_tag_patchAt_le S z hu).trans key

/-- **Supplied patches have tags.** If `‖Ω‖ = 1`, `L ≥ 2` and `p > 0`, a supplied patch has a
tag. With an empty outer sample this is the identity tag; with a nonempty outer sample and no tag
the cylinder sum would vanish and have error `1 > L^{-p}` on `Ω`.

Polynomial-PEPS manuscript, `03-patches.tex`, lines 26–45, and the one-branch encoding of an
empty outer square, `05-frames.tex`, lines 67–69. -/
theorem nonempty_tag (h : IsSuppliedPatch S P) (hΩ : ‖Ω‖ = 1) (hL : 2 ≤ L) (hp : 0 < p) :
    Nonempty P.Tag := by
  obtain ⟨z, u, hu, rfl⟩ := h
  rcases (patchAt S z hu).outer.eq_empty_or_nonempty with ho | ho
  · exact ⟨.inl ⟨(), ho⟩⟩
  · by_contra hne
    rw [not_nonempty_iff] at hne
    have hcyl : (patchAt S z hu).cylSum = 0 :=
      Finset.sum_eq_zero fun s _ => (hne.false (.inr ⟨s, ho⟩)).elim
    have he := norm_act_one_sub_cylSum_patchAt_le S z hu
    rw [hcyl, sub_zero, act_one, hΩ] at he
    have hlt : (L : ℝ) ^ (-p) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hL) (by linarith)
    linarith

end IsSuppliedPatch

end EncodedFrame

namespace Approximation

open EncodedFrame

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} {pos : ι → ℝ × ℝ} {κ Party : Type}

namespace GuideFrameRewrite

variable {G : GuideFrameRewrite pos q κ Party} {Ω : EuclideanSpace ℂ (ι → Fin q)}
  {B₀ C c : ℝ} {L : ℕ}

/-- **A supplied rewrite.** Every additional patch and every hole patch of the old and of the new
frame is chosen from the supply of Proposition 4.1 at test exponent `60`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 109–118. -/
def IsSupplied (G : GuideFrameRewrite pos q κ Party)
    (S : AdaptivePatchSupply pos Ω B₀ C c 60 L) : Prop :=
  (∀ z ∈ G.centers, IsSuppliedPatch S (G.patch z)) ∧
    (∀ a ∈ G.untouched ∪ G.oldAffected, IsSuppliedPatch S (G.holeOld a)) ∧
    ∀ a ∈ G.newAffected, IsSuppliedPatch S (G.holeNew a)

theorem rpow_neg_sixty (L : ℕ) : (L : ℝ) ^ (-(60 : ℝ)) = ((L : ℝ) ^ 60)⁻¹ := by
  rw [Real.rpow_neg (Nat.cast_nonneg _)]
  norm_cast

/-- **Patch data of a supplied rewrite.** For a rewrite between frames of guides whose patches are
supplied by Proposition 4.1 at test exponent `60`, with `‖Ω‖ = 1`, `L ≥ 2` and natural constants
`C' ≥ max 1 C` and `c' ≥ c`: every affected hole and every additional patch has at most
`C' L^{c'}` tags, every additional patch and every old affected hole has error at most `L^{-60}`
on `Ω`, and every hole of the old frame has a tag. These are the patch hypotheses of
`GuideFrameRewrite.PlaneConditions.exists_originalCircuit`.

Polynomial-PEPS manuscript, `03-patches.tex`, lines 26–49; `06-geometry.tex`, lines 109–124 and
574–583. -/
theorem IsSupplied.patchData {S : AdaptivePatchSupply pos Ω B₀ C c 60 L} (hG : G.IsSupplied S)
    (hΩ : ‖Ω‖ = 1) (hL : 2 ≤ L) {C' c' : ℕ} (hC : C ≤ C') (hC' : 1 ≤ C') (hc : c ≤ c') :
    (∀ a ∈ G.newAffected, Fintype.card (G.holeNew a).Tag ≤ C' * L ^ c') ∧
      (∀ z ∈ G.centers, Fintype.card (G.patch z).Tag ≤ C' * L ^ c') ∧
      (∀ a ∈ G.oldAffected, Fintype.card (G.holeOld a).Tag ≤ C' * L ^ c') ∧
      (∀ z ∈ G.centers, ‖act (G.patch z).proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹) ∧
      (∀ a ∈ G.oldAffected, ‖act (G.holeOld a).proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹) ∧
      ∀ z ∈ G.untouched ∪ G.oldAffected, Nonempty (G.holeOld z).Tag := by
  obtain ⟨hpatch, hold, hnew⟩ := hG
  have hL1 : 1 ≤ L := by omega
  have hold' : ∀ a ∈ G.oldAffected, IsSuppliedPatch S (G.holeOld a) :=
    fun a ha => hold a (Finset.mem_union_right _ ha)
  refine ⟨fun a ha => (hnew a ha).card_tag_le hL1 hC hC' hc,
    fun z hz => (hpatch z hz).card_tag_le hL1 hC hC' hc,
    fun a ha => (hold' a ha).card_tag_le hL1 hC hC' hc,
    fun z hz => rpow_neg_sixty L ▸ (hpatch z hz).norm_act_proj_sub_le,
    fun a ha => rpow_neg_sixty L ▸ (hold' a ha).norm_act_proj_sub_le,
    fun z hz => (hold z hz).nonempty_tag hΩ hL (by norm_num)⟩

/-- **A supplied small-patch rewrite between frames of guides as one gate.** Under the plane
conditions of Lemma 6.3, let the patches of the rewrite be supplied by Proposition 4.1 at test
exponent `60` for a unit vector `Ω` and `L ≥ 2`, and let `C' ≥ max 1 C` and `c' ≥ c` be natural
constants. If there are at most `b` additional patches, `b` old and `b` new affected holes and
`b` specified parties, and the specified list of parties is nonempty, then there is an original
circuit from the registers of the old frame to those of the new frame with at most one nonprivate
gate, every participant of a gate a specified party, gate expansion into at most `K L^e` allowed
monomials with at most `2b` normalized pair effects each and coefficients of total modulus at most
`K L^e`, mapping the reference vector of the old frame to that of the new frame up to
`(2b + 1) L^{-20}`. Here `K = (C' + 1)^{3b} (16 b² (C' + 1)^{6b} + 1)^{2b}` and
`e = 3bc' + 4b(3bc' + 30)`.

Polynomial-PEPS manuscript, Lemma 6.3 `lem:small-rewrite`, `05-frames.tex`, lines 188–218;
Proposition 4.1 `prop:patch`, `03-patches.tex`, lines 26–49; the holes and patches of the
protocol, `06-geometry.tex`, lines 109–124; the gates of Proposition 7.1, `06-geometry.tex`,
lines 574–583. -/
theorem PlaneConditions.exists_originalCircuit_of_isSupplied [NeZero q] (h : G.PlaneConditions)
    {S : AdaptivePatchSupply pos Ω B₀ C c 60 L} (hG : G.IsSupplied S) (hΩ : ‖Ω‖ = 1)
    (hL : 2 ≤ L) {C' c' b : ℕ} (hC : C ≤ C') (hC' : 1 ≤ C') (hc : c ≤ c')
    (hm : G.centers.card ≤ b) (hrold : G.oldAffected.card ≤ b) (hrnew : G.newAffected.card ≤ b)
    (hparties : G.parties.card ≤ b) (hS₀ : G.parties.Nonempty) :
    ∃ w : OriginalCircuit G.oldFrame.regs G.newFrame.regs, w.nonprivateCount ≤ 1 ∧
      (∀ g, (↑(w.participants g) : Set Party) ⊆ ↑G.parties) ∧
      w.IsExpansionBounded (2 * b) ((C' + 1) ^ (3 * b) * (16 * b ^ 2 * (C' + 1) ^ (6 * b) + 1) ^
        (2 * b) * L ^ (3 * b * c' + 4 * b * (3 * b * c' + 30)) : ℕ) ∧
      w.IsMonomialBounded ((C' + 1) ^ (3 * b) * (16 * b ^ 2 * (C' + 1) ^ (6 * b) + 1) ^ (2 * b) *
        L ^ (3 * b * c' + 4 * b * (3 * b * c' + 30))) ∧
      ‖w.eval (G.oldFrame.regIso.symm (G.oldFrame.refVec Ω)) -
          G.newFrame.regIso.symm (G.newFrame.refVec Ω)‖ ≤ (2 * b + 1) * ((L : ℝ) ^ 20)⁻¹ := by
  obtain ⟨hnew, hpatch, hold, hεpatch, hεold, htag⟩ := hG.patchData hΩ hL hC hC' hc
  exact h.exists_originalCircuit (by omega) hnew hpatch hold hm hrold hrnew hparties hΩ.le
    hεpatch hεold hS₀ htag

end GuideFrameRewrite

end Approximation

end TNLean.PEPS
