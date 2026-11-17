/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusDualFiniteFaceElimination
import TNLean.PEPS.TorusDualPresentationCompleteness
import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# A finite reduced-word classification for proper square support

For every proper allowed square support, construct one finite sequence of
actual native face substitutions, independent of the compared paths. Two
parallel labelled paths are generated-homotopic exactly when the transformed
free-group words have equal reduced lists.

The sequence has at most one entry per native vertex and uses only allowed
faces. Positive periods include one and two. This is an existence theorem
for a finite geometric normal form, not an extracted executable general
decision procedure or a complexity bound. Full support retains its separate
displacement classification.

Source: the restricted generated-move interpretation of SCP10,
arXiv:1001.3807v3, Lemma 6.14, lines 2199–2214.
See docs/paper-gaps/scp10_dual_proper_support_normal_form.tex.
-/

noncomputable section
namespace TNLean.PEPS

variable {width height : ℕ}
local notation "X" => TorusVertex width height
local notation "FG" => FreeGroup (X ⊕ X)
local instance properSupportQuiver : Quiver X := torusDualQuiver width height

private def eliminatedTransport (R : Finset X) (Φ : FG →* FG)
    (hΦ : ∀ v : X, (v.1 + 1, v.2 + 1) ∈ R → Φ (torusDualFaceWord v) = 1) :
    TorusDualFlatTransport (width := width) (height := height) (R : Set X)
      (fun _ => FG) where
  step e z := Φ (torusDualStepWord e) * z
  reverse_step e z := by
    cases e <;>
      simp [TorusDualStep.reverse, torusDualStepWord, map_inv]
  square x y hxy z := by
    have hr := hΦ (x, y) hxy
    rw [torusDualFaceWord, map_mul, map_inv] at hr
    have he := congrArg (fun g : FG => g * z) (mul_inv_eq_one.mp hr)
    simpa only [torusDualEastNorth, torusDualNorthEast, torusDualPathWord,
      torusDualStepWord, map_mul, map_one, mul_one, mul_assoc] using he

private theorem eliminatedTransport_eval [NeZero width] [NeZero height]
    (R : Finset X) (Φ : FG →* FG)
    (hΦ : ∀ v : X, (v.1 + 1, v.2 + 1) ∈ R → Φ (torusDualFaceWord v) = 1)
    {a b : X} (p : TorusDualPath a b) (z : FG) :
    (eliminatedTransport R Φ hΦ).eval p z = Φ (torusDualPathWord p) * z := by
  induction p with
  | nil => simp only [TorusDualFlatTransport.eval, torusDualPathWord, map_one, one_mul, id_eq]
  | cons p e ih =>
    change Φ (torusDualStepWord e) * (eliminatedTransport R Φ hΦ).eval p z =
      Φ (torusDualStepWord e * torusDualPathWord p) * z
    rw [ih, map_mul, mul_assoc]

variable [NeZero width] [NeZero height]

private theorem presentation_face_one (R : Finset X) (v : X)
    (hv : (v.1 + 1, v.2 + 1) ∈ R) :
    PresentedGroup.mk (torusDualPresentationRelators R : Set FG) (torusDualFaceWord v) = 1 := by
  classical
  -- Match the classical equality used to form the relator finset. Free-word reduction
  -- also supplies a computable equality, so `classical` alone does not select this one.
  let : DecidableEq FG := fun a b => Classical.propDecidable (a = b)
  apply PresentedGroup.one_of_mem
  change torusDualFaceWord v ∈ torusDualPresentationRelators R
  unfold torusDualPresentationRelators
  exact Finset.mem_union_right _ (Finset.mem_image.mpr
    ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩)

/-- Any finite sequence of allowed native face substitutions killing all allowed
face relators classifies parallel paths by their transformed free-group words.
The hypotheses are local finite certificate conditions, independent of the paths. -/
theorem torusDualHomotopy_iff_faceElimination_word_eq (R : Finset X) (l : List (X × Bool))
    (hm : ∀ d ∈ l, (d.1.1 + 1, d.1.2 + 1) ∈ R)
    (hf : ∀ v : X, (v.1 + 1, v.2 + 1) ∈ R →
      torusDualFaceEliminationSequence l (torusDualFaceWord v) = 1)
    {a b : X} (p q : TorusDualPath a b) :
    TorusDualHomotopy (R : Set X) p q ↔
      torusDualFaceEliminationSequence l (torusDualPathWord p) =
        torusDualFaceEliminationSequence l (torusDualPathWord q) := by
  constructor
  · intro h
    have he := h.flatTransport_eval_eq
      (eliminatedTransport R (torusDualFaceEliminationSequence l) hf) (1 : FG)
    simpa only [eliminatedTransport_eval, mul_one] using he
  · intro h
    let π := PresentedGroup.mk (torusDualPresentationRelators R : Set FG)
    have hπ := torusDualFaceEliminationSequence_preserves_flatRepresentation π l
      (fun d hd => presentation_face_one R d.1 (hm d hd))
    have hp := congrArg (fun f : FG →* PresentedGroup
      (torusDualPresentationRelators R : Set FG) => f (torusDualPathWord p)) hπ
    have hq := congrArg (fun f : FG →* PresentedGroup
      (torusDualPresentationRelators R : Set FG) => f (torusDualPathWord q)) hπ
    have he := congrArg π h
    apply (torusDualHomotopy_iff_presentation_word_eq R p q).mpr
    exact hp.symm.trans (he.trans hq)

/-- Every proper allowed primal square support admits a finite geometric
reduced-word classification of all parallel native paths. The actual face
substitution sequence is constructed from the support, uses only its faces,
and has length at most the number of native vertices. This theorem proves
existence of the normal form; no executable general decider is asserted. -/
theorem exists_torusDualProperSupportNormalForm (R : Finset X)
    (hR : R ≠ Finset.univ) :
    ∃ l : List (X × Bool), l.length ≤ Fintype.card X ∧
      (∀ d ∈ l, (d.1.1 + 1, d.1.2 + 1) ∈ R) ∧
      ∀ {a b : X} (p q : TorusDualPath a b),
        TorusDualHomotopy (R : Set X) p q ↔
          (torusDualFaceEliminationSequence l (torusDualPathWord p)).toWord =
            (torusDualFaceEliminationSequence l (torusDualPathWord q)).toWord := by
  obtain ⟨l, hlen, hm, hf⟩ := exists_torusDualFaceEliminationSequence R hR
  refine ⟨l, hlen, hm, ?_⟩
  intro a b p q
  exact (torusDualHomotopy_iff_faceElimination_word_eq R l hm hf p q).trans
    FreeGroup.toWord_inj.symm

end TNLean.PEPS
