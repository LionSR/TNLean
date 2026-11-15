/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusDualPathPresentation
import TNLean.PEPS.TorusDualFlatTransport
import Mathlib.Algebra.Group.End

/-!
# Completeness of the finite native dual-path presentation

Two native paths with the same endpoints are supported-homotopic exactly
when their actual words have the same image in the finite presentation of
native steps, allowed squares and fixed root routes. The converse normalizes
every locally flat fibre transport by those actual root routes. Its step
permutations satisfy all defining relators, so the presentation maps to the
permutation group and separates any nonhomotopic path pair.

This is a finite-presentation classification for the restricted-support
interpretation of SCP10, arXiv:1001.3807v3, Lemma 6.14, lines 2199–2214.
It has finitely many explicit generators and relators, but does not assert
a terminating word-normalization algorithm or finite-group test family.
Both periods are positive; labels remain distinct at periods one and two.
See `docs/paper-gaps/scp10_dual_finite_presentation.tex`.
-/

noncomputable section
namespace TNLean.PEPS

universe u
variable {width height : ℕ}
local notation "X" => TorusVertex width height
local notation "FT" => TorusDualFlatTransport (width := width) (height := height)
local instance presentationCompleteQuiver : Quiver X := torusDualQuiver width height
variable {R : Set (TorusVertex width height)} {Y : TorusVertex width height → Type u}

private def stepEquiv (F : FT R Y) {a b : X}
    (e : TorusDualStep a b) : Y a ≃ Y b where
  toFun := F.step e
  invFun := F.step e.reverse
  left_inv := F.reverse_step e
  right_inv := by
    intro z
    simpa only [TorusDualStep.reverse_reverse] using F.reverse_step e.reverse z

private def pathEquiv (F : FT R Y) {a : X} :
    {b : X} → TorusDualPath a b → Y a ≃ Y b
  | _, .nil => Equiv.refl _
  | _, .cons p e => (pathEquiv F p).trans (stepEquiv F e)

private theorem pathEquiv_apply (F : FT R Y)
    {a b : X} (p : TorusDualPath a b) (z : Y a) : pathEquiv F p z = F.eval p z := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    change F.step e (pathEquiv F p z) = F.step e (F.eval p z)
    rw [ih]

variable [NeZero width] [NeZero height]

private def rootEquiv (F : FT R Y) (v : X) : Y (0, 0) ≃ Y v :=
  pathEquiv F (torusDualRootRoute v)

private theorem rootEquiv_apply (F : FT R Y) (v : X) (z : Y (0, 0)) :
    rootEquiv F v z = F.eval (torusDualRootRoute v) z := pathEquiv_apply F _ z

private theorem rootEquiv_zero (F : FT R Y) :
    rootEquiv F ((0, 0) : X) = Equiv.refl _ := by
  simp only [rootEquiv, torusDualRootRoute_zero, pathEquiv]

private def normalizedStep (F : FT R Y) {a b : X}
    (e : TorusDualStep a b) : Equiv.Perm (Y (0, 0)) :=
  ((rootEquiv F a).trans (stepEquiv F e)).trans (rootEquiv F b).symm

private theorem normalizedStep_apply (F : FT R Y) {a b : X}
    (e : TorusDualStep a b) (z : Y (0, 0)) :
    normalizedStep F e z = (rootEquiv F b).symm (F.step e (rootEquiv F a z)) := rfl

private theorem normalizedStep_reverse (F : FT R Y) {a b : X}
    (e : TorusDualStep a b) : normalizedStep F e.reverse = (normalizedStep F e)⁻¹ := by
  ext z
  rfl

private def transportGenerators (F : FT R Y) :
    X ⊕ X → Equiv.Perm (Y (0, 0))
  | .inl (x, y) => normalizedStep F (.east x y)
  | .inr (x, y) => normalizedStep F (.north x y)

private theorem lift_step (F : FT R Y) {a b : X}
    (e : TorusDualStep a b) :
    FreeGroup.lift (transportGenerators F) (torusDualStepWord e) = normalizedStep F e := by
  cases e with
  | east x y => simp only [torusDualStepWord, FreeGroup.lift_apply_of, transportGenerators]
  | north x y => simp only [torusDualStepWord, FreeGroup.lift_apply_of, transportGenerators]
  | west x y =>
    simpa only [torusDualStepWord, map_inv, FreeGroup.lift_apply_of, transportGenerators,
      TorusDualStep.reverse] using (normalizedStep_reverse F (.east x y)).symm
  | south x y =>
    simpa only [torusDualStepWord, map_inv, FreeGroup.lift_apply_of, transportGenerators,
      TorusDualStep.reverse] using (normalizedStep_reverse F (.north x y)).symm

private theorem lift_word_apply (F : FT R Y) {a b : X}
    (p : TorusDualPath a b) (z : Y (0, 0)) :
    FreeGroup.lift (transportGenerators F) (torusDualPathWord p) z =
      (rootEquiv F b).symm (F.eval p (rootEquiv F a z)) := by
  induction p with
  | nil =>
    simp only [torusDualPathWord, map_one, Equiv.Perm.one_apply,
      TorusDualFlatTransport.eval, id_eq, Equiv.symm_apply_apply]
  | cons p e ih =>
    simp only [torusDualPathWord, map_mul, Equiv.Perm.mul_apply, lift_step,
      normalizedStep_apply, ih, Equiv.apply_symm_apply, TorusDualFlatTransport.eval]

private theorem lift_root_route (F : FT R Y) (v : X) :
    FreeGroup.lift (transportGenerators F) (torusDualPathWord (torusDualRootRoute v)) = 1 := by
  ext z
  rw [lift_word_apply, rootEquiv_zero]
  change (rootEquiv F v).symm (F.eval (torusDualRootRoute v) z) = z
  rw [← rootEquiv_apply]
  exact (rootEquiv F v).symm_apply_apply z

private theorem lift_face (F : FT R Y) (v : X)
    (hv : (v.1 + 1, v.2 + 1) ∈ R) :
    FreeGroup.lift (transportGenerators F) (torusDualFaceWord v) = 1 := by
  have h : FreeGroup.lift (transportGenerators F)
      (torusDualPathWord (torusDualEastNorth v.1 v.2)) =
      FreeGroup.lift (transportGenerators F)
        (torusDualPathWord (torusDualNorthEast v.1 v.2)) := by
    ext z
    rw [lift_word_apply, lift_word_apply]
    congr 1
    exact (TorusDualHomotopy.square v.1 v.2 hv).flatTransport_eval_eq F _
  simp only [torusDualFaceWord, map_mul, map_inv, h, mul_inv_cancel]

private theorem lift_relators (S : Finset X) (F : FT (S : Set X) Y) :
    ∀ r ∈ (torusDualPresentationRelators S : Set (FreeGroup (X ⊕ X))),
      FreeGroup.lift (transportGenerators F) r = 1 := by
  classical
  intro r hr
  change r ∈ torusDualPresentationRelators S at hr
  unfold torusDualPresentationRelators at hr
  rcases Finset.mem_union.mp hr with hr | hr
  · obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hr
    exact lift_root_route F v
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hr
    exact lift_face F v (Finset.mem_filter.mp hv).2

/-- Exact classification of finite native parallel paths by one explicit
finite presentation. Its generators are the two native positive steps at
each vertex, and its relators are the allowed squares and fixed root routes.
This does not assert a terminating normal-form algorithm or a finite-group
test family. Source: restricted generated homotopies in SCP10, Lemma 6.14. -/
theorem torusDualHomotopy_iff_presentation_word_eq (S : Finset X) {a b : X}
    (p q : TorusDualPath a b) :
    TorusDualHomotopy (S : Set X) p q ↔
      PresentedGroup.mk (torusDualPresentationRelators S : Set (FreeGroup (X ⊕ X)))
          (torusDualPathWord p) =
        PresentedGroup.mk (torusDualPresentationRelators S : Set (FreeGroup (X ⊕ X)))
          (torusDualPathWord q) := by
  constructor
  · exact fun h => h.presentation_word_eq
  · intro h
    apply (torusDualHomotopy_iff_flatTransport p q).mpr
    intro Z F z
    let f := PresentedGroup.toGroup (lift_relators S F)
    have hf := congrArg f h
    change FreeGroup.lift (transportGenerators F) (torusDualPathWord p) =
      FreeGroup.lift (transportGenerators F) (torusDualPathWord q) at hf
    have hz := congrArg (fun e : Equiv.Perm (Z (0, 0)) => e ((rootEquiv F a).symm z)) hf
    rw [lift_word_apply, lift_word_apply] at hz
    simp only [Equiv.apply_symm_apply] at hz
    exact (rootEquiv F b).symm.injective hz

end TNLean.PEPS
