/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ComplexOfRing
import TNLean.MPS.Symmetry.MPOSymmetry.AnomalyObstruction

/-!
# Computing action L-symbols from local identities

A local identity between the two action trees determines the selected L-symbol when the
target state is normal and has positive bond dimension. The required nonvanishing follows
from the actual action reduction. Ring-valued local identities can be transported into
the complex matrices before applying uniqueness.
-/

open MPSTensor

namespace MPOTensor.GroupFamily.ActionData

variable {G : Type} [Group G] {d D : ℕ} {F : GroupFamily G d} {A : MPSTensor d D}

/-- A dressed scalar between the two action trees equals the selected L-symbol. -/
theorem eq_lSymbol_of_isDressedProportional (fd : FusionData F) (ad : ActionData F A)
    (hA : Kraus.IsNormal A) (hD : 0 < D) (hinv : ∀ g, FixesMPV (F.tensor g) A)
    (g h : G) {z : ℂ}
    (hz : IsDressedProportional (actTensor (mulTensor (F.tensor g) (F.tensor h)) A)
      (ad.actV g h) (ad.fuseV fd g h) z) :
    z = ad.lSymbol fd () g h := by
  obtain ⟨W, hW⟩ := ad.exists_isReduction_actV g h
  exact hz.eq_of_forall_exists_ne_zero
    (ad.isDressedProportional_lSymbol hA hinv () g h)
    (hW.exists_mul_evalWord_ne_zero hA hD)

end MPOTensor.GroupFamily.ActionData

namespace MPSTensor

variable {R : Type*} [CommRing R] {d D E : ℕ}

/-- Equality of the dressed boundaries on each letter gives equality on every nonempty
word, by multiplication with its remaining letters. -/
theorem IsDressedProportional.of_forall_mul {B : MPSTensor d E}
    {L R' : Matrix (Fin D) (Fin E) ℂ} {z : ℂ}
    (h1 : ∀ i, L * B i = z • (R' * B i)) : IsDressedProportional B L R' z := by
  refine ⟨1, ?_⟩
  intro w hw
  cases w with
  | nil => simp at hw
  | cons i w =>
    simp only [Kraus.evalWord_cons, ← Matrix.mul_assoc, h1, Matrix.smul_mul]

/-- A one-letter matrix identity over a coefficient ring determines dressed
proportionality after mapping into the complex numbers. -/
theorem isDressedProportional_complexOfRing_of_forall_mul (f : R →+* ℂ)
    (B : Fin d → Matrix (Fin E) (Fin E) R)
    (L R' : Matrix (Fin D) (Fin E) R) (z : R)
    (h1 : ∀ i, L * B i = z • (R' * B i)) :
    IsDressedProportional (fun i ↦ complexOfRing f (B i))
      (complexOfRing f L) (complexOfRing f R') (f z) := by
  apply IsDressedProportional.of_forall_mul
  intro i
  rw [← complexOfRing_mul, ← complexOfRing_mul, h1, complexOfRing_smul]

end MPSTensor
