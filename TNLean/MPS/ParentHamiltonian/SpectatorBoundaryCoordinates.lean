/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.SpectatorBoundaryGram

/-!
# Three-interval coordinates for boundary maps

The left and right boundary maps for overlapping intervals are evaluated in
one physical configuration space. These coordinates are used in FNW Lemma 6.2
and Nachtergaele, arXiv:cond-mat/9410110, Lemma `commutation`.
-/

namespace MPSTensor
variable {d D : ℕ}

/-- Fixing the prefix of the reassociated tail boundary map leaves the
ordinary boundary vector on the middle and right intervals. -/
theorem reassocTailBoundaryMapES_apply_threeBlock
    (A : MPSTensor d D) (r m ℓ : ℕ)
    (y : BoundaryFamilySpace (D := D) (Cfg d r))
    (μr : Cfg d r) (μm : Cfg d m) (μℓ : Cfg d ℓ) :
    reassocTailBoundaryMapES A r m ℓ y
        (Fin.append (Fin.append μr μm) μℓ) =
      groundSpaceMap A (m + ℓ)
        (boundaryFamilyEquiv (D := D) (Cfg d r) y μr)
        (Fin.append μm μℓ) := by
  change tailBoundaryMapES A r (m + ℓ) y
      (((finCongr (Nat.add_assoc r m ℓ)).arrowCongr
        (Equiv.refl (Fin d))) (Fin.append (Fin.append μr μm) μℓ)) = _
  have hcfg :
      ((finCongr (Nat.add_assoc r m ℓ)).arrowCongr
        (Equiv.refl (Fin d))) (Fin.append (Fin.append μr μm) μℓ) =
        Fin.append μr (Fin.append μm μℓ) := by
    rw [Fin.append_assoc]
    rfl
  rw [hcfg]
  change tailBoundaryMap A r (m + ℓ)
      (boundaryFamilyEquiv (D := D) (Cfg d r) y)
      (Fin.append μr (Fin.append μm μℓ)) = _
  exact tailBoundaryMap_append A r (m + ℓ)
    (boundaryFamilyEquiv (D := D) (Cfg d r) y) μr (Fin.append μm μℓ)

end MPSTensor
