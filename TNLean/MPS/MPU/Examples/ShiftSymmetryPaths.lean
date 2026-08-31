/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Permutation
import TNLean.MPS.MPDO.AreaLaw

/-!
# The finite three-swap endpoint for the counter-shift MPU

The proof of arXiv:1703.09188, Proposition `prop:U1-U2-equiv-ancillatrick`
(lines 2217--2229), conjugates the swap endpoint by three layers of swaps after
adjoining one identity ancilla of dimension $d$. This module records only the
resulting finite permutation identity. It does not construct a path or an
action on the full enlarged operator algebra.
-/

namespace MPOTensor

/-- Configurations of two physical species and one $d$-dimensional identity
ancilla on a periodic chain of length $N$. -/
abbrev ShiftAncillaConfig (N d : ℕ) :=
  ((Fin N → Fin d) × (Fin N → Fin d)) × (Fin N → Fin d)

/-- The sitewise swap of the first and second physical species. -/
def shiftAncillaSwap₁₂ (N d : ℕ) : Equiv.Perm (ShiftAncillaConfig N d) where
  toFun σ := ((σ.1.2, σ.1.1), σ.2)
  invFun σ := ((σ.1.2, σ.1.1), σ.2)
  left_inv := by rintro ⟨⟨σ₁, σ₂⟩, a⟩; rfl
  right_inv := by rintro ⟨⟨σ₁, σ₂⟩, a⟩; rfl

/-- The sitewise swap of the second physical species with the ancilla. -/
def shiftAncillaSwap₂a (N d : ℕ) : Equiv.Perm (ShiftAncillaConfig N d) where
  toFun σ := ((σ.1.1, σ.2), σ.1.2)
  invFun σ := ((σ.1.1, σ.2), σ.1.2)
  left_inv := by rintro ⟨⟨σ₁, σ₂⟩, a⟩; rfl
  right_inv := by rintro ⟨⟨σ₁, σ₂⟩, a⟩; rfl

/-- The crossed swap of species $1$ with the neighboring ancilla in Figure
`fig:TR-ancilla`. The ancilla entering the first output is shifted by
`rotateConfig` inverse, while the first species entering the ancilla output is
shifted by `rotateConfig`. -/
def shiftAncillaSwap₁aNext (N d : ℕ) : Equiv.Perm (ShiftAncillaConfig N d) where
  toFun σ :=
    (((rotateConfig N d).symm σ.2, σ.1.2), (rotateConfig N d) σ.1.1)
  invFun σ :=
    (((rotateConfig N d).symm σ.2, σ.1.2), (rotateConfig N d) σ.1.1)
  left_inv := by
    rintro ⟨⟨σ₁, σ₂⟩, a⟩
    change
      ((((rotateConfig N d).symm ((rotateConfig N d) σ₁), σ₂),
        (rotateConfig N d) ((rotateConfig N d).symm a))) = ((σ₁, σ₂), a)
    simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨⟨σ₁, σ₂⟩, a⟩
    change
      ((((rotateConfig N d).symm ((rotateConfig N d) σ₁), σ₂),
        (rotateConfig N d) ((rotateConfig N d).symm a))) = ((σ₁, σ₂), a)
    simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply]

/-- The three swap layers shown below the $\tilde U_1$ endpoint in Figure
`fig:TR-ancilla`: first $S^{2,a}_{n,n}$, then $S^{1,2}_{n,n}$, and finally
$S^{1,a}_{n,n+1}$. -/
def shiftAncillaThreeSwap (N d : ℕ) : Equiv.Perm (ShiftAncillaConfig N d) :=
  ((shiftAncillaSwap₂a N d).trans (shiftAncillaSwap₁₂ N d)).trans
    (shiftAncillaSwap₁aNext N d)

/-- The ancilla-enlarged endpoint $\tilde U_2$: the two physical species shift
in opposite directions and the identity ancilla is fixed. -/
def shiftAncillaCounterShift (N d : ℕ) : Equiv.Perm (ShiftAncillaConfig N d) where
  toFun σ :=
    ((((rotateConfig N d).symm σ.1.2), (rotateConfig N d) σ.1.1), σ.2)
  invFun σ :=
    ((((rotateConfig N d).symm σ.1.2), (rotateConfig N d) σ.1.1), σ.2)
  left_inv := by
    rintro ⟨⟨σ₁, σ₂⟩, a⟩
    change
      ((((rotateConfig N d).symm ((rotateConfig N d) σ₁),
        (rotateConfig N d) ((rotateConfig N d).symm σ₂)), a)) = ((σ₁, σ₂), a)
    simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨⟨σ₁, σ₂⟩, a⟩
    change
      ((((rotateConfig N d).symm ((rotateConfig N d) σ₁),
        (rotateConfig N d) ((rotateConfig N d).symm σ₂)), a)) = ((σ₁, σ₂), a)
    simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply]

/-- Exact coordinate identity behind the three-swap ancilla construction.
Conjugating the sitewise physical swap by the three displayed swap layers sends
$((σ_1,σ_2),a)$ to $((R^{-1}σ_2,Rσ_1),a)$, where $R$ is the cyclic rotation.

Source: arXiv:1703.09188, Proposition `prop:U1-U2-equiv-ancillatrick` and Figure
`fig:TR-ancilla` (lines 2217--2229). -/
@[simp] theorem shiftAncillaThreeSwap_conj_swap₁₂_apply (N d : ℕ)
    (σ₁ σ₂ a : Fin N → Fin d) :
    (((shiftAncillaThreeSwap N d).trans (shiftAncillaSwap₁₂ N d)).trans
        (shiftAncillaThreeSwap N d).symm) ((σ₁, σ₂), a) =
      ((((rotateConfig N d).symm σ₂), (rotateConfig N d) σ₁), a) := by
  have rotate_symm_comp (σ : Fin N → Fin d) :
      (rotateConfig N d).symm (σ ∘ finRotate N) = σ := by
    change (rotateConfig N d).symm ((rotateConfig N d) σ) = σ
    exact (rotateConfig N d).symm_apply_apply σ
  simp [shiftAncillaThreeSwap, shiftAncillaSwap₂a, shiftAncillaSwap₁₂,
    shiftAncillaSwap₁aNext, rotate_symm_comp]

/-- The three-swap conjugation is exactly the ancilla-enlarged counter-shift
permutation. This is the finite endpoint equality from Figure
`fig:TR-ancilla`, without path or symmetry-action packaging.

Source: arXiv:1703.09188, Proposition `prop:U1-U2-equiv-ancillatrick` and Figure
`fig:TR-ancilla` (lines 2217--2229). -/
theorem shiftAncillaThreeSwap_conj_swap₁₂ (N d : ℕ) :
    ((shiftAncillaThreeSwap N d).trans (shiftAncillaSwap₁₂ N d)).trans
        (shiftAncillaThreeSwap N d).symm =
      shiftAncillaCounterShift N d := by
  apply Equiv.ext
  rintro ⟨⟨σ₁, σ₂⟩, a⟩
  exact shiftAncillaThreeSwap_conj_swap₁₂_apply N d σ₁ σ₂ a

/-- Permutation-matrix form of the exact finite three-swap endpoint identity. -/
theorem permMatrix_shiftAncillaThreeSwap_endpoint (N d : ℕ) :
    Equiv.Perm.permMatrix ℂ
        (((shiftAncillaThreeSwap N d).trans (shiftAncillaSwap₁₂ N d)).trans
          (shiftAncillaThreeSwap N d).symm) =
      Equiv.Perm.permMatrix ℂ (shiftAncillaCounterShift N d) := by
  rw [shiftAncillaThreeSwap_conj_swap₁₂]

/-- Matrix-conjugation form of the finite endpoint identity.

Source: arXiv:1703.09188, Proposition `prop:U1-U2-equiv-ancillatrick` and Figure
`fig:TR-ancilla` (lines 2217--2229). -/
theorem permMatrix_shiftAncillaThreeSwap_conj_swap₁₂ (N d : ℕ) :
    Equiv.Perm.permMatrix ℂ (shiftAncillaThreeSwap N d) *
          Equiv.Perm.permMatrix ℂ (shiftAncillaSwap₁₂ N d) *
        Equiv.Perm.permMatrix ℂ (shiftAncillaThreeSwap N d).symm =
      Equiv.Perm.permMatrix ℂ (shiftAncillaCounterShift N d) := by
  rw [← Matrix.permMatrix_mul, ← Matrix.permMatrix_mul]
  change
    Equiv.Perm.permMatrix ℂ
        (((shiftAncillaThreeSwap N d).trans (shiftAncillaSwap₁₂ N d)).trans
          (shiftAncillaThreeSwap N d).symm) =
      Equiv.Perm.permMatrix ℂ (shiftAncillaCounterShift N d)
  exact permMatrix_shiftAncillaThreeSwap_endpoint N d

end MPOTensor
