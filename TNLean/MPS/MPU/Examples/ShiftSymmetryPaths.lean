/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Permutation
import TNLean.MPS.MPDO.AreaLaw

/-!
# The finite endpoint of the literal three-swap circuit

The proof of arXiv:1703.09188, Proposition `prop:U1-U2-equiv-ancillatrick`
(lines 2217--2229), conjugates the swap endpoint by three layers of swaps after
adjoining one identity ancilla of dimension $d$. The literal labels in Figure
`fig:TR-ancilla` produce the coordinate map
$((σ_1,σ_2),a)\mapsto((Rσ_2,R^{-1}σ_1),a)$.

**Local fix.** The relation between this map and the paper's named MPU endpoints,
together with the reversed crossed swap, is recorded in
`docs/paper-gaps/mpu_ancilla_three_swap_orientation.tex`. This module proves only
the finite permutation identity. It does not identify the permutation matrix
with an ancilla-enlarged MPO, construct a path, or define an action on the full
enlarged operator algebra.
-/

namespace MPOTensor

/-- Configurations of two physical species and one $d$-dimensional identity
ancilla on a periodic chain of length $N$. -/
abbrev ShiftAncillaConfig (N d : ℕ) :=
  ((Fin N → Fin d) × (Fin N → Fin d)) × (Fin N → Fin d)

/-- The sitewise swap of the first and second physical species.

Source: arXiv:1703.09188, Figure `fig:TR-ancilla` and Proposition
`prop:U1-U2-equiv-ancillatrick` (lines 2217--2229). -/
def shiftAncillaSwap₁₂ (N d : ℕ) : Equiv.Perm (ShiftAncillaConfig N d) :=
  Function.Involutive.toPerm (fun σ => ((σ.1.2, σ.1.1), σ.2)) (by
    rintro ⟨⟨σ₁, σ₂⟩, a⟩
    rfl)

/-- The sitewise swap of the second physical species with the ancilla.

Source: arXiv:1703.09188, Figure `fig:TR-ancilla` and Proposition
`prop:U1-U2-equiv-ancillatrick` (lines 2217--2229). -/
def shiftAncillaSwap₂a (N d : ℕ) : Equiv.Perm (ShiftAncillaConfig N d) :=
  Function.Involutive.toPerm (fun σ => ((σ.1.1, σ.2), σ.1.2)) (by
    rintro ⟨⟨σ₁, σ₂⟩, a⟩
    rfl)

/-- The crossed swap $S^{1,a}_{n,n+1}$ in Figure `fig:TR-ancilla`.
Since `rotateConfig N d σ` evaluates to `σ` at the next site, the first output
receives the next-site ancilla and the ancilla output receives the previous-site
first species.

Source: arXiv:1703.09188, Figure `fig:TR-ancilla` and Proposition
`prop:U1-U2-equiv-ancillatrick` (lines 2217--2229). -/
def shiftAncillaSwap₁aNext (N d : ℕ) : Equiv.Perm (ShiftAncillaConfig N d) :=
  Function.Involutive.toPerm
    (fun σ =>
      (((rotateConfig N d) σ.2, σ.1.2), (rotateConfig N d).symm σ.1.1))
    (by
      rintro ⟨⟨σ₁, σ₂⟩, a⟩
      change
        ((((rotateConfig N d) ((rotateConfig N d).symm σ₁), σ₂),
          (rotateConfig N d).symm ((rotateConfig N d) a))) = ((σ₁, σ₂), a)
      simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply])

/-- Coordinate action of the source gate $S^{1,a}_{n,n+1}$ in Figure
`fig:TR-ancilla`.

Source: arXiv:1703.09188, Figure `fig:TR-ancilla` and Proposition
`prop:U1-U2-equiv-ancillatrick` (lines 2217--2229). -/
@[simp] theorem shiftAncillaSwap₁aNext_apply (N d : ℕ)
    (σ₁ σ₂ a : Fin N → Fin d) :
    shiftAncillaSwap₁aNext N d ((σ₁, σ₂), a) =
      (((rotateConfig N d) a, σ₂), (rotateConfig N d).symm σ₁) := by
  rfl

/-- The three swap layers shown above the $\tilde U_1$ endpoint in Figure
`fig:TR-ancilla`, read from the endpoint outwards: first $S^{1,a}_{n,n+1}$,
then $S^{1,2}_{n,n}$, and finally $S^{2,a}_{n,n}$.

Source: arXiv:1703.09188, Figure `fig:TR-ancilla` and Proposition
`prop:U1-U2-equiv-ancillatrick` (lines 2217--2229). -/
def shiftAncillaThreeSwap (N d : ℕ) : Equiv.Perm (ShiftAncillaConfig N d) :=
  ((shiftAncillaSwap₁aNext N d).trans (shiftAncillaSwap₁₂ N d)).trans
    (shiftAncillaSwap₂a N d)

/-- The counter-shift permutation produced by the literal figure labels: the
two physical species shift in opposite directions and the ancilla is fixed.

Source: arXiv:1703.09188, Figure `fig:TR-ancilla` and Proposition
`prop:U1-U2-equiv-ancillatrick` (lines 2217--2229). -/
def shiftAncillaCounterShift (N d : ℕ) : Equiv.Perm (ShiftAncillaConfig N d) :=
  Function.Involutive.toPerm
    (fun σ =>
      ((((rotateConfig N d) σ.1.2), (rotateConfig N d).symm σ.1.1), σ.2))
    (by
      rintro ⟨⟨σ₁, σ₂⟩, a⟩
      change
        ((((rotateConfig N d) ((rotateConfig N d).symm σ₁),
          (rotateConfig N d).symm ((rotateConfig N d) σ₂)), a)) = ((σ₁, σ₂), a)
      simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply])

/-- Exact coordinate identity for the three literal swap labels in Figure
`fig:TR-ancilla`. Conjugating the sitewise physical swap sends
$((σ_1,σ_2),a)$ to $((Rσ_2,R^{-1}σ_1),a)$, where $R$ is the cyclic rotation.
The relation between this coordinate permutation and the named MPU endpoints
requires a separate reindexing theorem and is not asserted here.

Source: arXiv:1703.09188, Proposition `prop:U1-U2-equiv-ancillatrick` and Figure
`fig:TR-ancilla` (lines 2217--2229). -/
@[simp] theorem shiftAncillaThreeSwap_conj_swap₁₂_apply (N d : ℕ)
    (σ₁ σ₂ a : Fin N → Fin d) :
    (((shiftAncillaThreeSwap N d).trans (shiftAncillaSwap₁₂ N d)).trans
        (shiftAncillaThreeSwap N d).symm) ((σ₁, σ₂), a) =
      ((((rotateConfig N d) σ₂), (rotateConfig N d).symm σ₁), a) := by
  have rotate_symm_comp (σ : Fin N → Fin d) :
      (rotateConfig N d).symm (σ ∘ finRotate N) = σ := by
    change (rotateConfig N d).symm ((rotateConfig N d) σ) = σ
    exact (rotateConfig N d).symm_apply_apply σ
  simp [shiftAncillaThreeSwap, shiftAncillaSwap₂a, shiftAncillaSwap₁₂,
    shiftAncillaSwap₁aNext, Function.Involutive.toPerm, rotate_symm_comp]

/-- The three-swap conjugation is exactly the counter-shift permutation
produced by the literal labels in Figure `fig:TR-ancilla`, without MPU,
path, or symmetry-action packaging.

Source: arXiv:1703.09188, Proposition `prop:U1-U2-equiv-ancillatrick` and Figure
`fig:TR-ancilla` (lines 2217--2229). -/
theorem shiftAncillaThreeSwap_conj_swap₁₂ (N d : ℕ) :
    ((shiftAncillaThreeSwap N d).trans (shiftAncillaSwap₁₂ N d)).trans
        (shiftAncillaThreeSwap N d).symm =
      shiftAncillaCounterShift N d := by
  apply Equiv.ext
  rintro ⟨⟨σ₁, σ₂⟩, a⟩
  exact shiftAncillaThreeSwap_conj_swap₁₂_apply N d σ₁ σ₂ a

/-- Permutation-matrix form of the exact finite three-swap endpoint identity.

Source: arXiv:1703.09188, Figure `fig:TR-ancilla` and Proposition
`prop:U1-U2-equiv-ancillatrick` (lines 2217--2229). -/
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
