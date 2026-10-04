/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.ScaledNormality
import TNLean.MPS.Symmetry.Defs

/-!
# On-site symmetry with a character

An on-site symmetry can multiply each tensor letter by the value of a character.
The periodic vector on a chain of length \(N\) then acquires the \(N\)-th power of that value.
The virtual gauge remains a conjugation on the bond space.

Source: Cirac--Pérez-García--Schuch--Verstraete, arXiv:2011.12127, §III.A,
`Papers/2011.12127/TN-Review-main.tex` lines 1147–1157.
-/

namespace MPSTensor

variable {G : Type*} [Monoid G] {d D : ℕ}

/-- On-site symmetry with character \(\varphi\): the tensor twisted by \(g\) is gauge
equivalent to \(\varphi(g) A\). Source: arXiv:2011.12127, §III.A, lines 1147–1157. -/
def IsOnSiteSymmetricUpToCharacter (A : MPSTensor d D)
    (U : G →* Matrix (Fin d) (Fin d) ℂ) (φ : G →* ℂ) : Prop :=
  ∀ g, GaugeEquiv (φ g • A) (twistedTensor A U g)

/-- The periodic coefficient on \(N\) sites acquires the character factor
\(\varphi(g)^N\), including at \(N=0\). Source: arXiv:2011.12127, §III.A, lines 1147–1157. -/
theorem IsOnSiteSymmetricUpToCharacter.mpv_twistedTensor
    {A : MPSTensor d D} {U : G →* Matrix (Fin d) (Fin d) ℂ} {φ : G →* ℂ}
    (h : IsOnSiteSymmetricUpToCharacter A U φ) (g : G) {N : ℕ}
    (s : Fin N → Fin d) :
    mpv (twistedTensor A U g) s = φ g ^ N * mpv A s := by
  rw [← (h g).sameMPV N s]
  exact mpv_smul (φ g) A s

end MPSTensor
