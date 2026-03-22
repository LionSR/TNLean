import TNLean.MPS.FundamentalTheorem.Basic

/-!
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Applications of the (single-block) Fundamental Theorem

This module packages a lightweight symmetry corollary used by the periodic FT
pipeline: rotating physical indices by a unitary matrix defines a new tensor,
and any MPV-level symmetry hypothesis can be converted into a virtual gauge
statement by `fundamentalTheorem_singleBlock`.

This is the project-level Lean wrapper for the easy part of the arXiv:1708.00029
§4 application pattern (`Bⁱ := ∑ⱼ uᵢⱼ Aʲ`, then apply FT to `A` and `B`).
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- Physical-index rotation of a tensor by a matrix `u` on the physical leg:

`(rotatePhysical u A) i = ∑ j, u i j • A j`.
-/
def rotatePhysical (u : Matrix (Fin d) (Fin d) ℂ) (A : MPSTensor d D) : MPSTensor d D :=
  fun i => ∑ j : Fin d, u i j • A j

@[simp] lemma rotatePhysical_apply
    (u : Matrix (Fin d) (Fin d) ℂ) (A : MPSTensor d D) (i : Fin d) :
    rotatePhysical u A i = ∑ j : Fin d, u i j • A j := rfl

/-- Symmetry-to-virtual-gauge wrapper.

If `A` is injective and has the same MPV family as its physical-leg rotation
`B = rotatePhysical u A`, then `B` is gauge equivalent to `A`.

This is the formal Lean bridge used in Corollary-4.1 style arguments: the
nontrivial analytic/group-theoretic part is in the hypothesis
`SameMPV A (rotatePhysical u A)`, and the conclusion is provided by the
single-block Fundamental Theorem. -/
theorem gaugeEquiv_of_sameMPV_rotatePhysical
    (u : Matrix (Fin d) (Fin d) ℂ)
    (A : MPSTensor d D)
    (hA : IsInjective A)
    (hSym : SameMPV A (rotatePhysical u A)) :
    GaugeEquiv A (rotatePhysical u A) :=
  fundamentalTheorem_singleBlock hA hSym

end MPSTensor
