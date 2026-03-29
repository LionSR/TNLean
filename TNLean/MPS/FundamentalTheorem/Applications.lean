import TNLean.MPS.FundamentalTheorem.Basic
import TNLean.MPS.Periodic.Defs

/-!
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Applications of the fundamental theorem

This module currently contains two layers:

1. A lightweight **single-block** symmetry wrapper (`rotatePhysical` +
   `gaugeEquiv_of_sameMPV_rotatePhysical`).
2. A **periodic-form assembly lemma** (`zGaugeEquiv_of_isIrreducibleForm_sameMPV_rotatePhysical`) that isolates the
   only missing input for the full Corollary 4.1 of arXiv:1708.00029 §4:
   the equal-case periodic FT theorem (`SameMPV` in irreducible form II ⇒ `ZGaugeEquiv`).

## Status for §4 (as of merged periodic FT infrastructure)

* Corollary 4.1 (symmetry corollary): reduced to one call to the periodic equal-case FT,
  once `rotatePhysical`-preservation of irreducible form II is available.
* Theorem 4.1 (`p`-refinement ↔ `p`-divisibility): still needs the periodic-block
  phase-distribution construction from §4, which depends on cyclic-sector arithmetic
  infrastructure used together with the periodic equal-case FT.
-/

open scoped Matrix BigOperators

namespace MPSTensor

noncomputable section

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

/-- Corollary 4.1 assembly step (periodic form).

Assume the periodic equal-case FT as a hypothesis (`hPeriodicEq`): whenever two tensors are
in irreducible form II and generate the same MPV family, they are `ℤ_m`-gauge equivalent for
some period `m > 0`. Then the symmetry corollary follows immediately for
`B := rotatePhysical u A` once `B` is known to be in irreducible form II.

This theorem intentionally packages the current dependency boundary: no additional overlap
arguments are needed *here* beyond the periodic equal-case FT input. -/
theorem zGaugeEquiv_of_isIrreducibleForm_sameMPV_rotatePhysical
    (u : Matrix (Fin d) (Fin d) ℂ)
    (A : MPSTensor d D)
    (hA : IsIrreducibleForm A)
    (hRot : IsIrreducibleForm (rotatePhysical u A))
    (hSym : SameMPV A (rotatePhysical u A))
    (hPeriodicEq :
      ∀ {X Y : MPSTensor d D},
        IsIrreducibleForm X →
        IsIrreducibleForm Y →
        SameMPV X Y →
        ∃ m : ℕ, 0 < m ∧ ZGaugeEquiv m X Y) :
    ∃ m : ℕ, 0 < m ∧ ZGaugeEquiv m A (rotatePhysical u A) :=
  hPeriodicEq hA hRot hSym

end

end MPSTensor
