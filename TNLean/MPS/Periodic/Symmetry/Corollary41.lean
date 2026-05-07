/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Periodic.Symmetry.EqualCaseFTHyp

/-!
# Corollary 4.1 for periodic MPS

This module contains the physical-symmetry-to-virtual-`Z`-gauge statements from
Section 4.2 of arXiv:1708.00029.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-! ## Corollary 4.1 — Physical on-site symmetry → virtual `Z`-gauge -/

section Corollary41

variable {d D : ℕ} {G : Type*} [Group G]

/-- The symmetry-twisted tensor (with `U` acting on the physical leg) coincides with the
physical-index rotation by `U g`. -/
lemma twistedTensor_eq_rotatePhysical
    (A : MPSTensor d D) (U : G →* Matrix (Fin d) (Fin d) ℂ) (g : G) :
    twistedTensor A U g = rotatePhysical (U g) A := rfl

/-- **Corollary 4.1 (arXiv:1708.00029, Section 4.2): physical symmetry → virtual `Z`-gauge.**

Let `A` be in irreducible form II and let `U : G →* Mat_d ℂ` be a representation of a
group `G` on the physical leg, acting unitarily. If `A` is on-site symmetric under `U`
(i.e. each twisted tensor `twistedTensor A U g` has the same MPV family as `A`), then
for each `g ∈ G` there exists a positive period `m_g` and a `Z_{m_g}`-gauge equivalence
between `A` and `twistedTensor A U g`.

In paper notation, for each `g` there exist matrices `Z_g, Y_g` with `Z_g^{m_g} = 1`,
`[A^i, Z_g] = 0`, and
`Z_g · A^i = Y_g · (twistedTensor A U g)^i · Y_g⁻¹`.

This generalises the single-`u` corollary obtained via
`zGaugeEquiv_of_isIrreducibleForm_sameMPV_rotatePhysical` to a full group of symmetries.
The projective-representation upgrade (joint factor system on the family `(Y_g)_{g∈G}`)
is left to subsequent SPT classification work; see
`MPS/Symmetry/VirtualRepresentation.lean` for the analogous injective construction.

The periodic equal-case FT is taken as an explicit hypothesis `hPeriodicEq` (see file
header for the rationale and status). -/
theorem cor_4_1_physical_symmetry_zgauge
    (A : MPSTensor d D)
    (hA : IsIrreducibleForm A)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hUnit : ∀ g : G, (U g) * (U g)ᴴ = 1)
    (hSym : IsOnSiteSymmetric A U)
    (hPeriodicEq : PeriodicEqualCaseFT d D) :
    ∀ g : G, ∃ m : ℕ, 0 < m ∧ ZGaugeEquiv m A (twistedTensor A U g) := by
  intro g
  -- Twisting by `U g` is the same as the physical-index rotation by `U g`.
  have hRotEq : twistedTensor A U g = rotatePhysical (U g) A :=
    twistedTensor_eq_rotatePhysical A U g
  -- The rotated tensor is again in irreducible form II (preserved by unitary rotation).
  have hRot : IsIrreducibleForm (rotatePhysical (U g) A) :=
    isIrreducibleForm_rotatePhysical A (U g) (hUnit g) hA
  -- The on-site symmetry hypothesis gives `SameMPV A (rotatePhysical (U g) A)`.
  have hSame : SameMPV A (rotatePhysical (U g) A) := by
    have := hSym g
    rwa [hRotEq] at this
  -- Apply the periodic equal-case Fundamental Theorem.
  rcases hPeriodicEq hA hRot hSame with ⟨m, hm_pos, hZGauge⟩
  exact ⟨m, hm_pos, by rw [hRotEq]; exact hZGauge⟩

/-- **A convenient reformulation of `cor_4_1_physical_symmetry_zgauge`** in the form most
useful for subsequent SPT arguments: extract the gauge `Y(g)` and matrix `Z(g)`
explicitly. -/
theorem cor_4_1_physical_symmetry_zgauge_explicit
    (A : MPSTensor d D)
    (hA : IsIrreducibleForm A)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hUnit : ∀ g : G, (U g) * (U g)ᴴ = 1)
    (hSym : IsOnSiteSymmetric A U)
    (hPeriodicEq : PeriodicEqualCaseFT d D) :
    ∀ g : G, ∃ (m : ℕ) (Y : GL (Fin D) ℂ) (Z : Matrix (Fin D) (Fin D) ℂ),
      0 < m ∧
      Z ^ m = 1 ∧
      (∀ i : Fin d, Z * A i = A i * Z) ∧
      (∀ i : Fin d,
        Z * A i =
          (Y : Matrix (Fin D) (Fin D) ℂ) * twistedTensor A U g i *
            (((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))) := by
  intro g
  rcases cor_4_1_physical_symmetry_zgauge A hA U hUnit hSym hPeriodicEq g with
    ⟨m, hm_pos, Y, Z, hZpow, hComm, hRel⟩
  exact ⟨m, Y, Z, hm_pos, hZpow, hComm, hRel⟩

end Corollary41

end MPSTensor
