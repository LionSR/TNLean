/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.Associator
import TNLean.MPS.Symmetry.MPOSymmetry.Defs

/-!
# Group fusion algebras from exact group representations

A family of matrix product operator tensors indexed by a finite group whose periodic operators
multiply as the group, `O_g O_h = O_{gh}` at every positive length, is a fusion algebra with the
group fusion rule `N_{gh}^k = δ_{k, gh}`, and every label is invertible with inverse `g⁻¹`.
Only the operator law is used; normality of the tensors, the other clause of
`MPOTensor.GroupFamily.IsNormalRepresentation`, is not needed.

## Main statements

* `MPOTensor.GroupFamily.isMPOFusionAlgebra`: the group fusion rules from the operator law.
* `MPOTensor.GroupFamily.IsNormalRepresentation.isMPOFusionAlgebra`: the same for a normal
  representation.
* `MPOTensor.GroupFamily.isInvertibleLabel_groupFusion`: every label of the group fusion ring
  is invertible.

## References

* J. Garre-Rubio, L. Lootens, A. Molnár, *Classifying phases protected by matrix product
  operator symmetries using matrix product states*, arXiv:2203.12563, `REsubmission.tex`,
  line 660 (the fusion ring of a group, `O_g O_h = O_{gh}`).
-/

namespace MPOTensor.GroupFamily

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}

/-- **The group fusion rules.** A group family whose periodic operators satisfy
`O_g O_h = O_{gh}` at every positive length is a fusion algebra with structure constants
`N_{gh}^k = δ_{k, gh}`.

Source: arXiv:2203.12563, line 660 (the fusion ring of a group). -/
theorem isMPOFusionAlgebra (F : GroupFamily G d)
    (hmul : ∀ g h N, 0 < N →
      mpo (F.tensor g) N * mpo (F.tensor h) N = mpo (F.tensor (g * h)) N) :
    IsMPOFusionAlgebra F.tensor fun a b c ↦ if c = a * b then 1 else 0 := by
  intro a b L hL
  rw [hmul a b L hL]
  simp [ite_smul]

/-- A normal representation of a finite group satisfies the group fusion rules.

Source: arXiv:2203.12563, line 660. -/
theorem IsNormalRepresentation.isMPOFusionAlgebra {F : GroupFamily G d}
    (hF : F.IsNormalRepresentation) :
    IsMPOFusionAlgebra F.tensor fun a b c ↦ if c = a * b then 1 else 0 :=
  F.isMPOFusionAlgebra hF.operator_mul

omit [Fintype G] in
/-- Every label of the group fusion ring is invertible, with inverse `a⁻¹` and unit `1`.

Source: arXiv:2203.12563, line 660. -/
theorem isInvertibleLabel_groupFusion (a : G) :
    IsInvertibleLabel (fun a b c : G ↦ if c = a * b then 1 else 0) 1 a :=
  ⟨a⁻¹, fun c ↦ by simp⟩

end MPOTensor.GroupFamily
