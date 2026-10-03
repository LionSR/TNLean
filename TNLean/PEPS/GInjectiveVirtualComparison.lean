/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GInjectiveRangeEquivalence
import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Comparing invariant virtual spaces with the same physical range

Suppose two group-injective tensor maps have the same physical range.
Their invariant virtual spaces are then uniquely identified by equality
of the physical image. The two virtual representations may act on
different vector spaces and may belong to different finite groups.

This is a local linear-algebra consequence of Schuch, Cirac, and
Pérez-García, arXiv:1001.3807, Definition 5.1,
`Papers/1001.3807/paper_v3.tex`, lines 1278–1296. It identifies the
invariant virtual spaces; it does not assert a decomposition into
individual bond maps or an isomorphism between the groups.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

namespace TNLean.PEPS

variable {G H W Z P : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
variable [AddCommGroup W] [Module ℂ W] [AddCommGroup Z] [Module ℂ Z]
variable [AddCommGroup P] [Module ℂ P]
variable {ρ : Representation ℂ G W} {σ : Representation ℂ H Z}
variable {T : W →ₗ[ℂ] P} {S : Z →ₗ[ℂ] P}

/-- Equal physical ranges induce a comparison of the invariant virtual spaces.
Source: local consequence of SCP10, Definition 5.1, lines 1278–1296. -/
noncomputable def IsGInjective.virtualEquiv (hT : IsGInjective ρ T)
    (hS : IsGInjective σ S) (hRange : T.range = S.range) :
    ρ.invariants ≃ₗ[ℂ] σ.invariants :=
  hT.invariantsRangeEquiv.trans
    ((LinearEquiv.ofEq T.range S.range hRange).trans hS.invariantsRangeEquiv.symm)

/-- Corresponding invariant virtual vectors have the same physical image.
Source: local consequence of SCP10, Definition 5.1, lines 1278–1296. -/
@[simp]
theorem IsGInjective.virtualEquiv_apply (hT : IsGInjective ρ T)
    (hS : IsGInjective σ S) (hRange : T.range = S.range) (x : ρ.invariants) :
    S (hT.virtualEquiv hS hRange x) = T x := by
  have h := congrArg Subtype.val (hS.invariantsRangeEquiv.apply_symm_apply
    (LinearEquiv.ofEq T.range S.range hRange (hT.invariantsRangeEquiv x)))
  simpa only [virtualEquiv, LinearEquiv.trans_apply, invariantsRangeEquiv_apply,
    LinearEquiv.coe_ofEq_apply] using h

/-- The comparison is the unique linear map preserving every physical image.
Source: local consequence of SCP10, Definition 5.1, lines 1278–1296. -/
theorem IsGInjective.virtualEquiv_unique (hT : IsGInjective ρ T)
    (hS : IsGInjective σ S) (hRange : T.range = S.range)
    (F : ρ.invariants →ₗ[ℂ] σ.invariants)
    (hF : ∀ x, S (F x) = T x) : F = (hT.virtualEquiv hS hRange).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply hS.invariantsRangeEquiv.injective
  apply Subtype.ext
  change S (F x) = S (hT.virtualEquiv hS hRange x)
  exact (hF x).trans (hT.virtualEquiv_apply hS hRange x).symm

/-- Reversing the physical comparison gives the inverse virtual equivalence.
Source: local consequence of SCP10, Definition 5.1, lines 1278–1296. -/
@[simp]
theorem IsGInjective.virtualEquiv_symm (hT : IsGInjective ρ T)
    (hS : IsGInjective σ S) (hRange : T.range = S.range) :
    (hT.virtualEquiv hS hRange).symm = hS.virtualEquiv hT hRange.symm := by
  apply LinearEquiv.toLinearMap_injective
  apply hS.virtualEquiv_unique hT hRange.symm
  intro x
  change T ((hT.virtualEquiv hS hRange).symm x) = S x
  simpa only [LinearEquiv.apply_symm_apply] using
    (hT.virtualEquiv_apply hS hRange ((hT.virtualEquiv hS hRange).symm x)).symm

omit [Fintype G] [Fintype H] in
/-- There is exactly one virtual linear equivalence preserving the physical image.
Source: local consequence of SCP10, Definition 5.1, lines 1278–1296. -/
theorem IsGInjective.existsUnique_virtualEquiv (hT : IsGInjective ρ T)
    (hS : IsGInjective σ S) (hRange : T.range = S.range) [Finite G] [Finite H] :
    ∃! F : ρ.invariants ≃ₗ[ℂ] σ.invariants, ∀ x, S (F x) = T x := by
  let := Fintype.ofFinite G
  let := Fintype.ofFinite H
  refine ⟨hT.virtualEquiv hS hRange, hT.virtualEquiv_apply hS hRange, fun F hF => ?_⟩
  apply LinearEquiv.toLinearMap_injective
  exact hT.virtualEquiv_unique hS hRange F.toLinearMap hF

omit [Fintype G] [Fintype H] in
/-- Equal physical ranges imply equal dimensions of the invariant virtual spaces.
Source: local consequence of SCP10, Definition 5.1, lines 1278–1296. -/
theorem IsGInjective.finrank_invariants_eq_of_range_eq (hT : IsGInjective ρ T)
    (hS : IsGInjective σ S) (hRange : T.range = S.range) [Finite G] [Finite H] :
    Module.finrank ℂ ρ.invariants = Module.finrank ℂ σ.invariants := by
  let := Fintype.ofFinite G
  let := Fintype.ofFinite H
  exact (hT.virtualEquiv hS hRange).finrank_eq

end TNLean.PEPS
