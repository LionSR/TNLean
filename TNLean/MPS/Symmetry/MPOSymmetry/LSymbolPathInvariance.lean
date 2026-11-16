/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.FiniteCocyclePath
import TNLean.MPS.Symmetry.MPOSymmetry.LSymbolContinuity

/-!
# Relative action classes along continuous reduction paths

Two invariant normal states of the same normal group MPO family have a relative scalar
two-cocycle: their common associator cancels. For finite groups, continuous tensor paths
with continuous left action caps have constant relative class. The right caps need not
be continuous. No continuous virtual projective representation is assumed.

**Scope restriction (continuous action caps):** This proves the scalar class step of
arXiv:2203.12563, Section 4, for fixed state bond dimensions and continuous actual left
action reductions. It does not construct those reductions from an independent physical
Hamiltonian path or handle changing minimal dimensions. The physical theorem remains open;
see `docs/paper-gaps/fbc25_controlled_z_split_index_class_scope.tex`.
-/

open scoped TNLean.Algebra.ScalarCohomology
open TNLean.Algebra

namespace MPOTensor.GroupFamily.ActionData

variable {G : Type} [Group G] {d D E : ℕ} {F : GroupFamily G d}

/-- The common associator cancels between the actual L-symbols of two invariant states,
so their ratio satisfies Mathlib's scalar two-cocycle condition. This requires neither
a trivial anomaly representative nor a normalized choice of reductions. -/
theorem relative_lSymbol_isMulCocycle₂
    (hF : F.IsNormalRepresentation) {A : MPSTensor d D} {B : MPSTensor d E}
    (hA : Kraus.IsNormal A) (hB : Kraus.IsNormal B) (hD : 0 < D) (hE : 0 < E)
    (hinvA : ∀ g, FixesMPV (F.tensor g) A) (hinvB : ∀ g, FixesMPV (F.tensor g) B)
    (fd : FusionData F) (ad : ActionData F A) (bd : ActionData F B) :
    groupCohomology.IsMulCocycle₂
      (fun p : G × G ↦ ad.lSymbol fd () p.1 p.2 / bd.lSymbol fd () p.1 p.2) := by
  apply (isMulCocycle₂_iff _).2
  intro g h k
  have hr := (ad.isCompatible_lSymbol (fd := fd) hF hA hD hinvA).mul_inv_one
    (bd.isCompatible_lSymbol (fd := fd) hF hB hE hinvB) () g h k
  simpa only [Pi.mul_apply, Pi.inv_apply, one_mul, div_eq_mul_inv] using hr.symm

/-- Actual relative action classes are constant along continuous normal invariant tensor
paths of fixed positive dimensions, when their left action caps are continuous. The
common fusion reductions are fixed. This supplies a path-to-class bridge without a
supplied virtual projective path; deriving the continuous caps and tensor realization
from a physical Hamiltonian path is a separate obligation. -/
theorem relative_lSymbol_endpoints_H2π_eq [Finite G]
    (hF : F.IsNormalRepresentation) (fd : FusionData F)
    (A : unitInterval → MPSTensor d D) (B : unitInterval → MPSTensor d E)
    (ad : ∀ t, ActionData F (A t)) (bd : ∀ t, ActionData F (B t))
    (hcA : Continuous A) (hcB : Continuous B)
    (hV : ∀ g, Continuous fun t ↦ (ad t).V g)
    (hV' : ∀ g, Continuous fun t ↦ (bd t).V g)
    (hA : ∀ t, Kraus.IsNormal (A t)) (hB : ∀ t, Kraus.IsNormal (B t))
    (hD : 0 < D) (hE : 0 < E)
    (hinvA : ∀ t g, FixesMPV (F.tensor g) (A t))
    (hinvB : ∀ t g, FixesMPV (F.tensor g) (B t)) :
    groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂
        (relative_lSymbol_isMulCocycle₂ hF (hA 1) (hB 1) hD hE
          (hinvA 1) (hinvB 1) fd (ad 1) (bd 1))) =
      groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂
        (relative_lSymbol_isMulCocycle₂ hF (hA 0) (hB 0) hD hE
          (hinvA 0) (hinvB 0) fd (ad 0) (bd 0))) := by
  apply H2π_eq_of_continuous_cocyclePath
    (fun t p ↦ (ad t).lSymbol fd () p.1 p.2 / (bd t).lSymbol fd () p.1 p.2)
    (fun t ↦ relative_lSymbol_isMulCocycle₂ hF (hA t) (hB t) hD hE
      (hinvA t) (hinvB t) fd (ad t) (bd t))
  intro g h
  convert (continuous_lSymbol fd A ad hcA hV hA hD hinvA g h).div
      (continuous_lSymbol fd B bd hcB hV' hB hE hinvB g h)
      (fun t ↦ ((bd t).lSymbol fd () g h).ne_zero) using 1
  funext t
  exact Units.val_div_eq_div_val _ _

end MPOTensor.GroupFamily.ActionData
