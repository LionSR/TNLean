/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.DependentTorusClosureTheorem
import TNLean.Algebra.SemiRegularGroupAlgebra

/-! # Source-faithful four-cut closure with unequal virtual and physical dimensions -/

noncomputable section
open TNLean.PEPS

namespace DependentTorusClosureTest

-- This signature retains eight independently typed virtual spaces, four independently
-- typed physical spaces, and each bond's own matching semi-regular representation.
example {G : Type*} [Group G] [Finite G]
    (D : DependentTorus.Bond → Type*) [∀ e, Fintype (D e)] [∀ e, DecidableEq (D e)]
    {Phys : DependentTorus.Vertex → Type*} [∀ v, Finite (Phys v)]
    (U : (e : DependentTorus.Bond) → G →* Matrix (D e) (D e) ℂ)
    (hU : ∀ e, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)))
    (A : (v : DependentTorus.Vertex) → DependentTorus.LocalConfig D v → Phys v → ℂ)
    (hA : ∀ v, IsGInjective (DependentBondNetwork.incidentRepresentation
      torusLabelledBondTail torusLabelledBondHead D U v)
      (DependentBondNetwork.localSiteMap torusLabelledBondTail torusLabelledBondHead D A v)) :
    DependentTorus.fourCutSpace D A = DependentTorus.commutingClosureSpan D U A :=
  DependentTorus.fourCutSpace_eq_commutingClosureSpan D U hU A hA

-- Only one of the eight actual bonds has dimension two; all others have dimension one.
private def edgeDimension (e : DependentTorus.Bond) : ℕ :=
  if e = ((0, 0), false) then 2 else 1
private abbrev BondAlphabet (e : DependentTorus.Bond) := Fin (edgeDimension e)
private instance (e : DependentTorus.Bond) : Nonempty (BondAlphabet e) := by
  dsimp [BondAlphabet, edgeDimension]
  split_ifs <;> infer_instance

private def U (e : DependentTorus.Bond) : Unit →* Matrix (BondAlphabet e) (BondAlphabet e) ℂ := 1

-- The distinguished edge is genuinely nonregular: it has two trivial copies.
private theorem U_semiRegular (e : DependentTorus.Bond) : Representation.IsSemiRegular
    (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)) := by
  classical
  let s : BondAlphabet e := Classical.choice inferInstance
  apply Representation.isSemiRegular_of_linearIndependent
  rw [Fintype.linearIndependent_iff]
  intro c hc g
  have h := congrArg (fun L : Module.End ℂ (BondAlphabet e → ℂ) ↦ L (fun _ ↦ 1) s) hc
  simpa [U] using h

example : Fintype.card (BondAlphabet ((0, 0), false)) = 2 := by decide
example : Fintype.card (BondAlphabet ((1, 0), false)) = 1 := by decide

-- The physical canonical configuration spaces also have different dimensions.
example : Fintype.card (DependentTorus.LocalConfig BondAlphabet (0, 0)) = 2 := by decide
example : Fintype.card (DependentTorus.LocalConfig BondAlphabet (0, 1)) = 1 := by decide

example :
    DependentTorus.fourCutSpace BondAlphabet (DependentTorus.canonicalSites BondAlphabet U) =
      DependentTorus.commutingClosureSpan BondAlphabet U
        (DependentTorus.canonicalSites BondAlphabet U) :=
  DependentTorus.fourCutSpace_eq_commutingClosureSpan BondAlphabet U U_semiRegular _
    (DependentBondNetwork.isGInjective_averagingSite
      torusLabelledBondTail torusLabelledBondHead BondAlphabet U)

-- Source geometry is exactly four sites, eight bonds, four incident endpoints per site,
-- and eight independent exposed endpoints on each of the four cuts.
example : Fintype.card DependentTorus.Vertex = 4 := by decide
example : Fintype.card DependentTorus.Bond = 8 := card_torusLabelledBond_two
example (v : DependentTorus.Vertex) :
    Fintype.card (DependentBondNetwork.IncidentEndpoint
      torusLabelledBondTail torusLabelledBondHead v) = 4 := card_torusIncidentEndpoint v
example (c r : ZMod 2) :
    Fintype.card (DependentBondNetwork.CutEndpoint (torusSeamCutBonds c r)) = 8 :=
  card_torusCutEndpoint_two c r

end DependentTorusClosureTest

set_option linter.hashCommand false

/--
info: 'TNLean.PEPS.DependentTorus.fourCutSpace_eq_commutingClosureSpan' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.DependentTorus.fourCutSpace_eq_commutingClosureSpan

/--
info: 'TNLean.PEPS.DependentTorus.coefficient_eq_zero_of_mem_fourCutSpace_not_flat' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.DependentTorus.coefficient_eq_zero_of_mem_fourCutSpace_not_flat

/--
info: 'TNLean.PEPS.DependentBondNetwork.iInf_cutSpace_eq_map_representationAveragingSite'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.DependentBondNetwork.iInf_cutSpace_eq_map_representationAveragingSite
