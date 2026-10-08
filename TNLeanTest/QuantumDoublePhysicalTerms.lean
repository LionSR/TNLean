/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Examples.QuantumDoubleBondParent
import TNLean.PEPS.Examples.QuantumDoublePlaquetteConstraint

/-!
# Exact physical quantum-double Hamiltonian regressions

The nonabelian tests distinguish multiplication side, inverse orientation, and
matrix ket action. The normalization test detects the missing group-order factor
in the displayed SCP10 sum. All physical spaces retain the forbidden basis spins.
-/

open TNLean.PEPS
open scoped BigOperators Matrix

namespace QuantumDoublePhysicalTermsTest

private abbrev S3 := Equiv.Perm (Fin 3)
private abbrev C2 := Equiv.Perm (Fin 2)
private abbrev SpinPair (G : Type*) := (G × G × G × G) × (G × G × G × G)

local instance : DecidableEq S3 := inferInstance

private def swap01 : S3 := Equiv.swap 0 1
private def swap12 : S3 := Equiv.swap 1 2
private def cycle : S3 := swap01 * swap12

-- An order-three group element prevents inverse orientation from collapsing.
example : cycle ^ 3 = 1 := by decide
example : cycle ≠ 1 := by decide
example : cycle ≠ cycle⁻¹ := by decide
example : swap01 * cycle⁻¹ ≠ cycle⁻¹ * swap01 := by decide
example : cycle * swap01 ≠ swap01 * cycle := by decide

private def inputSpins : SpinPair S3 :=
  ((swap01, swap01, swap12, cycle), (swap12, cycle, swap01, swap01))

private def expectedSpins : SpinPair S3 :=
  ((swap01 * cycle⁻¹, cycle * swap01, swap12, cycle),
    (swap12, cycle, swap01 * cycle⁻¹, cycle * swap01))

-- All four charged spins, and all four untouched spins, are checked together.
private theorem coherent_action : quantumDoubleKBondAction cycle inputSpins = expectedSpins := rfl

-- Reversing the whole action is genuinely a different physical operation.
private theorem inverse_action_distinct :
    expectedSpins ≠ quantumDoubleKBondAction cycle⁻¹ inputSpins := by decide

-- Multiplying on the other side is wrong on each of the two blocks.
example : (quantumDoubleKBondAction cycle inputSpins).1.1 ≠ cycle⁻¹ * swap01 := by
  decide

example : (quantumDoubleKBondAction cycle inputSpins).1.2.1 ≠ swap01 * cycle := by
  decide

example : (quantumDoubleKBondAction cycle inputSpins).2.2.2.1 ≠ cycle⁻¹ * swap01 := by
  decide

example : (quantumDoubleKBondAction cycle inputSpins).2.2.2.2 ≠ swap01 * cycle := by
  decide

/-- The actual matrix moves the ket forward, despite its inverse pullback formula. -/
theorem nonabelian_ket_action :
    quantumDoubleKBondMatrix cycle *ᵥ Pi.single inputSpins 1 =
      Pi.single expectedSpins 1 := by
  rw [quantumDoubleKBondMatrix_single, coherent_action]

/-- The inverse permutation would give a different matrix action. -/
theorem nonabelian_ket_inverse_rejected :
    quantumDoubleKBondMatrix cycle *ᵥ Pi.single inputSpins 1 ≠
      Pi.single (quantumDoubleKBondAction cycle⁻¹ inputSpins) 1 := by
  rw [nonabelian_ket_action]
  intro h
  have hc := congrFun h expectedSpins
  simp [inverse_action_distinct] at hc

-- One shared color changes on the left of q in both actual K tensors.
example :
    (quantumDoubleKSpins (swap12, cycle * swap01, cycle, 1),
      quantumDoubleKSpins (cycle, swap12, 1, cycle * swap01)) =
    quantumDoubleKBondAction cycle
      (quantumDoubleKSpins (swap12, swap01, cycle, 1),
        quantumDoubleKSpins (cycle, swap12, 1, swap01)) := by
  rw [quantumDoubleKSpins_bondLeft, quantumDoubleKSpins_bondRight]
  rfl

-- Right multiplication of the common virtual color is not the source action.
example :
    quantumDoubleKSpins (swap12, swap01 * cycle, cycle, 1) ≠
      quantumDoubleKBondLeft cycle (quantumDoubleKSpins (swap12, swap01, cycle, 1)) := by
  decide

example :
    quantumDoubleKSpins (cycle, swap12, 1, swap01 * cycle) ≠
      quantumDoubleKBondRight cycle (quantumDoubleKSpins (cycle, swap12, 1, swap01)) := by
  decide

private def forbiddenSpins : S3 × S3 × S3 × S3 := (cycle, 1, 1, 1)

private theorem forbidden_holonomy : quantumDoubleKHolonomy forbiddenSpins ≠ 1 := by
  decide

/-- The local projector excludes a genuine vector of the ambient physical space. -/
theorem local_forbidden_ket :
    quantumDoubleKLocalProjector *ᵥ Pi.single forbiddenSpins 1 = 0 := by
  rw [quantumDoubleKLocalProjector, Matrix.diagonal_mulVec_single]
  simp [forbidden_holonomy]

/-- The complementary Hamiltonian term acts as one on that forbidden ket. -/
theorem local_term_forbidden_ket :
    quantumDoubleKLocalTerm *ᵥ Pi.single forbiddenSpins 1 = Pi.single forbiddenSpins 1 := by
  rw [quantumDoubleKLocalTerm, Matrix.sub_mulVec, local_forbidden_ket, Matrix.one_mulVec, sub_zero]

-- This exclusion comes from the actual tensor coefficients, not a reduced alphabet.
example (p q r s : S3) : quantumDoubleKTensor S3 p q r s forbiddenSpins = 0 := by
  have hne : forbiddenSpins ≠ quantumDoubleKSpins (p, q, r, s) := by
    intro h
    apply forbidden_holonomy
    rw [h, quantumDoubleKHolonomy_spins]
  simp [quantumDoubleKTensor, hne]

/-- The first term's allowed space is exactly the actual tensor image. -/
theorem local_range_exact :
    LinearMap.range (siteMap (quantumDoubleKTensor S3)) =
      LinearMap.range (Matrix.mulVecLin (quantumDoubleKLocalProjector (G := S3))) :=
  range_siteMap_quantumDoubleKTensor

-- Both projector identities are checked on the entire nonabelian physical space.
example : quantumDoubleKLocalProjector (G := S3) * quantumDoubleKLocalProjector =
    quantumDoubleKLocalProjector :=
  quantumDoubleKLocalProjector_isStarProjection.isIdempotentElem

example : (quantumDoubleKLocalProjector (G := S3))ᴴ = quantumDoubleKLocalProjector :=
  quantumDoubleKLocalProjector_isStarProjection.isSelfAdjoint.star_eq

example : quantumDoubleKBondAverage (G := S3) * quantumDoubleKBondAverage =
    quantumDoubleKBondAverage :=
  quantumDoubleKBondAverage_isStarProjection.isIdempotentElem

example : (quantumDoubleKBondAverage (G := S3))ᴴ = quantumDoubleKBondAverage :=
  quantumDoubleKBondAverage_isStarProjection.isSelfAdjoint.star_eq

/-- The averaged operator fixes the actual contraction with six independent open colors. -/
theorem average_actual_contraction :
    quantumDoubleKBondAverage (G := S3) * quantumDoubleKBondContraction =
      quantumDoubleKBondContraction :=
  quantumDoubleKBondAverage_contraction

-- The actual contraction is nonzero, so the invariance check is not vacuous.
example : quantumDoubleKBondContraction (G := S3)
    ((1, 1, 1, 1), (1, 1, 1, 1)) ((1, 1, 1), (1, 1, 1)) = 1 := by
  simp [quantumDoubleKBondContraction, quantumDoubleKTensor, quantumDoubleKSpins, eq_comm]

/-- Exact two-block parent-space equality also holds for S3. -/
theorem bond_range_exact :
    LinearMap.range (Matrix.mulVecLin (quantumDoubleKBondContraction (G := S3))) =
      LinearMap.range (Matrix.mulVecLin (quantumDoubleKBondSupportProjector (G := S3))) :=
  range_quantumDoubleKBondContraction

/-- Every common local/coherent ground vector has a genuine two-block boundary preimage. -/
theorem actual_common_ground (v : SpinPair S3 → ℂ) :
    v ∈ LinearMap.range (Matrix.mulVecLin (quantumDoubleKBondContraction (G := S3))) ↔
      quantumDoubleKPairLocalProjector *ᵥ v = v ∧
        ∀ u x, v (quantumDoubleKBondAction u x) = v x :=
  mem_range_quantumDoubleKBondContraction_iff v

private def plaquetteSpins : QuantumDoubleKPlaquetteConfig S3 :=
  quantumDoubleKPlaquetteSpins ((1, 1, 1, 1), (1, 1, 1, 1))
    (cycle, swap01, swap12, 1)

-- The source order telescopes for genuine, noncommuting matched bond colors.
example : quantumDoubleKPlaquetteHolonomy plaquetteSpins = 1 :=
  quantumDoubleKPlaquetteHolonomy_spins _ _

-- Reading the same four physical spins in the reversed geometric order fails.
example :
    plaquetteSpins.1.1.2.1 * plaquetteSpins.1.2.2.2.1 *
      plaquetteSpins.2.1.2.2.2 * plaquetteSpins.2.2.1 ≠ 1 := by
  decide

-- Interchanging just the two bottom factors also fails in S3.
example :
    plaquetteSpins.1.1.2.1 * plaquetteSpins.2.1.2.2.2 *
      plaquetteSpins.2.2.1 * plaquetteSpins.1.2.2.2.1 ≠ 1 := by
  decide

private def nonflatPlaquette : QuantumDoubleKPlaquetteConfig S3 :=
  (((1, swap01, 1, 1), (1, 1, 1, 1)), ((1, 1, 1, 1), (1, 1, 1, 1)))

-- Non-flat holonomy is conjugated, not fixed pointwise, by the incident bond.
example :
    quantumDoubleKPlaquetteHolonomy (quantumDoubleKPlaquetteTopBond cycle nonflatPlaquette) =
      cycle * swap01 * cycle⁻¹ := by
  rw [quantumDoubleKPlaquetteHolonomy_topBond]
  rfl

example :
    quantumDoubleKPlaquetteHolonomy (quantumDoubleKPlaquetteTopBond cycle nonflatPlaquette) ≠
      quantumDoubleKPlaquetteHolonomy nonflatPlaquette := by
  decide

/-- The four-block term excludes a non-flat ket in its full sixteen-spin alphabet. -/
theorem plaquette_forbidden_ket :
    quantumDoubleKPlaquetteProjector *ᵥ Pi.single nonflatPlaquette 1 = 0 := by
  rw [quantumDoubleKPlaquetteProjector, Matrix.diagonal_mulVec_single]
  have hne : quantumDoubleKPlaquetteHolonomy nonflatPlaquette ≠ 1 := by decide
  simp [hne]

/-- The plaquette projector fixes the actual four-tensor contraction. -/
theorem plaquette_actual_contraction :
    quantumDoubleKPlaquetteProjector (G := S3) * quantumDoubleKPlaquetteContraction =
      quantumDoubleKPlaquetteContraction :=
  quantumDoubleKPlaquetteProjector_contraction

example : quantumDoubleKPlaquetteProjector (G := S3) * quantumDoubleKPlaquetteProjector =
    quantumDoubleKPlaquetteProjector :=
  quantumDoubleKPlaquetteProjector_isStarProjection.isIdempotentElem

example : (quantumDoubleKPlaquetteProjector (G := S3))ᴴ = quantumDoubleKPlaquetteProjector :=
  quantumDoubleKPlaquetteProjector_isStarProjection.isSelfAdjoint.star_eq

example : Commute (quantumDoubleKPlaquetteProjector (G := S3))
    (Matrix.permMatrixHom (R := ℂ) (quantumDoubleKPlaquetteTopBond cycle)) :=
  quantumDoubleKPlaquetteProjector_commute_topBond cycle

private noncomputable def unnormalizedC2Sum : Matrix (SpinPair C2) (SpinPair C2) ℂ :=
  ∑ u : C2, quantumDoubleKBondMatrix u

private theorem unnormalizedC2Sum_constant :
    unnormalizedC2Sum *ᵥ (fun _ => (1 : ℂ)) = fun _ => (2 : ℂ) := by
  rw [unnormalizedC2Sum, Matrix.sum_mulVec]
  simp only [quantumDoubleKBondMatrix_mulVec]
  ext x
  simp [Fintype.card_perm]

/-- The displayed source sum without 1/|G| does not fix an invariant vector. -/
theorem unnormalized_sum_does_not_fix :
    unnormalizedC2Sum *ᵥ (fun _ => (1 : ℂ)) ≠ (fun _ => (1 : ℂ)) := by
  rw [unnormalizedC2Sum_constant]
  intro h
  have hc := congrFun h ((1, 1, 1, 1), (1, 1, 1, 1))
  norm_num at hc

/-- The unnormalized source sum is not even idempotent for the two-element group. -/
theorem unnormalized_sum_not_idempotent : ¬ IsIdempotentElem unnormalizedC2Sum := by
  intro h
  have hv := congrArg (fun M => M *ᵥ (fun _ => (1 : ℂ))) h.eq
  rw [← Matrix.mulVec_mulVec, unnormalizedC2Sum_constant] at hv
  have heq : (fun _ : SpinPair C2 => (2 : ℂ)) = (2 : ℂ) • (fun _ => (1 : ℂ)) := by
    ext x
    simp
  rw [heq, Matrix.mulVec_smul, unnormalizedC2Sum_constant] at hv
  have hc := congrFun hv ((1, 1, 1, 1), (1, 1, 1, 1))
  norm_num at hc

/-- Inserting 1/|G| restores the required fixed-vector equation. -/
theorem normalized_sum_fixes :
    quantumDoubleKBondAverage (G := C2) *ᵥ (fun _ => (1 : ℂ)) =
      (fun _ => (1 : ℂ)) := by
  apply (quantumDoubleKBondAverage_mulVec_eq_self_iff _).mpr
  intros
  rfl

end QuantumDoublePhysicalTermsTest

set_option linter.hashCommand false

/--
info: 'QuantumDoublePhysicalTermsTest.nonabelian_ket_action' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumDoublePhysicalTermsTest.nonabelian_ket_action

/--
info: 'QuantumDoublePhysicalTermsTest.nonabelian_ket_inverse_rejected' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumDoublePhysicalTermsTest.nonabelian_ket_inverse_rejected

/--
info: 'QuantumDoublePhysicalTermsTest.local_forbidden_ket' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumDoublePhysicalTermsTest.local_forbidden_ket

/--
info: 'QuantumDoublePhysicalTermsTest.local_range_exact' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumDoublePhysicalTermsTest.local_range_exact

/--
info: 'QuantumDoublePhysicalTermsTest.average_actual_contraction' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumDoublePhysicalTermsTest.average_actual_contraction

/--
info: 'QuantumDoublePhysicalTermsTest.bond_range_exact' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumDoublePhysicalTermsTest.bond_range_exact

/--
info: 'QuantumDoublePhysicalTermsTest.plaquette_forbidden_ket' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumDoublePhysicalTermsTest.plaquette_forbidden_ket

/--
info: 'QuantumDoublePhysicalTermsTest.plaquette_actual_contraction' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumDoublePhysicalTermsTest.plaquette_actual_contraction

/--
info: 'QuantumDoublePhysicalTermsTest.unnormalized_sum_does_not_fix' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumDoublePhysicalTermsTest.unnormalized_sum_does_not_fix

/--
info: 'QuantumDoublePhysicalTermsTest.unnormalized_sum_not_idempotent' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumDoublePhysicalTermsTest.unnormalized_sum_not_idempotent

/--
info: 'QuantumDoublePhysicalTermsTest.normalized_sum_fixes' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumDoublePhysicalTermsTest.normalized_sum_fixes

/--
info: 'QuantumDoublePhysicalTermsTest.actual_common_ground' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumDoublePhysicalTermsTest.actual_common_ground
