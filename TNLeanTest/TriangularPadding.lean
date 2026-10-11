/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.TriangularPhysicalPadding
import TNLean.MPS.MPDO.TriangularPaddingDecomposition
import TNLean.MPS.MPDO.TriangularPaddingGauge

/-!
# Triangular physical padding regressions

The signatures retain the original virtual dimensions and the exact
rectangular decomposition matrices. Empty physical alphabets, zero virtual
dimensions, and empty target families are not excluded by padding itself.
Only the cross-kind gauge-separation assertions require positive dimension.
-/

set_option linter.hashCommand false

namespace TriangularPaddingTest

open MPOTensor

variable {d D D₁ D₂ : ℕ}

example (O : MPOTensor d D) : MPOTensor (d + 1) D := operatorPhysicalPadding O

example (A : MPSTensor d D) : MPOTensor (d + 1) D := statePhysicalPadding A

example (O : MPOTensor d D) (i j : Fin d) :
    operatorPhysicalPadding O i.castSucc j.castSucc = O i j :=
  operatorPhysicalPadding_castSucc_castSucc O i j

example (O : MPOTensor d D) (j : Fin (d + 1)) :
    operatorPhysicalPadding O (Fin.last d) j = 0 := operatorPhysicalPadding_last O j

example (O : MPOTensor d D) (i : Fin (d + 1)) :
    operatorPhysicalPadding O i (Fin.last d) = 0 := operatorPhysicalPadding_last_right O i

example (A : MPSTensor d D) (i : Fin d) :
    statePhysicalPadding A i.castSucc (Fin.last d) = A i :=
  statePhysicalPadding_castSucc_last A i

example (A : MPSTensor d D) (i : Fin (d + 1)) (j : Fin d) :
    statePhysicalPadding A i j.castSucc = 0 := statePhysicalPadding_castSucc_right A i j

example (A : MPSTensor d D) (j : Fin (d + 1)) :
    statePhysicalPadding A (Fin.last d) j = 0 := statePhysicalPadding_last A j

example (O : MPOTensor d D₁) (P : MPOTensor d D₂) :
    mulTensor (operatorPhysicalPadding O) (operatorPhysicalPadding P) =
      operatorPhysicalPadding (mulTensor O P) := mulTensor_operatorPhysicalPadding O P

example (O : MPOTensor d D₁) (A : MPSTensor d D₂) :
    mulTensor (operatorPhysicalPadding O) (statePhysicalPadding A) =
      statePhysicalPadding (actTensor O A) :=
  mulTensor_operatorPhysicalPadding_statePhysicalPadding O A

example (A : MPSTensor d D₁) (O : MPOTensor d D₂) :
    mulTensor (statePhysicalPadding A) (operatorPhysicalPadding O) = 0 :=
  mulTensor_statePhysicalPadding_operatorPhysicalPadding A O

example (A : MPSTensor d D₁) (B : MPSTensor d D₂) :
    mulTensor (statePhysicalPadding A) (statePhysicalPadding B) = 0 :=
  mulTensor_statePhysicalPadding_statePhysicalPadding A B

example {O : MPOTensor d D} (hO : Kraus.IsInjective O.toMPSTensor) :
    Kraus.IsInjective (operatorPhysicalPadding O).toMPSTensor :=
  isInjective_operatorPhysicalPadding hO

example {A : MPSTensor d D} (hA : Kraus.IsInjective A) :
    Kraus.IsInjective (statePhysicalPadding A).toMPSTensor :=
  isInjective_statePhysicalPadding hA

-- Padding and the zero-product theorem do not impose physical or bond positivity.
example (A : MPSTensor 0 0) (B : MPSTensor 0 2) :
    mulTensor (statePhysicalPadding A) (statePhysicalPadding B) = 0 :=
  mulTensor_statePhysicalPadding_statePhysicalPadding A B

section Decomposition

variable {ι : Type*} [Fintype ι] {δ : ι → ℕ}
  {V : ∀ c : ι, Matrix (Fin (δ c)) (Fin D) ℂ}
  {W : ∀ c : ι, Matrix (Fin D) (Fin (δ c)) ℂ}

example {O : MPOTensor d D} {T : ∀ c : ι, MPOTensor d (δ c)}
    (h : MPSTensor.IsBiorthogonalDecomposition O.toMPSTensor
      (fun c ↦ (T c).toMPSTensor) V W) :
    MPSTensor.IsBiorthogonalDecomposition (operatorPhysicalPadding O).toMPSTensor
      (fun c ↦ (operatorPhysicalPadding (T c)).toMPSTensor) V W :=
  h.operatorPhysicalPadding

example {B : MPSTensor d D} {A : ∀ c : ι, MPSTensor d (δ c)}
    (h : MPSTensor.IsBiorthogonalDecomposition B A V W) :
    MPSTensor.IsBiorthogonalDecomposition (statePhysicalPadding B).toMPSTensor
      (fun c ↦ (statePhysicalPadding (A c)).toMPSTensor) V W :=
  h.statePhysicalPadding

end Decomposition

-- Empty target families require neither an artificial zero-tensor label
-- nor an ambient identity resolution.
example {δ : Fin 0 → ℕ} {B : MPSTensor d D}
    {A : ∀ c : Fin 0, MPSTensor d (δ c)}
    {V : ∀ c : Fin 0, Matrix (Fin (δ c)) (Fin D) ℂ}
    {W : ∀ c : Fin 0, Matrix (Fin D) (Fin (δ c)) ℂ}
    (h : MPSTensor.IsBiorthogonalDecomposition B A V W) :
    MPSTensor.IsBiorthogonalDecomposition (statePhysicalPadding B).toMPSTensor
      (fun c ↦ (statePhysicalPadding (A c)).toMPSTensor) V W :=
  h.statePhysicalPadding

example {O P : MPOTensor d D}
    (h : MPSTensor.GaugePhaseEquiv (operatorPhysicalPadding O).toMPSTensor
      (operatorPhysicalPadding P).toMPSTensor) :
    MPSTensor.GaugePhaseEquiv O.toMPSTensor P.toMPSTensor :=
  gaugePhaseEquiv_of_operatorPhysicalPadding h

example {A B : MPSTensor d D}
    (h : MPSTensor.GaugePhaseEquiv (statePhysicalPadding A).toMPSTensor
      (statePhysicalPadding B).toMPSTensor) : MPSTensor.GaugePhaseEquiv A B :=
  gaugePhaseEquiv_of_statePhysicalPadding h

-- Only the target state is required to be injective in this direction.
example (O : MPOTensor d D) {A : MPSTensor d D} (hD : 0 < D)
    (hA : Kraus.IsInjective A) :
    ¬ MPSTensor.GaugePhaseEquiv (operatorPhysicalPadding O).toMPSTensor
      (statePhysicalPadding A).toMPSTensor :=
  not_gaugePhaseEquiv_operatorPhysicalPadding_statePhysicalPadding O hD hA

-- In the reverse direction only the target operator is required to be injective.
example (A : MPSTensor d D) {O : MPOTensor d D} (hD : 0 < D)
    (hO : Kraus.IsInjective O.toMPSTensor) :
    ¬ MPSTensor.GaugePhaseEquiv (statePhysicalPadding A).toMPSTensor
      (operatorPhysicalPadding O).toMPSTensor :=
  not_gaugePhaseEquiv_statePhysicalPadding_operatorPhysicalPadding A hD hO

/--
info: 'MPOTensor.mulTensor_operatorPhysicalPadding'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.mulTensor_operatorPhysicalPadding
/--
info: 'MPOTensor.mulTensor_operatorPhysicalPadding_statePhysicalPadding'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.mulTensor_operatorPhysicalPadding_statePhysicalPadding
/--
info: 'MPOTensor.mulTensor_statePhysicalPadding_operatorPhysicalPadding'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.mulTensor_statePhysicalPadding_operatorPhysicalPadding
/--
info: 'MPOTensor.mulTensor_statePhysicalPadding_statePhysicalPadding'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.mulTensor_statePhysicalPadding_statePhysicalPadding
/--
info: 'MPOTensor.isInjective_operatorPhysicalPadding'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.isInjective_operatorPhysicalPadding
/--
info: 'MPOTensor.isInjective_statePhysicalPadding'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.isInjective_statePhysicalPadding
/--
info: 'MPSTensor.IsBiorthogonalDecomposition.operatorPhysicalPadding'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.IsBiorthogonalDecomposition.operatorPhysicalPadding
/--
info: 'MPSTensor.IsBiorthogonalDecomposition.statePhysicalPadding'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.IsBiorthogonalDecomposition.statePhysicalPadding
/--
info: 'MPOTensor.gaugePhaseEquiv_of_operatorPhysicalPadding'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.gaugePhaseEquiv_of_operatorPhysicalPadding
/--
info: 'MPOTensor.gaugePhaseEquiv_of_statePhysicalPadding'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.gaugePhaseEquiv_of_statePhysicalPadding
/--
info: 'MPOTensor.not_gaugePhaseEquiv_operatorPhysicalPadding_statePhysicalPadding'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.not_gaugePhaseEquiv_operatorPhysicalPadding_statePhysicalPadding
/--
info: 'MPOTensor.not_gaugePhaseEquiv_statePhysicalPadding_operatorPhysicalPadding'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.not_gaugePhaseEquiv_statePhysicalPadding_operatorPhysicalPadding

end TriangularPaddingTest
