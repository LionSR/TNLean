/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BlockSumAdjointBoundary

/-!
# Normal periodic duality and arbitrary-boundary adjoint regressions

The signatures below retain raw normality, positive block dimensions, an
involutive label dual, and the explicit positive-length periodic physical
adjoint identities. No boundary adjoint formula is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.hashCommand false

open scoped Matrix BigOperators

namespace NormalAdjointBoundaryTest

-- The boundary is entrywise conjugated, including at zero length.
example {d D : ℕ} (A : MPOTensor d D) (X : Matrix (Fin D) (Fin D) ℂ) :
    (MPOTensor.mpoWithBoundary A X 0)ᴴ =
      MPOTensor.mpoWithBoundary (MPOTensor.physicalAdjointTensor A)
        (X.map (starRingEnd ℂ)) 0 :=
  MPOTensor.conjTranspose_mpoWithBoundary A X 0

section Blocks

variable {ι : Type*} {d : ℕ} {dim : ι → ℕ}
    (A : (a : ι) → MPOTensor d (dim a)) (dual : ι → ι)
    (hdual : Function.Involutive dual)
    (hNormal : ∀ a, Kraus.IsNormal (A a).toMPSTensor)
    (hDim : ∀ a, 0 < dim a)
    (hPeriodic : ∀ (a : ι) (N : ℕ), 0 < N →
      MPOTensor.mpo (A (dual a)) N = (MPOTensor.mpo (A a) N)ᴴ)

example (a : ι) : dim a = dim (dual a) :=
  MPOTensor.IsPeriodicAdjointFamily.bondDim_dual hPeriodic hdual hNormal hDim a

-- Normality suffices without a one-site injectivity hypothesis.
example (a : ι) :
    ∃ (V : Matrix (Fin (dim (dual a))) (Fin (dim a)) ℂ)
      (W : Matrix (Fin (dim a)) (Fin (dim (dual a))) ℂ),
      V * W = 1 ∧ W * V = 1 ∧
      (∀ i j, MPOTensor.physicalAdjointTensor (A a) i j = W * A (dual a) i j * V) ∧
      ∀ (X : Matrix (Fin (dim a)) (Fin (dim a)) ℂ) (N : ℕ),
        (MPOTensor.mpoWithBoundary (A a) X N)ᴴ =
          MPOTensor.mpoWithBoundary (A (dual a))
            (V * X.map (starRingEnd ℂ) * W) N :=
  MPOTensor.IsPeriodicAdjointFamily.exists_boundaryGauge hPeriodic hdual hNormal hDim a

end Blocks

section ActualBlockSum

variable {d r : ℕ} {dim : Fin r → ℕ}
    (A : (a : Fin r) → MPOTensor d (dim a)) (dual : Fin r → Fin r)
    (hdual : Function.Involutive dual)
    (hNormal : ∀ a, Kraus.IsNormal (A a).toMPSTensor)
    (hDim : ∀ a, 0 < dim a)
    (hPeriodic : ∀ (a : Fin r) (N : ℕ), 0 < N →
      MPOTensor.mpo (A (dual a)) N = (MPOTensor.mpo (A a) N)ᴴ)

-- The output is a boundary of the actual original block sum, chosen before N.
example (X : Matrix (Fin (∑ a, dim a)) (Fin (∑ a, dim a)) ℂ) :
    ∃ Y : Matrix (Fin (∑ a, dim a)) (Fin (∑ a, dim a)) ℂ,
      ∀ N : ℕ, 0 < N →
        (MPOTensor.mpoWithBoundary (MPOTensor.blockSum A) X N)ᴴ =
          MPOTensor.mpoWithBoundary (MPOTensor.blockSum A) Y N :=
  MPOTensor.IsPeriodicAdjointFamily.isBoundaryAdjointClosed_blockSum
    hPeriodic hdual hNormal hDim X

-- The same constructed gauges also handle empty-chain boundary traces.
example :
    ∃ (V : ∀ a, Matrix (Fin (dim (dual a))) (Fin (dim a)) ℂ)
      (W : ∀ a, Matrix (Fin (dim a)) (Fin (dim (dual a))) ℂ),
      ∀ X : Matrix (Fin (∑ a, dim a)) (Fin (∑ a, dim a)) ℂ,
        (MPOTensor.mpoWithBoundary (MPOTensor.blockSum A) X 0)ᴴ =
          MPOTensor.mpoWithBoundary (MPOTensor.blockSum A)
            (MPOTensor.blockSumAdjointBoundary dual V W X) 0 := by
  obtain ⟨V, W, _, _, _, hboundary⟩ :=
    MPOTensor.IsPeriodicAdjointFamily.exists_blockSumAdjointBoundary
      hPeriodic hdual hNormal hDim
  exact ⟨V, W, fun X ↦ hboundary X 0⟩

end ActualBlockSum

-- No nonempty label-family hypothesis is hidden in assembly.
example {d : ℕ} {dim : Fin 0 → ℕ}
    (A : (a : Fin 0) → MPOTensor d (dim a)) :
    MPOTensor.IsBoundaryAdjointClosed (MPOTensor.blockSum A) := by
  apply MPOTensor.IsPeriodicAdjointFamily.isBoundaryAdjointClosed_blockSum
    (dual := id)
  · intro a
    exact Fin.elim0 a
  · intro a
    rfl
  · intro a
    exact Fin.elim0 a
  · intro a
    exact Fin.elim0 a

/--
info: 'MPOTensor.IsPeriodicAdjointFamily.bondDim_dual'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.IsPeriodicAdjointFamily.bondDim_dual

/--
info: 'MPOTensor.IsPeriodicAdjointFamily.exists_boundaryGauge'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.IsPeriodicAdjointFamily.exists_boundaryGauge

/--
info: 'MPOTensor.IsPeriodicAdjointFamily.exists_blockSumAdjointBoundary'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.IsPeriodicAdjointFamily.exists_blockSumAdjointBoundary

/--
info: 'MPOTensor.IsPeriodicAdjointFamily.isBoundaryAdjointClosed_blockSum'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.IsPeriodicAdjointFamily.isBoundaryAdjointClosed_blockSum

end NormalAdjointBoundaryTest
