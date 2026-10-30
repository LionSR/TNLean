import TNLean.PEPS.Examples.QuantumDoubleRenormalization
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.ZMod.Basic

/-! Exact theorem boundaries and noncommutative order for the local four-T RG. -/

open scoped Matrix
open TNLean.PEPS

private abbrev S3 := Equiv.Perm (Fin 3)
private def a : S3 := Equiv.swap 0 1
private def b : S3 := Equiv.swap 1 2

-- This is a genuinely nonabelian finite group, and the printed pair map is not involutive.
example : a * b ≠ b * a := by decide
example : quantumDoubleRenormPair (quantumDoubleRenormPair (a, b)) ≠ (a, b) := by decide

-- The original clockwise product need not be one before the physical basis inversion.
example : quantumDoubleKHolonomy (b * a, b, 1, a) ≠ 1 := by decide
example : quantumDoubleRenormPhysical (b * a, b, 1, a) = (a * b, b, 1, 1) := by decide

-- Both inverses are checked on every S3 register, including outside tensor support.
example (x : S3 × S3) :
    quantumDoubleRenormPair.symm (quantumDoubleRenormPair x) = x :=
  quantumDoubleRenormPair.symm_apply_apply x
example (y : S3 × S3 × S3 × S3) :
    quantumDoubleRenormPhysical (quantumDoubleRenormPhysical.symm y) = y :=
  quantumDoubleRenormPhysical.apply_symm_apply y

-- No compatibility premise is supplied to the full four-T physical RG theorem.
example (α : QuantumDoubleRenormBoundary S3) (y : S3 × S3 × S3 × S3) :
    quantumDoubleElementaryBlock (quantumDoubleRenormBoundary.symm α)
        (quantumDoubleRenormPhysical.symm y) =
      (if quantumDoubleRenormSurplus α = 1 then (1 : ℂ) else 0) *
      (if y.2.2.2 = 1 then (1 : ℂ) else 0) *
      quantumDoubleRenormReducedTensor (y.1, y.2.1, y.2.2.1)
        (quantumDoubleRenormColors α) :=
  quantumDoubleElementaryBlock_physicalRG α y

-- The source K is the existing tensor, with all eight boundary registers retained.
example (α : QuantumDoubleRenormBoundary S3) (y : S3 × S3 × S3 × S3) :
    quantumDoubleElementaryBlock (quantumDoubleRenormBoundary.symm α)
        (quantumDoubleRenormPhysical.symm y) =
      (if quantumDoubleRenormSurplus α = 1 then (1 : ℂ) else 0) *
      quantumDoubleKTensor S3 α.1.1 α.2.1.1 α.2.2.1.1 α.2.2.2.1
        (quantumDoubleRenormReconstruct y) :=
  quantumDoubleElementaryBlock_toK α y

example : quantumDoubleRenormReducedTensor (G := S3) *
      (quantumDoubleRenormReducedTensor (G := S3))ᴴ =
    (6 : ℂ) • (1 : Matrix (S3 × S3 × S3) (S3 × S3 × S3) ℂ) := by
  simpa [show Fintype.card S3 = 6 by decide] using
    quantumDoubleRenormReducedTensor_mul_conjTranspose (G := S3)

example : quantumDoubleRenormNormalizedTensor (G := S3) *
      (quantumDoubleRenormNormalizedTensor (G := S3))ᴴ = 1 :=
  quantumDoubleRenormNormalizedTensor_mul_conjTranspose

-- The exact same theorem specializes to the abelian binary group.
private abbrev Bit := Multiplicative (ZMod 2)
example : ∀ a b : ZMod 2,
    quantumDoubleRenormPair (Multiplicative.ofAdd a, Multiplicative.ofAdd b) =
      (Multiplicative.ofAdd a, Multiplicative.ofAdd (a + b)) := by decide

example (α : QuantumDoubleRenormBoundary Bit) (y : Bit × Bit × Bit × Bit) :
    quantumDoubleElementaryBlock (quantumDoubleRenormBoundary.symm α)
        (quantumDoubleRenormPhysical.symm y) =
      (if quantumDoubleRenormSurplus α = 1 then (1 : ℂ) else 0) *
      (if y.2.2.2 = 1 then (1 : ℂ) else 0) *
      quantumDoubleRenormReducedTensor (y.1, y.2.1, y.2.2.1)
        (quantumDoubleRenormColors α) :=
  quantumDoubleElementaryBlock_physicalRG α y

private instance : DecidableEq (S3 × S3) := inferInstance
private instance : DecidableEq ((S3 × S3) × (S3 × S3)) := inferInstance

example : Equiv.Perm.permMatrix ℂ (quantumDoubleRenormPhysical (G := S3)).symm *
      quantumDoubleElementaryBlockMatrix *
      Equiv.Perm.permMatrix ℂ (quantumDoubleRenormBoundary (G := S3)) =
    quantumDoubleRenormFactorMatrix :=
  quantumDoubleElementaryBlockMatrix_physicalRG
