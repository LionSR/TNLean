/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Chain.VaryingBondChain
import TNLean.Algebra.FinCyclicInduction
import QICLean.Kraus.RectangularChain
import QICLean.Channel.WindowMinorization

/-!
# Actual rectangular intervals of a varying-bond ring

Natural-number cuts carry the actual cyclic bond dimensions. Site matrices retain their
original physical alphabet and are relabeled only through equality of the cut dimensions.
Their interval channels are ordered products of these actual rectangular site maps.

## References

* arXiv:2307.01696v2, paragraph "Inhomogeneous short-range correlated MPS".
-/

open Matrix Fin.NatCast
open scoped ComplexOrder

namespace VaryingBondChain

variable {d D N : ℕ} [NeZero N]

/-- The actual bond dimension at a natural-number cut, with the ring closure identified. -/
def bondDimAt (A : VaryingBondChain d D N) (i : ℕ) : ℕ := A.bondDim (i : Fin N)

@[simp] theorem bondDimAt_val (A : VaryingBondChain d D N) (i : Fin N) :
    bondDimAt A i.val = A.bondDim i := by simp [bondDimAt]

@[simp] theorem bondDimAt_length (A : VaryingBondChain d D N) :
    bondDimAt A N = bondDimAt A 0 := by simp [bondDimAt]

theorem bondDimAt_le (A : VaryingBondChain d D N) (i : ℕ) : bondDimAt A i ≤ D :=
  A.bondDim_le _

/-- The next natural-number cut is the outgoing cyclic bond of the original site. -/
theorem bondDimAt_succ (A : VaryingBondChain d D N) (i : ℕ) :
    bondDimAt A (i + 1) = A.bondDim (finRotate N (i : Fin N)) := by
  apply congrArg A.bondDim
  simp [finRotate_apply]

/-- The original site matrices on their actual successive cut spaces. -/
def siteTensorAt (A : VaryingBondChain d D N) (i : ℕ) (s : Fin d) :
    Matrix (Fin (bondDimAt A i)) (Fin (bondDimAt A (i + 1))) ℂ :=
  (A.tensor (i : Fin N) s).submatrix id (Fin.cast (bondDimAt_succ A i))

/-- The actual site transfer, with no zero padding or complementary Kraus operators. -/
noncomputable def siteTransferAt (A : VaryingBondChain d D N) (i : ℕ) :=
  Matrix.rectangularKrausMap (siteTensorAt A i)

theorem siteTransferAt_isKrausCPTP (A : VaryingBondChain d D N)
    (hA : ∀ i, IsKrausCPTP (Matrix.rectangularKrausMap (A.tensor i))) (i : ℕ) :
    IsKrausCPTP (siteTransferAt A i) :=
  Matrix.isKrausCPTP_rectangularKrausMap_finCast rfl (bondDimAt_succ A i)
    (A.tensor (i : Fin N)) (hA _)

/-- Compatible cut densities are derived from a fixed density of the actual full cycle.
Every nonwrapping interval transports its right reference to its left reference. -/
theorem exists_compatible_actual_densities (A : VaryingBondChain d D N)
    (hD : ∀ i, 0 < A.bondDim i)
    (hA : ∀ i, IsKrausCPTP (Matrix.rectangularKrausMap (A.tensor i))) :
    ∃ σ : ∀ a, a ≤ N → Matrix (Fin (bondDimAt A a)) (Fin (bondDimAt A a)) ℂ,
      (∀ a ha, (σ a ha).PosSemidef ∧ (σ a ha).trace = 1) ∧
      σ N le_rfl = Matrix.equivReindexMap (finCongr (bondDimAt_length A).symm)
        (σ 0 (Nat.zero_le N)) ∧
      ∀ a b (hab : a ≤ b) (hb : b ≤ N),
        Matrix.channelInterval (siteTransferAt A) a b hab (σ b hb) = σ a (hab.trans hb) :=
  Matrix.exists_compatible_channelInterval_densities (siteTransferAt A) N
    (hD 0) (bondDimAt_length A) (fun i _ => siteTransferAt_isKrausCPTP A hA i)

end VaryingBondChain
