import TNLean.MPS.Chain.FundamentalTheorem
import TNLean.MPS.Core.Blocking

/-!
# Fundamental Theorem for normal MPS chains via blocking

This file packages the standard blocking reduction for the chain Fundamental
Theorem: if a common blocking length `L` makes both tensors injective, then the
injective chain theorem applies to the blocked tensors.

At this stage the equality hypothesis is still the strong `SameMPV` condition
on the combined blocked-chain tensors (all lengths / mixed words), matching the
current `fundamentalTheorem_injective_chain` interface.
-/

open scoped Matrix

namespace MPSChainTensor
namespace MPSTensor

variable {d D : ℕ}

/-- Normality witness used in the chain-level blocking reduction:
there exists a blocking length whose blocked tensor is injective. -/
def IsNormal (A : MPSTensor d D) : Prop :=
  ∃ L : ℕ, MPSTensor.IsInjective (MPSTensor.blockTensor (d := d) (D := D) A L)

@[simp] lemma isNormal_iff (A : MPSTensor d D) :
    IsNormal A ↔ ∃ L : ℕ, MPSTensor.IsInjective (MPSTensor.blockTensor A L) :=
  Iff.rfl

/-- Translation-invariant chain obtained by repeating the blocked tensor
`blockTensor A L` on all `N` sites. -/
noncomputable def blockedChain (A : MPSTensor d D) (L N : ℕ) :
    MPSChainTensor (MPSTensor.blockPhysDim d L) D N :=
  fun _ => MPSTensor.blockTensor (d := d) (D := D) A L

lemma blockedChain_isInjective (A : MPSTensor d D) (L N : ℕ)
    (hA : MPSTensor.IsInjective (MPSTensor.blockTensor (d := d) (D := D) A L)) :
    MPSChainTensor.IsInjective (blockedChain (d := d) (D := D) A L N) := by
  intro k
  simpa [blockedChain] using hA

/-- **Fundamental theorem for normal tensors (blocked form).**

If a common blocking length `L` makes both tensors injective, then the blocked
chains are gauge equivalent whenever the combined blocked tensors satisfy
`SameMPV`. This is exactly the injective-chain theorem applied to `blockedChain`.
-/
theorem fundamentalTheorem_normal
    (A B : MPSTensor d D) (L N : ℕ)
    (hA_normal : IsNormal A) (hB_normal : IsNormal B)
    (hA_block : MPSTensor.IsInjective (MPSTensor.blockTensor (d := d) (D := D) A L))
    (_hB_block : MPSTensor.IsInjective (MPSTensor.blockTensor (d := d) (D := D) B L))
    (hMPV : MPSTensor.SameMPV
      (MPSTensor.chainCombinedTensor (blockedChain (d := d) (D := D) A L N))
      (MPSTensor.chainCombinedTensor (blockedChain (d := d) (D := D) B L N))) :
    MPSChainTensor.GaugeEquiv
      (blockedChain (d := d) (D := D) A L N)
      (blockedChain (d := d) (D := D) B L N) := by
  -- Keep the normality assumptions explicit in the theorem interface.
  let _hA : IsNormal A := hA_normal
  let _hB : IsNormal B := hB_normal
  exact MPSChainTensor.fundamentalTheorem_injective_chain
    (A := blockedChain (d := d) (D := D) A L N)
    (B := blockedChain (d := d) (D := D) B L N)
    (hA := blockedChain_isInjective (d := d) (D := D) A L N hA_block)
    (hMPV := hMPV)

end MPSTensor
end MPSChainTensor
