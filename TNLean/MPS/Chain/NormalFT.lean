import TNLean.MPS.Chain.FundamentalTheorem
import TNLean.MPS.Core.Blocking

/-!
# Blocked-chain endpoint for normal tensors

This module packages the existing injective chain Fundamental Theorem so it can
be applied to chains obtained by physically blocking a single-site tensor.

The project-level normality predicate is `MPSTensor.IsNormal` in
`TNLean/MPS/Defs.lean` (eventual block injectivity via `IsNBlkInjective`).
No duplicate normality definition is introduced here.
-/

open scoped Matrix

namespace MPSChainTensor

variable {d D : ℕ}

/-- Repeat the `L`-blocked tensor across a chain of length `n`. -/
noncomputable def blockedChain (A : MPSTensor d D) (L n : ℕ) :
    MPSChainTensor (MPSTensor.blockPhysDim d L) D n :=
  fun _ => MPSTensor.blockTensor (d := d) (D := D) A L

/-- If the blocked single tensor is injective, the corresponding constant chain
is injective at every site. -/
theorem blockedChain_isInjective (A : MPSTensor d D) (L n : ℕ)
    (hA_block : MPSTensor.IsInjective (MPSTensor.blockTensor (d := d) (D := D) A L)) :
    IsInjective (blockedChain (d := d) (D := D) A L n) := by
  intro k
  simpa [blockedChain] using hA_block

/-- Blocked normal-chain endpoint: apply the injective chain FT to blocked
constant chains.

`hA_block` is the needed block-injectivity hypothesis for the chosen
blocking length `L`; separate normality hypotheses are redundant in this
endpoint theorem. -/
theorem fundamentalTheorem_normal
    (A B : MPSTensor d D) (L n : ℕ)
    (hA_block : MPSTensor.IsInjective (MPSTensor.blockTensor (d := d) (D := D) A L))
    (hMPV : MPSTensor.SameMPV
      (MPSTensor.chainCombinedTensor (blockedChain (d := d) (D := D) A L n))
      (MPSTensor.chainCombinedTensor (blockedChain (d := d) (D := D) B L n))) :
    GaugeEquiv (blockedChain (d := d) (D := D) A L n)
      (blockedChain (d := d) (D := D) B L n) := by
  -- The underlying chain FT only needs injectivity of the left chain.
  exact fundamentalTheorem_injective_chain
    (A := blockedChain (d := d) (D := D) A L n)
    (B := blockedChain (d := d) (D := D) B L n)
    (hA := blockedChain_isInjective (d := d) (D := D) A L n hA_block)
    (hMPV := hMPV)

end MPSChainTensor
