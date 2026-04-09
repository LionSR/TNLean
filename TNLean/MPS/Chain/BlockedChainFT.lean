import TNLean.MPS.Core.Blocking
import TNLean.MPS.Chain.FundamentalTheorem

/-!
# Fundamental theorem endpoint for blocked chains

This module gives a blocked-chain endpoint. The theorem
`fundamentalTheorem_blockedChain` is stated for blocked chains built from a
common blocking length `L`.

Design note: we keep the endpoint in explicit-assumption style (`L`, `hA_block`,
`hMPV`) so downstream uses can choose blocking witnesses locally.
-/

namespace MPSTensor

variable {d D : ℕ}

/-- Equivalence between project `N`-block injectivity and injectivity of the physically
blocked tensor `blockTensor A N`. -/
lemma isNBlkInjective_iff_blockTensor_isInjective (A : MPSTensor d D) (N : ℕ) :
    IsNBlkInjective A N ↔ IsInjective (blockTensor A N) := by
  classical
  have hRange :
      Set.range (fun i : Fin (blockPhysDim d N) =>
        evalWord A (List.ofFn (decodeBlock d N i))) =
        Set.range (fun σ : Fin N → Fin d => evalWord A (List.ofFn σ)) := by
    ext M
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨decodeBlock d N i, rfl⟩
    · rintro ⟨σ, rfl⟩
      exact ⟨(Fintype.equivFin (Fin N → Fin d)) σ, by
        simp [decodeBlock]⟩
  unfold IsNBlkInjective IsInjective blockTensor
  have hSpan :
      Submodule.span ℂ
          (Set.range fun i : Fin (blockPhysDim d N) =>
            evalWord A (List.ofFn (decodeBlock d N i))) =
        Submodule.span ℂ (Set.range fun σ : Fin N → Fin d => evalWord A (List.ofFn σ)) := by
    simp [hRange]
  constructor
  · intro h
    exact hSpan.trans h
  · intro h
    exact hSpan.symm.trans h

end MPSTensor

namespace MPSChainTensor

variable {d D : ℕ}

/-- Constant blocked chain obtained by repeating `blockTensor A L` at every site. -/
noncomputable def blockedChain (A : MPSTensor d D) (L n : ℕ) :
    MPSChainTensor (MPSTensor.blockPhysDim d L) D n :=
  fun _ => MPSTensor.blockTensor A L

/-- If `A` is `L`-block injective, then the constant chain of `L`-blocked tensors
is injective at every site. -/
lemma blockedChain_isInjective (A : MPSTensor d D) (L n : ℕ)
    (hA : MPSTensor.IsNBlkInjective A L) :
    IsInjective (blockedChain A L n) := by
  intro k
  simpa [blockedChain] using
    (MPSTensor.isNBlkInjective_iff_blockTensor_isInjective A L).1 hA

/-- Fundamental theorem endpoint for blocked chains at a common blocking length.

The hypothesis `hA_block` chooses a witness `L` used in the blocked-chain
reduction to the injective-chain theorem. -/
theorem fundamentalTheorem_blockedChain
    (A B : MPSTensor d D) (L n : ℕ)
    (hA_block : MPSTensor.IsNBlkInjective A L)
    (hMPV : MPSTensor.SameMPV
      (MPSTensor.chainCombinedTensor (blockedChain A L n))
      (MPSTensor.chainCombinedTensor (blockedChain B L n))) :
    GaugeEquiv (blockedChain A L n) (blockedChain B L n) :=
  fundamentalTheorem_injective_chain
    (blockedChain A L n)
    (blockedChain B L n)
    (blockedChain_isInjective A L n hA_block)
    hMPV

end MPSChainTensor
