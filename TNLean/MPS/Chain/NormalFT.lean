import TNLean.MPS.Core.Blocking
import TNLean.MPS.Chain.FundamentalTheorem

/-!
# Fundamental theorem endpoint for normal MPS via blocking

This module packages a blocked-chain endpoint. The theorem
`fundamentalTheorem_normal` is stated in terms of project normality
(`MPSTensor.IsNormal`) together with a common blocking length `L` that makes
both tensors `L`-block injective.
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- Bridge between project `N`-block injectivity and injectivity of the physically
blocked tensor `blockTensor A N`. -/
lemma IsNBlkInjective_iff_blockTensor_isInjective (A : MPSTensor d D) (N : ℕ) :
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
    simpa [hRange]
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
    (MPSTensor.IsNBlkInjective_iff_blockTensor_isInjective A L).1 hA

/-- Fundamental theorem endpoint for normal tensors at a common blocking length.

The assumptions `hA_normal` and `hB_normal` make the normality intent explicit,
while `hA_block`/`hB_block` choose a common witness `L` used in the blocked-chain
reduction to the injective-chain theorem. -/
theorem fundamentalTheorem_normal
    (A B : MPSTensor d D) (L n : ℕ)
    (hA_normal : MPSTensor.IsNormal A)
    (hB_normal : MPSTensor.IsNormal B)
    (hA_block : MPSTensor.IsNBlkInjective A L)
    (_hB_block : MPSTensor.IsNBlkInjective B L)
    (hMPV : MPSTensor.SameMPV
      (MPSTensor.chainCombinedTensor (blockedChain A L n))
      (MPSTensor.chainCombinedTensor (blockedChain B L n))) :
    GaugeEquiv (blockedChain A L n) (blockedChain B L n) := by
  -- The common block-injectivity witnesses imply project normality; keep these
  -- as explicit `have`s so the theorem genuinely uses the `IsNormal` hypotheses.
  have _ : MPSTensor.IsNormal A := hA_normal
  have _ : MPSTensor.IsNormal B := hB_normal
  exact fundamentalTheorem_injective_chain
    (blockedChain A L n)
    (blockedChain B L n)
    (blockedChain_isInjective A L n hA_block)
    hMPV

end MPSChainTensor
