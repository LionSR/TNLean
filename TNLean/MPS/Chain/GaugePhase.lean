import TNLean.MPS.Chain.FundamentalTheorem

/-!
# Gauge-phase variant of the injective-chain Fundamental Theorem

This file upgrades the exact injective-chain Fundamental Theorem to the case
where the two **combined tensors** agree only up to a nonzero scalar.  The
result is the chain-level contraction statement needed in periodic Case 3:
from a gauge-phase equivalence between `chainCombinedTensor A` and
`chainCombinedTensor B`, one recovers a cyclic gauge on the underlying chain
together with a **common** nonzero phase on every site.

## Main declarations

* `MPSTensor.chainCombinedTensor_smul_chain`
* `MPSChainTensor.fundamentalTheorem_injective_chain_gaugePhase`

## Mathematical idea

If $\widetilde A$ and $\widetilde B$ denote the combined tensors of `A` and
`B`, and if
$$
\widetilde B = \zeta \cdot X \, \widetilde A \, X^{-1},
$$
then rescaling every site tensor of `B` by `ζ⁻¹` removes the global scalar on
its combined tensor.  The exact chain Fundamental Theorem then applies to the
rescaled chain, and multiplying the site relations back by `ζ` gives the
required cyclic gauge-phase relation.
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- Rescaling every site tensor in a chain rescales the combined tensor by the
same scalar. -/
theorem chainCombinedTensor_smul_chain {n : ℕ}
    (A : Fin n → MPSTensor d D) (ζ : ℂ) :
    chainCombinedTensor (fun k i => ζ • A k i) = ζ • chainCombinedTensor A := by
  funext j
  simp [chainCombinedTensor]

end MPSTensor

namespace MPSChainTensor

open MPSTensor

variable {d D n : ℕ}

/-- **Injective-chain contraction up to phase.**

If the combined tensors of two chains are gauge-phase equivalent, then the
chains themselves are cyclically gauge equivalent with one common nonzero phase
`ζ` multiplying every site tensor of `A`.

This is the finite-chain `$m$-factor cyclic contraction` used by the periodic
Case-3 program: once a cyclic family of sector-transition tensors is
formulated as an injective chain and the corresponding combined tensors are
known to satisfy `GaugePhaseEquiv`, the conclusion recovers sitewise
proportionality with a cyclic gauge. -/
theorem fundamentalTheorem_injective_chain_gaugePhase
    (A B : MPSChainTensor d D n)
    (hA : IsInjective A)
    (hGauge : MPSTensor.GaugePhaseEquiv
      (MPSTensor.chainCombinedTensor A)
      (MPSTensor.chainCombinedTensor B)) :
    ∃ Z : Fin n → GL (Fin D) ℂ,
      ∃ ζ : ℂ, ζ ≠ 0 ∧
        ∀ k : Fin n, ∀ i : Fin d,
          B k i =
            ζ • ((Z k : Matrix (Fin D) (Fin D) ℂ) * A k i *
              (((Z (cyclicSucc k))⁻¹ : GL (Fin D) ℂ) :
                Matrix (Fin D) (Fin D) ℂ)) := by
  rcases hGauge with ⟨X, ζ, hζ, hX⟩
  let B' : MPSChainTensor d D n := fun k i => ζ⁻¹ • B k i
  have hCombinedGauge :
      MPSTensor.GaugeEquiv
        (MPSTensor.chainCombinedTensor A)
        (MPSTensor.chainCombinedTensor B') := by
    refine ⟨X, ?_⟩
    intro j
    calc
      MPSTensor.chainCombinedTensor B' j
          = ζ⁻¹ • MPSTensor.chainCombinedTensor B j := by
              simpa [B'] using
                congrFun (MPSTensor.chainCombinedTensor_smul_chain (A := B) (ζ := ζ⁻¹)) j
      _ = ζ⁻¹ •
            (ζ • ((X : Matrix (Fin D) (Fin D) ℂ) *
              MPSTensor.chainCombinedTensor A j *
              ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))) := by
            rw [hX j]
      _ = ((X : Matrix (Fin D) (Fin D) ℂ) * MPSTensor.chainCombinedTensor A j *
            ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) := by
            simp [smul_smul, hζ]
  have hSame :
      MPSTensor.SameMPV
        (MPSTensor.chainCombinedTensor A)
        (MPSTensor.chainCombinedTensor B') :=
    MPSTensor.GaugeEquiv.sameMPV hCombinedGauge
  obtain ⟨Z, hZ⟩ := fundamentalTheorem_injective_chain A B' hA hSame
  refine ⟨Z, ζ, hζ, ?_⟩
  intro k i
  calc
    B k i
        = ζ • B' k i := by
            simp [B', smul_smul, hζ]
    _ = ζ •
          ((Z k : Matrix (Fin D) (Fin D) ℂ) * A k i *
            (((Z (cyclicSucc k))⁻¹ : GL (Fin D) ℂ) :
              Matrix (Fin D) (Fin D) ℂ)) := by
          rw [hZ k i]

end MPSChainTensor
