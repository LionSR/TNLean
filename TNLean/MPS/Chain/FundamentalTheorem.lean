/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Chain.AlgebraIsomorphism
import TNLean.MPS.FundamentalTheorem.Basic

/-!
# Fundamental Theorem for injective MPS chains

Two injective MPS chains `A` and `B` whose combined tensors
`chainCombinedTensor A` and `chainCombinedTensor B` generate the same MPV
family are related by cyclic gauge transformations on the virtual bonds.

The hypothesis `SameMPV (chainCombinedTensor A) (chainCombinedTensor B)` is
trace agreement for all mixed-site words of all lengths. The paper passes
from fixed-length `SameState` to this hypothesis via a blocking
argument for `n ≥ 3`; this step is not formalized here.

## References

* [arXiv:1804.04964](https://arxiv.org/abs/1804.04964), Theorem 1
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

/-- **Combined-tensor form of the injective chain Fundamental Theorem**
(Theorem 1 of arXiv:1804.04964).

If `A` and `B` are nonempty chains of positive bond dimension, with `A`
injective and `SameMPV (chainCombinedTensor A) (chainCombinedTensor B)`, then
`A` and `B` are cyclically gauge equivalent. The hypothesis is stated for the combined
tensors, whose physical index in `Fin (n * d)` is identified with a pair
`(k, i)` by `finProdFinEquiv`. The proof produces a uniform gauge (the same
`X ∈ GL(D, ℂ)` at every bond), which is a special case of cyclic gauge
equivalence. -/
theorem fundamentalTheorem_injective_chain
    (A B : MPSChainTensor d D n)
    (hn : 0 < n) (_hD : 0 < D)
    (hA : IsInjective A)
    (hMPV : MPSTensor.SameMPV (MPSTensor.chainCombinedTensor A)
      (MPSTensor.chainCombinedTensor B)) :
    GaugeEquiv A B := by
  /- Note: this formulation only assumes injectivity of `A`. The proof applies
  the single-block theorem to `chainCombinedTensor A`; no separate injectivity
  hypothesis on `B` is required. -/
  have hCA : MPSTensor.IsInjective (MPSTensor.chainCombinedTensor A) :=
    MPSTensor.chainCombinedTensor_isInjective A ⟨0, hn⟩ (hA ⟨0, hn⟩)
  obtain ⟨X, hX⟩ := MPSTensor.fundamentalTheorem_singleBlock hCA hMPV
  exact ⟨fun _ => X, fun k i => by
    have := hX (finProdFinEquiv (k, i))
    simp only [MPSTensor.chainCombinedTensor_apply] at this
    exact this⟩

/-- **Injective-chain Fundamental Theorem up to a nonzero scalar.**

For nonempty chains of positive bond dimension, if
`GaugePhaseEquiv (chainCombinedTensor A) (chainCombinedTensor B)` and `A` is
injective, there exist `Z_k ∈ GL(D, ℂ)` and `ζ ≠ 0` such that
$$
  B_k^i = \zeta\, Z_k\, A_k^i\, Z_{k+1}^{-1}
$$
for all sites `k` and physical indices `i`. -/
theorem fundamentalTheorem_injective_chain_gaugePhase
    (A B : MPSChainTensor d D n)
    (hn : 0 < n) (hD : 0 < D)
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
  obtain ⟨Z, hZ⟩ := fundamentalTheorem_injective_chain A B' hn hD hA hSame
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
