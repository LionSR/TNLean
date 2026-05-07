import TNLean.MPS.Chain.FundamentalTheorem

/-!
# Gauge-phase variant of the injective-chain Fundamental Theorem

If the combined tensors `chainCombinedTensor A` and `chainCombinedTensor B`
are gauge-phase equivalent, i.e. there exist `X ∈ GL(D, ℂ)` and `ζ ≠ 0` with
$$
  (\operatorname{chainCombinedTensor} B)^j
    = \zeta\, X\,(\operatorname{chainCombinedTensor} A)^j\,X^{-1},
$$
then the chains themselves are cyclically gauge equivalent with a common
nonzero phase `ζ` multiplying every site tensor:
$$
  B_k^i = \zeta\, Z_k\, A_k^i\, Z_{k+1}^{-1}.
$$

## Main declarations

* `MPSTensor.chainCombinedTensor_smul_chain`
* `MPSChainTensor.fundamentalTheorem_injective_chain_gaugePhase`
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

/-- **Injective-chain Fundamental Theorem up to gauge phase.**

If `GaugePhaseEquiv (chainCombinedTensor A) (chainCombinedTensor B)` and
`A` is injective, there exist `Z_k ∈ GL(D, ℂ)` and `ζ ≠ 0` such that
$$
  B_k^i = \zeta\, Z_k\, A_k^i\, Z_{k+1}^{-1}
$$
for all sites `k` and physical indices `i`. -/
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
