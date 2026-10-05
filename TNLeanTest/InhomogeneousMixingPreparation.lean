import TNLean.MPS.Preparation.InhomogeneousMixingPreparation

/-! Exact ordered mixing has zero normalized pair error, including a single block. -/

open Matrix MPSTensor MPSPreparation
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

example {D d N M : ℕ} [NeZero M] {σ : Matrix (Fin D) (Fin D) ℂ}
    (hσ : σ.PosDef) (htr : σ.trace = 1) (A : MPSChainTensor d D N)
    (ℓ : Fin M → ℕ) (hN : ∑ j, ℓ j = N)
    (hblock : ∀ j, transferMatrix (Kraus.transferMap (chainBlockTensor A hN j)) =
      transferMatrix (Kraus.transferMap (fixedPointTensor σ)))
    (hwhole : transferMatrix (Kraus.transferMap (MPSChainTensor.blockTensor A)) =
      transferMatrix (Kraus.transferMap (fixedPointTensor σ))) :
    1 - ‖⟪pairFamilyVector (fun _ : Fin M => fixedPointPair σ),
      (‖chainPosState A hN‖ : ℂ)⁻¹ • chainPosState A hN⟫_ℂ‖ ≤ 0 := by
  obtain ⟨C, _, hC⟩ := exists_one_sub_norm_inner_chainPosState_le hσ htr
  have h := hC A ℓ hN (δ := 0) le_rfl
    (fun j => by rw [hblock j, sub_self, norm_zero])
    (by rw [hwhole, sub_self, norm_zero])
  simpa only [mul_zero] using h
