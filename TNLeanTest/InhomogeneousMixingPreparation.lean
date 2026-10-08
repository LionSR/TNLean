import TNLean.MPS.Preparation.InhomogeneousDoeblinPreparation

/-! Exact ordered mixing has zero normalized pair error, including a single block. -/

open Matrix MPSTensor MPSPreparation QuantumCircuit
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Kronecker
  Matrix.Norms.L2Operator

/-! The Gram bound is uniform before choosing the physical dimension, tensor, or PSD reference.
The separate zero-reference check excludes an accidental trace-one or faithfulness requirement. -/

example (D : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ {d : ℕ} (A : MPSTensor d D)
      (σ : Matrix (Fin D) (Fin D) ℂ), σ.PosSemidef →
      ‖(physicalMatrix A)ᴴ * physicalMatrix A -
          σᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)‖ ≤
        K * ‖transferMatrix (Kraus.transferMap A) -
          transferMatrix (Kraus.transferMap (fixedPointTensor σ))‖ := by
  obtain ⟨K, hK, h⟩ := exists_norm_gram_transferMatrix_sub_le D
  exact ⟨K, hK, fun A σ hσ => (h A σ hσ).1⟩

example (D : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ {d : ℕ} (A : MPSTensor d D),
      ‖transferMatrix (Kraus.transferMap A) -
          transferMatrix (Kraus.transferMap (fixedPointTensor (0 : Matrix (Fin D) (Fin D) ℂ)))‖ ≤
        K * ‖(physicalMatrix A)ᴴ * physicalMatrix A‖ := by
  obtain ⟨K, hK, h⟩ := exists_norm_gram_transferMatrix_sub_le D
  refine ⟨K, hK, fun A => ?_⟩
  simpa using (h A 0 Matrix.PosSemidef.zero).2

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

/-! The maximal domination endpoint gives physical preparation without a singular logarithm. -/

example (d D : ℕ) (hd : 0 < d) (A : ∀ N, MPSChainTensor d D N)
    {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef) (htr : σ.trace = 1)
    (htp : ∀ (N : ℕ) [NeZero N] (j : Fin N),
      IsTracePreservingMap (Kraus.transferMap (A N j)))
    (hfix : ∀ (N : ℕ) [NeZero N] (j : Fin N), Kraus.transferMap (A N j) σ = σ)
    (hchoi : ∀ (N : ℕ) [NeZero N] (j : Fin N),
      ChoiRectangular.choiMatrix (Kraus.transferMap (A N j)) ≥
        ((1 : ℂ) / D) • (σ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ))) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (N : ℕ) [NeZero N],
      ∃ (ψ : MPVSpace d N) (T : ℕ), ‖ψ‖ = 1 ∧ (T : ℝ) ≤ C * Real.log (N / ε) ∧
        IsPreparedInDepth T (fun s => ψ s) ∧
        1 - ‖⟪ψ, (‖chainState (A N)‖ : ℂ)⁻¹ • chainState (A N)⟫_ℂ‖ ≤ ε :=
  exists_isPreparedInDepth_inhomogeneous_le_log_of_choi_domination d D hd A hσ htr
    (η := 1) zero_lt_one le_rfl htp hfix (by simpa only [Complex.ofReal_one] using hchoi)

/-! AKLT-type dimensions are undersized at one site but large enough at the compiler threshold. -/

example : (3 : ℕ) ^ 1 < 2 * 2 := by decide

example (q : ℕ) (hq : 3 * 2 ≤ q) : 2 * 2 ≤ 3 ^ q := by
  exact (by decide : 2 * 2 ≤ 3 ^ (3 * 2)).trans
    (Nat.pow_le_pow_right (by decide) hq)

/-! The eventual physical conclusion uses the original family and has no nonzero-target premise. -/

example
    (d D : ℕ) (hd : 0 < d) (A : ∀ N, MPSChainTensor d D N)
    {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef) (htr : σ.trace = 1)
    (K r : ℝ) (hK : 0 < K) (hr : 0 < r)
    (hmix : ∀ (N : ℕ) [NeZero N] {M : ℕ} (ℓ : Fin M → ℕ)
      (hN : ∑ j, ℓ j = N) (j : Fin M), 0 < ℓ j →
      ‖transferMatrix ((List.ofFn fun i : Fin (ℓ j) =>
          Kraus.transferMap (A N (blockSite hN j i))).prod) -
        transferMatrix (Kraus.transferMap (fixedPointTensor σ))‖ ≤
          K * Real.exp (-(r * ℓ j))) :
    ∃ N₀ : ℕ, ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
      ∃ (ψ : MPVSpace d N) (T : ℕ), ‖ψ‖ = 1 ∧ (T : ℝ) ≤ C * Real.log (N / ε) ∧
        IsPreparedInDepth T (fun s => ψ s) ∧
        1 - ‖⟪ψ, (‖chainState (A N)‖ : ℂ)⁻¹ • chainState (A N)⟫_ℂ‖ ≤ ε :=
  exists_isPreparedInDepth_inhomogeneous_le_log_eventually_of_ordered_mixing
    d D hd A hσ htr K r hK hr hmix
