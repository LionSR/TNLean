/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTAlgebraTensorClause
import TNLean.MPS.MPDO.VerticalSectorCoefficientComparison
import TNLean.MPS.SharedInfra.BlockAssembly
import TNLean.MPS.Tactic.Basic

/-!
# Simultaneous operator representations of a blocked vertical tensor

This file develops the two closed-chain representations of the two-site
blocked tensor used in CPSV16, Appendix C.4, lines 2011--2018.  The first
step identifies its vertical reading with the product of two copies of the
one-site vertical tensor.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.4, lines 2011--2018
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

noncomputable section

namespace MPOTensor

variable {d D : ℕ}

/-- The vertical reading of a two-site physical block is the product tensor
of two copies of the one-site vertical reading.

This is the local tensor identity underlying the second representation of
the blocked closed-chain operator in CPSV16, Appendix C.4, lines 2011--2018.
-/
theorem verticalBNTMPO_verticalTensor_blockTwo (M : MPOTensor d D) :
    verticalBNTMPO (verticalTensor (blockTwo M)) =
      mulTensor (verticalBNTMPO (verticalTensor M))
        (verticalBNTMPO (verticalTensor M)) := by
  ext a b x y
  simp [verticalBNTMPO, verticalTensor, blockTwo, mulTensor,
    Matrix.mul_apply, Matrix.sum_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply]


variable {D g : ℕ} {dim mult : Fin g → ℕ}

/-- Closed chains of a vertical assembly split into its weighted sector
closed chains.

This is the block-diagonal expansion used in CPSV16, Appendix C.4, lines
2011--2018. -/
theorem mpo_verticalBNTMPO_verticalAssembledTensor_eq_sum
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (A : (α : Fin g) → MPSTensor (D * D) (dim α)) (L : ℕ) :
    mpo (verticalBNTMPO (verticalAssembledTensor dim mult weight A)) L =
      ∑ α, (∑ q, weight α q ^ L) • mpo (verticalBNTMPO (A α)) L := by
  ext σ τ
  rw [← MPSTensor.mpv_toMPSTensor_pairConfig
    (verticalBNTMPO (verticalAssembledTensor dim mult weight A)) σ τ]
  simp only [verticalBNTMPO_toMPSTensor]
  rw [mpv_verticalAssembledTensor_eq_sum, Fintype.sum_sigma]
  simp only [Matrix.sum_apply, Matrix.smul_apply,
    ← MPSTensor.mpv_toMPSTensor_pairConfig, verticalBNTMPO_toMPSTensor,
    smul_eq_mul, Finset.sum_mul]

/-- A coisometric vertical canonical-form reconstruction gives the weighted
sector expansion of every positive-length closed chain.

Source: CPSV16, Appendix C.4, lines 2011--2018. -/
theorem mpo_verticalBNTMPO_eq_sum_of_coisometry_reconstruction
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (A : (α : Fin g) → MPSTensor (D * D) (dim α))
    (T : MPSTensor (D * D) d)
    (U : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ)
    (hU : U * Uᴴ = 1)
    (hReconstruct : ∀ v,
      T v = Uᴴ * verticalAssembledTensor dim mult weight A v * U)
    {L : ℕ} (hL : 0 < L) :
    mpo (verticalBNTMPO T) L =
      ∑ α, (∑ q, weight α q ^ L) • mpo (verticalBNTMPO (A α)) L := by
  calc
    mpo (verticalBNTMPO T) L =
        mpo (verticalBNTMPO (verticalAssembledTensor dim mult weight A)) L := by
      ext σ τ
      rw [← MPSTensor.mpv_toMPSTensor_pairConfig,
        ← MPSTensor.mpv_toMPSTensor_pairConfig]
      simp only [verticalBNTMPO_toMPSTensor]
      exact MPSTensor.sameMPV₂Pos_of_coisometry_reconstruction
        T (verticalAssembledTensor dim mult weight A) U hU hReconstruct L hL _
    _ = _ := mpo_verticalBNTMPO_verticalAssembledTensor_eq_sum weight A L

/-- Unitary conjugacy after reindexing, with a common scalar on every tensor
letter, multiplies the length-`L` closed-chain operator by the `L`-th power of
that scalar.

This is the gauge-invariance step in CPSV16, Appendix C.4, lines 2011--2018. -/
theorem mpo_verticalBNTMPO_eq_pow_smul_of_unitary_reindex
    {n₁ n₂ : ℕ} (A₁ : MPSTensor (D * D) n₁)
    (A₂ : MPSTensor (D * D) n₂) (c : ℂ) (hDim : n₁ = n₂)
    (V : Matrix.unitaryGroup (Fin n₂) ℂ)
    (hLetter : ∀ ab,
      A₂ ab = c • ((V : Matrix (Fin n₂) (Fin n₂) ℂ) *
        Matrix.reindexAlgEquiv ℂ ℂ (finCongr hDim) (A₁ ab) *
          (V : Matrix (Fin n₂) (Fin n₂) ℂ)ᴴ))
    (L : ℕ) :
    mpo (verticalBNTMPO A₂) L = c ^ L • mpo (verticalBNTMPO A₁) L := by
  classical
  let A₁' : MPSTensor (D * D) n₂ := fun ab =>
    Matrix.reindexAlgEquiv ℂ ℂ (finCongr hDim) (A₁ ab)
  have hReindex : MPSTensor.SameMPV₂ A₁ A₁' := by
    mpv_ext
    simp only [MPSTensor.mpv, MPSTensor.coeff]
    change Matrix.trace (MPSTensor.evalWord A₁ (List.ofFn σ)) =
      Matrix.trace (MPSTensor.evalWord
        (fun ab => Matrix.reindex (finCongr hDim) (finCongr hDim) (A₁ ab))
        (List.ofFn σ))
    rw [MPSTensor.evalWord_reindex, Matrix.trace_reindex]
    simp
  have hScaled (N : ℕ) (σ : Fin N → Fin (D * D)) :
      MPSTensor.mpv A₂ σ = c ^ N * MPSTensor.mpv A₁' σ := by
    have hA₂ : A₂ = fun ab => c • ((V : Matrix (Fin n₂) (Fin n₂) ℂ) *
        A₁' ab * (V : Matrix (Fin n₂) (Fin n₂) ℂ)ᴴ) := by
      funext ab
      exact hLetter ab
    rw [hA₂, MPSTensor.mpv_smul]
    congr 1
    have hGauge := MPSTensor.sameMPV_conj_unitary A₁' (star V)
    simpa only [Unitary.coe_star, star_star, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose] using (hGauge N σ).symm
  ext σ τ
  simp only [Matrix.smul_apply]
  let pair : Fin L → Fin (D * D) := fun n => finProdFinEquiv (σ n, τ n)
  calc
    mpo (verticalBNTMPO A₂) L σ τ = MPSTensor.mpv A₂ pair := by
      simpa [pair] using
        (MPSTensor.mpv_toMPSTensor_pairConfig (verticalBNTMPO A₂) σ τ).symm
    _ = c ^ L * MPSTensor.mpv A₁' pair := hScaled L pair
    _ = c ^ L * MPSTensor.mpv A₁ pair := by rw [hReindex L pair]
    _ = c ^ L * mpo (verticalBNTMPO A₁) L σ τ := by
      rw [← MPSTensor.mpv_toMPSTensor_pairConfig]
      simp [pair]

/-- The two closed-chain representations, given the sector correspondence
and its coefficient comparison.

This is the algebraic assembly of CPSV16, Appendix C.4, lines 2011--2018. -/
theorem blockedVerticalOperatorRepresentations_of_unitaryBlockEquiv
    {g₁ g₂ d D : ℕ}
    (dim₁ mult₁ : Fin g₁ → ℕ)
    (weight₁ : (α : Fin g₁) → Fin (mult₁ α) → ℂ)
    (dim₂ mult₂ : Fin g₂ → ℕ)
    (weight₂ : (β : Fin g₂) → Fin (mult₂ β) → ℂ)
    (M : MPOTensor d D)
    (A₁ : (α : Fin g₁) → MPSTensor (D * D) (dim₁ α))
    (A₂ : (β : Fin g₂) → MPSTensor (D * D) (dim₂ β))
    (U₁ : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g₁, mult₁ α), verticalCopyDim dim₁ mult₁ q))
      (Fin d) ℂ)
    (U₂ : Matrix
      (Fin (∑ q : Fin (∑ β : Fin g₂, mult₂ β), verticalCopyDim dim₂ mult₂ q))
      (Fin (d * d)) ℂ)
    (hU₁ : U₁ * U₁ᴴ = 1)
    (hU₂ : U₂ * U₂ᴴ = 1)
    (hReconstruct₁ : ∀ ab, verticalTensor M ab =
      U₁ᴴ * verticalAssembledTensor dim₁ mult₁ weight₁ A₁ ab * U₁)
    (hReconstruct₂ : ∀ ab, verticalTensor (blockTwo M) ab =
      U₂ᴴ * verticalAssembledTensor dim₂ mult₂ weight₂ A₂ ab * U₂)
    (sigma : Fin g₁ ≃ Fin g₂)
    (hDim : ∀ i, dim₁ i = dim₂ (sigma i))
    (V : ∀ i, Matrix.unitaryGroup (Fin (dim₂ (sigma i))) ℂ)
    (hLetter : ∀ (i : Fin g₁) (ab : Fin (D * D)),
      A₂ (sigma i) ab =
        (verticalMultiplicityTrace weight₁ i /
          verticalMultiplicityTrace weight₂ (sigma i)) •
        ((V i : Matrix (Fin (dim₂ (sigma i))) (Fin (dim₂ (sigma i))) ℂ) *
          Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDim i)) (A₁ i ab) *
          (V i : Matrix (Fin (dim₂ (sigma i))) (Fin (dim₂ (sigma i))) ℂ)ᴴ))
    {L : ℕ} (hL : 0 < L) :
    mpo (verticalBNTMPO (verticalTensor (blockTwo M))) L =
        ∑ i,
          (((verticalMultiplicityTrace weight₁ i /
              verticalMultiplicityTrace weight₂ (sigma i)) ^ L) *
            (∑ q, weight₂ (sigma i) q ^ L)) •
            mpo (verticalBNTMPO (A₁ i)) L ∧
      mpo (verticalBNTMPO (verticalTensor (blockTwo M))) L =
        ∑ i, ∑ j,
          ((∑ q, weight₁ i q ^ L) * (∑ r, weight₁ j r ^ L)) •
            (mpo (verticalBNTMPO (A₁ i)) L *
              mpo (verticalBNTMPO (A₁ j)) L) := by
  have hOne := mpo_verticalBNTMPO_eq_sum_of_coisometry_reconstruction
    weight₁ A₁ (verticalTensor M) U₁ hU₁ hReconstruct₁ hL
  have hTwo := mpo_verticalBNTMPO_eq_sum_of_coisometry_reconstruction
    weight₂ A₂ (verticalTensor (blockTwo M)) U₂ hU₂ hReconstruct₂ hL
  constructor
  · rw [hTwo]
    rw [← sigma.sum_comp]
    apply Finset.sum_congr rfl
    intro i _
    rw [mpo_verticalBNTMPO_eq_pow_smul_of_unitary_reindex
      (A₁ i) (A₂ (sigma i))
      (verticalMultiplicityTrace weight₁ i /
        verticalMultiplicityTrace weight₂ (sigma i))
      (hDim i) (V i) (hLetter i) L]
    rw [smul_smul, mul_comm]
  · rw [verticalBNTMPO_verticalTensor_blockTwo, mpo_mulTensor, hOne]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

/-- The one-site and blocked vertical canonical forms give two simultaneous
representations of the same positive-length blocked closed-chain operator.
The sector relabelling, bond-dimension identifications, and unitary gauges are
the witnesses obtained from the transported vertical-sector comparison.

Source: CPSV16, arXiv:1606.00608, Appendix C.4, lines 2001--2018. The first
conjunct retains the tensor-letter identity of lines 2001--2008; the two
operator representations are lines 2011--2018.

**Local fix (blocked coefficient exponent):** CPSV16 Appendix C.4, line 2013
prints $m_γ^L/n_γ$. The line-2008 tensor scaling and line 2040 give
$(m_γ/n_γ)^L$. Documented in
`docs/paper-gaps/cpsv16_blocked_operator_trace_ratio_exponent.tex`. -/
theorem transportedVerticalSector_exists_blockedOperatorRepresentations
    {g₁ g₂ d D : ℕ}
    (dim₁ mult₁ : Fin g₁ → ℕ)
    (weight₁ : (α : Fin g₁) → Fin (mult₁ α) → ℂ)
    (dim₂ mult₂ : Fin g₂ → ℕ)
    (weight₂ : (β : Fin g₂) → Fin (mult₂ β) → ℂ)
    (hMult₁ : ∀ α, 0 < mult₁ α)
    (hWeight₁ : ∀ α q, (0 : ℂ) < weight₁ α q)
    (hMult₂ : ∀ β, 0 < mult₂ β)
    (hWeight₂ : ∀ β q, (0 : ℂ) < weight₂ β q)
    (M : MPOTensor d D)
    (A₁ : (α : Fin g₁) → MPSTensor (D * D) (dim₁ α))
    (A₂ : (β : Fin g₂) → MPSTensor (D * D) (dim₂ β))
    (hBNT₁ : MPSTensor.IsCPSVBasisOfNormalTensors (verticalTensor M)
      (fun α ↦ ⟨dim₁ α, A₁ α⟩))
    (hBNT₂ : MPSTensor.IsCPSVBasisOfNormalTensors (verticalTensor (blockTwo M))
      (fun β ↦ ⟨dim₂ β, A₂ β⟩))
    (U₁ : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g₁, mult₁ α), verticalCopyDim dim₁ mult₁ q))
      (Fin d) ℂ)
    (U₂ : Matrix
      (Fin (∑ q : Fin (∑ β : Fin g₂, mult₂ β), verticalCopyDim dim₂ mult₂ q))
      (Fin (d * d)) ℂ)
    (hU₁ : U₁ * U₁ᴴ = 1)
    (hU₂ : U₂ * U₂ᴴ = 1)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ)
    (hTCPTP : IsKrausCPTP T)
    (hSCPTP : IsKrausCPTP S)
    (hForward₁ : ∀ ab, U₁ * verticalTensor M ab * U₁ᴴ =
      verticalAssembledTensor dim₁ mult₁ weight₁ A₁ ab)
    (hReconstruct₁ : ∀ ab, verticalTensor M ab =
      U₁ᴴ * verticalAssembledTensor dim₁ mult₁ weight₁ A₁ ab * U₁)
    (hForward₂ : ∀ ab, U₂ * verticalTensor (blockTwo M) ab * U₂ᴴ =
      verticalAssembledTensor dim₂ mult₂ weight₂ A₂ ab)
    (hReconstruct₂ : ∀ ab, verticalTensor (blockTwo M) ab =
      U₂ᴴ * verticalAssembledTensor dim₂ mult₂ weight₂ A₂ ab * U₂)
    (hTphys : ∀ X, T (physClose1 M X) = physClose2 M X)
    (hSphys : ∀ X, S (physClose2 M X) = physClose1 M X)
    {L : ℕ} (hL : 0 < L) :
    ∃ sigma : Fin g₁ ≃ Fin g₂,
      ∃ hDim : ∀ i, dim₁ i = dim₂ (sigma i),
        ∃ V : ∀ i, Matrix.unitaryGroup (Fin (dim₂ (sigma i))) ℂ,
          (∀ (i : Fin g₁) (ab : Fin (D * D)),
            A₂ (sigma i) ab =
              (verticalMultiplicityTrace weight₁ i /
                verticalMultiplicityTrace weight₂ (sigma i)) •
              ((V i : Matrix (Fin (dim₂ (sigma i)))
                  (Fin (dim₂ (sigma i))) ℂ) *
                Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDim i)) (A₁ i ab) *
                (V i : Matrix (Fin (dim₂ (sigma i)))
                  (Fin (dim₂ (sigma i))) ℂ)ᴴ)) ∧
          mpo (verticalBNTMPO (verticalTensor (blockTwo M))) L =
              ∑ i,
                (((verticalMultiplicityTrace weight₁ i /
                    verticalMultiplicityTrace weight₂ (sigma i)) ^ L) *
                  (∑ q, weight₂ (sigma i) q ^ L)) •
                  mpo (verticalBNTMPO (A₁ i)) L ∧
          mpo (verticalBNTMPO (verticalTensor (blockTwo M))) L =
            ∑ i, ∑ j,
              ((∑ q, weight₁ i q ^ L) * (∑ r, weight₁ j r ^ L)) •
                (mpo (verticalBNTMPO (A₁ i)) L *
                  mpo (verticalBNTMPO (A₁ j)) L) := by
  obtain ⟨sigma, hDim, V, _, hLetter⟩ :=
    transportedVerticalSector_exists_unitaryBlockEquiv_coefficient_eq
      dim₁ mult₁ weight₁ dim₂ mult₂ weight₂
      hMult₁ hWeight₁ hMult₂ hWeight₂ M A₁ A₂ hBNT₁ hBNT₂
      U₁ U₂ hU₁ hU₂ T S hTCPTP hSCPTP
      hForward₁ hReconstruct₁ hForward₂ hReconstruct₂ hTphys hSphys
  obtain ⟨hFirst, hSecond⟩ :=
    blockedVerticalOperatorRepresentations_of_unitaryBlockEquiv
      dim₁ mult₁ weight₁ dim₂ mult₂ weight₂ M A₁ A₂ U₁ U₂ hU₁ hU₂
      hReconstruct₁ hReconstruct₂ sigma hDim V hLetter hL
  exact ⟨sigma, hDim, V, hLetter, hFirst, hSecond⟩

end MPOTensor
