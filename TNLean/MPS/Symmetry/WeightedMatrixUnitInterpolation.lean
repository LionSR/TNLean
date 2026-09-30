/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Defs
import TNLean.MPS.Core.CyclicTrace
import TNLean.MPS.Symmetry.MatrixUnitFixedPoint
import TNLean.MPS.Symmetry.BondInterpolation
import TNLean.MPS.Symmetry.BondRegrouping
import TNLean.MPS.Symmetry.BondInterpolationSymmetry
import TNLean.Algebra.MatrixCyclicPathSum

/-!
# Weighted matrix-unit tensor for the bond interpolation

The normalized bond coefficient matrix gives a family of diagonal weights
`w_a(γ)`. Assigning the physical letter `(a,b)` the matrix `w_a(γ) E_{ab}`
produces the cyclic product of the incoming bond coefficients at every
positive chain length. This is the MPS form of the direct-sum bond path in
Schuch–Pérez-García–Cirac, arXiv:1010.3732, Section II.F.2, equation
`eq:sym:omega-gamma`.

**Local fix (second-block range):** The second block has indices
`D₀+1,\ldots,D₀+D₁`; see
`docs/paper-gaps/spc11_spt_interpolation_upper_range.tex`.
-/

open scoped Matrix

namespace MPSTensor

/-- A matrix-unit MPS whose row index carries the normalized bond weight.
Schuch–Pérez-García–Cirac, arXiv:1010.3732, Section II.F.2,
equation `eq:sym:omega-gamma`. -/
noncomputable def weightedMatrixUnitInterpolation (D₀ D₁ : ℕ) (γ : ℝ) :
    MPSTensor ((D₀ + D₁) * (D₀ + D₁)) (D₀ + D₁) :=
  fun p =>
    normalizedBondInterpolationMatrix D₀ D₁ γ
      (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).1 •
      matrixUnitFixedPoint (D₀ + D₁) p

@[simp]
theorem weightedMatrixUnitInterpolation_apply (D₀ D₁ : ℕ) (γ : ℝ)
    (a b : Fin (D₀ + D₁)) :
    weightedMatrixUnitInterpolation D₀ D₁ γ (finProdFinEquiv (a, b)) =
      normalizedBondInterpolationMatrix D₀ D₁ γ a a •
        Matrix.single a b (1 : ℂ) := by
  simp [weightedMatrixUnitInterpolation]

/-- Each weighted letter is the corresponding matrix unit multiplied on
the left by the diagonal bond coefficient matrix. -/
theorem weightedMatrixUnitInterpolation_eq_left_mul
    (D₀ D₁ : ℕ) (γ : ℝ)
    (p : Fin ((D₀ + D₁) * (D₀ + D₁))) :
    weightedMatrixUnitInterpolation D₀ D₁ γ p =
      normalizedBondInterpolationMatrix D₀ D₁ γ *
        matrixUnitFixedPoint (D₀ + D₁) p := by
  obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective p
  rw [weightedMatrixUnitInterpolation_apply, matrixUnitFixedPoint_apply]
  ext i j
  simp [normalizedBondInterpolationMatrix, bondInterpolationMatrix,
    Matrix.diagonal_mul, Matrix.single_apply]
  by_cases h : a = i ∧ b = j
  · obtain ⟨rfl, rfl⟩ := h
    rfl
  · simp [h]

/-- The weighted matrix-unit tensor is locally covariant under the
physical action induced by the common-factor virtual direct sum.
Schuch–Pérez-García–Cirac, arXiv:1010.3732, Section II.F.2,
equations `eq:sym:omega-gamma` and `eq:1d-sym:jointsym`. -/
theorem twistedTensor_weightedMatrixUnitInterpolation
    {G : Type*} [Group G] {D₀ D₁ : ℕ} {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω)
    (g : G) (γ : ℝ) (p : Fin ((D₀ + D₁) * (D₀ + D₁))) :
    twistedTensor (weightedMatrixUnitInterpolation D₀ D₁ γ)
      (ρ₀.directSum ρ₁).onSiteMatrix g p =
      (ρ₀.directSum ρ₁).adjoint g⁻¹
        (weightedMatrixUnitInterpolation D₀ D₁ γ p) := by
  let ρ := ρ₀.directSum ρ₁
  let W := normalizedBondInterpolationMatrix D₀ D₁ γ
  have hW : Commute W ((ρ.X g⁻¹ : GL (Fin (D₀ + D₁)) ℂ) :
      Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ) := by
    change W * _ = _ * W
    simp only [W, normalizedBondInterpolationMatrix,
      Matrix.smul_mul, Matrix.mul_smul]
    exact congrArg _ (bondInterpolationMatrix_commute_directSum ρ₀ ρ₁ g⁻¹ γ).eq
  have hTw : twistedTensor (weightedMatrixUnitInterpolation D₀ D₁ γ)
      ρ.onSiteMatrix g p =
      W * twistedTensor (matrixUnitFixedPoint (D₀ + D₁)) ρ.onSiteMatrix g p := by
    simp only [twistedTensor, weightedMatrixUnitInterpolation_eq_left_mul,
      Finset.mul_sum, Matrix.mul_smul]
    rfl
  rw [hTw, twistedTensor_matrixUnitFixedPoint]
  rw [weightedMatrixUnitInterpolation_eq_left_mul]
  change W * ((ρ.X g⁻¹ : Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ) *
      matrixUnitFixedPoint (D₀ + D₁) p *
      (((ρ.X g⁻¹)⁻¹ : GL (Fin (D₀ + D₁)) ℂ) : Matrix _ _ ℂ)) =
    (ρ.X g⁻¹ : Matrix _ _ ℂ) *
      (W * matrixUnitFixedPoint (D₀ + D₁) p) *
      (((ρ.X g⁻¹)⁻¹ : GL (Fin (D₀ + D₁)) ℂ) : Matrix _ _ ℂ)
  calc
    W * (((ρ.X g⁻¹ : GL (Fin (D₀ + D₁)) ℂ) : Matrix _ _ ℂ) *
      matrixUnitFixedPoint (D₀ + D₁) p *
      (((ρ.X g⁻¹)⁻¹ : GL (Fin (D₀ + D₁)) ℂ) : Matrix _ _ ℂ)) =
        (W * (ρ.X g⁻¹ : Matrix _ _ ℂ)) *
          matrixUnitFixedPoint (D₀ + D₁) p *
          (((ρ.X g⁻¹)⁻¹ : GL (Fin (D₀ + D₁)) ℂ) : Matrix _ _ ℂ) := by
      simp [Matrix.mul_assoc]
    _ = ((ρ.X g⁻¹ : Matrix _ _ ℂ) * W) *
          matrixUnitFixedPoint (D₀ + D₁) p *
          (((ρ.X g⁻¹)⁻¹ : GL (Fin (D₀ + D₁)) ℂ) : Matrix _ _ ℂ) := by
      rw [hW.eq]
    _ = _ := by simp [Matrix.mul_assoc]

/-- The entire weighted matrix-unit interpolation is symmetric under the
physical representation induced by the common-factor virtual direct sum.
The on-site action is independent of `γ`.
Schuch–Pérez-García–Cirac, arXiv:1010.3732, Section II.F.2,
equations `eq:sym:omega-gamma` and `eq:1d-sym:jointsym`. -/
theorem weightedMatrixUnitInterpolation_isOnSiteSymmetric
    {G : Type*} [Group G] {D₀ D₁ : ℕ} {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω)
    (γ : ℝ) :
    IsOnSiteSymmetric (weightedMatrixUnitInterpolation D₀ D₁ γ)
      (ρ₀.directSum ρ₁).onSiteMatrix := by
  intro g
  apply GaugeEquiv.sameMPV
  exact ⟨(ρ₀.directSum ρ₁).X g⁻¹,
    fun p => twistedTensor_weightedMatrixUnitInterpolation ρ₀ ρ₁ g γ p⟩

/-- Unitary virtual summands induce a unitary physical action throughout
the weighted interpolation. Schuch–Pérez-García–Cirac,
arXiv:1010.3732, Section II.F.2, equation `eq:1d-sym:jointsym`. -/
theorem weightedMatrixUnitInterpolation_physical_unitary
    {G : Type*} [Group G] {D₀ D₁ : ℕ} {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈
      Matrix.unitaryGroup (Fin D₀) ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈
      Matrix.unitaryGroup (Fin D₁) ℂ) (g : G) :
    (ρ₀.directSum ρ₁).onSiteMatrix g ∈
      Matrix.unitaryGroup (Fin ((D₀ + D₁) * (D₀ + D₁))) ℂ := by
  exact (ρ₀.directSum ρ₁).onSiteMatrix_mem_unitaryGroup
    (fun k => ρ₀.directSum_mem_unitaryGroup ρ₁ k (h₀ k) (h₁ k)) g

/-- The weighted MPS tensor depends continuously on the interpolation
parameter when both endpoint bond spaces are nonzero. -/
theorem continuous_weightedMatrixUnitInterpolation {D₀ D₁ : ℕ}
    (h₀ : 0 < D₀) (h₁ : 0 < D₁) :
    Continuous (weightedMatrixUnitInterpolation D₀ D₁) := by
  apply continuous_pi
  intro p
  exact ((continuous_normalizedBondInterpolationMatrix h₀ h₁).matrix_elem
    (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).1).smul continuous_const

/-- At every positive length, the weighted matrix-unit MPV is the product
of its diagonal bond coefficients when the matrix-unit indices close
cyclically, and zero otherwise. This is the trace identity behind the
independent-bond description of Schuch–Pérez-García–Cirac,
arXiv:1010.3732, Section II.F.2. -/
theorem mpv_weightedMatrixUnitInterpolation (D₀ D₁ L : ℕ) (γ : ℝ)
    (σ : Fin (L + 1) → Fin ((D₀ + D₁) * (D₀ + D₁))) :
    let a : Fin (L + 1) → Fin (D₀ + D₁) :=
      fun n => (finProdFinEquiv.symm (σ n)).1
    let b : Fin (L + 1) → Fin (D₀ + D₁) :=
      fun n => (finProdFinEquiv.symm (σ n)).2
    mpv (weightedMatrixUnitInterpolation D₀ D₁ γ) σ =
      if ∀ n, b n = a (finRotate (L + 1) n) then
        ∏ n, normalizedBondInterpolationMatrix D₀ D₁ γ (a n) (a n)
      else 0 := by
  dsimp only
  rw [mpv_eq, coeff_eq, evalWord_ofFn_eq_prod]
  have hletter : (fun n : Fin (L + 1) =>
      weightedMatrixUnitInterpolation D₀ D₁ γ (σ n)) =
      (fun n => normalizedBondInterpolationMatrix D₀ D₁ γ
        (finProdFinEquiv.symm (σ n)).1 (finProdFinEquiv.symm (σ n)).1 •
        Matrix.single (finProdFinEquiv.symm (σ n)).1
          (finProdFinEquiv.symm (σ n)).2 (1 : ℂ)) := by
    funext n
    obtain ⟨⟨a, b⟩, h⟩ := finProdFinEquiv.surjective (σ n)
    rw [← h]
    simp
  rw [hletter, Matrix.trace_ofFn_prod_smul_single]

/-- The positive-length MPV coefficient is the product of independent
incoming-bond amplitudes. The bond joining site `n` to its successor has
matrix entry indexed by the right register at `n` and the left register at
the successor. Schuch–Pérez-García–Cirac, arXiv:1010.3732,
Section II.F.2, equation `eq:sym:omega-gamma`. -/
theorem mpv_weightedMatrixUnitInterpolation_eq_bondProduct
    (D₀ D₁ L : ℕ) (γ : ℝ)
    (σ : Fin (L + 1) → Fin ((D₀ + D₁) * (D₀ + D₁))) :
    mpv (weightedMatrixUnitInterpolation D₀ D₁ γ) σ =
      ∏ n : Fin (L + 1), normalizedBondInterpolationMatrix D₀ D₁ γ
        (finProdFinEquiv.symm (σ n)).2
        (finProdFinEquiv.symm (σ (finRotate (L + 1) n))).1 := by
  let a : Fin (L + 1) → Fin (D₀ + D₁) :=
    fun n => (finProdFinEquiv.symm (σ n)).1
  let b : Fin (L + 1) → Fin (D₀ + D₁) :=
    fun n => (finProdFinEquiv.symm (σ n)).2
  rw [mpv_weightedMatrixUnitInterpolation]
  dsimp only
  split_ifs with h
  · calc
      ∏ n, normalizedBondInterpolationMatrix D₀ D₁ γ (a n) (a n) =
          ∏ n, normalizedBondInterpolationMatrix D₀ D₁ γ
            (a (finRotate (L + 1) n)) (a (finRotate (L + 1) n)) := by
        exact (Equiv.prod_comp (finRotate (L + 1)) _).symm
      _ = ∏ n, normalizedBondInterpolationMatrix D₀ D₁ γ
            (b n) (a (finRotate (L + 1) n)) := by
        apply Finset.prod_congr rfl
        intro n _
        exact congrArg
          (fun x => normalizedBondInterpolationMatrix D₀ D₁ γ x
            (a (finRotate (L + 1) n))) (h n).symm
  · obtain ⟨n, hn⟩ := not_forall.mp h
    symm
    apply (Finset.prod_eq_zero (Finset.mem_univ n))
    have hzero : bondInterpolationMatrix D₀ D₁ γ
        (b n) (a (finRotate (L + 1) n)) = 0 := by
      exact Matrix.diagonal_apply_ne _ hn
    change ((Real.sqrt (bondInterpolationSquaredNorm D₀ D₁ γ) : ℂ)⁻¹) •
      bondInterpolationMatrix D₀ D₁ γ (b n) (a (finRotate (L + 1) n)) = 0
    rw [hzero, smul_zero]

/-- After regrouping the physical registers as incoming bonds, the
positive-length MPV is exactly the product of the bond-vector coordinates.
This is the coefficient identity used to transfer independent-bond parent
Hamiltonians to the MPS physical sites. -/
theorem mpv_weightedMatrixUnitInterpolation_eq_incomingBondProduct
    (D₀ D₁ L : ℕ) (γ : ℝ)
    (σ : Fin (L + 1) → Fin ((D₀ + D₁) * (D₀ + D₁))) :
    mpv (weightedMatrixUnitInterpolation D₀ D₁ γ) σ =
      ∏ i : Fin (L + 1), normalizedBondInterpolationMatrix D₀ D₁ γ
        ((incomingBondEquiv (D₀ + D₁) (L + 1) σ i).1)
        ((incomingBondEquiv (D₀ + D₁) (L + 1) σ i).2) := by
  rw [mpv_weightedMatrixUnitInterpolation_eq_bondProduct]
  rw [← Equiv.prod_comp (finRotate (L + 1))
    (fun i => normalizedBondInterpolationMatrix D₀ D₁ γ
      ((incomingBondEquiv (D₀ + D₁) (L + 1) σ i).1)
      ((incomingBondEquiv (D₀ + D₁) (L + 1) σ i).2))]
  simp [incomingBondEquiv]

/-- The first endpoint state is the product of normalized diagonal bonds
on the first summand, embedded in the common physical alphabet. This is an
identity of positive-length MPV coefficients, rather than a letterwise
identity with a zero-padded smaller tensor. -/
theorem mpv_weightedMatrixUnitInterpolation_zero
    (D₀ D₁ L : ℕ)
    (σ : Fin (L + 1) → Fin ((D₀ + D₁) * (D₀ + D₁))) :
    mpv (weightedMatrixUnitInterpolation D₀ D₁ 0) σ =
      ∏ i : Fin (L + 1),
        let b := incomingBondEquiv (D₀ + D₁) (L + 1) σ i
        if b.1 = b.2 then
          match finSumFinEquiv.symm b.1 with
          | Sum.inl _ => ((Real.sqrt (D₀ : ℝ) : ℂ)⁻¹)
          | Sum.inr _ => 0
        else 0 := by
  rw [mpv_weightedMatrixUnitInterpolation_eq_incomingBondProduct]
  simp only [normalizedBondInterpolationMatrix_zero_apply]
  rfl

/-- The second endpoint state is the product of normalized diagonal bonds
on the second summand, embedded in the same physical alphabet. -/
theorem mpv_weightedMatrixUnitInterpolation_one
    (D₀ D₁ L : ℕ)
    (σ : Fin (L + 1) → Fin ((D₀ + D₁) * (D₀ + D₁))) :
    mpv (weightedMatrixUnitInterpolation D₀ D₁ 1) σ =
      ∏ i : Fin (L + 1),
        let b := incomingBondEquiv (D₀ + D₁) (L + 1) σ i
        if b.1 = b.2 then
          match finSumFinEquiv.symm b.1 with
          | Sum.inl _ => 0
          | Sum.inr _ => ((Real.sqrt (D₁ : ℝ) : ℂ)⁻¹)
        else 0 := by
  rw [mpv_weightedMatrixUnitInterpolation_eq_incomingBondProduct]
  simp only [normalizedBondInterpolationMatrix_one_apply]
  rfl

end MPSTensor
