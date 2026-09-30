/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.WeightedMatrixUnitInterpolation
import TNLean.MPS.Symmetry.BondProductPhysicalParentHamiltonian
import TNLean.MPS.ParentHamiltonian.PeriodicShortGapContinuity
import TNLean.MPS.Symmetry.PhysicalIsometricEmbedding
import TNLean.MPS.Symmetry.BondProductEndpointGroundSpace

/-!
# Periodic ground states of the bond-product interpolation

The cyclic matrix-product state of the weighted matrix-unit tensor is the
transported product of its bond vectors. This identifies the ground line of
the independent-bond Hamiltonian at every interpolation parameter. At each
endpoint, the cyclic state also agrees with that of the normalized
matrix-unit tensor embedded from the corresponding summand, so its canonical
parent annihilates the same product-bond state. The second endpoint follows
from the first by exchanging the summands.

Source: Schuch--Pérez-García--Cirac, arXiv:1010.3732, Sections II.D.2 and II.F.2.
-/

open scoped Matrix

namespace MPSTensor

private def leftSummandIndex (D₀ D₁ : ℕ) [NeZero D₀]
    (a : Fin (D₀ + D₁)) : Fin D₀ :=
  match finSumFinEquiv.symm a with
  | Sum.inl x => x
  | Sum.inr _ => 0

private noncomputable def leftSummandWeight (D₀ D₁ : ℕ)
    (a : Fin (D₀ + D₁)) : ℂ :=
  match finSumFinEquiv.symm a with
  | Sum.inl _ => (↑(Real.sqrt (D₀ : ℝ)) : ℂ)⁻¹
  | Sum.inr _ => 0

/-- Include a physical matrix-unit label from the first summand in the
common alphabet. Source: arXiv:1010.3732, Section II.F.2. -/
def leftPhysicalIndex (D₀ D₁ : ℕ) :
    Fin (D₀ * D₀) → Fin ((D₀ + D₁) * (D₀ + D₁)) :=
  fun p => finProdFinEquiv
    (finSumFinEquiv (Sum.inl (finProdFinEquiv.symm p).1),
      finSumFinEquiv (Sum.inl (finProdFinEquiv.symm p).2))

/-- Distinct first-summand matrix-unit labels remain distinct in the
common alphabet. Source: arXiv:1010.3732, Section II.F.2. -/
theorem leftPhysicalIndex_injective (D₀ D₁ : ℕ) :
    Function.Injective (leftPhysicalIndex D₀ D₁) := by
  intro p q hpq
  apply finProdFinEquiv.symm.injective
  have h := finProdFinEquiv.injective hpq
  exact Prod.ext
    (Sum.inl_injective (finSumFinEquiv.injective (congrArg Prod.fst h)))
    (Sum.inl_injective (finSumFinEquiv.injective (congrArg Prod.snd h)))

/-- The canonical inclusion of the first summand's physical matrix-unit
alphabet into the common alphabet. Source: arXiv:1010.3732, Section II.F.2,
equation `eq:sym:omega-gamma`. -/
def leftPhysicalIsometry (D₀ D₁ : ℕ) :
    Matrix (Fin ((D₀ + D₁) * (D₀ + D₁))) (Fin (D₀ * D₀)) ℂ :=
  fun p q => if p = leftPhysicalIndex D₀ D₁ q then 1 else 0

/-- Matrix entries of the canonical physical inclusion, in pair
coordinates. Source: arXiv:1010.3732, Section II.F.2. -/
@[simp] theorem leftPhysicalIsometry_apply_pair (D₀ D₁ : ℕ)
    (p : Fin ((D₀ + D₁) * (D₀ + D₁))) (c d : Fin D₀) :
    leftPhysicalIsometry D₀ D₁ p (finProdFinEquiv (c, d)) =
      if p = finProdFinEquiv
        (finSumFinEquiv (Sum.inl c), finSumFinEquiv (Sum.inl d)) then 1 else 0 := by
  change (if p = leftPhysicalIndex D₀ D₁ (finProdFinEquiv (c, d)) then 1 else 0) = _
  have h : leftPhysicalIndex D₀ D₁ (finProdFinEquiv (c, d)) =
      finProdFinEquiv
        (finSumFinEquiv (Sum.inl c), finSumFinEquiv (Sum.inl d)) := by
    simp [leftPhysicalIndex]
  rw [h]

theorem leftPhysicalIsometry_conjTranspose_mul_self (D₀ D₁ : ℕ) :
    (leftPhysicalIsometry D₀ D₁)ᴴ * leftPhysicalIsometry D₀ D₁ = 1 := by
  ext p q
  simp [Matrix.mul_apply, leftPhysicalIsometry, Matrix.one_apply,
    (leftPhysicalIndex_injective D₀ D₁).eq_iff, eq_comm]

/-- The normalized diagonal bond of the first summand is the image of the
matrix-unit bond under the physical inclusion. Source: arXiv:1010.3732,
Section II.D.2, equation `eq:phase-nosym:iso-hamiltonian`. -/
theorem leftPhysicalIsometry_mulVec_matrixUnitBondVector
    (D₀ D₁ : ℕ) :
    leftPhysicalIsometry D₀ D₁ *ᵥ matrixUnitBondVector D₀ =
      normalizedBondInterpolationVector D₀ D₁ 0 := by
  funext p
  obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective p
  simp only [Matrix.mulVec, dotProduct, leftPhysicalIsometry,
    normalizedBondInterpolationVector]
  rw [normalizedBondInterpolationMatrix_zero_apply]
  cases ha : finSumFinEquiv.symm a with
  | inl x =>
    cases hb : finSumFinEquiv.symm b with
    | inl y =>
      have ha' : a = finSumFinEquiv (Sum.inl x) := by
        simpa using congrArg finSumFinEquiv ha
      have hb' : b = finSumFinEquiv (Sum.inl y) := by
        simpa using congrArg finSumFinEquiv hb
      rw [ha', hb']
      simp only [ite_mul, one_mul, zero_mul]
      let q₀ := finProdFinEquiv (x, y)
      have hq₀ : finProdFinEquiv
          (finSumFinEquiv (Sum.inl x), finSumFinEquiv (Sum.inl y)) =
          leftPhysicalIndex D₀ D₁ q₀ := by
        simp [q₀, leftPhysicalIndex]
      have hsum : (∑ q : Fin (D₀ * D₀),
          if finProdFinEquiv
            (finSumFinEquiv (Sum.inl x), finSumFinEquiv (Sum.inl y)) =
              leftPhysicalIndex D₀ D₁ q then matrixUnitBondVector D₀ q else 0) =
          matrixUnitBondVector D₀ q₀ := by
        calc
          _ = if finProdFinEquiv
                (finSumFinEquiv (Sum.inl x), finSumFinEquiv (Sum.inl y)) =
                leftPhysicalIndex D₀ D₁ q₀ then matrixUnitBondVector D₀ q₀ else 0 := by
              apply Finset.sum_eq_single q₀
              · intro q _ hne
                have hneq : finProdFinEquiv
                    (finSumFinEquiv (Sum.inl x), finSumFinEquiv (Sum.inl y)) ≠
                    leftPhysicalIndex D₀ D₁ q := by
                  intro h
                  apply hne
                  exact ((leftPhysicalIndex_injective D₀ D₁) (hq₀.symm.trans h)).symm
                have hneq' : finProdFinEquiv
                    (Fin.castAdd D₁ x, Fin.castAdd D₁ y) ≠
                    leftPhysicalIndex D₀ D₁ q := by
                  simpa using hneq
                simp [hneq']
              · simp
          _ = _ := by
            have hq₀' : finProdFinEquiv
                (Fin.castAdd D₁ x, Fin.castAdd D₁ y) =
                leftPhysicalIndex D₀ D₁ q₀ := by
              simpa using hq₀
            simp [hq₀']
      rw [hsum]
      simp [q₀, matrixUnitBondVector_apply]
    | inr y =>
      have hb' : b = finSumFinEquiv (Sum.inr y) := by
        simpa using congrArg finSumFinEquiv hb
      have hp : ∀ q : Fin (D₀ * D₀),
          finProdFinEquiv (a, b) ≠ leftPhysicalIndex D₀ D₁ q := by
        intro q h
        have hcol := congrArg (fun z => (finProdFinEquiv.symm z).2) h
        have hcol' : finSumFinEquiv (Sum.inr y) =
            finSumFinEquiv (Sum.inl (finProdFinEquiv.symm q).2) := by
          simpa [leftPhysicalIndex, hb'] using hcol
        cases finSumFinEquiv.injective hcol'
      have hne : a ≠ b := by
        intro h
        have h' := congrArg finSumFinEquiv.symm h
        simp [ha, hb] at h'
      simp only [ite_mul, one_mul, zero_mul]
      calc
        (∑ q, if finProdFinEquiv (a, b) = leftPhysicalIndex D₀ D₁ q then
            matrixUnitBondVector D₀ q else 0) = 0 :=
          Finset.sum_eq_zero (fun q _ => by simp [hp q])
        _ = _ := by simp [hne]
  | inr x =>
    have ha' : a = finSumFinEquiv (Sum.inr x) := by
      simpa using congrArg finSumFinEquiv ha
    have hp : ∀ q : Fin (D₀ * D₀),
        finProdFinEquiv (a, b) ≠ leftPhysicalIndex D₀ D₁ q := by
      intro q h
      have hrow := congrArg (fun z => (finProdFinEquiv.symm z).1) h
      have hrow' : finSumFinEquiv (Sum.inr x) =
          finSumFinEquiv (Sum.inl (finProdFinEquiv.symm q).1) := by
        simpa [leftPhysicalIndex, ha'] using hrow
      cases finSumFinEquiv.injective hrow'
    have hp' : ∀ q : Fin (D₀ * D₀),
        finProdFinEquiv (Fin.natAdd D₀ x, b) ≠ leftPhysicalIndex D₀ D₁ q := by
      simpa [ha'] using hp
    simp [ha', hp']

/-- The first matrix-unit summand, embedded in the common physical
alphabet and normalized by the square root of its bond dimension. Source:
arXiv:1010.3732, Section II.F.2, equation `eq:sym:omega-gamma`. -/
noncomputable def leftEmbeddedMatrixUnitFixedPoint (D₀ D₁ : ℕ)
    [NeZero D₀] : MPSTensor ((D₀ + D₁) * (D₀ + D₁)) D₀ :=
  fun p =>
    (if (finSumFinEquiv.symm (finProdFinEquiv.symm p).2).isLeft then
      leftSummandWeight D₀ D₁ (finProdFinEquiv.symm p).1 else 0) •
      Matrix.single
        (leftSummandIndex D₀ D₁ (finProdFinEquiv.symm p).1)
        (leftSummandIndex D₀ D₁ (finProdFinEquiv.symm p).2) (1 : ℂ)

/-- The explicit endpoint tensor is the canonical physical isometric
embedding of the normalized matrix-unit tensor on the first summand. Source:
arXiv:1010.3732, Sections II.D.2 and II.F.2. -/
theorem leftEmbeddedMatrixUnitFixedPoint_eq_physicalEmbedding
    (D₀ D₁ : ℕ) [NeZero D₀] :
    leftEmbeddedMatrixUnitFixedPoint D₀ D₁ =
      fun p => ∑ q : Fin (D₀ * D₀),
        leftPhysicalIsometry D₀ D₁ p q •
          ((↑(Real.sqrt (D₀ : ℝ)) : ℂ)⁻¹ • matrixUnitFixedPoint D₀ q) := by
  funext p
  obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective p
  cases ha : finSumFinEquiv.symm a with
  | inl x =>
    cases hb : finSumFinEquiv.symm b with
    | inl y =>
      have ha' : a = finSumFinEquiv (Sum.inl x) := by
        simpa using congrArg finSumFinEquiv ha
      have hb' : b = finSumFinEquiv (Sum.inl y) := by
        simpa using congrArg finSumFinEquiv hb
      have hp : finProdFinEquiv (a, b) =
          leftPhysicalIndex D₀ D₁ (finProdFinEquiv (x, y)) := by
        rw [ha', hb']
        simp [leftPhysicalIndex]
      rw [hp]
      simp only [leftEmbeddedMatrixUnitFixedPoint, leftPhysicalIsometry,
        leftPhysicalIndex_injective D₀ D₁ |>.eq_iff]
      simp [leftSummandWeight, leftSummandIndex, leftPhysicalIndex,
        matrixUnitFixedPoint_apply]
    | inr y =>
      have hb' : b = finSumFinEquiv (Sum.inr y) := by
        simpa using congrArg finSumFinEquiv hb
      have hp : ∀ q : Fin (D₀ * D₀),
          finProdFinEquiv (a, b) ≠ leftPhysicalIndex D₀ D₁ q := by
        intro q h
        have hcol := congrArg (fun z => (finProdFinEquiv.symm z).2) h
        have hcol' : finSumFinEquiv (Sum.inr y) =
            finSumFinEquiv (Sum.inl (finProdFinEquiv.symm q).2) := by
          simpa [leftPhysicalIndex, hb'] using hcol
        cases finSumFinEquiv.injective hcol'
      have hzero : leftEmbeddedMatrixUnitFixedPoint D₀ D₁
          (finProdFinEquiv (a, b)) = 0 := by
        simp [leftEmbeddedMatrixUnitFixedPoint, hb']
      rw [hzero]
      exact (Finset.sum_eq_zero (fun q _ => by
        simp [leftPhysicalIsometry, hp q])).symm
  | inr x =>
    have ha' : a = finSumFinEquiv (Sum.inr x) := by
      simpa using congrArg finSumFinEquiv ha
    have hp : ∀ q : Fin (D₀ * D₀),
        finProdFinEquiv (a, b) ≠ leftPhysicalIndex D₀ D₁ q := by
      intro q h
      have hrow := congrArg (fun z => (finProdFinEquiv.symm z).1) h
      have hrow' : finSumFinEquiv (Sum.inr x) =
          finSumFinEquiv (Sum.inl (finProdFinEquiv.symm q).1) := by
        simpa [leftPhysicalIndex, ha'] using hrow
      cases finSumFinEquiv.injective hrow'
    have hzero : leftEmbeddedMatrixUnitFixedPoint D₀ D₁
        (finProdFinEquiv (a, b)) = 0 := by
      simp [leftEmbeddedMatrixUnitFixedPoint, leftSummandWeight, ha']
    rw [hzero]
    exact (Finset.sum_eq_zero (fun q _ => by
      simp [leftPhysicalIsometry, hp q])).symm

/-- The first embedded endpoint remains one-site injective. Source:
arXiv:1010.3732, Section II.D.2. -/
theorem leftEmbeddedMatrixUnitFixedPoint_isInjective
    (D₀ D₁ : ℕ) [NeZero D₀] :
    Kraus.IsInjective (leftEmbeddedMatrixUnitFixedPoint D₀ D₁) := by
  rw [leftEmbeddedMatrixUnitFixedPoint_eq_physicalEmbedding]
  apply isInjective_kraus_isometry
    (fun q : Fin (D₀ * D₀) =>
      (↑(Real.sqrt (D₀ : ℝ)) : ℂ)⁻¹ • matrixUnitFixedPoint D₀ q)
    (leftPhysicalIsometry D₀ D₁)
    (leftPhysicalIsometry_conjTranspose_mul_self D₀ D₁)
  apply (matrixUnitFixedPoint_isInjective D₀).smul
  exact inv_ne_zero (by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast NeZero.pos D₀))))

private theorem mpv_leftEmbeddedMatrixUnitFixedPoint
    (D₀ D₁ L : ℕ) [NeZero D₀]
    (σ : Fin (L + 1) → Fin ((D₀ + D₁) * (D₀ + D₁))) :
    let a : Fin (L + 1) → Fin (D₀ + D₁) :=
      fun n => (finProdFinEquiv.symm (σ n)).1
    let b : Fin (L + 1) → Fin (D₀ + D₁) :=
      fun n => (finProdFinEquiv.symm (σ n)).2
    mpv (leftEmbeddedMatrixUnitFixedPoint D₀ D₁) σ =
      if ∀ n, leftSummandIndex D₀ D₁ (b n) =
          leftSummandIndex D₀ D₁ (a (finRotate (L + 1) n)) then
        ∏ n, if (finSumFinEquiv.symm (b n)).isLeft then
          leftSummandWeight D₀ D₁ (a n) else 0
      else 0 := by
  dsimp only
  rw [mpv_eq, coeff_eq, evalWord_ofFn_eq_prod]
  change (List.ofFn fun n : Fin (L + 1) =>
    (if (finSumFinEquiv.symm (finProdFinEquiv.symm (σ n)).2).isLeft then
      leftSummandWeight D₀ D₁ (finProdFinEquiv.symm (σ n)).1 else 0) •
      Matrix.single
        (leftSummandIndex D₀ D₁ (finProdFinEquiv.symm (σ n)).1)
        (leftSummandIndex D₀ D₁ (finProdFinEquiv.symm (σ n)).2)
        (1 : ℂ)).prod.trace = _
  rw [Matrix.trace_ofFn_prod_smul_single]

private theorem leftSummandWeight_eq_normalizedBondInterpolationMatrix_zero
    (D₀ D₁ : ℕ) (a : Fin (D₀ + D₁)) :
    leftSummandWeight D₀ D₁ a =
      normalizedBondInterpolationMatrix D₀ D₁ 0 a a := by
  rw [normalizedBondInterpolationMatrix_zero_apply]
  simp only [↓reduceIte]
  rfl

private theorem leftSummandIndex_eq_iff {D₀ D₁ : ℕ} [NeZero D₀]
    {a b : Fin (D₀ + D₁)}
    (ha : (finSumFinEquiv.symm a).isLeft)
    (hb : (finSumFinEquiv.symm b).isLeft) :
    leftSummandIndex D₀ D₁ a = leftSummandIndex D₀ D₁ b ↔ a = b := by
  obtain ⟨x, rfl⟩ : ∃ x : Fin D₀, a = finSumFinEquiv (Sum.inl x) := by
    cases h : finSumFinEquiv.symm a with
    | inl x => exact ⟨x, by simpa using congrArg finSumFinEquiv h⟩
    | inr x => simp [h] at ha
  obtain ⟨y, rfl⟩ : ∃ y : Fin D₀, b = finSumFinEquiv (Sum.inl y) := by
    cases h : finSumFinEquiv.symm b with
    | inl y => exact ⟨y, by simpa using congrArg finSumFinEquiv h⟩
    | inr y => simp [h] at hb
  simp [leftSummandIndex]

/-- At the first endpoint, mixed-summand letters contribute to open words
but disappear from every cyclic trace. -/
theorem mpv_leftEmbeddedMatrixUnitFixedPoint_eq_weighted_zero
    (D₀ D₁ L : ℕ) [NeZero D₀]
    (σ : Fin (L + 1) → Fin ((D₀ + D₁) * (D₀ + D₁))) :
    mpv (leftEmbeddedMatrixUnitFixedPoint D₀ D₁) σ =
      mpv (weightedMatrixUnitInterpolation D₀ D₁ 0) σ := by
  let a : Fin (L + 1) → Fin (D₀ + D₁) :=
    fun n => (finProdFinEquiv.symm (σ n)).1
  let b : Fin (L + 1) → Fin (D₀ + D₁) :=
    fun n => (finProdFinEquiv.symm (σ n)).2
  rw [mpv_leftEmbeddedMatrixUnitFixedPoint,
    mpv_weightedMatrixUnitInterpolation]
  dsimp only
  change (if ∀ n, leftSummandIndex D₀ D₁ (b n) =
      leftSummandIndex D₀ D₁ (a (finRotate (L + 1) n)) then
      ∏ n, if (finSumFinEquiv.symm (b n)).isLeft then
        leftSummandWeight D₀ D₁ (a n) else 0 else 0) =
    if ∀ n, b n = a (finRotate (L + 1) n) then
      ∏ n, normalizedBondInterpolationMatrix D₀ D₁ 0 (a n) (a n) else 0
  by_cases h : ∀ n, b n = a (finRotate (L + 1) n)
  · have hd : ∀ n, leftSummandIndex D₀ D₁ (b n) =
        leftSummandIndex D₀ D₁ (a (finRotate (L + 1) n)) :=
      fun n => congrArg _ (h n)
    simp only [ite_eq_left h, ite_eq_left hd]
    by_cases ha : ∀ n, (finSumFinEquiv.symm (a n)).isLeft
    · apply Finset.prod_congr rfl
      intro n _
      have hb : (finSumFinEquiv.symm (b n)).isLeft := by
        rw [h n]
        exact ha _
      simp only [ite_eq_left hb]
      exact leftSummandWeight_eq_normalizedBondInterpolationMatrix_zero D₀ D₁ (a n)
    · obtain ⟨n, hn⟩ := not_forall.mp ha
      obtain ⟨m, hm⟩ := (finRotate (L + 1)).surjective n
      have hb : ¬ (finSumFinEquiv.symm (b m)).isLeft := by
        rw [h m, hm]
        exact hn
      have hleft : (∏ n, if (finSumFinEquiv.symm (b n)).isLeft then
          leftSummandWeight D₀ D₁ (a n) else 0) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ m) (by simp [hb])
      have hweight : normalizedBondInterpolationMatrix D₀ D₁ 0 (a n) (a n) = 0 := by
        rw [← leftSummandWeight_eq_normalizedBondInterpolationMatrix_zero]
        cases hs : finSumFinEquiv.symm (a n) with
        | inl x => simp [hs] at hn
        | inr x => simp [leftSummandWeight, hs]
      rw [hleft, Finset.prod_eq_zero (Finset.mem_univ n) hweight]
  · simp only [ite_eq_right h]
    by_cases hd : ∀ n, leftSummandIndex D₀ D₁ (b n) =
        leftSummandIndex D₀ D₁ (a (finRotate (L + 1) n))
    · simp only [ite_eq_left hd]
      have hbad : ¬ ∀ n, (finSumFinEquiv.symm (a n)).isLeft ∧
          (finSumFinEquiv.symm (b n)).isLeft := by
        intro hall
        apply h
        intro n
        exact (leftSummandIndex_eq_iff (hall _).2 (hall _).1).mp (hd n)
      obtain ⟨n, hn⟩ := not_forall.mp hbad
      have hz : (if (finSumFinEquiv.symm (b n)).isLeft then
          leftSummandWeight D₀ D₁ (a n) else 0) = 0 := by
        by_cases hb : (finSumFinEquiv.symm (b n)).isLeft
        · have ha : ¬ (finSumFinEquiv.symm (a n)).isLeft := by
            exact fun h₁ => hn ⟨h₁, hb⟩
          simp only [ite_eq_left hb]
          cases hs : finSumFinEquiv.symm (a n) with
          | inl x => simp [hs] at ha
          | inr x => simp [leftSummandWeight, hs]
        · simp [hb]
      exact Finset.prod_eq_zero (Finset.mem_univ n) hz
    · simp only [ite_eq_right hd]

private theorem incomingBondUnitaryLin_bondProductState_apply
    (D N : ℕ) (η : Fin (D * D) → ℂ)
    (σ : Fin N → Fin (D * D)) :
    incomingBondUnitaryLin D N (bondProductState η N) σ =
      ∏ i : Fin N, η (finProdFinEquiv (incomingBondEquiv D N σ i)) := by
  simp [incomingBondUnitaryLin, bondMatrixEquiv_symm_eq_toEuclideanLin,
    Matrix.permMatrix_mulVec,
    bondProductState, bondProductVector, incomingBondPerm]

/-- The weighted matrix-unit state is the independent-bond product state,
regrouped into physical-site coordinates. -/
theorem weightedMatrixUnitInterpolation_mpv_eq_bondProductState
    (D₀ D₁ L : ℕ) (γ : ℝ) :
    (WithLp.linearEquiv 2 ℂ
      (NSiteSpace ((D₀ + D₁) * (D₀ + D₁)) (L + 1))).symm
      (mpv (weightedMatrixUnitInterpolation D₀ D₁ γ)) =
    incomingBondUnitaryLin (D₀ + D₁) (L + 1)
      (bondProductState (normalizedBondInterpolationVector D₀ D₁ γ) (L + 1)) := by
  ext σ
  rw [incomingBondUnitaryLin_bondProductState_apply]
  simpa [normalizedBondInterpolationVector, PiLp.toLp_apply] using
    mpv_weightedMatrixUnitInterpolation_eq_incomingBondProduct D₀ D₁ L γ σ

/-- At every positive chain length, the independent-bond Hamiltonian has
the same ground line as the weighted matrix-unit MPS. This remains valid at
the endpoints, where the weighted tensor is not injective. -/
theorem normalizedPhysicalBondInterpolation_groundSpace_eq_weightedMpvLine
    {D₀ D₁ : ℕ} (h₀ : 0 < D₀) (h₁ : 0 < D₁)
    (γ : ℝ) (L : ℕ) :
    LinearMap.ker (physicalBondProductParentHamiltonianLin
      (normalizedBondInterpolationVector D₀ D₁ γ) (by omega : 1 ≤ L + 1)) =
      (periodicMpvLineMap
        (weightedMatrixUnitInterpolation D₀ D₁ γ) (L + 1)).range := by
  rw [normalizedPhysicalBondInterpolation_parent_groundSpace h₀ h₁ γ
    (by omega : 1 ≤ L + 1)]
  rw [← weightedMatrixUnitInterpolation_mpv_eq_bondProductState]
  simp only [periodicMpvLineMap]
  rw [ContinuousLinearMap.range_smulRight_apply
    (by norm_num : (1 : ℂ →L[ℂ] ℂ) ≠ 0)]

/-- The first embedded summand's periodic parent Hamiltonian annihilates
the first endpoint bond-product state. Source: arXiv:1010.3732,
Section II.F.2, equation `eq:sym:omega-gamma`. -/
theorem leftEmbeddedMatrixUnitFixedPoint_parent_annihilates_bondProductState
    (D₀ D₁ L : ℕ) [NeZero D₀] :
    parentHamiltonianES (leftEmbeddedMatrixUnitFixedPoint D₀ D₁) 2 (L + 2)
      (incomingBondUnitaryLin (D₀ + D₁) (L + 2)
        (bondProductState (normalizedBondInterpolationVector D₀ D₁ 0) (L + 2))) =
      0 := by
  let e := WithLp.linearEquiv 2 ℂ
    (NSiteSpace ((D₀ + D₁) * (D₀ + D₁)) (L + 2))
  have hstate : incomingBondUnitaryLin (D₀ + D₁) (L + 2)
      (bondProductState (normalizedBondInterpolationVector D₀ D₁ 0) (L + 2)) =
      e.symm (mpv (leftEmbeddedMatrixUnitFixedPoint D₀ D₁)) := by
    rw [← weightedMatrixUnitInterpolation_mpv_eq_bondProductState D₀ D₁ (L + 1) 0]
    apply congrArg e.symm
    funext σ
    exact (mpv_leftEmbeddedMatrixUnitFixedPoint_eq_weighted_zero D₀ D₁ (L + 1) σ).symm
  rw [hstate]
  change e.symm (parentHamiltonian (leftEmbeddedMatrixUnitFixedPoint D₀ D₁)
    2 (L + 2) (e (e.symm (mpv (leftEmbeddedMatrixUnitFixedPoint D₀ D₁))))) = 0
  rw [e.apply_symm_apply,
    parentHamiltonian_annihilates (leftEmbeddedMatrixUnitFixedPoint D₀ D₁) 2 (L + 2)
      (by omega : 2 ≤ L + 2)]
  rfl

/-- Every periodic ground state of the first endpoint bond-product
Hamiltonian is annihilated by the embedded summand parent Hamiltonian.
Source: arXiv:1010.3732, Section II.F.2. -/
theorem normalizedPhysicalBondInterpolation_zero_ker_le_leftEmbedded_parent_ker
    (D₀ D₁ L : ℕ) [NeZero D₀] (h₁ : 0 < D₁) :
    LinearMap.ker (physicalBondProductParentHamiltonianLin
      (normalizedBondInterpolationVector D₀ D₁ 0)
      (by omega : 1 ≤ L + 2)) ≤
    LinearMap.ker (parentHamiltonianES
      (leftEmbeddedMatrixUnitFixedPoint D₀ D₁) 2 (L + 2)) := by
  rw [normalizedPhysicalBondInterpolation_parent_groundSpace (NeZero.pos D₀) h₁ 0
    (by omega : 1 ≤ L + 2)]
  apply Submodule.span_le.mpr
  intro v hv
  have hv' : v = incomingBondUnitaryLin (D₀ + D₁) (L + 2)
      (bondProductState (normalizedBondInterpolationVector D₀ D₁ 0) (L + 2)) :=
    Set.mem_singleton_iff.mp hv
  subst v
  exact LinearMap.mem_ker.mpr
    (leftEmbeddedMatrixUnitFixedPoint_parent_annihilates_bondProductState D₀ D₁ L)

private def flipPhysicalIndex (D₀ D₁ : ℕ) :
    Fin ((D₀ + D₁) * (D₀ + D₁)) →
      Fin ((D₁ + D₀) * (D₁ + D₀)) :=
  fun p => finProdFinEquiv
    (finAddFlip (finProdFinEquiv.symm p).1,
      finAddFlip (finProdFinEquiv.symm p).2)

private def flipPhysicalEquiv (D₀ D₁ : ℕ) :
    Fin ((D₀ + D₁) * (D₀ + D₁)) ≃
      Fin ((D₁ + D₀) * (D₁ + D₀)) :=
  (finProdFinEquiv :
    (Fin (D₀ + D₁) × Fin (D₀ + D₁)) ≃
      Fin ((D₀ + D₁) * (D₀ + D₁))).symm |>.trans
    ((finAddFlip : Fin (D₀ + D₁) ≃ Fin (D₁ + D₀)).prodCongr
      (finAddFlip : Fin (D₀ + D₁) ≃ Fin (D₁ + D₀))) |>.trans
    finProdFinEquiv

private theorem flipPhysicalEquiv_apply (D₀ D₁ : ℕ)
    (p : Fin ((D₀ + D₁) * (D₀ + D₁))) :
    flipPhysicalEquiv D₀ D₁ p = flipPhysicalIndex D₀ D₁ p := rfl

private theorem normalizedBondInterpolationMatrix_one_flip
    (D₀ D₁ : ℕ) (a b : Fin (D₀ + D₁)) :
    normalizedBondInterpolationMatrix D₀ D₁ 1 a b =
      normalizedBondInterpolationMatrix D₁ D₀ 0
        (finAddFlip a) (finAddFlip b) := by
  rw [normalizedBondInterpolationMatrix_one_apply,
    normalizedBondInterpolationMatrix_zero_apply]
  cases ha : finSumFinEquiv.symm a with
  | inl x =>
    cases hb : finSumFinEquiv.symm b with
    | inl y => simp [finAddFlip, ha, hb]
    | inr y => simp [finAddFlip, ha, hb]
  | inr x =>
    cases hb : finSumFinEquiv.symm b with
    | inl y =>
      have ha' : a = finSumFinEquiv (Sum.inr x) := by
        simpa using congrArg finSumFinEquiv ha
      have hb' : b = finSumFinEquiv (Sum.inl y) := by
        simpa using congrArg finSumFinEquiv hb
      rw [ha', hb']
      have hleft : Fin.natAdd D₀ x ≠ Fin.castAdd D₁ y := by
        intro h
        have h' := congrArg finSumFinEquiv.symm h
        simp at h'
      have hright : Fin.castAdd D₀ x ≠ Fin.natAdd D₁ y := by
        intro h
        have h' := congrArg finSumFinEquiv.symm h
        simp at h'
      simp [finAddFlip, hleft, hright]
    | inr y =>
      have ha' : a = finSumFinEquiv (Sum.inr x) := by
        simpa using congrArg finSumFinEquiv ha
      have hb' : b = finSumFinEquiv (Sum.inr y) := by
        simpa using congrArg finSumFinEquiv hb
      rw [ha', hb']
      simp [finAddFlip]

/-- The second embedded summand is the first embedded summand after
exchanging the two virtual blocks and relabelling the physical alphabet.
Source: arXiv:1010.3732, Section II.F.2, equation `eq:sym:omega-gamma`. -/
noncomputable def rightEmbeddedMatrixUnitFixedPoint (D₀ D₁ : ℕ)
    [NeZero D₁] : MPSTensor ((D₀ + D₁) * (D₀ + D₁)) D₁ :=
  Kraus.reindexPhysical (flipPhysicalIndex D₀ D₁)
    (leftEmbeddedMatrixUnitFixedPoint D₁ D₀)

/-- The physical isometry embedding the second normalized matrix-unit
summand is the first inclusion after exchanging the two blocks. Source:
arXiv:1010.3732, Section II.F.2, equation `eq:sym:omega-gamma`. -/
def rightPhysicalIsometry (D₀ D₁ : ℕ) :
    Matrix (Fin ((D₀ + D₁) * (D₀ + D₁))) (Fin (D₁ * D₁)) ℂ :=
  fun p q => leftPhysicalIsometry D₁ D₀ (flipPhysicalEquiv D₀ D₁ p) q

theorem rightPhysicalIsometry_conjTranspose_mul_self (D₀ D₁ : ℕ) :
    (rightPhysicalIsometry D₀ D₁)ᴴ * rightPhysicalIsometry D₀ D₁ = 1 := by
  ext p q
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    rightPhysicalIsometry]
  have hsum := Equiv.sum_comp (flipPhysicalEquiv D₀ D₁)
    (fun j => star (leftPhysicalIsometry D₁ D₀ j p) *
      leftPhysicalIsometry D₁ D₀ j q)
  rw [hsum]
  exact congrArg (fun M : Matrix (Fin (D₁ * D₁)) (Fin (D₁ * D₁)) ℂ => M p q)
    (leftPhysicalIsometry_conjTranspose_mul_self D₁ D₀)

/-- The second endpoint tensor is the physical isometric embedding of
the normalized matrix-unit tensor on the second summand. Source:
arXiv:1010.3732, Sections II.D.2 and II.F.2. -/
theorem rightEmbeddedMatrixUnitFixedPoint_eq_physicalEmbedding
    (D₀ D₁ : ℕ) [NeZero D₁] :
    rightEmbeddedMatrixUnitFixedPoint D₀ D₁ =
      fun p => ∑ q : Fin (D₁ * D₁),
        rightPhysicalIsometry D₀ D₁ p q •
          ((↑(Real.sqrt (D₁ : ℝ)) : ℂ)⁻¹ • matrixUnitFixedPoint D₁ q) := by
  funext p
  change leftEmbeddedMatrixUnitFixedPoint D₁ D₀ (flipPhysicalIndex D₀ D₁ p) = _
  rw [leftEmbeddedMatrixUnitFixedPoint_eq_physicalEmbedding]
  rfl

/-- The second embedded endpoint remains one-site injective. Source:
arXiv:1010.3732, Section II.D.2. -/
theorem rightEmbeddedMatrixUnitFixedPoint_isInjective
    (D₀ D₁ : ℕ) [NeZero D₁] :
    Kraus.IsInjective (rightEmbeddedMatrixUnitFixedPoint D₀ D₁) := by
  rw [rightEmbeddedMatrixUnitFixedPoint_eq_physicalEmbedding]
  apply isInjective_kraus_isometry
    (fun q : Fin (D₁ * D₁) =>
      (↑(Real.sqrt (D₁ : ℝ)) : ℂ)⁻¹ • matrixUnitFixedPoint D₁ q)
    (rightPhysicalIsometry D₀ D₁)
    (rightPhysicalIsometry_conjTranspose_mul_self D₀ D₁)
  apply (matrixUnitFixedPoint_isInjective D₁).smul
  exact inv_ne_zero (by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast NeZero.pos D₁))))

private theorem mpv_weightedMatrixUnitInterpolation_one_flip
    (D₀ D₁ L : ℕ)
    (σ : Fin (L + 1) → Fin ((D₀ + D₁) * (D₀ + D₁))) :
    mpv (weightedMatrixUnitInterpolation D₀ D₁ 1) σ =
      mpv (weightedMatrixUnitInterpolation D₁ D₀ 0)
        (fun n => flipPhysicalIndex D₀ D₁ (σ n)) := by
  rw [mpv_weightedMatrixUnitInterpolation_eq_bondProduct,
    mpv_weightedMatrixUnitInterpolation_eq_bondProduct]
  apply Finset.prod_congr rfl
  intro n _
  simpa [flipPhysicalIndex] using
    normalizedBondInterpolationMatrix_one_flip D₀ D₁
      (finProdFinEquiv.symm (σ n)).2
      (finProdFinEquiv.symm (σ (finRotate (L + 1) n))).1

/-- The cyclic state of the second embedded summand agrees with the
second endpoint of the weighted bond path. Source: arXiv:1010.3732,
Section II.F.2, equation `eq:sym:omega-gamma`. -/
theorem mpv_rightEmbeddedMatrixUnitFixedPoint_eq_weighted_one
    (D₀ D₁ L : ℕ) [NeZero D₁]
    (σ : Fin (L + 1) → Fin ((D₀ + D₁) * (D₀ + D₁))) :
    mpv (rightEmbeddedMatrixUnitFixedPoint D₀ D₁) σ =
      mpv (weightedMatrixUnitInterpolation D₀ D₁ 1) σ := by
  rw [rightEmbeddedMatrixUnitFixedPoint, mpv_reindexPhysical,
    mpv_leftEmbeddedMatrixUnitFixedPoint_eq_weighted_zero,
    mpv_weightedMatrixUnitInterpolation_one_flip]

/-- The second embedded summand's periodic parent Hamiltonian annihilates
the second endpoint bond-product state. Source: arXiv:1010.3732,
Section II.F.2, equation `eq:sym:omega-gamma`. -/
theorem rightEmbeddedMatrixUnitFixedPoint_parent_annihilates_bondProductState
    (D₀ D₁ L : ℕ) [NeZero D₁] :
    parentHamiltonianES (rightEmbeddedMatrixUnitFixedPoint D₀ D₁) 2 (L + 2)
      (incomingBondUnitaryLin (D₀ + D₁) (L + 2)
        (bondProductState (normalizedBondInterpolationVector D₀ D₁ 1) (L + 2))) =
      0 := by
  let e := WithLp.linearEquiv 2 ℂ
    (NSiteSpace ((D₀ + D₁) * (D₀ + D₁)) (L + 2))
  have hstate : incomingBondUnitaryLin (D₀ + D₁) (L + 2)
      (bondProductState (normalizedBondInterpolationVector D₀ D₁ 1) (L + 2)) =
      e.symm (mpv (rightEmbeddedMatrixUnitFixedPoint D₀ D₁)) := by
    rw [← weightedMatrixUnitInterpolation_mpv_eq_bondProductState D₀ D₁ (L + 1) 1]
    apply congrArg e.symm
    funext σ
    exact (mpv_rightEmbeddedMatrixUnitFixedPoint_eq_weighted_one D₀ D₁ (L + 1) σ).symm
  rw [hstate]
  change e.symm (parentHamiltonian (rightEmbeddedMatrixUnitFixedPoint D₀ D₁)
    2 (L + 2) (e (e.symm (mpv (rightEmbeddedMatrixUnitFixedPoint D₀ D₁))))) = 0
  rw [e.apply_symm_apply,
    parentHamiltonian_annihilates (rightEmbeddedMatrixUnitFixedPoint D₀ D₁) 2 (L + 2)
      (by omega : 2 ≤ L + 2)]
  rfl

/-- Every periodic ground state of the second endpoint bond-product
Hamiltonian is annihilated by the embedded summand parent Hamiltonian.
Source: arXiv:1010.3732, Section II.F.2. -/
theorem normalizedPhysicalBondInterpolation_one_ker_le_rightEmbedded_parent_ker
    (D₀ D₁ L : ℕ) [NeZero D₁] (h₀ : 0 < D₀) :
    LinearMap.ker (physicalBondProductParentHamiltonianLin
      (normalizedBondInterpolationVector D₀ D₁ 1)
      (by omega : 1 ≤ L + 2)) ≤
    LinearMap.ker (parentHamiltonianES
      (rightEmbeddedMatrixUnitFixedPoint D₀ D₁) 2 (L + 2)) := by
  rw [normalizedPhysicalBondInterpolation_parent_groundSpace h₀ (NeZero.pos D₁) 1
    (by omega : 1 ≤ L + 2)]
  apply Submodule.span_le.mpr
  intro v hv
  have hv' : v = incomingBondUnitaryLin (D₀ + D₁) (L + 2)
      (bondProductState (normalizedBondInterpolationVector D₀ D₁ 1) (L + 2)) :=
    Set.mem_singleton_iff.mp hv
  subst v
  exact LinearMap.mem_ker.mpr
    (rightEmbeddedMatrixUnitFixedPoint_parent_annihilates_bondProductState D₀ D₁ L)


end MPSTensor
