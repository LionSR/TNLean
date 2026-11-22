/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.StandardFormFromGates
import TNLean.MPS.MPU.StandardFormInterpolation
import TNLean.MPS.MPU.CanonicalFormAncillaBlocking
import TNLean.MPS.CanonicalForm.ProjectorClosureSpectral
import QICLean.Algebra.Matrix.MatrixSingleSpan
import QICLean.Channel.Schmidt.Rank

/-!
# A tensor in canonical form for given standard-form gates

Given unitary gates `u : ℂ^d ⊗ ℂ^d → ℂ^ℓ ⊗ ℂ^r` and `v : ℂ^r ⊗ ℂ^ℓ → ℂ^d ⊗ ℂ^d`, the two-layer
circuit of `u` on unshifted pairs and `v` on shifted pairs is a matrix product unitary on the
chain of pairs (arXiv:1703.09188, equation `StandardForm`, lines 603--617). This file constructs
a tensor on pairs, in canonical form (lines 258--267), whose standard form has exactly the gates
`u, v` and whose periodic operators are those of the circuit.

The bond of the tensor is the operator-Schmidt rank `K` of `v` across the cut separating
`(i₁, s)` from `(i₂, t)`. A full-rank factorization of `v` into half factors `X₁, X₂` gives the
tensor `tensorOfHalves X₁ X₂ u`. Its letters are
`W^{(i₁,i₂), j} = ∑_{t,s} u((t,s), j) · x_{i₁,t} y_{i₂,s}ᵀ`, where the vectors `x` (columns of
`X₂`) span `ℂ^K` and the vectors `y` (rows of `X₁`) span its dual, because the factorization has
full rank. Since `u` is invertible, the letters span all `K × K` matrices. The tensor is therefore
injective, hence irreducible, and rescaling by the square root of the Perron eigenvalue of its
transfer map gives a canonical block.

## Main results

* `MPSTensor.isMPUCanonicalForm_of_isIrreducibleFamily`: a nonzero irreducible tensor is in
  canonical form, with one block.
* `MPOTensor.exists_isMPUCanonicalForm_twoSiteStandardFormData`: for unitary gates `u, v`, a tensor
  in canonical form with standard form `(u, v)` and the periodic operators of
  `standardFormTensorOfGates u v`.
-/

open scoped Matrix
open Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- **A nonzero irreducible tensor is in canonical form**, with one block. The transfer map has a
positive Perron eigenvalue `r` with a positive-definite eigenvector, and `r^{-1/2} A` is an
irreducible block with transfer spectral radius one; `A` is that block with weight `r^{1/2}`.

Source: arXiv:1703.09188, canonical form, lines 258--267, with the normalization of the blocks;
the Perron eigenvalue is Wolf, Theorem 6.3. -/
theorem isMPUCanonicalForm_of_isIrreducibleFamily [NeZero D] (A : MPSTensor d D)
    (hIrr : Kraus.IsIrreducibleFamily A) (hA : ∃ i, A i ≠ 0) : IsMPUCanonicalForm A := by
  obtain ⟨ρ, r, hρ, hr, hEig⟩ := exists_posDef_transferMap_eigenvector_of_irreducible A hIrr hA
  set c : ℂ := ((Real.sqrt r : ℝ) : ℂ)
  have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hr).ne'
  have hr_ne : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hcc : c⁻¹ * starRingEnd ℂ c⁻¹ = (r : ℂ)⁻¹ := by
    rw [map_inv₀, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
      Real.mul_self_sqrt hr.le]
  have hfix : Kraus.transferMap (ι := Fin d) (n := Fin D) (fun i => c⁻¹ • A i) ρ = ρ := by
    rw [transferMap_smul, hcc, hEig, smul_smul, inv_mul_cancel₀ hr_ne, one_smul]
  have hIrrScaled : Kraus.IsIrreducibleFamily (fun i => c⁻¹ • A i) :=
    isIrreducibleTensor_smul (inv_ne_zero hc) A hIrr
  have hblock : IsMPUCanonicalBlock (fun i => c⁻¹ • A i) := by
    refine ⟨hIrrScaled, ?_⟩
    simpa using
      (spectralRadius_eq_of_posDef_eigenvector_of_irreducible_cp
        (Kraus.transferMap (ι := Fin d) (n := Fin D) (fun i => c⁻¹ • A i))
        (Kraus.transferMap_isCPMap _)
        (Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily _ hIrrScaled)
        ρ 1 hρ (by norm_num) (by simpa using hfix))
  obtain ⟨data⟩ := hblock.isMPUCanonicalForm
  have hA' : (fun i => c • (c⁻¹ • A i)) = A := by
    funext i
    rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
  exact hA' ▸ ⟨data.smul c hc⟩

end MPSTensor

namespace MPOTensor

variable {d ℓ r : ℕ}

/-- The shifted gate as a matrix across the cut separating `(i₁, s)` from `(i₂, t)`. -/
def shiftedGateCut (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ) :
    Matrix (Fin d × Fin r) (Fin d × Fin ℓ) ℂ :=
  fun p q => v (p.1, q.1) (p.2, q.2)

/-- The letters of the tensor of half factors, as sums of outer products. -/
private theorem tensorOfHalves_apply_finProd {K : ℕ} (X₁ : Matrix (Fin d × Fin K) (Fin r) ℂ)
    (X₂ : Matrix (Fin K × Fin d) (Fin ℓ) ℂ) (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ)
    (i₁ i₂ : Fin d) (j : Fin d × Fin d) :
    tensorOfHalves X₁ X₂ u (finProdFinEquiv (i₁, i₂)) (finProdFinEquiv j) =
      ∑ t : Fin ℓ, ∑ s : Fin r, u (t, s) j •
        Matrix.vecMulVec (fun α => X₂ (α, i₁) t) (fun γ => X₁ (i₂, γ) s) := by
  ext α γ
  simp only [tensorOfHalves, Equiv.symm_apply_apply, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

/-- Pairing the letters with the conjugate row `(t, s)` of the coisometric gate `u` isolates one
outer product of half-factor columns. -/
private theorem sum_star_smul_tensorOfHalves {K : ℕ} (X₁ : Matrix (Fin d × Fin K) (Fin r) ℂ)
    (X₂ : Matrix (Fin K × Fin d) (Fin ℓ) ℂ) (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ)
    (hu : u * uᴴ = 1) (i₁ i₂ : Fin d) (t : Fin ℓ) (s : Fin r) :
    (∑ j : Fin d × Fin d, star (u (t, s) j) •
        tensorOfHalves X₁ X₂ u (finProdFinEquiv (i₁, i₂)) (finProdFinEquiv j)) =
      Matrix.vecMulVec (fun α => X₂ (α, i₁) t) (fun γ => X₁ (i₂, γ) s) := by
  have hδ : ∀ (t' : Fin ℓ) (s' : Fin r),
      (∑ j : Fin d × Fin d, star (u (t, s) j) * u (t', s') j) =
        if (t', s') = (t, s) then 1 else 0 := fun t' s' ↦ by
    have h := congrFun (congrFun hu (t', s')) (t, s)
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at h
    rw [← h]
    exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
  ext α γ
  simp only [tensorOfHalves_apply_finProd, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul]
  calc (∑ j : Fin d × Fin d, star (u (t, s) j) *
        ∑ t' : Fin ℓ, ∑ s' : Fin r, u (t', s') j * (X₂ (α, i₁) t' * X₁ (i₂, γ) s'))
      = ∑ t' : Fin ℓ, ∑ s' : Fin r,
          (∑ j : Fin d × Fin d, star (u (t, s) j) * u (t', s') j) *
            (X₂ (α, i₁) t' * X₁ (i₂, γ) s') := by
        simp_rw [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun t' _ ↦ ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
    _ = X₂ (α, i₁) t * X₁ (i₂, γ) s := by
        simp_rw [hδ, Prod.mk.injEq, ite_and, ite_mul, one_mul, zero_mul]
        simp [Finset.sum_ite_eq']

/-- A full-rank matrix `C : K × n` has a right inverse column for every coordinate. -/
private theorem exists_mulVec_eq_single {n : Type*} [Fintype n] {K : ℕ}
    (C : Matrix (Fin K) n ℂ) (hC : K ≤ C.rank) (a : Fin K) :
    ∃ w : n → ℂ, C *ᵥ w = Pi.single a 1 := by
  have htop : LinearMap.range C.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    apply le_antisymm (Submodule.finrank_le _)
    simpa [Matrix.rank] using hC
  obtain ⟨w, hw⟩ := (LinearMap.range_eq_top.mp htop) (Pi.single a 1)
  exact ⟨w, hw⟩

/-- **A tensor in canonical form with given standard-form gates.** For unitary gates `u, v`, there
is a tensor `W` on pairs of sites, in canonical form, with a standard form whose gates are exactly
`u, v`, and with the periodic operators of the circuit of `u` on unshifted and `v` on shifted
pairs, that is, of `standardFormTensorOfGates u v`, at every positive length. Its bond dimension
is the operator-Schmidt rank of `v` across the cut separating `(i₁, s)` from `(i₂, t)`.

Source: arXiv:1703.09188, equation `StandardForm` and Definition `SF`, lines 603--622, and the
canonical form, lines 258--267. -/
theorem exists_isMPUCanonicalForm_twoSiteStandardFormData [NeZero d] [NeZero ℓ] [NeZero r]
    (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ) (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ)
    (hu : u.IsUnitaryBetween) (hv : v.IsUnitaryBetween) :
    ∃ (K : ℕ) (W : MPOTensor (d * d) K),
      MPSTensor.IsMPUCanonicalForm W.toMPSTensor ∧ Nonempty (TwoSiteStandardFormData W u v) ∧
        ∀ N : ℕ, 0 < N → mpo W N = mpo (standardFormTensorOfGates u v) N := by
  classical
  set V := shiftedGateCut v
  set K := V.rank
  obtain ⟨B, C, hBC⟩ := Matrix.exists_mul_eq_of_rank_le V (le_refl K)
  set X₁ : Matrix (Fin d × Fin K) (Fin r) ℂ := fun p s => B (p.1, s) p.2
  set X₂ : Matrix (Fin K × Fin d) (Fin ℓ) ℂ := fun p t => C p.1 (p.2, t)
  set W := tensorOfHalves X₁ X₂ u
  -- The shifted gate is not zero, so its rank is positive.
  have hv0 : v ≠ 0 := by
    intro h0
    have h1 : vᴴ * v = 1 := hv.1
    rw [h0, Matrix.mul_zero] at h1
    have := congrFun (congrFun h1 (0, 0)) (0, 0)
    simp at this
  have hK : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · exfalso
      apply hv0
      have hV0 : V = 0 := by
        rw [← hBC]
        ext p q
        simp only [Matrix.mul_apply, Matrix.zero_apply]
        exact Finset.sum_eq_zero fun k _ ↦ absurd k.2 (by omega)
      ext p q
      have := congrFun (congrFun hV0 (p.1, q.1)) (p.2, q.2)
      simpa [V, shiftedGateCut] using this
    · exact h
  have : NeZero K := ⟨hK.ne'⟩
  -- The standard form.
  have hvapply : ∀ (i₁ i₂ : Fin d) (s : Fin r) (t : Fin ℓ),
      v (i₁, i₂) (s, t) = ∑ β : Fin K, X₁ (i₁, β) s * X₂ (β, i₂) t := fun i₁ i₂ s t ↦ by
    have := congrFun (congrFun hBC (i₁, s)) (i₂, t)
    simp only [Matrix.mul_apply] at this
    simpa [V, shiftedGateCut, X₁, X₂] using this.symm
  let S : TwoSiteStandardFormData W u v :=
    { phys_pos := NeZero.pos d
      bond_pos := hK
      left_pos := NeZero.pos ℓ
      right_pos := NeZero.pos r
      X₁ := X₁
      X₂ := X₂
      u_unitary := hu
      v_unitary := hv
      v_apply := hvapply
      W_apply := fun _ _ _ _ ↦ rfl }
  refine ⟨K, W, ?_, ⟨S⟩, fun N hN ↦
    TwoSiteStandardFormData.mpo_eq_of_same_gates S
      (standardFormTensorOfGatesData u v hu hv) N hN⟩
  -- Full rank of the two factors.
  have hrankC : K ≤ C.rank := by
    calc K = (B * C).rank := by rw [hBC]
      _ ≤ C.rank := Matrix.rank_mul_le_right B C
  have hrankB : K ≤ Bᵀ.rank := by
    calc K = (B * C).rank := by rw [hBC]
      _ ≤ B.rank := Matrix.rank_mul_le_left B C
      _ = Bᵀ.rank := (Matrix.rank_transpose B).symm
  -- The letters span every matrix unit.
  have hinj : Kraus.IsInjective W.toMPSTensor := by
    refine Submodule.eq_top_of_forall_single_mem _ fun a b ↦ ?_
    set T := Submodule.span ℂ (Set.range W.toMPSTensor)
    have hletter : ∀ (i₁ i₂ : Fin d) (j : Fin d × Fin d),
        W (finProdFinEquiv (i₁, i₂)) (finProdFinEquiv j) ∈ T := fun i₁ i₂ j ↦ by
      refine Submodule.subset_span ⟨finProdFinEquiv (finProdFinEquiv (i₁, i₂),
        finProdFinEquiv j), ?_⟩
      simp [toMPSTensor]
    -- Each outer product of a column of `X₂` with a row of `X₁` is in the span.
    have houter : ∀ (i₁ i₂ : Fin d) (t : Fin ℓ) (s : Fin r),
        Matrix.vecMulVec (fun α => X₂ (α, i₁) t) (fun γ => X₁ (i₂, γ) s) ∈ T := by
      intro i₁ i₂ t s
      have hsum := sum_star_smul_tensorOfHalves X₁ X₂ u hu.2 i₁ i₂ t s
      rw [← hsum]
      exact Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ (hletter i₁ i₂ j)
    obtain ⟨w, hw⟩ := exists_mulVec_eq_single C hrankC a
    obtain ⟨w', hw'⟩ := exists_mulVec_eq_single Bᵀ hrankB b
    have hunit : Matrix.single a b (1 : ℂ) = ∑ p : Fin d × Fin ℓ, ∑ q : Fin d × Fin r,
        (w p * w' q) • Matrix.vecMulVec (fun α => X₂ (α, p.1) p.2) (fun γ => X₁ (q.1, γ) q.2) := by
      ext α γ
      have hsingle : Matrix.single a b (1 : ℂ) α γ =
          (Pi.single a (1 : ℂ) : Fin K → ℂ) α * (Pi.single b (1 : ℂ) : Fin K → ℂ) γ := by
        rcases eq_or_ne α a with rfl | h₁
        · rcases eq_or_ne γ b with rfl | h₂
          · simp
          · simp [h₂, h₂.symm]
        · simp [h₁, h₁.symm]
      have h1 := congrFun hw α
      have h2 := congrFun hw' γ
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply] at h1 h2
      simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul,
        X₁, X₂]
      calc Matrix.single a b (1 : ℂ) α γ
          = (Pi.single a (1 : ℂ) : Fin K → ℂ) α * (Pi.single b (1 : ℂ) : Fin K → ℂ) γ := hsingle
        _ = (∑ p, C α p * w p) * (∑ q, B q γ * w' q) := by rw [← h1, ← h2]
        _ = _ := by
            rw [Finset.sum_mul_sum]
            exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
    rw [hunit]
    exact Submodule.sum_mem _ fun p _ ↦ Submodule.sum_mem _ fun q _ ↦
      Submodule.smul_mem _ _ (houter p.1 q.1 p.2 q.2)
  have hne : ∃ i, W.toMPSTensor i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    have hspan : Submodule.span ℂ (Set.range W.toMPSTensor) = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro _ ⟨i, rfl⟩
      exact h i
    have h1 : (1 : Matrix (Fin K) (Fin K) ℂ) ∈ Submodule.span ℂ (Set.range W.toMPSTensor) := by
      rw [hinj.span_eq_top]
      exact Submodule.mem_top
    rw [hspan, Submodule.mem_bot] at h1
    exact one_ne_zero h1
  exact MPSTensor.isMPUCanonicalForm_of_isIrreducibleFamily _
    (Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM _
      (Kraus.injective_implies_irreducibleCP _ hinj)) hne

end MPOTensor
