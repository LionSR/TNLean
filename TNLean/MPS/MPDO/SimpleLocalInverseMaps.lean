/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.AreaLaw
import TNLean.MPS.MPDO.ZCL
import TNLean.MPS.Chain.VirtualInsertion

/-!
# Local inverse maps for simple MPDO tensors

This file develops the inverse tensor and the induced physical realization
maps used in the local argument of Appendix C.2 of arXiv:1606.00608. It also
identifies the normalized virtual tail that closes the three-site marginal of
the four-site matrix product operator.
-/

open scoped Matrix ComplexOrder BigOperators

namespace MPOTensor

section InjectiveInverseMaps

variable {d D : ℕ}

/-- A simple MPO tensor is injective when its doubled-index MPS tensor is
injective. This is the exact hypothesis needed for the local inverse-map layer
in Appendix C.2. -/
abbrev IsInjective (K : MPOTensor d D) : Prop :=
  Kraus.IsInjective K.toMPSTensor

/-- A concrete inverse tensor `K⁻¹` obtained from a right inverse to the linear
combination map of the doubled-index MPS tensor.

For each physical index `p : Fin (d * d)`, the matrix `inverseTensor K hK p`
collects the coefficients of the standard matrix basis under the chosen right
inverse. Equivalently, its `(α, β)` entry is the coefficient of `K p` in the
expansion of the matrix unit `|α⟩⟨β|`. -/
noncomputable def inverseTensor (K : MPOTensor d D) (hK : K.IsInjective) :
    Fin (d * d) → Matrix (Fin D) (Fin D) ℂ :=
  fun p => Matrix.of fun α β =>
    Kraus.decompositionMap (A := K.toMPSTensor) hK (Matrix.single α β (1 : ℂ)) p

/-- Contracting the chosen inverse tensor with the local MPO tensor recovers the
matrix units on the virtual bond space. This is the Lean form of the paper's
inverse-map identity for an injective simple tensor. -/
theorem inverseTensor_spec (K : MPOTensor d D) (hK : K.IsInjective)
    (α β : Fin D) :
    ∑ p : Fin (d * d), inverseTensor K hK p α β • K.toMPSTensor p =
      Matrix.single α β (1 : ℂ) := by
  change
    ∑ p : Fin (d * d),
      Kraus.decompositionMap (A := K.toMPSTensor) hK
          (Matrix.single α β (1 : ℂ)) p • K.toMPSTensor p
        = Matrix.single α β (1 : ℂ)
  exact Kraus.decompositionMap_sum (A := K.toMPSTensor) hK
    (Matrix.single α β (1 : ℂ))

/-- The virtual matrix obtained by tracing the fourth physical site of the
normalized four-site MPO:

\[
  R_4 = \operatorname{tr}(\rho^{(4)}(K))^{-1}
    \sum_i K^{i,i}.
\]

The scalar is the normalization of the full four-site state. This matrix is
the one-site specialization of the virtual tail in the three-site marginal
formula at lines 1343--1348, later denoted by $m$ at lines 1430--1433.

Source: arXiv:1606.00608, lines 792--793 and Appendix C.2, lines 1343--1348.
The later inverse-map contraction at lines 1415--1438 uses this tail but is not
part of the definition. -/
noncomputable def normalizedFourSiteTail (K : MPOTensor d D) :
    Matrix (Fin D) (Fin D) ℂ :=
  (Matrix.trace (mpo K 4))⁻¹ • physTraceTransfer K

/-- The normalized three-site marginal of the four-site MPO is the product of
the first three local tensors closed against `normalizedFourSiteTail`:

\[
  \bigl(\sigma^{(4)}_3(K)\bigr)_{u,v}
    = \operatorname{tr}\!\left(K^{u_1,v_1}K^{u_2,v_2}K^{u_3,v_3}R_4\right).
\]

This is the four-site instance of the three-site marginal formula at lines
1343--1348. It supplies the normalized tail occurring in the inverse-map
calculation at lines 1415--1438; it does not make the subsequent comparison
with the Hayashi decomposition.

Source: arXiv:1606.00608, lines 792--793 and Appendix C.2, lines 1343--1348;
compare lines 1415--1438. -/
theorem reducedBlockState_four_three_apply
    (K : MPOTensor d D) (u v : Fin 3 → Fin d) :
    K.reducedBlockState 4 3 (by omega) u v =
      Matrix.trace
        (K.evalWord (List.ofFn u) (List.ofFn v) * normalizedFourSiteTail K) := by
  rw [reducedBlockState_eq_sum]
  rw [normalizedMPO, normalizedFourSiteTail, physTraceTransfer]
  simp only [Matrix.smul_apply, mpo_apply, mpoMatrixEntry]
  have hwords (a : Fin 3 → Fin d) (x : Fin 1 → Fin d) :
      List.ofFn (Fin.append a x ∘ Fin.cast (show 4 = 3 + 1 by omega)) =
        List.ofFn a ++ List.ofFn x := by
    rw [← List.ofFn_fin_append]
    congr 1
  simp_rw [hwords]
  have heval (x : Fin 1 → Fin d) :
      K.evalWord (List.ofFn u ++ List.ofFn x) (List.ofFn v ++ List.ofFn x) =
        K.evalWord (List.ofFn u) (List.ofFn v) *
          K.evalWord (List.ofFn x) (List.ofFn x) := by
    exact evalWord_append K _ _ _ _ (by simp)
  simp_rw [heval]
  let z : Fin 1 := 0
  have hone (x : Fin 1 → Fin d) :
      K.evalWord (List.ofFn x) (List.ofFn x) = K (x z) (x z) := by
    simp [z]
  simp_rw [hone]
  rw [← Equiv.sum_comp (Equiv.funUnique (Fin 1) (Fin d)).symm
    (fun x : Fin 1 → Fin d ↦
      (K.mpo 4).trace⁻¹ •
        Matrix.trace
          (K.evalWord (List.ofFn u) (List.ofFn v) * K (x z) (x z)))]
  simp only [Equiv.funUnique_symm_apply, uniqueElim_const]
  simp_rw [← Matrix.trace_smul]
  rw [← Matrix.trace_sum]
  congr 1
  rw [← Finset.smul_sum]
  rw [← Finset.mul_sum]
  rw [Matrix.mul_smul]

/-- The normalized one-site tail is nonzero whenever the four-site MPO has
nonzero trace. Equivalently, the normalized three-site marginal cannot be
closed against the zero virtual matrix.

This is the four-site instance of the observation that the matrix $m$ in
Appendix C.2 has a nonzero entry; the source uses such an entry in the next
sector-factorization step.

Source: arXiv:1606.00608, Appendix C.2, lines 1431--1434, with the
normalization convention at lines 792--793. -/
theorem normalizedFourSiteTail_ne_zero
    (K : MPOTensor d D) (htrace : (mpo K 4).trace ≠ 0) :
    normalizedFourSiteTail K ≠ 0 := by
  intro htail
  have hred : K.reducedBlockState 4 3 (by omega) = 0 := by
    ext u v
    rw [reducedBlockState_four_three_apply, htail]
    simp
  have hunit := reducedBlockState_trace K 4 3 (by omega) htrace
  rw [hred] at hunit
  simp at hunit

/-- A nonzero four-site trace supplies virtual indices at which the normalized
one-site tail does not vanish:

\[
  \exists\,\beta,\alpha,\qquad (R_4)_{\beta,\alpha}\ne 0.
\]

These are precisely the indices selected at line 1434 before the sector
factorization at lines 1435--1437; no SAL or injectivity hypothesis is needed
for this selection once the four-site state has nonzero trace.

Source: arXiv:1606.00608, Appendix C.2, lines 1431--1437. -/
theorem exists_normalizedFourSiteTail_entry_ne_zero
    (K : MPOTensor d D) (htrace : (mpo K 4).trace ≠ 0) :
    ∃ β α : Fin D, normalizedFourSiteTail K β α ≠ 0 := by
  by_contra h
  push Not at h
  apply normalizedFourSiteTail_ne_zero K htrace
  ext β α
  exact h β α

/-- The contraction obtained by applying the inverse tensor to the first and
third sites of a three-site MPO word.

Here `R` is the virtual matrix obtained by contracting the remaining sites.
With $X_{\alpha,\beta}$ denoting the corresponding component of
${\cal K}^{-1}$, this is the left-hand side of the double-sum contraction
identity at lines 1415--1438 of arXiv:1606.00608.

Source: arXiv:1606.00608, Appendix C.2, lines 1415--1438. -/
noncomputable def inverseMapThreeSiteContraction
    (K : MPOTensor d D) (hK : K.IsInjective)
    (R : Matrix (Fin D) (Fin D) ℂ)
    (α₁ β₁ α₃ β₃ : Fin D) (p₂ : Fin (d * d)) : ℂ :=
  ∑ p₁ : Fin (d * d), ∑ p₃ : Fin (d * d),
    inverseTensor K hK p₁ α₁ β₁ * inverseTensor K hK p₃ α₃ β₃ *
      Matrix.trace
        (K.toMPSTensor p₁ * K.toMPSTensor p₂ * K.toMPSTensor p₃ * R)

/-- Applying ${\cal K}^{-1}$ to the two end sites leaves one entry of the
middle tensor and the complementary entry of the virtual tail:

\[
  \sum_{p_1,p_3} ({\cal K}^{-1})^{\alpha_1,\beta_1}_{p_1}
    ({\cal K}^{-1})^{\alpha_3,\beta_3}_{p_3}
    \tr({\cal K}^{p_1}{\cal K}^{p_2}{\cal K}^{p_3}R)
  = {\cal K}^{p_2}_{\beta_1,\alpha_3}R_{\beta_3,\alpha_1}.
\]

This is the contraction-collapse step at lines 1422--1438 of arXiv:1606.00608,
immediately before the sector-factorization equation.

**Local fix (tail index):** the source display at lines 1422--1438
writes $m_{\beta_3,\alpha_3}$. Direct contraction of the two matrix units
gives $m_{\beta_3,\alpha_1}$, as shown by the formula above. The correction
is recorded in
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

Source: arXiv:1606.00608, Appendix C.2, lines 1422--1438. -/
theorem inverseMapThreeSiteContraction_eq
    (K : MPOTensor d D) (hK : K.IsInjective)
    (R : Matrix (Fin D) (Fin D) ℂ)
    (α₁ β₁ α₃ β₃ : Fin D) (p₂ : Fin (d * d)) :
    inverseMapThreeSiteContraction K hK R α₁ β₁ α₃ β₃ p₂ =
      K.toMPSTensor p₂ β₁ α₃ * R β₃ α₁ := by
  classical
  let a : Fin (d * d) → ℂ := fun p ↦ inverseTensor K hK p α₁ β₁
  let b : Fin (d * d) → ℂ := fun p ↦ inverseTensor K hK p α₃ β₃
  let C : Fin (d * d) → Matrix (Fin D) (Fin D) ℂ := K.toMPSTensor
  change
    (∑ p₁ : Fin (d * d), ∑ p₃ : Fin (d * d),
      (a p₁ * b p₃) • Matrix.trace (C p₁ * C p₂ * C p₃ * R)) =
        C p₂ β₁ α₃ * R β₃ α₁
  simp_rw [← Matrix.trace_smul]
  simp_rw [← Matrix.trace_sum Finset.univ]
  have hmat :
      (∑ i, ∑ j, (a i * b j) • (C i * C p₂ * C j * R)) =
        (∑ i, a i • C i) * C p₂ * (∑ j, b j • C j) * R := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    simp [Matrix.mul_assoc, smul_smul, mul_comm]
  have ha : ∑ i, a i • C i = Matrix.single α₁ β₁ (1 : ℂ) := by
    simpa [a, C] using inverseTensor_spec K hK α₁ β₁
  have hb : ∑ i, b i • C i = Matrix.single α₃ β₃ (1 : ℂ) := by
    simpa [b, C] using inverseTensor_spec K hK α₃ β₃
  rw [hmat, ha, hb, Matrix.single_mul_mul_single, Matrix.trace_single_mul]
  simp

/-- The physical realization map for a right virtual insertion on an injective
simple MPO tensor. This is the MPO encoding of
`MPSTensor.physRealize` for the doubled-index tensor. -/
noncomputable def physRealize (K : MPOTensor d D) (hK : K.IsInjective)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    Matrix (Fin (d * d)) (Fin (d * d)) ℂ :=
  MPSTensor.physRealize K.toMPSTensor hK X

/-- Defining property of `MPOTensor.physRealize`. -/
theorem physRealize_spec (K : MPOTensor d D) (hK : K.IsInjective)
    (X : Matrix (Fin D) (Fin D) ℂ) (p : Fin (d * d)) :
    K.toMPSTensor p * X =
      ∑ q, (physRealize K hK X) p q • K.toMPSTensor q :=
  MPSTensor.physRealize_spec K.toMPSTensor hK X p

/-- `MPOTensor.physRealize` is multiplicative. -/
theorem physRealize_mul (K : MPOTensor d D) (hK : K.IsInjective)
    (X Y : Matrix (Fin D) (Fin D) ℂ) :
    physRealize K hK (X * Y) = physRealize K hK X * physRealize K hK Y :=
  MPSTensor.physRealize_mul K.toMPSTensor hK X Y

/-- The physical realization map for a left virtual insertion on an injective
simple MPO tensor. -/
noncomputable def physRealizeLeft (K : MPOTensor d D) (hK : K.IsInjective)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    Matrix (Fin (d * d)) (Fin (d * d)) ℂ :=
  MPSTensor.physRealizeLeft K.toMPSTensor hK X

/-- Defining property of `MPOTensor.physRealizeLeft`. -/
theorem physRealizeLeft_spec (K : MPOTensor d D) (hK : K.IsInjective)
    (X : Matrix (Fin D) (Fin D) ℂ) (p : Fin (d * d)) :
    X * K.toMPSTensor p =
      ∑ q, (physRealizeLeft K hK X) p q • K.toMPSTensor q :=
  MPSTensor.physRealizeLeft_spec K.toMPSTensor hK X p

end InjectiveInverseMaps

end MPOTensor
