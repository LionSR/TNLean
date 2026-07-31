/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.BNT.Bridge
import TNLean.MPS.RFP.BNTOrthogonality
import TNLean.MPS.RFP.StructuralFull

/-!
# Residual-isometry form of the renormalization fixed-point structure

For a family of normal-tensor blocks $B$ whose direct sum is a renormalization
fixed point, this file converts the block-level cross-block vanishing of
`mixedTransferMap₂ (B j) (B j')` (arXiv:1606.00608, Theorem charact-MPS, the
cross-block part of eq:III_isometry, line 551) into the literal residual-isometry
equation between the residual tensors $U_j$,
\[
  \sum_i (U_j^i)_{\alpha,\beta}\,\overline{(U_{j'}^i)_{\alpha',\beta'}}
    = \delta_{j,j'}\delta_{\alpha,\alpha'}\delta_{\beta,\beta'} ,
\]
the full isometry condition of Corollary III.cor3 (arXiv:1606.00608, line 584).

## Main results

* `mixedTransferMap₂_conj_apply` — covariance of the mixed transfer operator
  under a two-sided change of variables $A^i = X_A D_A U^i X_A^{-1}$.
* `mixedTransferMap₂_eq_zero_of_conj` — cancelling the invertible outer factors
  turns the vanishing of `mixedTransferMap₂ A B` into that of
  `mixedTransferMap₂ U V`.
* `mixedTransferMap₂_eq_zero_of_gaugePhaseEquiv` — the corresponding
  gauge-phase transport API for two tensor legs.
* `residual_isometry_entry_of_mixedTransferMap₂_eq_zero` — reading off a matrix
  entry turns the vanishing operator into the entrywise residual-isometry sum.
* `IsResidualIsometryFamily` — the full isometry condition eq:III_isometry as a
  predicate on a family of residual tensors (the within-block orthonormality
  together with the cross-block vanishing).
* `exists_residualIsometryFamily_of_isTransferIdempotent_directSum` — under whole-tensor RFP of
  the direct sum, the residual tensors of the isometry canonical forms of the
  blocks satisfy `IsResidualIsometryFamily`.
* `isTransferIdempotent_directSumTensor_iff` — the distinct-blocks renormalization-fixed-point
  characterization: the direct sum is a renormalization fixed point if and only
  if each block is in isometry canonical form and the cross-block mixed transfer
  operators vanish.

## Route

Each block in isometry canonical form is $A_j^i = X_j \sqrt{\Lambda_j} U_j^i
X_j^{-1}$ with $X_j$ and $\sqrt{\Lambda_j}$ invertible.  Substituting the
decomposition into the mixed transfer operator exposes the residual operator
`mixedTransferMap₂ (U j) (U j')` conjugated by the invertible outer factors, so
the block-level vanishing transfers to the residual operator; reading the
$(\alpha,\alpha')$ entry of the operator applied to the matrix unit
`Matrix.single β β' 1` recovers the entrywise sum.  The within-block diagonal
$j = j'$ case is already `IsIsometryCanonicalForm`.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

/-! ## Cancelling invertible factors -/

section Cancellation

variable {D₁ D₂ : ℕ}

/-- If $M P N = 0$ with $M$ and $N$ invertible, then $P = 0$. -/
private lemma eq_zero_of_invertible_mul_mul
    (M : Matrix (Fin D₁) (Fin D₁) ℂ) (N : Matrix (Fin D₂) (Fin D₂) ℂ)
    (P : Matrix (Fin D₁) (Fin D₂) ℂ)
    (hM : M.det ≠ 0) (hN : N.det ≠ 0)
    (h : M * P * N = 0) : P = 0 := by
  have hMu : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  have hNu : IsUnit N.det := isUnit_iff_ne_zero.mpr hN
  have e : M⁻¹ * (M * P * N) * N⁻¹ = P := by
    rw [Matrix.mul_assoc M P N, ← Matrix.mul_assoc M⁻¹ M (P * N),
      Matrix.nonsing_inv_mul M hMu, Matrix.one_mul, Matrix.mul_assoc P N N⁻¹,
      Matrix.mul_nonsing_inv N hNu, Matrix.mul_one]
  have h2 : M⁻¹ * (M * P * N) * N⁻¹ = 0 := by rw [h, Matrix.mul_zero, Matrix.zero_mul]
  rwa [e] at h2

/-- **Covariance of the mixed transfer operator under a two-sided change of
variables.** If $A^i = X_A D_A U^i X_A^{-1}$ and $B^i = X_B D_B V^i X_B^{-1}$,
then the mixed transfer operator of $A$ and $B$ is the mixed transfer operator of
the residual tensors $U$ and $V$, conjugated by the invertible outer factors:
\[
  \mathcal{E}_{A,B}(Y)
    = X_A D_A\,\mathcal{E}_{U,V}\!\bigl(X_A^{-1} Y (X_B^{-1})^\dagger\bigr)\,
      (X_B D_B)^\dagger .
\]
This is the algebraic identity underlying the passage from the block-level
vanishing to eq:III_isometry (arXiv:1606.00608, line 551). -/
lemma mixedTransferMap₂_conj_apply
    (A U : MPSTensor d D₁) (B V : MPSTensor d D₂)
    (Xa Da : Matrix (Fin D₁) (Fin D₁) ℂ) (Xb Db : Matrix (Fin D₂) (Fin D₂) ℂ)
    (hA : ∀ i, A i = Xa * Da * U i * Xa⁻¹)
    (hB : ∀ i, B i = Xb * Db * V i * Xb⁻¹)
    (Y : Matrix (Fin D₁) (Fin D₂) ℂ) :
    mixedTransferMap₂ A B Y
      = Xa * Da * mixedTransferMap₂ U V (Xa⁻¹ * Y * (Xb⁻¹)ᴴ) * (Xb * Db)ᴴ := by
  simp only [mixedTransferMap₂_apply, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hA i, hB i]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- **The residual operator vanishes.** If $A$ and $B$ decompose with invertible
outer factors as $A^i = X_A D_A U^i X_A^{-1}$, $B^i = X_B D_B V^i X_B^{-1}$, and
the mixed transfer operator of $A$ and $B$ vanishes, then the mixed transfer
operator of the residual tensors $U$ and $V$ vanishes.

This cancels the invertible conjugation in `mixedTransferMap₂_conj_apply`
(arXiv:1606.00608, line 551). -/
lemma mixedTransferMap₂_eq_zero_of_conj
    (A U : MPSTensor d D₁) (B V : MPSTensor d D₂)
    (Xa Da : Matrix (Fin D₁) (Fin D₁) ℂ) (Xb Db : Matrix (Fin D₂) (Fin D₂) ℂ)
    (hA : ∀ i, A i = Xa * Da * U i * Xa⁻¹)
    (hB : ∀ i, B i = Xb * Db * V i * Xb⁻¹)
    (hXa : Xa.det ≠ 0) (hDa : Da.det ≠ 0)
    (hXb : Xb.det ≠ 0) (hDb : Db.det ≠ 0)
    (hAB : mixedTransferMap₂ A B = 0) :
    mixedTransferMap₂ U V = 0 := by
  have hXau : IsUnit Xa.det := isUnit_iff_ne_zero.mpr hXa
  have hXbu : IsUnit Xb.det := isUnit_iff_ne_zero.mpr hXb
  refine LinearMap.ext fun Z => ?_
  rw [LinearMap.zero_apply]
  have hXaInv : Xa⁻¹ * Xa = 1 := Matrix.nonsing_inv_mul Xa hXau
  have hXbInv : Xbᴴ * (Xb⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul Xb hXbu, Matrix.conjTranspose_one]
  have hCV : Xa⁻¹ * (Xa * Z * Xbᴴ) * (Xb⁻¹)ᴴ = Z := by
    rw [Matrix.mul_assoc Xa Z Xbᴴ, ← Matrix.mul_assoc Xa⁻¹ Xa (Z * Xbᴴ), hXaInv,
      Matrix.one_mul, Matrix.mul_assoc Z Xbᴴ (Xb⁻¹)ᴴ, hXbInv, Matrix.mul_one]
  have hcov := mixedTransferMap₂_conj_apply A U B V Xa Da Xb Db hA hB (Xa * Z * Xbᴴ)
  rw [hCV] at hcov
  have hAB_app : mixedTransferMap₂ A B (Xa * Z * Xbᴴ) = 0 := by simp [hAB]
  rw [hAB_app] at hcov
  refine eq_zero_of_invertible_mul_mul (Xa * Da) ((Xb * Db)ᴴ)
    (mixedTransferMap₂ U V Z) ?_ ?_ hcov.symm
  · rw [Matrix.det_mul]; exact mul_ne_zero hXa hDa
  · rw [Matrix.det_conjTranspose, Matrix.det_mul]
    exact star_ne_zero.mpr (mul_ne_zero hXb hDb)

/-- Vanishing of a rectangular mixed transfer map descends through independent
gauge-phase equivalences on its two tensor legs. -/
theorem mixedTransferMap₂_eq_zero_of_gaugePhaseEquiv
    {A U : MPSTensor d D₁} {B V : MPSTensor d D₂}
    (hA : GaugePhaseEquiv U A) (hB : GaugePhaseEquiv V B)
    (hAB : mixedTransferMap₂ A B = 0) :
    mixedTransferMap₂ U V = 0 := by
  obtain ⟨Xa, ζa, hζa, hrelA⟩ := hA
  obtain ⟨Xb, ζb, hζb, hrelB⟩ := hB
  let Da : Matrix (Fin D₁) (Fin D₁) ℂ := ζa • 1
  let Db : Matrix (Fin D₂) (Fin D₂) ℂ := ζb • 1
  apply mixedTransferMap₂_eq_zero_of_conj A U B V
    (Xa : Matrix (Fin D₁) (Fin D₁) ℂ) Da
    (Xb : Matrix (Fin D₂) (Fin D₂) ℂ) Db
  · intro i
    rw [hrelA i]
    simp [Da, Matrix.mul_assoc]
  · intro i
    rw [hrelB i]
    simp [Db, Matrix.mul_assoc]
  · exact Matrix.GeneralLinearGroup.det_ne_zero Xa
  · simp [Da, hζa]
  · exact Matrix.GeneralLinearGroup.det_ne_zero Xb
  · simp [Db, hζb]
  · exact hAB

/-- Transport across equalities of the two bond dimensions preserves
vanishing of the rectangular mixed transfer map. -/
theorem mixedTransferMap₂_cast_eq_zero_iff
    {D₁ D₁' D₂ D₂' : ℕ} (h₁ : D₁ = D₁') (h₂ : D₂ = D₂')
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) :
    mixedTransferMap₂
        (cast (congr_arg (MPSTensor d) h₁) A)
        (cast (congr_arg (MPSTensor d) h₂) B) = 0 ↔
      mixedTransferMap₂ A B = 0 := by
  subst D₁'
  subst D₂'
  rfl

/-- **Entrywise form of the vanishing residual operator.** If
`mixedTransferMap₂ U V` vanishes, then for all virtual indices
\[
  \sum_i (U^i)_{\alpha,\beta}\,\overline{(V^i)_{\alpha',\beta'}} = 0 .
\]
This is the entrywise reading of the operator equation (arXiv:1606.00608,
line 551), obtained by evaluating at the matrix unit `Matrix.single β β' 1` and
reading the $(\alpha, \alpha')$ entry. -/
lemma residual_isometry_entry_of_mixedTransferMap₂_eq_zero
    (U : MPSTensor d D₁) (V : MPSTensor d D₂)
    (h : mixedTransferMap₂ U V = 0)
    (α β : Fin D₁) (α' β' : Fin D₂) :
    ∑ i : Fin d, U i α β * star (V i α' β') = 0 := by
  have key : ∀ i : Fin d, U i α β * star (V i α' β') =
      (U i * Matrix.single β β' (1 : ℂ) * (V i)ᴴ) α α' := by
    intro i
    rw [Matrix.mul_apply, Finset.sum_eq_single β']
    · rw [Matrix.mul_single_apply_same, Matrix.conjTranspose_apply, mul_one]
    · intro t _ ht
      rw [Matrix.mul_single_apply_of_ne (M := U i) (hbj := ht), zero_mul]
    · intro hmem; exact absurd (Finset.mem_univ β') hmem
  simp_rw [key]
  rw [← Matrix.sum_apply, ← mixedTransferMap₂_apply, h]
  simp

end Cancellation

/-! ## Per-block renormalization fixed point -/

section Blocks

variable {r : ℕ} {dim : Fin r → ℕ}

/-- Whole-tensor RFP of the direct sum makes each block a renormalization fixed
point: the diagonal $j = j'$ mixed transfer operator is `transferMap (B j)`,
whose idempotence is `IsTransferIdempotent (B j)` (arXiv:1606.00608, Definition 3.2). -/
lemma isTransferIdempotent_block_of_isTransferIdempotent_directSum [∀ k, NeZero (dim k)]
    (B : (k : Fin r) → MPSTensor d (dim k))
    (hRFP : IsTransferIdempotent (directSumTensor B)) (j : Fin r) :
    IsTransferIdempotent (B j) := by
  have hidem := mixedTransferMap₂_isIdempotentElem_of_isTransferIdempotent_directSum B hRFP j j
  rwa [mixedTransferMap₂_self] at hidem

/-- **Residual isometry family** (arXiv:1606.00608, eq:III_isometry, line 551).
A family of residual tensors $U_j$ satisfies the source isometry condition when
the within-block pair-index orthonormality holds for each block and the
cross-block sums vanish between distinct blocks:
\[
  \sum_i (U_j^i)_{\alpha,\beta}\,\overline{(U_{j'}^i)_{\alpha',\beta'}}
    = \delta_{j,j'}\delta_{\alpha,\alpha'}\delta_{\beta,\beta'} .
\]
The $j = j'$ case is the within-block orthonormality and the $j \ne j'$ case is
the cross-block vanishing between distinct blocks. -/
def IsResidualIsometryFamily (U : (j : Fin r) → MPSTensor d (dim j)) : Prop :=
  (∀ (j : Fin r) (α β α' β' : Fin (dim j)),
      ∑ i : Fin d, U j i α β * star (U j i α' β') =
        if α = α' ∧ β = β' then 1 else 0) ∧
  (∀ (j j' : Fin r), j ≠ j' →
      ∀ (α β : Fin (dim j)) (α' β' : Fin (dim j')),
        ∑ i : Fin d, U j i α β * star (U j' i α' β') = 0)

/-- Package per-block isometry canonical forms and cross mixed-map vanishing into a
single residual-isometry family.

This is the algebraic content of the joint isometry equation
(arXiv:1606.00608, eq. `III_isometry`, line 551) once the diagonal and off-diagonal
block statements have been established. It is neutral about how those two inputs
were obtained and includes the empty family. -/
theorem exists_residualIsometryFamily_of_isIsometryCanonicalForm
    (B : (k : Fin r) → MPSTensor d (dim k))
    (hICF : ∀ k, IsIsometryCanonicalForm (B k))
    (hcross : ∀ j j' : Fin r, j ≠ j' → mixedTransferMap₂ (B j) (B j') = 0) :
    ∃ (X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
      (Λ : (j : Fin r) → Fin (dim j) → ℝ)
      (U : (j : Fin r) → MPSTensor d (dim j)),
      (∀ j, (X j).det ≠ 0) ∧
      (∀ j k, 0 < Λ j k) ∧
      (∀ j, ∑ k, Λ j k = 1) ∧
      (∀ j i, B j i =
        X j * Matrix.diagonal (fun k => (Real.sqrt (Λ j k) : ℂ)) * U j i * (X j)⁻¹) ∧
      IsResidualIsometryFamily U := by
  classical
  choose X Λ U hXdet hΛpos hΛsum hUiso hdecomp using hICF
  have hDdet : ∀ j,
      (Matrix.diagonal (fun k => (Real.sqrt (Λ j k) : ℂ))).det ≠ 0 := by
    intro j
    rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff]
    intro k _
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hΛpos j k)).ne'
  refine ⟨X, Λ, U, hXdet, hΛpos, hΛsum, hdecomp, ?_, ?_⟩
  · intro j α β α' β'
    have h := hUiso j (α, β) (α', β')
    have hstar := congrArg star h
    rw [star_sum] at hstar
    simp only [star_mul', star_star] at hstar
    rw [hstar]
    simp only [apply_ite (star : ℂ → ℂ), star_one, star_zero, Prod.mk.injEq]
  · intro j j' hjj' α β α' β'
    have hUjj' : mixedTransferMap₂ (U j) (U j') = 0 :=
      mixedTransferMap₂_eq_zero_of_conj (B j) (U j) (B j') (U j')
        (X j) (Matrix.diagonal (fun k => (Real.sqrt (Λ j k) : ℂ)))
        (X j') (Matrix.diagonal (fun k => (Real.sqrt (Λ j' k) : ℂ)))
        (hdecomp j) (hdecomp j')
        (hXdet j) (hDdet j) (hXdet j') (hDdet j') (hcross j j' hjj')
    exact residual_isometry_entry_of_mixedTransferMap₂_eq_zero
      (U j) (U j') hUjj' α β α' β'

/-- **Residual-isometry form of the cross-block RFP structure.**

For a family of normal, irreducible, left-canonical blocks $B$, no two
gauge-phase equivalent, whose direct sum is a renormalization fixed point, the
residual tensors of the per-block isometry canonical forms satisfy the full
source isometry condition eq:III_isometry (arXiv:1606.00608, line 551): there
are invertible $X_j$, positive trace-normalized diagonal weights $\Lambda_j$, and
residual tensors $U_j$ with $B_j^i = X_j \sqrt{\Lambda_j} U_j^i X_j^{-1}$ and
`IsResidualIsometryFamily U`.  This is the residual-isometry content of
Corollary III.cor3 (arXiv:1606.00608, line 584) at the level of the
normal-tensor blocks.

**Scope restriction (whole-tensor canonical form):** the load-bearing hypothesis
is whole-tensor RFP of the direct sum together with the explicit per-block
normality, irreducibility, left-canonical condition, and gauge-phase
distinctness of a basis of normal tensors.  Corollary III.cor3 starts instead
from a single predicate "$A$ in canonical form is RFP"; extracting the per-block
normality, irreducibility, left-canonical condition, and gauge-phase
distinctness from that predicate is a separate step.  This restriction is
recorded in the paper-gap note docs/paper-gaps/cpsv16_rfp_isometry_scope.tex. -/
theorem exists_residualIsometryFamily_of_isTransferIdempotent_directSum [∀ k, NeZero (dim k)]
    (B : (k : Fin r) → MPSTensor d (dim k))
    (hnormal : ∀ k, IsNormal (B k))
    (hirr : ∀ k, IsIrreducibleTensor (B k))
    (hleft : ∀ k, ∑ i : Fin d, (B k i)ᴴ * B k i = 1)
    (hdist : ∀ j k : Fin r, j ≠ k → ∀ h : dim j = dim k,
      ¬ GaugePhaseEquiv (cast (congrArg (MPSTensor d) h) (B j)) (B k))
    (hRFP : IsTransferIdempotent (directSumTensor B)) :
    ∃ (X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
      (Λ : (j : Fin r) → Fin (dim j) → ℝ)
      (U : (j : Fin r) → MPSTensor d (dim j)),
      (∀ j, (X j).det ≠ 0) ∧
      (∀ j k, 0 < Λ j k) ∧
      (∀ j, ∑ k, Λ j k = 1) ∧
      (∀ j i, B j i =
        X j * Matrix.diagonal (fun k => (Real.sqrt (Λ j k) : ℂ)) * U j i * (X j)⁻¹) ∧
      IsResidualIsometryFamily U := by
  classical
  have hICF : ∀ j, IsIsometryCanonicalForm (B j) := fun j =>
    isIsometryCanonicalForm_of_rfp_nt (B j) (hnormal j)
      (isTransferIdempotent_block_of_isTransferIdempotent_directSum B hRFP j) (hleft j)
  exact exists_residualIsometryFamily_of_isIsometryCanonicalForm B hICF
    (isBNTLocallyOrthogonal_of_isTransferIdempotent_directSum
      B hirr hleft hdist hRFP)

/-! ## Backward direction: a direct sum of isometry-canonical-form blocks is a
renormalization fixed point -/

/-- Idempotence of the block-diagonal transfer sum when each block is in isometry
canonical form and the cross-block mixed transfer operators vanish.

The $(j,j')$ bond block of the transfer sum acts as `mixedTransferMap₂ (B j)
(B j')` on the $(j,j')$ block of the argument
(`blockDiagonal'_transferSum_toBlock`).  Each diagonal block contributes
`transferMap (B j)`, which is idempotent because $B_j$ is a renormalization fixed
point (`isTransferIdempotent_of_isIsometryCanonicalForm`); each off-diagonal block vanishes by
the cross-block orthogonality hypothesis.  This is the block-space form of the
backward direction of the
structural characterization of pure-state renormalization fixed points
(arXiv:1606.00608, Theorem charact-MPS, line 543). -/
theorem blockTransferSum_idempotent_of_isIsometryCanonicalForm
    (B : (k : Fin r) → MPSTensor d (dim k))
    (hCF : ∀ k, IsIsometryCanonicalForm (B k))
    (hortho : ∀ j j' : Fin r, j ≠ j' → mixedTransferMap₂ (B j) (B j') = 0)
    (Y : Matrix ((k : Fin r) × Fin (dim k)) ((k : Fin r) × Fin (dim k)) ℂ) :
    blockTransferSum B (blockTransferSum B Y) = blockTransferSum B Y := by
  apply blockTransferSum_idempotent_of_pairwise_mixedTransferMap₂ B (Y := Y)
  intro j j'
  by_cases hjj' : j = j'
  · subst hjj'
    rw [mixedTransferMap₂_self]
    exact isTransferIdempotent_of_isIsometryCanonicalForm (B j) (hCF j)
  · rw [hortho j j' hjj']
    exact IsIdempotentElem.zero

/-- **Backward direction of the structural characterization of pure-state
renormalization fixed points** (arXiv:1606.00608, Theorem charact-MPS, line 543),
multiplicity-one case.

A direct sum of blocks each in isometry canonical form whose cross-block mixed
transfer operators vanish is a renormalization fixed point.  The cross-block
hypothesis is the off-diagonal ($j \ne j'$) content of the isometry
condition (arXiv:1606.00608, line 551), so it belongs to the
source's isometry form rather than being an added assumption; the within-block
diagonal content is `IsIsometryCanonicalForm`.

The direct-sum transfer map is block diagonal as a superoperator: its $(j,j')$
bond block acts as `mixedTransferMap₂ (B j) (B j')` on the $(j,j')$ block of the
argument.  The diagonal blocks are idempotent (per-block renormalization fixed
point) and the off-diagonal blocks vanish, so the whole map is idempotent.

**Scope restriction (multiplicity-one canonical form):** the source's canonical
form allows each normal tensor to repeat with a multiplicity and a
phase; this is the distinct-blocks (multiplicity-one, phase-one) case, where the
direct sum carries one copy of each block.  Recorded in the paper-gap note
docs/paper-gaps/cpsv16_rfp_isometry_scope.tex. -/
theorem isTransferIdempotent_directSumTensor_of_isIsometryCanonicalForm
    (B : (k : Fin r) → MPSTensor d (dim k))
    (hCF : ∀ k, IsIsometryCanonicalForm (B k))
    (hortho : ∀ j j' : Fin r, j ≠ j' → mixedTransferMap₂ (B j) (B j') = 0) :
    IsTransferIdempotent (directSumTensor B) := by
  classical
  set e := finSigmaFinEquiv (m := r) (n := dim)
  change transferMap (directSumTensor B) ∘ₗ transferMap (directSumTensor B)
      = transferMap (directSumTensor B)
  refine LinearMap.ext fun Z => ?_
  rw [LinearMap.comp_apply]
  obtain ⟨Y, rfl⟩ : ∃ Y, Matrix.reindex e e Y = Z :=
    ⟨(Matrix.reindex e e).symm Z, (Matrix.reindex e e).apply_symm_apply Z⟩
  calc
    transferMap (directSumTensor B)
          (transferMap (directSumTensor B) (Matrix.reindex e e Y))
        = transferMap (directSumTensor B)
            (Matrix.reindex e e (blockTransferSum B Y)) := by
          rw [transferMap_directSumTensor_reindex B Y]
    _ = Matrix.reindex e e (blockTransferSum B (blockTransferSum B Y)) :=
          transferMap_directSumTensor_reindex B (blockTransferSum B Y)
    _ = Matrix.reindex e e (blockTransferSum B Y) := by
          rw [blockTransferSum_idempotent_of_isIsometryCanonicalForm B hCF hortho Y]
    _ = transferMap (directSumTensor B) (Matrix.reindex e e Y) :=
          (transferMap_directSumTensor_reindex B Y).symm

/-- **Distinct-blocks structural characterization of pure-state renormalization
fixed points** (arXiv:1606.00608, Theorem charact-MPS, line 543),
multiplicity-one case.

For a family of normal, irreducible, left-canonical blocks $B$, no two
gauge-phase equivalent and each of positive bond dimension ($\dim_k \ge 1$), the
direct sum is a renormalization fixed point if and only if each block is in
isometry canonical form and the mixed transfer operators between distinct blocks
vanish.  In symbols, `IsTransferIdempotent (directSumTensor B)` holds exactly when both
`IsIsometryCanonicalForm (B k)` for every $k$ and
`mixedTransferMap₂ (B j) (B j') = 0` for all $j \ne j'$.

The forward direction combines the per-block isometry canonical form — each
block is a renormalization fixed point by
`isTransferIdempotent_block_of_isTransferIdempotent_directSum`, hence
in isometry canonical form by `isIsometryCanonicalForm_of_rfp_nt` — with the
cross-block vanishing `isBNTLocallyOrthogonal_of_isTransferIdempotent_directSum`.  The backward
direction is `isTransferIdempotent_directSumTensor_of_isIsometryCanonicalForm`.

**Scope restriction (multiplicity-one canonical form):** the source canonical
form $A^i = \bigoplus_{j} \bigoplus_{q} \mu_{j,q} X_{j,q} \Lambda_j U^i_j
X_{j,q}^{-1}$ allows each normal tensor to repeat with a multiplicity $r_j$ and a
unit-modulus phase $\mu_{j,q}$; this is the distinct-blocks (multiplicity-one,
phase-one) case, where the direct sum carries one copy of each block.  Recorded
in the paper-gap note docs/paper-gaps/cpsv16_rfp_isometry_scope.tex. -/
theorem isTransferIdempotent_directSumTensor_iff [∀ k, NeZero (dim k)]
    (B : (k : Fin r) → MPSTensor d (dim k))
    (hnormal : ∀ k, IsNormal (B k))
    (hirr : ∀ k, IsIrreducibleTensor (B k))
    (hleft : ∀ k, ∑ i : Fin d, (B k i)ᴴ * B k i = 1)
    (hdist : ∀ j k : Fin r, j ≠ k → ∀ h : dim j = dim k,
      ¬ GaugePhaseEquiv (cast (congrArg (MPSTensor d) h) (B j)) (B k)) :
    IsTransferIdempotent (directSumTensor B) ↔
      ((∀ k, IsIsometryCanonicalForm (B k)) ∧
        (∀ j j' : Fin r, j ≠ j' → mixedTransferMap₂ (B j) (B j') = 0)) := by
  constructor
  · intro hRFP
    refine ⟨fun k => ?_, ?_⟩
    · exact isIsometryCanonicalForm_of_rfp_nt (B k) (hnormal k)
        (isTransferIdempotent_block_of_isTransferIdempotent_directSum B hRFP k) (hleft k)
    · exact isBNTLocallyOrthogonal_of_isTransferIdempotent_directSum B hirr hleft hdist hRFP
  · rintro ⟨hCF, hortho⟩
    exact isTransferIdempotent_directSumTensor_of_isIsometryCanonicalForm B hCF hortho

end Blocks

namespace IsBNTCanonicalForm

variable {P : SectorDecomposition d}

/-- **Multiplicity-one characterization for the basis of normal tensors.**

If `P` is in BNT canonical form, then the direct sum of its distinct basis
tensors is a renormalization fixed point exactly when every basis tensor is in
isometry canonical form and the mixed transfer operators between distinct
basis tensors vanish.  The blockwise normality, irreducibility,
left-canonical normalization, positive bond dimensions, and gauge-phase
distinctness required by `isTransferIdempotent_directSumTensor_iff` all follow from the one
BNT canonical-form hypothesis.

This is the multiplicity-one, phase-one specialization of CPSV16,
Theorem `charact-MPS` and Corollary `III.cor3` (arXiv:1606.00608, lines
543--584).  The repeated-copy physical-space construction remains separate;
see `docs/paper-gaps/cpsv16_rfp_isometry_scope.tex`. -/
theorem isTransferIdempotent_basisDirectSum_iff (hCF : IsBNTCanonicalForm P) :
    IsTransferIdempotent (directSumTensor P.basis) ↔
      ((∀ k, IsIsometryCanonicalForm (P.basis k)) ∧
        ∀ j j' : Fin P.basisCount, j ≠ j' →
          mixedTransferMap₂ (P.basis j) (P.basis j') = 0) := by
  letI : ∀ k : Fin P.basisCount, NeZero (P.basisDim k) :=
    fun k => ⟨(hCF.basis_dim_pos k).ne'⟩
  exact isTransferIdempotent_directSumTensor_iff P.basis hCF.basis_isNormal
    hCF.basis_irreducible hCF.basis_left_canonical hCF.basis_distinct

/-- **Residual isometry family for a BNT basis direct sum.**

If `P` is in BNT canonical form and the direct sum of its basis tensors is a
renormalization fixed point, then those basis tensors have simultaneous
trace-normalized isometry canonical forms whose residual tensors satisfy the
full within-block and cross-block isometry equations.

This is the multiplicity-one, phase-one form of CPSV16, Corollary `III.cor3`
(arXiv:1606.00608, lines 583--589).  The repeated-copy physical-space
construction remains outside this statement; see
`docs/paper-gaps/cpsv16_rfp_isometry_scope.tex`. -/
theorem exists_residualIsometryFamily_of_isTransferIdempotent_basisDirectSum
    (hCF : IsBNTCanonicalForm P) (hRFP : IsTransferIdempotent (directSumTensor P.basis)) :
    ∃ (X : (j : Fin P.basisCount) →
        Matrix (Fin (P.basisDim j)) (Fin (P.basisDim j)) ℂ)
      (Λ : (j : Fin P.basisCount) → Fin (P.basisDim j) → ℝ)
      (U : (j : Fin P.basisCount) → MPSTensor d (P.basisDim j)),
      (∀ j, (X j).det ≠ 0) ∧
      (∀ j k, 0 < Λ j k) ∧
      (∀ j, ∑ k, Λ j k = 1) ∧
      (∀ j i, P.basis j i =
        X j * Matrix.diagonal (fun k => (Real.sqrt (Λ j k) : ℂ)) *
          U j i * (X j)⁻¹) ∧
      IsResidualIsometryFamily U := by
  letI : ∀ k : Fin P.basisCount, NeZero (P.basisDim k) :=
    fun k => ⟨(hCF.basis_dim_pos k).ne'⟩
  exact exists_residualIsometryFamily_of_isTransferIdempotent_directSum P.basis
    hCF.basis_isNormal hCF.basis_irreducible hCF.basis_left_canonical hCF.basis_distinct hRFP

end IsBNTCanonicalForm

end MPSTensor
