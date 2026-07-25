/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.FixedPoint.StationarySupport
import TNLean.MPS.RFP.NNCPHMultiSector
import TNLean.MPS.RFP.PhysicalObservableRealization

/-!
# Conditional converse from zero correlation length to a renormalization fixed point

This file formalizes the multiplicity-one correlation contradiction in the proof of
arXiv:1606.00608, Theorem 3.8, lines 1250--1268. The converse is conditional on the
spectral assertion made at line 1250: every non-idempotent normal block has a nonzero
subleading eigenvalue with normalized left and right eigenvectors.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ}

section SectorMaps

variable (dim)

/-- Compression of a matrix on a direct-sum bond space to one diagonal sector. -/
noncomputable def directSumSectorCompression (j : Fin r) :
    Matrix (Fin (∑ k, dim k)) (Fin (∑ k, dim k)) ℂ →ₗ[ℂ]
      Matrix (Fin (dim j)) (Fin (dim j)) ℂ where
  toFun X := X.submatrix
    (fun a ↦ finSigmaFinEquiv ⟨j, a⟩) (fun a ↦ finSigmaFinEquiv ⟨j, a⟩)
  map_add' X Y := by ext a b; simp
  map_smul' c X := by ext a b; simp

private theorem sectorSingleSum_apply_same (j : Fin r)
    (R : Matrix (Fin (dim j)) (Fin (dim j)) ℂ) (a c : Fin (dim j)) :
    (∑ x, ∑ y, Matrix.single (finSigmaFinEquiv ⟨j, x⟩)
      (finSigmaFinEquiv ⟨j, y⟩) (R x y))
        (finSigmaFinEquiv ⟨j, a⟩) (finSigmaFinEquiv ⟨j, c⟩) = R a c := by
  classical
  simp only [Matrix.sum_apply]
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single c]
    · simp
    · intro y _ hy
      simp [hy]
    · simp
  · intro x _ hx
    apply Finset.sum_eq_zero
    intro y _
    simp [hx]
  · simp

private theorem sectorSingleSum_apply_left_ne (j k : Fin r) (hjk : j ≠ k)
    (R : Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (a : Fin (dim k)) (v : Fin (∑ x, dim x)) :
    (∑ x, ∑ y, Matrix.single (finSigmaFinEquiv ⟨j, x⟩)
      (finSigmaFinEquiv ⟨j, y⟩) (R x y)) (finSigmaFinEquiv ⟨k, a⟩) v = 0 := by
  classical
  simp only [Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro x _
  apply Finset.sum_eq_zero
  intro y _
  simp [hjk]

private theorem sectorSingleSum_apply_right_ne (j k : Fin r) (hjk : j ≠ k)
    (R : Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (u : Fin (∑ x, dim x)) (c : Fin (dim k)) :
    (∑ x, ∑ y, Matrix.single (finSigmaFinEquiv ⟨j, x⟩)
      (finSigmaFinEquiv ⟨j, y⟩) (R x y)) u (finSigmaFinEquiv ⟨k, c⟩) = 0 := by
  classical
  simp only [Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro x _
  apply Finset.sum_eq_zero
  intro y _
  simp [hjk]

/-- Inclusion of a matrix into one diagonal sector of a direct-sum bond space. -/
noncomputable def directSumSectorInclusion (j : Fin r) :
    Matrix (Fin (dim j)) (Fin (dim j)) ℂ →ₗ[ℂ]
      Matrix (Fin (∑ k, dim k)) (Fin (∑ k, dim k)) ℂ :=
  Matrix.traceAdjointMap (directSumSectorCompression dim j)

/-- Entrywise formula for inclusion into one diagonal sector. -/
theorem directSumSectorInclusion_eq_sum (j : Fin r)
    (R : Matrix (Fin (dim j)) (Fin (dim j)) ℂ) :
    directSumSectorInclusion dim j R = ∑ a, ∑ c,
      Matrix.single (finSigmaFinEquiv ⟨j, a⟩) (finSigmaFinEquiv ⟨j, c⟩) (R a c) := by
  classical
  apply (Matrix.ext_iff_trace_mul_right).2
  intro X
  change Matrix.trace
    (Matrix.traceAdjointMap (directSumSectorCompression dim j) R * X) = _
  rw [Matrix.trace_traceAdjointMap_mul]
  simp only [Matrix.sum_mul, Matrix.trace_sum, Matrix.trace_single_mul]
  simp [directSumSectorCompression, Matrix.trace, Matrix.diag, Matrix.mul_apply]


@[simp] theorem directSumSectorCompression_inclusion (j : Fin r)
    (R : Matrix (Fin (dim j)) (Fin (dim j)) ℂ) :
    directSumSectorCompression dim j (directSumSectorInclusion dim j R) = R := by
  rw [directSumSectorInclusion_eq_sum]
  ext a c
  exact sectorSingleSum_apply_same (dim := dim) j R a c

/-- A sector-supported rank-one map sends `X` to
`trace (l * X_jj) • R`, included in sector `j`. -/
noncomputable def directSumSectorRankOne (j : Fin r)
    (R l : Matrix (Fin (dim j)) (Fin (dim j)) ℂ) :
    Matrix (Fin (∑ k, dim k)) (Fin (∑ k, dim k)) ℂ →ₗ[ℂ]
      Matrix (Fin (∑ k, dim k)) (Fin (∑ k, dim k)) ℂ :=
  (((Matrix.traceLinearMap (Fin (dim j)) ℂ ℂ).comp
      (LinearMap.mulLeft ℂ l)).comp (directSumSectorCompression dim j)).smulRight
    (directSumSectorInclusion dim j R)

/-- The matrix-entry formula produced by simultaneous block injectivity is the
sector-supported rank-one map. -/
theorem directSumSectorRankOne_apply (j : Fin r)
    (R l : Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (X : Matrix (Fin (∑ k, dim k)) (Fin (∑ k, dim k)) ℂ) :
    directSumSectorRankOne dim j R l X =
      ∑ z : Fin (dim j) × Fin (dim j) × Fin (dim j) × Fin (dim j),
        (R z.1 z.2.2.1 * l z.2.2.2 z.2.1) • Matrix.single
          (finSigmaFinEquiv ⟨j, z.1⟩)
          (finSigmaFinEquiv ⟨j, z.2.2.1⟩)
          (X (finSigmaFinEquiv ⟨j, z.2.1⟩)
            (finSigmaFinEquiv ⟨j, z.2.2.2⟩)) := by
  classical
  change Matrix.trace (l * directSumSectorCompression dim j X) •
      directSumSectorInclusion dim j R = _
  have htrace : Matrix.trace (l * directSumSectorCompression dim j X) =
      ∑ e, ∑ b, l e b * X (finSigmaFinEquiv ⟨j, b⟩)
        (finSigmaFinEquiv ⟨j, e⟩) := by
    rfl
  rw [htrace, directSumSectorInclusion_eq_sum]
  conv_rhs =>
    rw [Fintype.sum_prod_type]
    enter [2, a]
    rw [Fintype.sum_prod_type]
    enter [2, b]
    rw [Fintype.sum_prod_type]
  ext u v
  rw [← finSigmaFinEquiv.apply_symm_apply u, ← finSigmaFinEquiv.apply_symm_apply v]
  obtain ⟨k, a⟩ := finSigmaFinEquiv.symm u
  obtain ⟨k', c⟩ := finSigmaFinEquiv.symm v
  by_cases hk : k = j
  · subst k
    by_cases hk' : k' = j
    · subst k'
      simp only [Matrix.smul_apply, smul_eq_mul]
      rw [sectorSingleSum_apply_same (dim := dim)]
      simp only [Matrix.smul_single, smul_eq_mul, Matrix.sum_apply,
        Matrix.single_apply, Equiv.apply_eq_iff_eq, Sigma.mk.injEq, heq_iff_eq]
      simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, Finset.sum_const_zero]
      calc
        (∑ e, ∑ b, l e b * X (finSigmaFinEquiv ⟨j, b⟩)
            (finSigmaFinEquiv ⟨j, e⟩)) * R a c =
            ∑ e, ∑ b, (l e b * X (finSigmaFinEquiv ⟨j, b⟩)
              (finSigmaFinEquiv ⟨j, e⟩)) * R a c := by
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro e _
                rw [Finset.sum_mul]
        _ = ∑ b, ∑ e, (l e b * X (finSigmaFinEquiv ⟨j, b⟩)
              (finSigmaFinEquiv ⟨j, e⟩)) * R a c := Finset.sum_comm
        _ = ∑ b, ∑ e, R a c * l e b * X (finSigmaFinEquiv ⟨j, b⟩)
              (finSigmaFinEquiv ⟨j, e⟩) := by
                apply Finset.sum_congr rfl
                intro b _
                apply Finset.sum_congr rfl
                intro e _
                ring
    · simp [Matrix.sum_apply, Sigma.mk.injEq, Ne.symm hk']
  · simp [Matrix.sum_apply, Sigma.mk.injEq, Ne.symm hk]



@[simp] theorem directSumSectorCompression_reindex
    (j : Fin r)
    (Y : Matrix ((k : Fin r) × Fin (dim k)) ((k : Fin r) × Fin (dim k)) ℂ) :
    directSumSectorCompression dim j
        (Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv Y) =
      Y.submatrix (blockIncl j dim) (blockIncl j dim) := by
  ext a b
  simp [directSumSectorCompression, blockIncl, Matrix.reindex_apply]

/-- Compression to a diagonal sector intertwines the direct-sum transfer map
with the transfer map of that sector. -/
theorem directSumSectorCompression_transferMap
    (B : (k : Fin r) → MPSTensor d (dim k)) (j : Fin r)
    (X : Matrix (Fin (∑ k, dim k)) (Fin (∑ k, dim k)) ℂ) :
    directSumSectorCompression dim j (transferMap (directSumTensor B) X) =
      transferMap (B j) (directSumSectorCompression dim j X) := by
  classical
  let e := finSigmaFinEquiv (m := r) (n := dim)
  let Y := Matrix.reindex e.symm e.symm X
  have hXY : Matrix.reindex e e Y = X := by
    ext u v
    simp [Y, e, Matrix.reindex_apply]
  have hblock := blockDiagonal'_transferSum_toBlock B Y j j
  calc
    directSumSectorCompression dim j (transferMap (directSumTensor B) X) =
        directSumSectorCompression dim j
          (transferMap (directSumTensor B) (Matrix.reindex e e Y)) := by rw [hXY]
    _ = directSumSectorCompression dim j
          (Matrix.reindex e e (blockTransferSum B Y)) := by
            rw [transferMap_directSumTensor_reindex]
    _ = transferMap (B j)
          (Y.submatrix (blockIncl j dim) (blockIncl j dim)) := by
            rw [directSumSectorCompression_reindex]
            simpa only [blockTransferSum, mixedTransferMap₂_self] using hblock
    _ = transferMap (B j) (directSumSectorCompression dim j X) := by
            apply congrArg (transferMap (B j))
            ext a b
            simp [directSumSectorCompression, blockIncl, Y, e, Matrix.reindex_apply]

/-- Compression to one sector intertwines every power of the two transfer maps. -/
theorem directSumSectorCompression_transferMap_pow
    (B : (k : Fin r) → MPSTensor d (dim k)) (j : Fin r) (n : ℕ)
    (X : Matrix (Fin (∑ k, dim k)) (Fin (∑ k, dim k)) ℂ) :
    directSumSectorCompression dim j (((transferMap (directSumTensor B)) ^ n) X) =
      ((transferMap (B j)) ^ n) (directSumSectorCompression dim j X) := by
  induction n generalizing X with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply,
        ih, directSumSectorCompression_transferMap]

/-- The operator trace of a sector-supported rank-one map is the matrix trace
of the product of its two defining matrices. -/
theorem trace_directSumSectorRankOne (j : Fin r)
    (R l : Matrix (Fin (dim j)) (Fin (dim j)) ℂ) :
    LinearMap.trace ℂ (Matrix (Fin (∑ k, dim k)) (Fin (∑ k, dim k)) ℂ)
      (directSumSectorRankOne dim j R l) = Matrix.trace (l * R) := by
  rw [directSumSectorRankOne, LinearMap.trace_smulRight,
    LinearMap.comp_apply, LinearMap.comp_apply,
    directSumSectorCompression_inclusion, LinearMap.mulLeft_apply,
    Matrix.traceLinearMap_apply]

end SectorMaps

section Eigenvectors

/-- A left eigenvector for the trace-pairing adjoint evaluates a power of the
original map by the corresponding eigenvalue power. -/
theorem trace_mul_pow_apply_of_traceAdjointMap_hasEigenvector
    {D : ℕ} (E : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ))
    {ν : ℂ} {l : Matrix (Fin D) (Fin D) ℂ}
    (hl : Module.End.HasEigenvector (Matrix.traceAdjointMap E) ν l)
    (n : ℕ) (X : Matrix (Fin D) (Fin D) ℂ) :
    Matrix.trace (l * (E ^ n) X) = ν ^ n * Matrix.trace (l * X) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ← Matrix.trace_traceAdjointMap_mul,
        hl.apply_eq_smul, Matrix.smul_mul, Matrix.trace_smul, ih,
        pow_succ]
      ring

end Eigenvectors

namespace IsBNTCanonicalForm

variable {P : SectorDecomposition d}

/-- The literal two-point calculation in arXiv:1606.00608, lines 1250--1268:
a selected block with a nonzero subleading left/right eigenvector pair is
incompatible with positive-gap physical correlation independence.

The right eigenvector is retained because the source argument assumes the full
normalized pair. The displayed orientation of the two observables uses the left
eigenvector equation. -/
theorem not_isPositiveGapPhysicalCID_basisDirectSum_of_basis_spectral_pair
    (hCF : IsBNTCanonicalForm P) (j : Fin P.basisCount)
    {ν : ℂ} {r l : Matrix (Fin (P.basisDim j)) (Fin (P.basisDim j)) ℂ}
    (hν_ne : ν ≠ 0) (hν_norm : ‖ν‖ < 1)
    (hr : Module.End.HasEigenvector (transferMap (P.basis j)) ν r)
    (hl : Module.End.HasEigenvector
      (Matrix.traceAdjointMap (transferMap (P.basis j))) ν l)
    (hlr : Matrix.trace (l * r) = 1) :
    ¬ IsPositiveGapPhysicalCID (directSumTensor P.basis) := by
  classical
  have _hr_ne : r ≠ 0 := hr.2
  letI : NeZero (P.basisDim j) := ⟨(hCF.basis_dim_pos j).ne'⟩
  let E := transferMap (P.basis j)
  have hCh : IsChannel E := by
    exact transferMap_isChannel (P.basis j) (hCF.basis_left_canonical j)
  have hIrr : IsIrreducibleMap E :=
    isIrreducibleCP_transferMap_of_isIrreducibleTensor
      (P.basis j) (hCF.basis_irreducible j)
  let ρ := Channel.stationaryState E hCh hIrr (hCF.basis_dim_pos j)
  have hρ := Channel.stationaryState_spec hCh hIrr (hCF.basis_dim_pos j)
  have hρ_trace : Matrix.trace ρ = 1 := hρ.1.2
  have hρ_fixed : E ρ = ρ := hρ.2.2
  obtain ⟨L, hL_pos, _, hObs⟩ :=
    hCF.exists_basis_physicalObservableTransfer_rankOne_le_three_totalDim_pow_five
  obtain ⟨O₁, hO₁⟩ := hObs j ρ l
  obtain ⟨O₂, hO₂⟩ := hObs j r 1
  have hO₁_map : physicalObservableTransfer (directSumTensor P.basis) L O₁ =
      directSumSectorRankOne P.basisDim j ρ l := by
    apply LinearMap.ext
    intro X
    rw [hO₁ X, directSumSectorRankOne_apply]
  have hO₂_map : physicalObservableTransfer (directSumTensor P.basis) L O₂ =
      directSumSectorRankOne P.basisDim j r 1 := by
    apply LinearMap.ext
    intro X
    rw [hO₂ X, directSumSectorRankOne_apply]
  intro hCID
  have hEq := hCID L L O₁ O₂ 1 2 2 1 hL_pos hL_pos
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hExpectation (n₁ n₂ : ℕ) (hn₂ : 0 < n₂) :
      physicalTwoPointExpectation (directSumTensor P.basis) L L O₁ O₂ n₁ n₂ =
        ν ^ n₁ := by
    unfold physicalTwoPointExpectation
    rw [hO₁_map, hO₂_map]
    have hcomp : directSumSectorRankOne P.basisDim j r 1 ∘ₗ
          ((transferMap (directSumTensor P.basis)) ^ n₂) ∘ₗ
          directSumSectorRankOne P.basisDim j ρ l ∘ₗ
          ((transferMap (directSumTensor P.basis)) ^ n₁) =
        (ν ^ n₁) • directSumSectorRankOne P.basisDim j r l := by
      apply LinearMap.ext
      intro X
      let c := Matrix.trace (l * directSumSectorCompression P.basisDim j
        (((transferMap (directSumTensor P.basis)) ^ n₁) X))
      have hc : c = ν ^ n₁ * Matrix.trace
          (l * directSumSectorCompression P.basisDim j X) := by
        change Matrix.trace (l * directSumSectorCompression P.basisDim j
          (((transferMap (directSumTensor P.basis)) ^ n₁) X)) = _
        rw [show directSumSectorCompression P.basisDim j
            (((transferMap (directSumTensor P.basis)) ^ n₁) X) =
          (E ^ n₁) (directSumSectorCompression P.basisDim j X) from
            directSumSectorCompression_transferMap_pow (dim := P.basisDim)
              (B := P.basis) (j := j) n₁ X]
        exact trace_mul_pow_apply_of_traceAdjointMap_hasEigenvector E hl n₁ _
      have hρ_pow_all : ∀ n : ℕ, (E ^ n) ρ = ρ := by
        intro n
        induction n with
        | zero => simp
        | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, hρ_fixed]
      have hρ_pow : (E ^ n₂) ρ = ρ := hρ_pow_all n₂
      have hmid : directSumSectorCompression P.basisDim j
          (((transferMap (directSumTensor P.basis)) ^ n₂)
            (c • directSumSectorInclusion P.basisDim j ρ)) = c • ρ := by
        calc
          _ = (E ^ n₂) (directSumSectorCompression P.basisDim j
                (c • directSumSectorInclusion P.basisDim j ρ)) :=
            directSumSectorCompression_transferMap_pow (dim := P.basisDim)
              (B := P.basis) (j := j) n₂ _
          _ = (E ^ n₂) (c • ρ) := by rw [map_smul, directSumSectorCompression_inclusion]
          _ = c • (E ^ n₂) ρ := by rw [map_smul]
          _ = c • ρ := by rw [hρ_pow]
      change Matrix.trace (1 * directSumSectorCompression P.basisDim j
          (((transferMap (directSumTensor P.basis)) ^ n₂)
            (c • directSumSectorInclusion P.basisDim j ρ))) •
          directSumSectorInclusion P.basisDim j r =
        ν ^ n₁ • (Matrix.trace (l * directSumSectorCompression P.basisDim j X) •
          directSumSectorInclusion P.basisDim j r)
      rw [hmid, Matrix.one_mul, Matrix.trace_smul, hρ_trace, hc]
      simp [smul_smul]
    rw [hcomp, map_smul, trace_directSumSectorRankOne, hlr]
    simp
  rw [hExpectation 1 2 (by norm_num), hExpectation 2 1 (by norm_num),
    pow_one, pow_two] at hEq
  have hν_one : ν = 1 := by
    exact (mul_left_cancel₀ hν_ne (by simpa [mul_assoc] using hEq)).symm
  rw [hν_one, norm_one] at hν_norm
  exact (lt_irrefl 1 hν_norm)

/-- Conditional reverse implication at the multiplicity-one representative.
The additional hypothesis is precisely the spectral assertion invoked at
arXiv:1606.00608, line 1250 for a non-idempotent normal block. -/
theorem isTransferIdempotent_basisDirectSum_of_isPositiveGapBNTZCL_of_spectral_pair
    (hCF : IsBNTCanonicalForm P)
    (hspectral : ∀ j : Fin P.basisCount,
      ¬ IsTransferIdempotent (P.basis j) →
        ∃ (ν : ℂ) (r l : Matrix (Fin (P.basisDim j)) (Fin (P.basisDim j)) ℂ),
          ν ≠ 0 ∧ ‖ν‖ < 1 ∧
          Module.End.HasEigenvector (transferMap (P.basis j)) ν r ∧
          Module.End.HasEigenvector
            (Matrix.traceAdjointMap (transferMap (P.basis j))) ν l ∧
          Matrix.trace (l * r) = 1)
    (hZCL : IsPositiveGapBNTZCL (directSumTensor P.basis) P.basis) :
    IsTransferIdempotent (directSumTensor P.basis) := by
  letI : ∀ j : Fin P.basisCount, NeZero (P.basisDim j) :=
    fun j ↦ ⟨(hCF.basis_dim_pos j).ne'⟩
  apply (isTransferIdempotent_directSumTensor_iff_pairwise_mixedTransferMap₂_isIdempotentElem
    P.basis).2
  intro j j'
  by_cases hEq : j = j'
  · subst j'
    rw [mixedTransferMap₂_self]
    by_contra hnot
    obtain ⟨ν, r, l, hν_ne, hν_norm, hr, hl, hlr⟩ := hspectral j hnot
    exact hCF.not_isPositiveGapPhysicalCID_basisDirectSum_of_basis_spectral_pair
      j hν_ne hν_norm hr hl hlr hZCL.2.1
  · rw [hZCL.2.2 j j' hEq]
    exact IsIdempotentElem.zero

/-- Conditional equivalence between positive-gap BNT zero correlation length
and transfer idempotence for the multiplicity-one representative. -/
theorem isPositiveGapBNTZCL_basisDirectSum_iff_isTransferIdempotent_of_spectral_pair
    (hCF : IsBNTCanonicalForm P)
    (hspectral : ∀ j : Fin P.basisCount,
      ¬ IsTransferIdempotent (P.basis j) →
        ∃ (ν : ℂ) (r l : Matrix (Fin (P.basisDim j)) (Fin (P.basisDim j)) ℂ),
          ν ≠ 0 ∧ ‖ν‖ < 1 ∧
          Module.End.HasEigenvector (transferMap (P.basis j)) ν r ∧
          Module.End.HasEigenvector
            (Matrix.traceAdjointMap (transferMap (P.basis j))) ν l ∧
          Matrix.trace (l * r) = 1) :
    IsPositiveGapBNTZCL (directSumTensor P.basis) P.basis ↔
      IsTransferIdempotent (directSumTensor P.basis) := by
  constructor
  · exact hCF.isTransferIdempotent_basisDirectSum_of_isPositiveGapBNTZCL_of_spectral_pair
      hspectral
  · exact hCF.isTransferIdempotent_basisDirectSum_isPositiveGapBNTZCL

/-- Source physical BNT zero correlation length implies transfer idempotence at
the multiplicity-one representative under the line-1250 spectral assertion. -/
theorem isTransferIdempotent_basisDirectSum_of_isPhysicalBNTZCL_of_spectral_pair
    (hCF : IsBNTCanonicalForm P)
    (hspectral : ∀ j : Fin P.basisCount,
      ¬ IsTransferIdempotent (P.basis j) →
        ∃ (ν : ℂ) (r l : Matrix (Fin (P.basisDim j)) (Fin (P.basisDim j)) ℂ),
          ν ≠ 0 ∧ ‖ν‖ < 1 ∧
          Module.End.HasEigenvector (transferMap (P.basis j)) ν r ∧
          Module.End.HasEigenvector
            (Matrix.traceAdjointMap (transferMap (P.basis j))) ν l ∧
          Matrix.trace (l * r) = 1)
    (hZCL : IsPhysicalBNTZCL (directSumTensor P.basis) P.basis) :
    IsTransferIdempotent (directSumTensor P.basis) :=
  hCF.isTransferIdempotent_basisDirectSum_of_isPositiveGapBNTZCL_of_spectral_pair
    hspectral (isPositiveGapBNTZCL_of_isPhysicalBNTZCL _ _ hZCL)

end IsBNTCanonicalForm

end MPSTensor
