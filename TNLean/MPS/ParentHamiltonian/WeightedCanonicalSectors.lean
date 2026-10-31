/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.WeightedCanonicalPhysicalLimit
import TNLean.MPS.ParentHamiltonian.HalfChainSourceSpectrum
import QICLean.Algebra.ScalarCommutant
import QICLean.Algebra.L2OpNormReindex
import Mathlib.LinearAlgebra.Eigenspace.Zero

/-!
# Dominant sectors of a weighted canonical tensor

Each canonical sector projection is a transfer eigenvector with eigenvalue
its squared weight. Spectral-radius normalization forces a unit-weight
sector. Algebraic simplicity of the peripheral eigenvalue makes this sector
unique. These assertions use the actual weighted tensor, rather than
assuming a dominant-block reduction.

Source: PGVWC07, arXiv:quant-ph/0608197, Theorem 4, lines 742–759, and
Condition C2, lines 954–963. For several blocks the generic exclusion of
peripheral degeneracy is counted with multiplicity, as distinguished in
`docs/paper-gaps/pgvwc07_half_chain_spectrum_conventions.tex`; the earlier
one-block hypothesis about distinct eigenvalue values is unchanged.

**Scope restriction (multiplicity-aware C2):** `existsUnique_weight_eq_one_of_c2`,
`exists_dominantBlock_physical_limit_of_c2`, `isNormalTensor_of_weight_eq_one_of_c2`
and `exists_dominantNormalBlock_physical_limit_of_c2` assume that every peripheral
eigenvalue of the transfer map is one with algebraic multiplicity one. The literal
reading of PGVWC07 Condition C2 (lines 954–963) excludes only other peripheral values,
and the multi-block theorem under that literal reading remains open. Documented in
`docs/paper-gaps/pgvwc07_half_chain_spectrum_conventions.tex`. The sector, spectral-radius
and remainder results of this module are unconditional and outside this restriction.
-/

open scoped Matrix BigOperators Matrix.Norms.L2Operator ComplexOrder Topology ENNReal

namespace MPSTensor.PGVWC07CanonicalFormData

variable {d D : ℕ} {A : MPSTensor d D} (h : PGVWC07CanonicalFormData A)

/-- Each canonical block supplies its own strictly positive diagonal dual
fixed point normalized to trace one. No stationary density is assumed in
addition to the canonical data. Source: PGVWC07, Theorem 4, lines 753–755,
and Theorem 6, lines 970–993. -/
theorem exists_normalized_diagonal_dualFixedPoint (k : Fin h.r) :
    ∃ lam : Fin (h.dim k) → ℝ, (∀ a, 0 < lam a) ∧ (∑ a, lam a = 1) ∧
      ∑ i, (h.blocks k i)ᴴ * (Matrix.diagonal fun a => (lam a : ℂ)) * h.blocks k i =
        Matrix.diagonal fun a => (lam a : ℂ) := by
  classical
  obtain ⟨Λ, hΛ, hDiag, hFix⟩ := h.dual_fixedPoint k
  have hPositive : ∀ a, 0 < (Λ a a).re := fun a =>
    (Complex.pos_iff.mp (hΛ.diag_pos (i := a))).1
  have hReal : ∀ a, ((Λ a a).re : ℂ) = Λ a a := fun a =>
    Complex.ext rfl (Complex.pos_iff.mp (hΛ.diag_pos (i := a))).2
  have hDiagReal : Matrix.diagonal (fun a => ((Λ a a).re : ℂ)) = Λ := by
    rw [show (fun a => ((Λ a a).re : ℂ)) = Matrix.diag Λ from funext hReal]
    exact hDiag.diagonal_diag
  let s : ℝ := ∑ a, (Λ a a).re
  have hs : 0 < s := Finset.sum_pos (fun a _ => hPositive a) Finset.univ_nonempty
  let lam : Fin (h.dim k) → ℝ := fun a => (Λ a a).re / s
  have hNormalized : Matrix.diagonal (fun a => (lam a : ℂ)) = (s : ℂ)⁻¹ • Λ := by
    calc
      _ = Matrix.diagonal ((s : ℂ)⁻¹ • (fun a => ((Λ a a).re : ℂ))) := by
        congr 1
        funext a
        change (((Λ a a).re / s : ℝ) : ℂ) = (s : ℂ)⁻¹ * ((Λ a a).re : ℂ)
        rw [Complex.ofReal_div, div_eq_mul_inv, mul_comm]
      _ = _ := by rw [Matrix.diagonal_smul, hDiagReal]
  refine ⟨lam, fun a => div_pos (hPositive a) hs, ?_, ?_⟩
  · change (∑ a, (Λ a a).re / s) = 1
    rw [← Finset.sum_div]
    exact div_self hs.ne'
  · simp only [hNormalized, Matrix.mul_smul, Matrix.smul_mul, ← Finset.smul_sum, hFix]

/-- A block diagonal observable evolves independently in each weighted
canonical sector. Source: PGVWC07, Theorem 4, lines 745–757. -/
theorem transferMap_reindex_blockDiagonal
    (X : ∀ k, Matrix (Fin (h.dim k)) (Fin (h.dim k)) ℂ) :
    Kraus.transferMap A (Matrix.reindex h.index h.index (Matrix.blockDiagonal' X)) =
      Matrix.reindex h.index h.index (Matrix.blockDiagonal' fun k =>
        (h.weight k : ℂ) ^ 2 • Kraus.transferMap (h.blocks k) (X k)) := by
  classical
  have hi : ∀ i, A i * Matrix.reindex h.index h.index (Matrix.blockDiagonal' X) *
      (A i)ᴴ = Matrix.reindexLinearEquiv ℂ ℂ h.index h.index
      (Matrix.blockDiagonal'AddMonoidHom _ _ ℂ fun k =>
        (h.weight k : ℂ) ^ 2 • (h.blocks k i * X k * (h.blocks k i)ᴴ)) := by
    intro i
    rw [Matrix.coe_reindexLinearEquiv, Matrix.blockDiagonal'AddMonoidHom_apply,
      h.reconstruct i, Matrix.conjTranspose_reindex]
    simp only [Matrix.reindex_apply]
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
      Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul,
      ← Matrix.blockDiagonal'_mul]
    refine congrArg (fun M => Matrix.submatrix M _ _)
      (congrArg Matrix.blockDiagonal' (funext fun k => ?_))
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, Complex.star_def, Complex.conj_ofReal, sq]
  rw [Kraus.transferMap_apply, Finset.sum_congr rfl fun i _ => hi i,
    ← map_sum, ← map_sum, Matrix.coe_reindexLinearEquiv,
    Matrix.blockDiagonal'AddMonoidHom_apply]
  refine congrArg (Matrix.reindex h.index h.index)
    (congrArg Matrix.blockDiagonal' (funext fun k => ?_))
  simp only [Finset.sum_apply, ← Finset.smul_sum, Kraus.transferMap_apply]

/-- The actual orthogonal projection onto a canonical bond sector. Source:
PGVWC07, Theorem 4, lines 745–751. -/
noncomputable def sectorProjection (k : Fin h.r) : Matrix (Fin D) (Fin D) ℂ :=
  Matrix.reindex h.index h.index (Matrix.blockProjection (n := fun k => Fin (h.dim k)) k)

private theorem sectorProjection_diag (k j : Fin h.r) (a : Fin (h.dim j)) :
    h.sectorProjection k (h.index ⟨j, a⟩) (h.index ⟨j, a⟩) = if j = k then 1 else 0 := by
  classical
  by_cases hj : j = k
  · subst j
    simp [sectorProjection, Matrix.blockProjection, Matrix.reindex_apply]
  · simp [sectorProjection, Matrix.blockProjection, Matrix.reindex_apply, hj]

/-- Every canonical sector is nonzero because its bond dimension is positive.
Source: PGVWC07, Theorem 4, lines 745–751, with the positive-block convention. -/
theorem sectorProjection_ne_zero (k : Fin h.r) : h.sectorProjection k ≠ 0 := by
  intro hz
  have hentry := h.sectorProjection_diag k k ⟨0, h.dim_pos k⟩
  rw [hz] at hentry
  simp at hentry

/-- The transfer eigenvalue of a canonical sector projection is the square
of its canonical weight. Source: PGVWC07, Theorem 4, lines 745–757. -/
theorem transferMap_sectorProjection (k : Fin h.r) :
    Kraus.transferMap A (h.sectorProjection k) =
      (h.weight k : ℂ) ^ 2 • h.sectorProjection k := by
  classical
  unfold sectorProjection Matrix.blockProjection
  rw [h.transferMap_reindex_blockDiagonal]
  change _ = Matrix.reindex h.index h.index
    ((h.weight k : ℂ) ^ 2 • Matrix.blockDiagonal'
      (fun j => if j = k then (1 : Matrix (Fin (h.dim j)) (Fin (h.dim j)) ℂ) else 0))
  rw [← Matrix.blockDiagonal'_smul]
  refine congrArg (Matrix.reindex h.index h.index)
    (congrArg Matrix.blockDiagonal' (funext fun j => ?_))
  by_cases hj : j = k
  · subst j
    simp [Pi.smul_apply, h.unital]
  · simp [hj, Pi.smul_apply]

/-- Each squared canonical weight occurs in the actual transfer spectrum.
Source: PGVWC07, Theorem 4, lines 745–757. -/
theorem hasEigenvalue_weight_sq (k : Fin h.r) :
    Module.End.HasEigenvalue (Kraus.transferMap A) ((h.weight k : ℂ) ^ 2) := by
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := h.sectorProjection k)
  exact ⟨Module.End.mem_eigenspace_iff.mpr (h.transferMap_sectorProjection k),
    h.sectorProjection_ne_zero k⟩

/-- An eigenvector in any canonical block lifts to the corresponding
weighted eigenvalue of the actual tensor. Source: PGVWC07, Theorem 4,
lines 745–757; this is the sector restriction used in normalized C2. -/
theorem hasEigenvalue_of_block {k : Fin h.r} {μ : ℂ}
    (hμ : Module.End.HasEigenvalue (Kraus.transferMap (h.blocks k)) μ) :
    Module.End.HasEigenvalue (Kraus.transferMap A) ((h.weight k : ℂ) ^ 2 * μ) := by
  classical
  obtain ⟨X, hX⟩ := hμ.exists_hasEigenvector
  let blocks : ∀ j, Matrix (Fin (h.dim j)) (Fin (h.dim j)) ℂ := Pi.single k X
  let Y := Matrix.reindex h.index h.index (Matrix.blockDiagonal' blocks)
  have hYne : Y ≠ 0 := by
    intro hz
    apply hX.2
    ext a b
    have hentry := congrFun (congrFun hz (h.index ⟨k, a⟩)) (h.index ⟨k, b⟩)
    simpa [Y, blocks, Matrix.reindex_apply] using hentry
  have hY : Kraus.transferMap A Y = ((h.weight k : ℂ) ^ 2 * μ) • Y := by
    dsimp only [Y]
    rw [h.transferMap_reindex_blockDiagonal]
    change _ = Matrix.reindex h.index h.index
      (((h.weight k : ℂ) ^ 2 * μ) • Matrix.blockDiagonal' blocks)
    rw [← Matrix.blockDiagonal'_smul]
    refine congrArg (Matrix.reindex h.index h.index)
      (congrArg Matrix.blockDiagonal' (funext fun j => ?_))
    by_cases hj : j = k
    · subst j
      simp only [blocks, Pi.single_eq_same, Pi.smul_apply, hX.apply_eq_smul, smul_smul]
    · simp only [blocks, Pi.single_eq_of_ne hj, map_zero, Pi.smul_apply, smul_zero]
  exact Module.End.hasEigenvalue_of_hasEigenvector
    ⟨Module.End.mem_eigenspace_iff.mpr hY, hYne⟩

/-- Spectral-radius normalization supplies a unit-weight sector, without
assuming that any canonical weight was already equal to one. Source:
PGVWC07, normalized Condition C2, lines 954–963. -/
theorem exists_weight_eq_one
    (hRadius : spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
        (Kraus.transferMap A)) = 1) :
    ∃ k, h.weight k = 1 := by
  classical
  have hD : D ≠ 0 := by
    intro hzero
    subst D
    have hMapZero :
        ((Module.End.toContinuousLinearMap (Matrix (Fin 0) (Fin 0) ℂ))
          (Kraus.transferMap A)) = 0 := Subsingleton.elim _ _
    rw [hMapZero, spectrum.spectralRadius_zero] at hRadius
    exact zero_ne_one hRadius
  let : NeZero D := ⟨hD⟩
  by_contra hnone
  have hlt : ∀ k, h.weight k < 1 := by
    intro k
    exact lt_of_le_of_ne (h.weight_le_one k) (fun hk => hnone ⟨k, hk⟩)
  have hDiag : Matrix.blockDiagonal' (fun k => (h.weight k : ℂ) ^ 2 •
      (1 : Matrix (Fin (h.dim k)) (Fin (h.dim k)) ℂ)) =
      Matrix.diagonal (fun p : (k : Fin h.r) × Fin (h.dim k) => (h.weight p.1 : ℂ) ^ 2) := by
    ext ⟨k, a⟩ ⟨j, b⟩
    by_cases hkj : k = j
    · subst j
      simp [Matrix.blockDiagonal'_apply_eq, Matrix.diagonal_apply, Matrix.one_apply]
    · simp [Matrix.blockDiagonal'_apply_ne _ _ _ hkj, hkj]
  have hNorm : ‖Kraus.transferMap A 1‖ < 1 := by
    rw [Kraus.transferMap_apply]
    simp only [Matrix.mul_one]
    rw [h.sum_mul_conjTranspose_eq, Matrix.l2_opNorm_reindex_equiv, hDiag,
      Matrix.l2_opNorm_diagonal]
    apply (pi_norm_lt_iff zero_lt_one).mpr
    intro p
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg (h.weight_pos p.1).le]
    exact pow_lt_one₀ (h.weight_pos p.1).le (hlt p.1) (by omega)
  have hBound := (Kraus.isPositiveMap_mapLM A).spectralRadius_le_nnnorm_map_one
  have hStrict : spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
        (Kraus.transferMap A)) < 1 :=
    lt_of_le_of_lt hBound (by exact_mod_cast hNorm)
  rw [hRadius] at hStrict
  exact lt_irrefl _ hStrict

/-- Algebraic simplicity of the peripheral eigenvalue excludes two distinct
unit-weight canonical sectors. This is the multiplicity part of the generic
Condition C2 in PGVWC07, lines 954–963. -/
theorem weight_eq_one_unique_of_simple_fixedEigenvalue
    (hSimple : (Kraus.transferMap A).charpoly.rootMultiplicity 1 = 1)
    {k j : Fin h.r} (hk : h.weight k = 1) (hj : h.weight j = 1) : k = j := by
  classical
  have hPk : h.sectorProjection k ∈ Module.End.eigenspace (Kraus.transferMap A) 1 := by
    rw [Module.End.mem_eigenspace_iff, h.transferMap_sectorProjection, hk]
    simp
  have hPj : h.sectorProjection j ∈ Module.End.eigenspace (Kraus.transferMap A) 1 := by
    rw [Module.End.mem_eigenspace_iff, h.transferMap_sectorProjection, hj]
    simp
  have hSpan : Submodule.span ℂ {h.sectorProjection k} =
      Module.End.eigenspace (Kraus.transferMap A) 1 := by
    apply Submodule.eq_of_le_of_finrank_le
      (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hPk))
    rw [finrank_span_singleton (h.sectorProjection_ne_zero k)]
    simpa only [hSimple] using LinearMap.finrank_eigenspace_le (Kraus.transferMap A) 1
  rw [← hSpan] at hPj
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hPj
  by_contra hkj
  have hentry := congrFun (congrFun hc (h.index ⟨j, ⟨0, h.dim_pos j⟩⟩))
    (h.index ⟨j, ⟨0, h.dim_pos j⟩⟩)
  simp [h.sectorProjection_diag, Ne.symm hkj] at hentry

/-- The normalized generic C2 hypothesis, counted with algebraic
multiplicity, determines a unique unit-weight canonical block. No dominant
sector is supplied as a premise. Source: PGVWC07, lines 954–963; the
multiplicity convention is explained in the module docstring. -/
theorem existsUnique_weight_eq_one_of_c2
    (hRadius : spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
        (Kraus.transferMap A)) = 1)
    (hC2 : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → ‖μ‖ = 1 →
      μ = 1 ∧ (Kraus.transferMap A).charpoly.rootMultiplicity μ = 1) :
    ∃! k, h.weight k = 1 := by
  obtain ⟨k, hk⟩ := h.exists_weight_eq_one hRadius
  have hOne : Module.End.HasEigenvalue (Kraus.transferMap A) 1 := by
    simpa only [hk, Complex.ofReal_one, one_pow] using h.hasEigenvalue_weight_sq k
  have hSimple := (hC2 1 hOne (by simp)).2
  exact ⟨k, hk, fun j hj => (h.weight_eq_one_unique_of_simple_fixedEigenvalue hSimple hk hj).symm⟩

/-- The dominant-block physical approximation is derived from normalized
C2 and the actual weighted decomposition. The remainder convergence is a
conclusion, not an assumption. Source: PGVWC07, Theorem 6, lines 970–993,
with normalized generic C2 at lines 954–963. -/
theorem exists_dominantBlock_physical_limit_of_c2
    (hRadius : spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
        (Kraus.transferMap A)) = 1)
    (hC2 : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → ‖μ‖ = 1 →
      μ = 1 ∧ (Kraus.transferMap A).charpoly.rootMultiplicity μ = 1) :
    ∃ k, h.weight k = 1 ∧ (∀ j, h.weight j = 1 → j = k) ∧
      Filter.Tendsto (fun N => ‖mpvState A N - mpvState (h.blocks k) N‖)
        Filter.atTop (𝓝 (0 : ℝ)) := by
  classical
  obtain ⟨k, hk, hUnique⟩ := h.existsUnique_weight_eq_one_of_c2 hRadius hC2
  have hFilter : Finset.univ.filter (fun j => h.weight j = 1) = {k} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨hUnique j, fun hj => by simpa only [hj] using hk⟩
  refine ⟨k, hk, hUnique, ?_⟩
  simpa only [hFilter, Finset.sum_singleton] using h.tendsto_norm_mpvState_sub_unitWeight_sum

/-- Normalized generic C2 makes every unit-weight canonical block normal.
The block radius and irreducibility follow from its canonical conditions;
its peripheral eigenvalues lift to those of the actual weighted tensor.
Source: PGVWC07, Condition C2 and Theorem 6, lines 954–993. -/
theorem isNormalTensor_of_weight_eq_one_of_c2
    (hC2 : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → ‖μ‖ = 1 →
      μ = 1 ∧ (Kraus.transferMap A).charpoly.rootMultiplicity μ = 1)
    {k : Fin h.r} (hk : h.weight k = 1) : IsNormalTensor (h.blocks k) := by
  have hOne : Kraus.transferMap (h.blocks k) 1 = 1 := by
    simpa only [Kraus.transferMap_apply, Matrix.mul_one] using h.unital k
  have hPeripheral : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap (h.blocks k)) μ →
      ‖μ‖ = 1 → μ = 1 := by
    intro μ hμ hnorm
    have hAmbient : Module.End.HasEigenvalue (Kraus.transferMap A) μ := by
      simpa only [hk, Complex.ofReal_one, one_pow, one_mul] using h.hasEigenvalue_of_block hμ
    exact (hC2 μ hAmbient hnorm).1
  exact ⟨h.isIrreducibleFamily_blocks k,
    (Kraus.isPositiveMap_mapLM (h.blocks k)).spectralRadius_eq_one_of_map_one_eq_one hOne,
    isPrimitive_of_unique_norm_one (Kraus.transferMap (h.blocks k)) 1 hOne one_ne_zero hPeripheral⟩

/-- The actual weighted state has a unique dominant normal block, and its
physical remainder tends to zero, from canonical form and normalized generic
C2 alone. Source: PGVWC07, Theorem 6, lines 954–993. -/
theorem exists_dominantNormalBlock_physical_limit_of_c2
    (hRadius : spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
        (Kraus.transferMap A)) = 1)
    (hC2 : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → ‖μ‖ = 1 →
      μ = 1 ∧ (Kraus.transferMap A).charpoly.rootMultiplicity μ = 1) :
    ∃ k, h.weight k = 1 ∧ (∀ j, h.weight j = 1 → j = k) ∧
      IsNormalTensor (h.blocks k) ∧
      Filter.Tendsto (fun N => ‖mpvState A N - mpvState (h.blocks k) N‖)
        Filter.atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨k, hk, hUnique, hPhysical⟩ := h.exists_dominantBlock_physical_limit_of_c2 hRadius hC2
  exact ⟨k, hk, hUnique, h.isNormalTensor_of_weight_eq_one_of_c2 hC2 hk, hPhysical⟩

end MPSTensor.PGVWC07CanonicalFormData
