/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.EigenvectorProjection
import TNLean.MPS.MPDO.TopologicalDensityDecomposition

/-!
# Terminal spectral projections in the recursive MPDO form

For the length-independent case after Theorem 4.14 of arXiv:1606.00608, the
terminal bond matrices in the recursively fused operator have spectral
decompositions.  Their rank-one spectral projections propagate through every
fusion history and through the adjoint sequential fusion coisometry.  The
resulting all-label operators are pairwise orthogonal projections, commute with
the multiplicity-weight factor, and resolve the recursive factor as a
nonnegative weighted sum.

The terminal matrices are not additional input.  Their positivity is supplied
by the one-site positivity theorem for the original MPDO.

## Main results

* `MPOTensor.BNTFusionTensorClause.hasTerminalSpectralProjectorRefinement`:
  a length-independent fusion clause has the all-label spectral refinement.
* `MPOTensor.terminalSpectralProjectorRefinement_of_isRFPViaTS`: under
  normalized BNT-refined horizontal form, the source-facing theorem makes all
  spectral choices internally.  The literal canonical-form implication remains
  open.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  lines 999--1012
-/

open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace MPOTensor.BNTFusionTensorClause

variable {d D : ℕ} {M : MPOTensor d D}

/-- The terminal bond matrix obtained by closing the horizontal operator leg
of one BNT tensor.

Source: arXiv:1606.00608, lines 1003--1012. -/
def terminalMatrix (H : BNTFusionTensorClause M) (γ : Fin H.labelCount) :
    Matrix (Fin (H.bondDim γ)) (Fin (H.bondDim γ)) ℂ :=
  physTraceTransfer (verticalBNTMPO (H.tensor γ))

/-- A BNT label together with one eigenvector index of its terminal bond
matrix.

Source: arXiv:1606.00608, lines 1009--1012. -/
abbrev TerminalSpectralIndex (H : BNTFusionTensorClause M) : Type :=
  (γ : Fin H.labelCount) × Fin (H.bondDim γ)

/-- The real eigenvalue attached to a terminal spectral index.

Source: arXiv:1606.00608, lines 1009--1012. -/
def terminalEigenvalue (H : BNTFusionTensorClause M) (hM : IsMPDO M)
    (s : H.TerminalSpectralIndex) : ℝ :=
  (H.physTraceTransfer_verticalBNTMPO_posSemidef hM s.1).isHermitian.eigenvalues s.2

/-- The rank-one spectral projection attached to a terminal spectral index.

Source: arXiv:1606.00608, lines 1009--1012. -/
def terminalEigenProjection (H : BNTFusionTensorClause M) (hM : IsMPDO M)
    (s : H.TerminalSpectralIndex) :
    Matrix (Fin (H.bondDim s.1)) (Fin (H.bondDim s.1)) ℂ :=
  (H.physTraceTransfer_verticalBNTMPO_posSemidef hM s.1).isHermitian.eigenvectorProjection s.2

/-- Terminal eigenvalues are nonnegative.

Source: arXiv:1606.00608, lines 1009--1012. -/
theorem terminalEigenvalue_nonneg (H : BNTFusionTensorClause M) (hM : IsMPDO M)
    (s : H.TerminalSpectralIndex) :
    0 ≤ H.terminalEigenvalue hM s :=
  (H.physTraceTransfer_verticalBNTMPO_posSemidef hM s.1).eigenvalues_nonneg s.2

/-- Every terminal spectral component is an orthogonal projection.

Source: arXiv:1606.00608, lines 1009--1012. -/
theorem terminalEigenProjection_isOrthogonalProjection
    (H : BNTFusionTensorClause M) (hM : IsMPDO M)
    (s : H.TerminalSpectralIndex) :
    IsOrthogonalProjection (H.terminalEigenProjection hM s) :=
  Matrix.IsHermitian.isOrthogonalProjection_eigenvectorProjection
    (H.physTraceTransfer_verticalBNTMPO_posSemidef hM s.1).isHermitian s.2

/-- Distinct spectral components of one terminal matrix are orthogonal.

Source: arXiv:1606.00608, lines 1009--1012. -/
theorem terminalEigenProjection_mul_eq_zero (H : BNTFusionTensorClause M)
    (hM : IsMPDO M) (γ : Fin H.labelCount)
    {i j : Fin (H.bondDim γ)} (hij : i ≠ j) :
    H.terminalEigenProjection hM ⟨γ, i⟩ *
        H.terminalEigenProjection hM ⟨γ, j⟩ = 0 :=
  Matrix.IsHermitian.eigenvectorProjection_mul_eq_zero_of_ne
    (H.physTraceTransfer_verticalBNTMPO_posSemidef hM γ).isHermitian hij

/-- Each terminal bond matrix is the nonnegative weighted sum of its rank-one
spectral projections.

Source: arXiv:1606.00608, lines 1009--1012. -/
theorem terminalMatrix_eq_sum_eigenvalue_smul_projection
    (H : BNTFusionTensorClause M) (hM : IsMPDO M)
    (γ : Fin H.labelCount) :
    H.terminalMatrix γ =
      ∑ k : Fin (H.bondDim γ),
        (H.terminalEigenvalue hM ⟨γ, k⟩ : ℂ) •
          H.terminalEigenProjection hM ⟨γ, k⟩ := by
  simpa [terminalMatrix, terminalEigenvalue, terminalEigenProjection] using
    (Matrix.IsHermitian.eq_sum_eigenvalues_smul_eigenvectorProjection
      (H.physTraceTransfer_verticalBNTMPO_posSemidef hM γ).isHermitian)

/-- The terminal family supported at one label and one spectral index.

Source: arXiv:1606.00608, lines 1009--1012. -/
def terminalEigenProjectionFamily (H : BNTFusionTensorClause M)
    (hM : IsMPDO M) (s : H.TerminalSpectralIndex)
    (γ : Fin H.labelCount) :
    Matrix (Fin (H.bondDim γ)) (Fin (H.bondDim γ)) ℂ :=
  if hγ : γ = s.1 then
    hγ.symm ▸ H.terminalEigenProjection hM s
  else
    0

/-- Every member of a terminal spectral family is an orthogonal projection.

Source: arXiv:1606.00608, lines 1009--1012. -/
theorem terminalEigenProjectionFamily_isOrthogonalProjection
    (H : BNTFusionTensorClause M) (hM : IsMPDO M)
    (s : H.TerminalSpectralIndex) (γ : Fin H.labelCount) :
    IsOrthogonalProjection (H.terminalEigenProjectionFamily hM s γ) := by
  by_cases hγ : γ = s.1
  · subst γ
    simpa [terminalEigenProjectionFamily] using
      H.terminalEigenProjection_isOrthogonalProjection hM s
  · simp only [terminalEigenProjectionFamily, dif_neg hγ]
    exact ⟨Matrix.isHermitian_zero, by simp⟩

/-- Terminal families attached to distinct spectral indices multiply to zero.

Source: arXiv:1606.00608, lines 1009--1012. -/
theorem terminalEigenProjectionFamily_mul_eq_zero
    (H : BNTFusionTensorClause M) (hM : IsMPDO M)
    {s t : H.TerminalSpectralIndex} (hst : s ≠ t)
    (γ : Fin H.labelCount) :
    H.terminalEigenProjectionFamily hM s γ *
        H.terminalEigenProjectionFamily hM t γ = 0 := by
  rcases s with ⟨α, i⟩
  rcases t with ⟨β, j⟩
  by_cases hγα : γ = α
  · subst γ
    by_cases hαβ : α = β
    · subst β
      have hij : i ≠ j := by
        intro hij
        subst j
        exact hst rfl
      simpa [terminalEigenProjectionFamily] using
        H.terminalEigenProjection_mul_eq_zero hM α hij
    · simp [terminalEigenProjectionFamily, hαβ]
  · simp [terminalEigenProjectionFamily, hγα]

/-- The sequential fusion map in copy-chain coordinates is a coisometry.

Source: arXiv:1606.00608, lines 1003--1010. The source embedding is the
adjoint of this retained-row map. -/
theorem verticalCopyChainFusionCoisometry_mul_conjTranspose
    (H : BNTFusionTensorClause M) {N : ℕ}
    (p : Fin (N + 1) → H.VerticalCopy) :
    H.verticalCopyChainFusionCoisometry p *
        (H.verticalCopyChainFusionCoisometry p)ᴴ = 1 := by
  unfold verticalCopyChainFusionCoisometry
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    BNTFusionCoisometryFamily.sequentialFusionCoisometry_mul_conjTranspose,
    Matrix.submatrix_one_equiv]

/-- The recursive history operator with one terminal spectral family.

Source: arXiv:1606.00608, lines 1003--1012. -/
def recursiveTerminalEigenProjectorQ (H : BNTFusionTensorClause M)
    (hM : IsMPDO M) {N : ℕ} (p : Fin (N + 1) → H.VerticalCopy)
    (s : H.TerminalSpectralIndex) :
    Matrix
      (H.toBNTFusionCoisometryFamily.FusionHistoryIndex
        (p 0).1 (H.reverseAppendedLabels p))
      (H.toBNTFusionCoisometryFamily.FusionHistoryIndex
        (p 0).1 (H.reverseAppendedLabels p)) ℂ :=
  H.toBNTFusionCoisometryFamily.recursiveProjectorQ
    (H.terminalEigenProjectionFamily hM s)
    (p 0).1 (H.reverseAppendedLabels p)

/-- One recursively transported terminal spectral projection in a fixed
copy-chain configuration.

Source: arXiv:1606.00608, lines 1003--1012. -/
def topologicalSpectralProjectorBlock (H : BNTFusionTensorClause M)
    (hM : IsMPDO M) {N : ℕ} (p : Fin (N + 1) → H.VerticalCopy)
    (s : H.TerminalSpectralIndex) :
    Matrix (H.VerticalCopyChainFiber p) (H.VerticalCopyChainFiber p) ℂ :=
  (H.verticalCopyChainFusionCoisometry p)ᴴ *
    H.recursiveTerminalEigenProjectorQ hM p s *
      H.verticalCopyChainFusionCoisometry p

/-- The all-label recursively transported projection attached to one terminal
spectral index on a positive chain of length `N + 1`.

Source: arXiv:1606.00608, lines 1003--1012. -/
def topologicalSpectralProjectorSucc (H : BNTFusionTensorClause M)
    (hM : IsMPDO M) (N : ℕ) (s : H.TerminalSpectralIndex) :
    Matrix (Fin (N + 1) → Fin H.verticalRetainedDim)
      (Fin (N + 1) → Fin H.verticalRetainedDim) ℂ :=
  Matrix.reindex (H.verticalCopyChainEquiv N).symm
    (H.verticalCopyChainEquiv N).symm
      (Matrix.blockDiagonal' fun p ↦ H.topologicalSpectralProjectorBlock hM p s)

/-- Length independence makes every recursive terminal spectral operator a
self-adjoint idempotent.

Source: arXiv:1606.00608, lines 1003--1012. -/
theorem recursiveTerminalEigenProjectorQ_isStarProjection
    (H : BNTFusionTensorClause M) (hM : IsMPDO M)
    (hLI : (BNTLabelCoefficientFamily.ofChi H.chi).LengthIndependent)
    {N : ℕ} (p : Fin (N + 1) → H.VerticalCopy)
    (s : H.TerminalSpectralIndex) :
    IsStarProjection (H.recursiveTerminalEigenProjectorQ hM p s) := by
  apply H.toBNTFusionCoisometryFamily.recursiveProjectorQ_isStarProjection
    (BNTLabelCoefficientFamily.ofChi H.chi)
    (BNTLabelCoefficientFamily.ofChi_hasPositiveLengthChiTracePowerForm H.chi)
    hLI
  intro γ
  exact (H.terminalEigenProjectionFamily_isOrthogonalProjection
    hM s γ).isStarProjection

/-- Transport through the adjoint sequential fusion coisometry gives an
orthogonal projection in every copy-chain block.

Source: arXiv:1606.00608, lines 1003--1012. -/
theorem topologicalSpectralProjectorBlock_isOrthogonalProjection
    (H : BNTFusionTensorClause M) (hM : IsMPDO M)
    (hLI : (BNTLabelCoefficientFamily.ofChi H.chi).LengthIndependent)
    {N : ℕ} (p : Fin (N + 1) → H.VerticalCopy)
    (s : H.TerminalSpectralIndex) :
    (H.topologicalSpectralProjectorBlock hM p s).IsHermitian ∧
      H.topologicalSpectralProjectorBlock hM p s *
        H.topologicalSpectralProjectorBlock hM p s =
          H.topologicalSpectralProjectorBlock hM p s := by
  have hP := IsStarProjection.conjTranspose_mul_mul_of_mul_conjTranspose_eq_one
    (H.recursiveTerminalEigenProjectorQ_isStarProjection hM hLI p s)
    (H.verticalCopyChainFusionCoisometry p)
    (H.verticalCopyChainFusionCoisometry_mul_conjTranspose p)
  rw [isStarProjection_iff'] at hP
  exact ⟨by
    unfold topologicalSpectralProjectorBlock
    change
      ((H.verticalCopyChainFusionCoisometry p)ᴴ *
        H.recursiveTerminalEigenProjectorQ hM p s *
          H.verticalCopyChainFusionCoisometry p)ᴴ =
        (H.verticalCopyChainFusionCoisometry p)ᴴ *
          H.recursiveTerminalEigenProjectorQ hM p s *
            H.verticalCopyChainFusionCoisometry p
    simpa [Matrix.star_eq_conjTranspose] using hP.2, hP.1⟩

/-- Recursive history operators attached to distinct terminal spectral indices
multiply to zero.

Source: arXiv:1606.00608, lines 1003--1012. -/
theorem recursiveTerminalEigenProjectorQ_mul_eq_zero
    (H : BNTFusionTensorClause M) (hM : IsMPDO M)
    (hLI : (BNTLabelCoefficientFamily.ofChi H.chi).LengthIndependent)
    {N : ℕ} (p : Fin (N + 1) → H.VerticalCopy)
    {s t : H.TerminalSpectralIndex} (hst : s ≠ t) :
    H.recursiveTerminalEigenProjectorQ hM p s *
        H.recursiveTerminalEigenProjectorQ hM p t = 0 := by
  unfold recursiveTerminalEigenProjectorQ
  rw [
    H.toBNTFusionCoisometryFamily.recursiveProjectorQ_eq_unweighted
      (BNTLabelCoefficientFamily.ofChi H.chi)
      (BNTLabelCoefficientFamily.ofChi_hasPositiveLengthChiTracePowerForm H.chi)
      hLI,
    H.toBNTFusionCoisometryFamily.recursiveProjectorQ_eq_unweighted
      (BNTLabelCoefficientFamily.ofChi H.chi)
      (BNTLabelCoefficientFamily.ofChi_hasPositiveLengthChiTracePowerForm H.chi)
      hLI,
    ← Matrix.blockDiagonal'_mul]
  ext ⟨h, x⟩ ⟨h', y⟩
  by_cases hhh' : h = h'
  · subst h'
    simp only [Matrix.blockDiagonal'_apply_eq]
    change
      (H.terminalEigenProjectionFamily hM s h.1 *
          H.terminalEigenProjectionFamily hM t h.1) x y = (0 : ℂ)
    rw [H.terminalEigenProjectionFamily_mul_eq_zero hM hst h.1]
    rfl
  · change _ = (0 : ℂ)
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ hhh']

/-- Distinct terminal spectral projections remain orthogonal after transport
through the adjoint sequential fusion coisometry.

Source: arXiv:1606.00608, lines 1003--1012. -/
theorem topologicalSpectralProjectorBlock_mul_eq_zero
    (H : BNTFusionTensorClause M) (hM : IsMPDO M)
    (hLI : (BNTLabelCoefficientFamily.ofChi H.chi).LengthIndependent)
    {N : ℕ} (p : Fin (N + 1) → H.VerticalCopy)
    {s t : H.TerminalSpectralIndex} (hst : s ≠ t) :
    H.topologicalSpectralProjectorBlock hM p s *
        H.topologicalSpectralProjectorBlock hM p t = 0 := by
  let W := H.verticalCopyChainFusionCoisometry p
  let Qs := H.recursiveTerminalEigenProjectorQ hM p s
  let Qt := H.recursiveTerminalEigenProjectorQ hM p t
  change (Wᴴ * Qs * W) * (Wᴴ * Qt * W) = 0
  calc
    (Wᴴ * Qs * W) * (Wᴴ * Qt * W) =
        Wᴴ * Qs * (W * Wᴴ) * Qt * W := by simp only [Matrix.mul_assoc]
    _ = Wᴴ * (Qs * Qt) * W := by
      rw [H.verticalCopyChainFusionCoisometry_mul_conjTranspose p]
      simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = 0 := by
      rw [H.recursiveTerminalEigenProjectorQ_mul_eq_zero hM hLI p hst,
        Matrix.mul_zero, Matrix.zero_mul]

/-- Every all-label terminal spectral component is an orthogonal projection at
each positive chain length.

Source: arXiv:1606.00608, lines 1003--1012. -/
theorem topologicalSpectralProjectorSucc_isOrthogonalProjection
    (H : BNTFusionTensorClause M) (hM : IsMPDO M)
    (hLI : (BNTLabelCoefficientFamily.ofChi H.chi).LengthIndependent)
    (N : ℕ) (s : H.TerminalSpectralIndex) :
    (H.topologicalSpectralProjectorSucc hM N s).IsHermitian ∧
      H.topologicalSpectralProjectorSucc hM N s *
        H.topologicalSpectralProjectorSucc hM N s =
          H.topologicalSpectralProjectorSucc hM N s := by
  constructor
  · unfold topologicalSpectralProjectorSucc
    apply Matrix.IsHermitian.reindex
    rw [Matrix.isHermitian_blockDiagonal'_iff]
    intro p
    exact (H.topologicalSpectralProjectorBlock_isOrthogonalProjection
      hM hLI p s).1
  · unfold topologicalSpectralProjectorSucc
    simp only [Matrix.reindex_apply]
    rw [Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal'_mul]
    have hFamily :
        (fun p : Fin (N + 1) → H.VerticalCopy ↦
          H.topologicalSpectralProjectorBlock hM p s *
            H.topologicalSpectralProjectorBlock hM p s) =
          fun p ↦ H.topologicalSpectralProjectorBlock hM p s := by
      funext p
      exact (H.topologicalSpectralProjectorBlock_isOrthogonalProjection
        hM hLI p s).2
    rw [hFamily]

/-- All-label projections attached to distinct terminal spectral indices
multiply to zero at every positive chain length.

Source: arXiv:1606.00608, lines 1003--1012. -/
theorem topologicalSpectralProjectorSucc_mul_eq_zero
    (H : BNTFusionTensorClause M) (hM : IsMPDO M)
    (hLI : (BNTLabelCoefficientFamily.ofChi H.chi).LengthIndependent)
    (N : ℕ) {s t : H.TerminalSpectralIndex} (hst : s ≠ t) :
    H.topologicalSpectralProjectorSucc hM N s *
        H.topologicalSpectralProjectorSucc hM N t = 0 := by
  unfold topologicalSpectralProjectorSucc
  simp only [Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal'_mul]
  have hFamily :
      (fun p : Fin (N + 1) → H.VerticalCopy ↦
        H.topologicalSpectralProjectorBlock hM p s *
          H.topologicalSpectralProjectorBlock hM p t) = 0 := by
    funext p
    exact H.topologicalSpectralProjectorBlock_mul_eq_zero hM hLI p hst
  rw [hFamily, Matrix.blockDiagonal'_zero]
  rfl

/-- Summing all spectral families with their terminal eigenvalues reconstructs
each terminal matrix.

Source: arXiv:1606.00608, lines 1009--1012. -/
theorem sum_terminalEigenvalue_smul_projectionFamily
    (H : BNTFusionTensorClause M) (hM : IsMPDO M)
    (γ : Fin H.labelCount) :
    ∑ s : H.TerminalSpectralIndex,
        (H.terminalEigenvalue hM s : ℂ) •
          H.terminalEigenProjectionFamily hM s γ =
      H.terminalMatrix γ := by
  rw [Fintype.sum_sigma, Finset.sum_eq_single γ]
  · simpa [terminalEigenProjectionFamily] using
      (H.terminalMatrix_eq_sum_eigenvalue_smul_projection hM γ).symm
  · intro α _ hαγ
    apply Finset.sum_eq_zero
    intro k _
    simp [terminalEigenProjectionFamily, Ne.symm hαγ]
  · simp

/-- The recursive history construction is linear in its terminal matrix
family. -/
private theorem sum_smul_recursiveProjectorQ
    {Λ ι : Type*} [Fintype Λ] [DecidableEq Λ] [Fintype ι]
    {p : ℕ} (Fam : BNTFusionCoisometryFamily Λ p)
    (a : ι → ℂ)
    (P : ι → ∀ γ : Λ,
      Matrix (Fin (Fam.bondDim γ)) (Fin (Fam.bondDim γ)) ℂ)
    (α : Λ) (previous : List Λ) :
    ∑ i : ι, a i • Fam.recursiveProjectorQ (P i) α previous =
      Fam.recursiveProjectorQ (fun γ ↦ ∑ i : ι, a i • P i γ) α previous := by
  unfold BNTFusionCoisometryFamily.recursiveProjectorQ
  ext ⟨h, x⟩ ⟨h', y⟩
  by_cases hhh' : h = h'
  · subst h'
    simp only [Matrix.sum_apply, Matrix.smul_apply,
      Matrix.blockDiagonal'_apply_eq, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · simp [Matrix.sum_apply, Matrix.smul_apply,
      Matrix.blockDiagonal'_apply_ne _ _ _ hhh']

/-- The eigenvalue-weighted sum of the recursive spectral history operators
reconstructs the recursive terminal operator.

Source: arXiv:1606.00608, lines 1003--1012. -/
theorem sum_terminalEigenvalue_smul_recursiveTerminalEigenProjectorQ
    (H : BNTFusionTensorClause M) (hM : IsMPDO M)
    {N : ℕ} (p : Fin (N + 1) → H.VerticalCopy) :
    ∑ s : H.TerminalSpectralIndex,
        (H.terminalEigenvalue hM s : ℂ) •
          H.recursiveTerminalEigenProjectorQ hM p s =
      H.verticalCopyChainProjectorQ p := by
  unfold recursiveTerminalEigenProjectorQ verticalCopyChainProjectorQ
  rw [sum_smul_recursiveProjectorQ]
  congr 2
  funext γ
  exact H.sum_terminalEigenvalue_smul_projectionFamily hM γ

/-- The eigenvalue-weighted sum of the transported copy-chain projections
reconstructs the recursive topological block.

Source: arXiv:1606.00608, lines 1003--1012. -/
theorem sum_terminalEigenvalue_smul_topologicalSpectralProjectorBlock
    (H : BNTFusionTensorClause M) (hM : IsMPDO M)
    {N : ℕ} (p : Fin (N + 1) → H.VerticalCopy) :
    ∑ s : H.TerminalSpectralIndex,
        (H.terminalEigenvalue hM s : ℂ) •
          H.topologicalSpectralProjectorBlock hM p s =
      (H.verticalCopyChainFusionCoisometry p)ᴴ *
        H.verticalCopyChainProjectorQ p *
          H.verticalCopyChainFusionCoisometry p := by
  unfold topologicalSpectralProjectorBlock
  calc
    ∑ s : H.TerminalSpectralIndex,
        (H.terminalEigenvalue hM s : ℂ) •
          ((H.verticalCopyChainFusionCoisometry p)ᴴ *
            H.recursiveTerminalEigenProjectorQ hM p s *
              H.verticalCopyChainFusionCoisometry p) =
      (H.verticalCopyChainFusionCoisometry p)ᴴ *
        (∑ s : H.TerminalSpectralIndex,
          (H.terminalEigenvalue hM s : ℂ) •
            H.recursiveTerminalEigenProjectorQ hM p s) *
          H.verticalCopyChainFusionCoisometry p := by
            rw [Matrix.mul_sum, Matrix.sum_mul]
            apply Finset.sum_congr rfl
            intro s _
            rw [Matrix.mul_smul, Matrix.smul_mul]
    _ = _ := by
      rw [H.sum_terminalEigenvalue_smul_recursiveTerminalEigenProjectorQ hM p]

/-- The eigenvalue-weighted sum of the all-label spectral projections
reconstructs the recursive topological factor at every positive chain length.

Source: arXiv:1606.00608, lines 1003--1012. -/
theorem sum_terminalEigenvalue_smul_topologicalSpectralProjectorSucc
    (H : BNTFusionTensorClause M) (hM : IsMPDO M) (N : ℕ) :
    ∑ s : H.TerminalSpectralIndex,
        (H.terminalEigenvalue hM s : ℂ) •
          H.topologicalSpectralProjectorSucc hM N s =
      H.topologicalRecursiveFactorSucc N := by
  ext i j
  obtain ⟨⟨p, x⟩, rfl⟩ := (H.verticalCopyChainEquiv N).symm.surjective i
  obtain ⟨⟨q, y⟩, rfl⟩ := (H.verticalCopyChainEquiv N).symm.surjective j
  unfold topologicalSpectralProjectorSucc topologicalRecursiveFactorSucc
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, Equiv.apply_symm_apply]
  by_cases hpq : p = q
  · subst q
    simp only [Matrix.blockDiagonal'_apply_eq]
    simpa only [Matrix.sum_apply, Matrix.smul_apply] using
      congrFun (congrFun
        (H.sum_terminalEigenvalue_smul_topologicalSpectralProjectorBlock hM p) x) y
  · simp [Matrix.blockDiagonal'_apply_ne _ _ _ hpq]

/-- The all-label multiplicity-weight factor commutes with every terminal
spectral projection.

Source: arXiv:1606.00608, commutator identity at lines 1000--1012. -/
theorem topologicalMultiplicityWeightFactorSucc_commutes_spectralProjector
    (H : BNTFusionTensorClause M) (hM : IsMPDO M)
    (N : ℕ) (s : H.TerminalSpectralIndex) :
    H.topologicalMultiplicityWeightFactorSucc N *
        H.topologicalSpectralProjectorSucc hM N s =
      H.topologicalSpectralProjectorSucc hM N s *
        H.topologicalMultiplicityWeightFactorSucc N := by
  unfold topologicalMultiplicityWeightFactorSucc
    topologicalSpectralProjectorSucc
  simp only [Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
    ← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
  congr 1
  funext p
  simp

/-- The all-label density operator is the eigenvalue-weighted sum of the
multiplicity-weight factor restricted to the terminal spectral projections.

Source: arXiv:1606.00608, lines 999--1012. -/
theorem topologicalDensityOperatorSucc_eq_sum_terminalSpectralProjector
    (H : BNTFusionTensorClause M) (hM : IsMPDO M) (N : ℕ) :
    H.topologicalDensityOperatorSucc N =
      ∑ s : H.TerminalSpectralIndex,
        (H.terminalEigenvalue hM s : ℂ) •
          (H.topologicalMultiplicityWeightFactorSucc N *
            H.topologicalSpectralProjectorSucc hM N s) := by
  calc
    H.topologicalDensityOperatorSucc N =
        H.topologicalMultiplicityWeightFactorSucc N *
          H.topologicalRecursiveFactorSucc N :=
      H.topologicalDensityOperatorSucc_eq_multiplicityWeight_mul_recursiveFactor N
    _ = H.topologicalMultiplicityWeightFactorSucc N *
        (∑ s : H.TerminalSpectralIndex,
          (H.terminalEigenvalue hM s : ℂ) •
            H.topologicalSpectralProjectorSucc hM N s) := by
      rw [H.sum_terminalEigenvalue_smul_topologicalSpectralProjectorSucc hM N]
    _ = _ := by
      rw [Matrix.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      rw [Matrix.mul_smul]

/-- The terminal spectral refinement of the all-label recursive density
factor.  The eigenweights are nonnegative; at every positive chain length the
transported operators are self-adjoint idempotents, are pairwise orthogonal,
resolve the recursive factor, commute with the multiplicity-weight factor, and
give the corresponding weighted density decomposition.

Source: arXiv:1606.00608, lines 999--1012.  This predicate stops before the
commuting-Hamiltonian and Gibbs-state conclusion beginning at line 1013. -/
def HasTerminalSpectralProjectorRefinement (H : BNTFusionTensorClause M)
    (hM : IsMPDO M) : Prop :=
  (∀ s : H.TerminalSpectralIndex, 0 ≤ H.terminalEigenvalue hM s) ∧
    ∀ N : ℕ,
      (∀ s : H.TerminalSpectralIndex,
        (H.topologicalSpectralProjectorSucc hM N s).IsHermitian ∧
          H.topologicalSpectralProjectorSucc hM N s *
              H.topologicalSpectralProjectorSucc hM N s =
            H.topologicalSpectralProjectorSucc hM N s) ∧
      (∀ s t : H.TerminalSpectralIndex, s ≠ t →
        H.topologicalSpectralProjectorSucc hM N s *
            H.topologicalSpectralProjectorSucc hM N t = 0) ∧
      (∑ s : H.TerminalSpectralIndex,
          (H.terminalEigenvalue hM s : ℂ) •
            H.topologicalSpectralProjectorSucc hM N s =
        H.topologicalRecursiveFactorSucc N) ∧
      (∀ s : H.TerminalSpectralIndex,
        H.topologicalMultiplicityWeightFactorSucc N *
            H.topologicalSpectralProjectorSucc hM N s =
          H.topologicalSpectralProjectorSucc hM N s *
            H.topologicalMultiplicityWeightFactorSucc N) ∧
      H.topologicalDensityOperatorSucc N =
        ∑ s : H.TerminalSpectralIndex,
          (H.terminalEigenvalue hM s : ℂ) •
            (H.topologicalMultiplicityWeightFactorSucc N *
              H.topologicalSpectralProjectorSucc hM N s)

/-- Length independence gives the terminal spectral projector refinement for
one chosen BNT fusion clause.

Source: arXiv:1606.00608, lines 1003--1012. -/
theorem hasTerminalSpectralProjectorRefinement
    (H : BNTFusionTensorClause M) (hM : IsMPDO M)
    (hLI : (BNTLabelCoefficientFamily.ofChi H.chi).LengthIndependent) :
    H.HasTerminalSpectralProjectorRefinement hM := by
  refine ⟨H.terminalEigenvalue_nonneg hM, fun N ↦ ?_⟩
  exact ⟨H.topologicalSpectralProjectorSucc_isOrthogonalProjection hM hLI N,
    fun _ _ hst ↦ H.topologicalSpectralProjectorSucc_mul_eq_zero hM hLI N hst,
    H.sum_terminalEigenvalue_smul_topologicalSpectralProjectorSucc hM N,
    H.topologicalMultiplicityWeightFactorSucc_commutes_spectralProjector hM N,
    H.topologicalDensityOperatorSucc_eq_sum_terminalSpectralProjector hM N⟩

end MPOTensor.BNTFusionTensorClause

namespace MPOTensor

variable {d D : ℕ}

/-- The BNT fusion clause selected from the renormalization fixed-point
construction under normalized BNT-refined horizontal form.

**Scope restriction (BNT-refined horizontal form):** `IsHorizontalCF` is
stronger than the literal CPSV canonical form; see
`docs/paper-gaps/cpgsv17_vertical_cf_grouping.tex`.

Source: arXiv:1606.00608, Theorem 4.14(i),(iii), lines 972--993. -/
noncomputable def rfpBNTFusionTensorClause (M : MPOTensor d D)
    (hHorizontal : IsHorizontalCF M) (hM : IsMPDO M)
    (hRFP : IsRFPViaTS M) : BNTFusionTensorClause M :=
  Classical.choice
    (HasBNTFusionTensorClause.of_isRFPViaTS M hHorizontal hM hRFP)

/-- **Terminal spectral projector refinement for a length-independent RFP
MPDO.**

The fusion clause is fixed under normalized BNT-refined horizontal form by
`rfpBNTFusionTensorClause M hHorizontal hM hRFP`; no additional fusion clause,
spectral family, or projector hypothesis is assumed.  Length independence is
stated on the coefficient family of exactly that RFP-derived clause.  This is
the present clause-relative representation of the source length-independence
assumption.

The conclusion supplies the line-999 density decomposition, the line-1001
factor commutator, and the nonnegative terminal eigenweights with compatible
all-label orthogonal projectors and their weighted reconstruction.

**Scope restriction (BNT-refined horizontal form):** `IsHorizontalCF` is
stronger than the literal CPSV canonical form used by Proposition 4.13 and
Theorem 4.14; see `docs/paper-gaps/cpgsv17_vertical_cf_grouping.tex`.

Source: arXiv:1606.00608, lines 999--1012.  This theorem does not assert the
commuting nearest-neighbor Hamiltonian or Gibbs-state conclusion beginning at
line 1013. -/
theorem terminalSpectralProjectorRefinement_of_isRFPViaTS
    (M : MPOTensor d D) (hHorizontal : IsHorizontalCF M) (hM : IsMPDO M)
    (hRFP : IsRFPViaTS M)
    (hLI : (BNTLabelCoefficientFamily.ofChi
      (rfpBNTFusionTensorClause M hHorizontal hM hRFP).chi).LengthIndependent) :
    let H := rfpBNTFusionTensorClause M hHorizontal hM hRFP
    H.HasTopologicalDensityDecomposition ∧
      H.HasTopologicalDensityFactorCommutator ∧
        H.HasTerminalSpectralProjectorRefinement hM := by
  dsimp only
  exact ⟨BNTFusionTensorClause.hasTopologicalDensityDecomposition
      (rfpBNTFusionTensorClause M hHorizontal hM hRFP),
    BNTFusionTensorClause.hasTopologicalDensityFactorCommutator
      (rfpBNTFusionTensorClause M hHorizontal hM hRFP),
    BNTFusionTensorClause.hasTerminalSpectralProjectorRefinement
      (rfpBNTFusionTensorClause M hHorizontal hM hRFP) hM hLI⟩

end MPOTensor
