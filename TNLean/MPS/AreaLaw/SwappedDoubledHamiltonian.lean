/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.DoubledHamiltonian
import TNLean.Lattice.RegionalSwapSupport

/-!
# The swapped doubled Hamiltonian on a chain

Conjugating each doubled interaction by the regional sheet swap preserves its
support and the bound `2 * J`. The normalized tensor square of the original
ground vector and its swap image have energy `2 * E₀` and lower gap `Δ`.

## Main results

* `ChainHamiltonian.swappedDoubled`: the conjugated doubled interaction family.
* `ChainHamiltonian.swappedDoubled_operator`: the exact conjugated operator.
* `ChainHamiltonian.doubled_swappedDoubled_isGappedGroundState`: the normalized
  explicit ground vectors, their doubled energy and their inherited lower gap.

**Scope restriction (contiguous chains):** The physical sites are `Fin L`.
The broader source domain may have gaps; see
`docs/paper-gaps/tnlean_one_dimensional_connected_domain_scope.tex`.

Source: TNLean one-dimensional note, `part2a_mps_information.tex`, lines 355–363.
No equality of spectral gaps or Gaussian-filter construction is asserted.
-/

open Matrix QuantumCircuit
open scoped Kronecker Matrix.Norms.L2Operator ComplexOrder
open TNLean.Lattice (norm_sheetSwapOp_le_one
  reindex_sheetSwapOp_conj_doubledHamiltonian_mem_supportedOperators sheetSwap sheetSwapOp)

namespace TNLean.MPS.AreaLaw

/-- The doubled interactions conjugated by the regional sheet swap.
Source: TNLean note, `part2a_mps_information.tex`, lines 355–363. -/
noncomputable def ChainHamiltonian.swappedDoubled
    {L q R : ℕ} {J : ℝ} (h : ChainHamiltonian L q R J) (D : Finset (Fin L)) :
    ChainHamiltonian L (q * q) R (2 * J) where
  term X :=
    let e := sitePairConfigurationEquiv (Fin L) q q
    let F := Matrix.reindex e e (sheetSwapOp q D)
    F * h.doubled.term X * Fᴴ
  supported X := by
    apply isSupportedOn_of_mem_supportedOperators
    exact reindex_sheetSwapOp_conj_doubledHamiltonian_mem_supportedOperators
      D X.1 (mem_supportedOperators_of_isSupportedOn (h.supported X))
  hermitian X :=
    Matrix.isHermitian_mul_mul_conjTranspose _ (h.doubled.hermitian X)
  norm_le X := by
    let e := sitePairConfigurationEquiv (Fin L) q q
    let F := Matrix.reindex e e (sheetSwapOp q D)
    have hF : ‖F‖ ≤ 1 := by
      simpa only [F, Matrix.l2_opNorm_reindex_equiv] using norm_sheetSwapOp_le_one (q := q) D
    have hFadj : ‖Fᴴ‖ ≤ 1 := by simpa only [Matrix.l2_opNorm_conjTranspose] using hF
    change ‖F * h.doubled.term X * Fᴴ‖ ≤ 2 * J
    simpa only [one_mul, mul_one] using
      norm_mul_le_of_le (norm_mul_le_of_le hF (h.doubled.norm_le X)) hFadj

/-- The sum of the swapped interactions is the conjugate of the doubled operator.
Source: TNLean note, `part2a_mps_information.tex`, lines 355–363. -/
lemma ChainHamiltonian.swappedDoubled_operator
    {L q R : ℕ} {J : ℝ} (h : ChainHamiltonian L q R J)
    (D : Finset (Fin L)) :
    let e := QuantumCircuit.sitePairConfigurationEquiv (Fin L) q q
    let F := Matrix.reindex e e (TNLean.Lattice.sheetSwapOp q D)
    (h.swappedDoubled D).operator = F * h.doubled.operator * Fᴴ := by
  simp only [ChainHamiltonian.operator, ChainHamiltonian.swappedDoubled,
    Matrix.sum_mul, Matrix.mul_sum]

/-- The paired tensor-square ground vector and its regional swap image
have doubled energy and the original positive lower-gap bound.
Source: TNLean note, `part2a_mps_information.tex`, lines 355–363. -/
theorem ChainHamiltonian.doubled_swappedDoubled_isGappedGroundState
    {L q R : ℕ} {J E₀ Δ : ℝ} (h : ChainHamiltonian L q R J)
    (D : Finset (Fin L)) {Ω : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : Matrix.IsGappedGroundState h.operator E₀ Ω Δ) (hΔ : 0 < Δ) :
    let e := QuantumCircuit.sitePairConfigurationEquiv (Fin L) q q
    let F := Matrix.reindex e e (TNLean.Lattice.sheetSwapOp q D)
    let ψ₀ := Matrix.doubledVector (WithLp.ofLp Ω)
    let Ψ : EuclideanSpace ℂ (Fin L → Fin (q * q)) :=
      WithLp.toLp 2 (ψ₀ ∘ e.symm)
    let Φ : EuclideanSpace ℂ (Fin L → Fin (q * q)) :=
      WithLp.toLp 2 (F *ᵥ WithLp.ofLp Ψ)
    Matrix.IsGappedGroundState h.doubled.operator (2 * E₀) Ψ Δ ∧
      Matrix.IsGappedGroundState (h.swappedDoubled D).operator (2 * E₀) Φ Δ := by
  classical
  let e := sitePairConfigurationEquiv (Fin L) q q
  let F := Matrix.reindex e e (sheetSwapOp q D)
  let ψ₀ := Matrix.doubledVector (WithLp.ofLp Ω)
  let Ψ : EuclideanSpace ℂ (Fin L → Fin (q * q)) := WithLp.toLp 2 (ψ₀ ∘ e.symm)
  let Φ : EuclideanSpace ℂ (Fin L → Fin (q * q)) :=
    WithLp.toLp 2 (F *ᵥ WithLp.ofLp Ψ)
  change Matrix.IsGappedGroundState h.doubled.operator (2 * E₀) Ψ Δ ∧
    Matrix.IsGappedGroundState (h.swappedDoubled D).operator (2 * E₀) Φ Δ
  obtain ⟨hΩ, heigen, hgap⟩ := Matrix.isGappedGroundState_iff.mp hgs
  have hΩsum : ∑ i, ‖WithLp.ofLp Ω i‖ ^ 2 = 1 := by
    rw [← EuclideanSpace.norm_sq_eq, hΩ]
    norm_num
  have hgapΨ : (h.doubled.operator - ((2 * E₀ : ℝ) : ℂ) • 1 -
      (Δ : ℂ) • (1 - vecMulVec (WithLp.ofLp Ψ) (star (WithLp.ofLp Ψ)))).PosSemidef := by
    have hg := (hgap.doubled_gap hΩsum hΔ.le).submatrix e.symm
    rw [h.doubled_operator]
    convert hg using 1
    change _ = (Matrix.reindexAlgEquiv ℂ ℂ e)
      (doubledHamiltonian h.operator - ((2 * E₀ : ℝ) : ℂ) • 1 -
        (Δ : ℂ) • (1 - vecMulVec ψ₀ (star ψ₀)))
    simp only [map_sub, map_smul, map_one]
    rfl
  have hΨ : ‖Ψ‖ = 1 := by
    have hi := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).norm_map
      (WithLp.toLp 2 ψ₀)
    change ‖Ψ‖ = ‖WithLp.toLp 2 ψ₀‖ at hi
    exact hi.trans (Matrix.norm_doubledVector hΩsum)
  have heigenΨ : h.doubled.operator *ᵥ WithLp.ofLp Ψ =
      ((2 * E₀ : ℝ) : ℂ) • WithLp.ofLp Ψ := by
    rw [h.doubled_operator]
    change Matrix.reindex e e (doubledHamiltonian h.operator) *ᵥ
      (ψ₀ ∘ e.symm) = _
    rw [Matrix.reindex_mulVec, Matrix.doubledHamiltonian_mulVec heigen]
    rfl
  have hF : F ∈ Matrix.unitaryGroup _ ℂ :=
    Matrix.reindex_mem_unitaryGroup e (sheetSwapOp q D)
      (sheetSwap q D).permMatrix_mem_unitaryGroup
  refine ⟨Matrix.isGappedGroundState_iff.mpr ⟨hΨ, heigenΨ, hgapΨ⟩, ?_⟩
  apply Matrix.isGappedGroundState_iff.mpr
  rw [h.swappedDoubled_operator]
  change ‖Φ‖ = 1 ∧ (F * h.doubled.operator * Fᴴ) *ᵥ (F *ᵥ WithLp.ofLp Ψ) =
    ((2 * E₀ : ℝ) : ℂ) • (F *ᵥ WithLp.ofLp Ψ) ∧ _
  refine ⟨?_, Matrix.mulVec_unitary_conj_eigenvector hF heigenΨ,
    hgapΨ.gap_unitary_conj hF⟩
  change ‖WithLp.toLp 2 (F *ᵥ WithLp.ofLp Ψ)‖ = 1
  rw [Matrix.norm_toLp_mulVec_of_unitary hF]
  exact hΨ

end TNLean.MPS.AreaLaw
