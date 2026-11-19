/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.DoubledHamiltonian
import TNLean.Lattice.RegionalSwapSupport
import QICLean.ManyBody.Hamiltonian.KroneckerSum

/-!
# The swapped doubled Hamiltonian on a chain

Conjugating each doubled interaction by the regional sheet swap preserves its
support and the bound `2 * J`. The normalized tensor square of the original
ground vector and its swap image have energy `2 * E₀` and lower gap `Δ`.

## Main results

* `ManyBody.ChainInteraction.swappedDoubled`: the conjugated doubled interaction family.
* `ManyBody.ChainInteraction.swappedDoubled_hamiltonian`: the exact conjugated operator.
* `ManyBody.ChainInteraction.doubled_swappedDoubled_isGapped`: the normalized
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

open ManyBody (IsGapped groundSpace ChainInteraction)

namespace TNLean.MPS.AreaLaw

/-- The doubled interactions conjugated by the regional sheet swap.
Source: TNLean note, `part2a_mps_information.tex`, lines 355–363. -/
noncomputable def _root_.ManyBody.ChainInteraction.swappedDoubled
    {L q R : ℕ} (h : ManyBody.ChainInteraction L q R) (D : Finset (Fin L)) :
    ManyBody.ChainInteraction L (q * q) R where
  term X :=
    let e := sitePairConfigurationEquiv (Fin L) q q
    let F := Matrix.reindex e e (sheetSwapOp q D)
    F * h.doubled.term X * Fᴴ
  mem X := by
    exact reindex_sheetSwapOp_conj_doubledHamiltonian_mem_supportedOperators
      D X.1 (h.mem X)

/-- The swapped doubled terms of Hermitian terms are Hermitian.
Source: TNLean note, `part2a_mps_information.tex`, lines 355–363. -/
theorem _root_.ManyBody.ChainInteraction.isHermitian_swappedDoubled_term {L q R : ℕ}
    (h : ManyBody.ChainInteraction L q R) (hh : ∀ X, (h.term X).IsHermitian)
    (D : Finset (Fin L)) (X : ManyBody.ChainSupport L R) :
    ((h.swappedDoubled D).term X).IsHermitian :=
  Matrix.isHermitian_mul_mul_conjTranspose _ (h.isHermitian_doubled_term hh X)

/-- Each swapped doubled term has norm at most `2 * J`.
Source: TNLean note, `part2a_mps_information.tex`, lines 355–363. -/
theorem _root_.ManyBody.ChainInteraction.norm_swappedDoubled_term_le {L q R : ℕ} {J : ℝ}
    (h : ManyBody.ChainInteraction L q R) (hhJ : ∀ X, ‖h.term X‖ ≤ J)
    (D : Finset (Fin L)) (X : ManyBody.ChainSupport L R) :
    ‖(h.swappedDoubled D).term X‖ ≤ 2 * J := by
  let e := sitePairConfigurationEquiv (Fin L) q q
  let F := Matrix.reindex e e (sheetSwapOp q D)
  have hF : ‖F‖ ≤ 1 := by
    simpa only [F, Matrix.l2_opNorm_reindex_equiv] using norm_sheetSwapOp_le_one (q := q) D
  have hFadj : ‖Fᴴ‖ ≤ 1 := by simpa only [Matrix.l2_opNorm_conjTranspose] using hF
  change ‖F * h.doubled.term X * Fᴴ‖ ≤ 2 * J
  simpa only [one_mul, mul_one] using
    norm_mul_le_of_le (norm_mul_le_of_le hF (h.norm_doubled_term_le hhJ X)) hFadj

/-- The sum of the swapped interactions is the conjugate of the doubled operator.
Source: TNLean note, `part2a_mps_information.tex`, lines 355–363. -/
lemma _root_.ManyBody.ChainInteraction.swappedDoubled_hamiltonian
    {L q R : ℕ} (h : ChainInteraction L q R)
    (D : Finset (Fin L)) :
    let e := QuantumCircuit.sitePairConfigurationEquiv (Fin L) q q
    let F := Matrix.reindex e e (TNLean.Lattice.sheetSwapOp q D)
    (h.swappedDoubled D).hamiltonian = F * h.doubled.hamiltonian * Fᴴ := by
  simp only [ManyBody.Interaction.hamiltonian, ManyBody.ChainInteraction.swappedDoubled,
    Matrix.sum_mul, Matrix.mul_sum]

/-- The paired tensor-square ground vector and its regional swap image
have doubled energy and the original positive lower-gap bound.
Source: TNLean note, `part2a_mps_information.tex`, lines 355–363. -/
theorem _root_.ManyBody.ChainInteraction.doubled_swappedDoubled_isGapped
    {L q R : ℕ} {E₀ Δ : ℝ} (h : ChainInteraction L q R) (hh : ∀ X, (h.term X).IsHermitian)
    (D : Finset (Fin L)) {Ω : EuclideanSpace ℂ (Fin L → Fin q)}
    (hΩ : ‖Ω‖ = 1) (hgap : IsGapped h.hamiltonian E₀ Δ)
    (hspan : groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω}) (hΔ : 0 < Δ) :
    let e := QuantumCircuit.sitePairConfigurationEquiv (Fin L) q q
    let F := Matrix.reindex e e (TNLean.Lattice.sheetSwapOp q D)
    let ψ₀ := Matrix.doubledVector (WithLp.ofLp Ω)
    let Ψ : EuclideanSpace ℂ (Fin L → Fin (q * q)) :=
      WithLp.toLp 2 (ψ₀ ∘ e.symm)
    let Φ : EuclideanSpace ℂ (Fin L → Fin (q * q)) :=
      WithLp.toLp 2 (F *ᵥ WithLp.ofLp Ψ)
    (‖Ψ‖ = 1 ∧ IsGapped h.doubled.hamiltonian (2 * E₀) Δ ∧
      groundSpace h.doubled.hamiltonian (2 * E₀) = Submodule.span ℂ {Ψ}) ∧
      (‖Φ‖ = 1 ∧ IsGapped (h.swappedDoubled D).hamiltonian (2 * E₀) Δ ∧
        groundSpace (h.swappedDoubled D).hamiltonian (2 * E₀) = Submodule.span ℂ {Φ}) := by
  classical
  let e := sitePairConfigurationEquiv (Fin L) q q
  let F := Matrix.reindex e e (sheetSwapOp q D)
  let ψ₀ := Matrix.doubledVector (WithLp.ofLp Ω)
  let Ψ : EuclideanSpace ℂ (Fin L → Fin (q * q)) := WithLp.toLp 2 (ψ₀ ∘ e.symm)
  let Φ : EuclideanSpace ℂ (Fin L → Fin (q * q)) :=
    WithLp.toLp 2 (F *ᵥ WithLp.ofLp Ψ)
  change (‖Ψ‖ = 1 ∧ IsGapped h.doubled.hamiltonian (2 * E₀) Δ ∧
    groundSpace h.doubled.hamiltonian (2 * E₀) = Submodule.span ℂ {Ψ}) ∧
    (‖Φ‖ = 1 ∧ IsGapped (h.swappedDoubled D).hamiltonian (2 * E₀) Δ ∧
      groundSpace (h.swappedDoubled D).hamiltonian (2 * E₀) = Submodule.span ℂ {Φ})
  have hH := (ManyBody.Interaction.isHermitian_hamiltonian hh)
  have hgK := hgap.kronecker_add hH hH hgap (Or.inl hΔ.le)
  have hsK := ManyBody.groundSpace_kronecker_add_eq_span hH hH hgap hgap hΔ.le hΔ.le hspan hspan
  rw [min_self] at hgK
  have hgapD : IsGapped h.doubled.hamiltonian (2 * E₀) Δ := by
    rw [h.doubled_hamiltonian, ManyBody.isGapped_reindex_iff, two_mul]
    exact hgK
  have hspanD : groundSpace h.doubled.hamiltonian (2 * E₀) = Submodule.span ℂ {Ψ} := by
    rw [h.doubled_hamiltonian, two_mul]
    exact ManyBody.groundSpace_reindex_eq_span e hsK
  have hΩsum : ∑ i, ‖WithLp.ofLp Ω i‖ ^ 2 = 1 := by
    rw [← EuclideanSpace.norm_sq_eq, hΩ]
    norm_num
  have hΨ : ‖Ψ‖ = 1 := by
    have hi := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).norm_map
      (WithLp.toLp 2 ψ₀)
    change ‖Ψ‖ = ‖WithLp.toLp 2 ψ₀‖ at hi
    exact hi.trans (Matrix.norm_doubledVector hΩsum)
  have hF : F ∈ Matrix.unitaryGroup _ ℂ :=
    Matrix.reindex_mem_unitaryGroup e (sheetSwapOp q D)
      (sheetSwap q D).permMatrix_mem_unitaryGroup
  refine ⟨⟨hΨ, hgapD, hspanD⟩, ?_⟩
  have hΦ : Matrix.toEuclideanLin F Ψ = Φ := rfl
  have hΦn : ‖Φ‖ = 1 := by
    change ‖WithLp.toLp 2 (F *ᵥ WithLp.ofLp Ψ)‖ = 1
    rw [Matrix.norm_toLp_mulVec_of_unitary hF]
    exact hΨ
  rw [h.swappedDoubled_hamiltonian, ← hΦ]
  exact ⟨by rw [hΦ]; exact hΦn, (ManyBody.isGapped_unitary_conj_iff hF).mpr hgapD,
    ManyBody.groundSpace_unitary_conj_eq_span hF hspanD⟩

end TNLean.MPS.AreaLaw
