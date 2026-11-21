/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.ProjectionGeometry
import TNLean.MPS.ParentHamiltonian.CyclicWindow
import QICLean.ManyBody.Hamiltonian.Martingale.AbstractCriterion
import TNLean.MPS.ParentHamiltonian.Martingale.Transport

/-!
# Martingale quadratic-form reduction chain

**Root-only.** This file contains the reduction theorems that convert
explicit local-projection bounds into the quadratic-form inequality
\(H² ≥ γ H\) for the Hamiltonian \(H\) of the parent interaction on the ring
(`parentRingInteraction`) and then into the norm lower bound \(γ ‖v‖ ≤ ‖H v‖\) on the
orthogonal complement of its kernel.

The chain proceeds from the most abstract (ordered row-sum of local
cross-term bounds) through finite-overlap reductions down to the
concrete cyclic-window overlap predicate and its row-cardinality bound
\(2(L - 1)\). The final reduction theorems (`*_gap_bound_of_cyclic_window_*`)
supply all the already-proved structural input (local projection,
non-overlap positivity, and row cardinality) and leave only the
source anticommutator estimate as a remaining hypothesis.

The abstract spectral-theorem step
(`FrustrationFree.spectralGap_of_martingale_of_finiteDimensional`) and the
projection-geometry lemmas (`ProjectionGeometry.quadraticForm_sum_*`) supply the
reusable algebra, while the MPS-specific definitions and structural theorems
live in `Martingale.Transport`.

The uniform reductions are stated, in the last section, for the Hamiltonian of the parent
interaction on the ring on rings of \(N ≥ 2L\) sites and the operators of its terms. The
fixed-chain quadratic-form reductions `parentHamiltonianES_quadratic_form_of_*`, stated for the
Euclidean-space operators `localTermES` and `parentHamiltonianES` at every chain length without
\(L ≤ N\), are kept as they are until the parent interaction on the ring is defined for every
chain length.
-/

open scoped BigOperators InnerProductSpace

namespace MPSTensor

variable {d D : ℕ}

/-! ### Martingale quadratic-form reduction -/

/-- Fixed-chain martingale quadratic-form estimate from ordered local
cross-term row bounds.

This theorem is the parent-Hamiltonian instantiation of the abstract projection
geometry in `ProjectionGeometry.quadraticForm_sum_projections_of_ordered_rowSum`.
The local projection input is supplied by `localTermES_isSymmetricProjection`, so
its hypotheses are only the ordered row-summable cross-term bounds

\(\operatorname{Re}\langle h_i v, h_j v\rangle ≥
-(1 - γ)c_{ij}\operatorname{Re}\langle h_i v, v\rangle\).

Under these hypotheses the Euclidean-space Hamiltonian satisfies \(H² ≥ γ H\)
as a quadratic form, the shape consumed by the abstract spectral-theorem step
`FrustrationFree.spectralGap_of_martingale_of_finiteDimensional`. -/
theorem parentHamiltonianES_quadratic_form_of_ordered_local_term_bounds
    (A : MPSTensor d D) (L N : ℕ) {γ : ℝ} (hγle : γ ≤ 1)
    (c : Fin N → Fin N → ℝ)
    (hRow : ∀ i : Fin N, (∑ j ∈ Finset.univ.erase i, c i j) ≤ 1)
    (hCross : ∀ i j : Fin N, j ∈ Finset.univ.erase i →
      ∀ v : EuclideanSpace ℂ (Cfg d N),
        - (1 - γ) * c i j * (⟪localTermES A L i v, v⟫_ℂ).re ≤
          (⟪localTermES A L i v, localTermES A L j v⟫_ℂ).re) :
    ∀ v : EuclideanSpace ℂ (Cfg d N),
      γ * (⟪parentHamiltonianES A L N v, v⟫_ℂ).re ≤
        (⟪parentHamiltonianES A L N v,
          parentHamiltonianES A L N v⟫_ℂ).re := by
  intro v
  simpa [parentHamiltonianES_eq_sum_localTermES A L N] using
    (ProjectionGeometry.quadraticForm_sum_projections_of_ordered_rowSum
      (ι := Fin N) (E := EuclideanSpace ℂ (Cfg d N)) hγle
      (fun i : Fin N => localTermES A L i)
      (fun i : Fin N => localTermES_isSymmetricProjection A L i) c hRow hCross v)

/-- Fixed-chain martingale quadratic-form estimate from source anticommutator
row bounds.

arXiv:2011.12127, Section IV.C, lines 2176-2179, use the local estimate
\[
  h_i h_j+h_j h_i \ge -c_{ij}(1-\gamma)(h_i+h_j)
\]
with row-summable coefficients. This theorem is the Euclidean-space
parent-Hamiltonian instantiation of that anticommutator form. The column-sum
hypothesis is stated separately; it follows from the row-sum condition when the
coefficient matrix is symmetric. -/
theorem parentHamiltonianES_quadratic_form_of_anticommutator_local_term_bounds
    (A : MPSTensor d D) (L N : ℕ) {γ : ℝ} (hγle : γ ≤ 1)
    (c : Fin N → Fin N → ℝ)
    (hRow : ∀ i : Fin N, (∑ j ∈ Finset.univ.erase i, c i j) ≤ 1)
    (hCol : ∀ j : Fin N, (∑ i ∈ Finset.univ.erase j, c i j) ≤ 1)
    (hAnti : ∀ i j : Fin N, j ∈ Finset.univ.erase i →
      ∀ v : EuclideanSpace ℂ (Cfg d N),
        - (1 - γ) * c i j *
            ((⟪localTermES A L i v, v⟫_ℂ).re +
              (⟪localTermES A L j v, v⟫_ℂ).re) ≤
          (⟪localTermES A L i v, localTermES A L j v⟫_ℂ).re +
            (⟪localTermES A L j v, localTermES A L i v⟫_ℂ).re) :
    ∀ v : EuclideanSpace ℂ (Cfg d N),
      γ * (⟪parentHamiltonianES A L N v, v⟫_ℂ).re ≤
        (⟪parentHamiltonianES A L N v,
          parentHamiltonianES A L N v⟫_ℂ).re := by
  intro v
  simpa [parentHamiltonianES_eq_sum_localTermES A L N] using
    (ProjectionGeometry.quadraticForm_sum_projections_of_anticommutator_rowCol
      (ι := Fin N) (E := EuclideanSpace ℂ (Cfg d N)) hγle
      (fun i : Fin N => localTermES A L i)
      (fun i : Fin N => localTermES_isSymmetricProjection A L i) c hRow hCol hAnti v)

private lemma martingale_coefficient_le_one (L : ℕ) (hL : 1 < L) :
    ((1 : ℝ) / (4 * (L : ℝ))) ≤ 1 := by
  have hLpos : (0 : ℝ) < (L : ℝ) := by
    exact_mod_cast Nat.zero_lt_of_lt hL
  have hLge_one : (1 : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast Nat.le_of_lt hL
  exact (div_le_one (mul_pos (by norm_num) hLpos)).2 (by nlinarith [hLge_one])

/-- Fixed-chain martingale quadratic-form estimate from a finite-overlap
anticommutator estimate.

This version chooses coefficient \(1/m\) on the marked overlapping pairs and
\(0\) otherwise. It is the finite-overlap specialization of the source
anticommutator condition
\[
  h_i h_j+h_j h_i\ge -(1-\gamma)m^{-1}(h_i+h_j).
\]
The row and column cardinality hypotheses make the coefficient sums at most
one; non-overlapping pairs are handled by non-negativity of the corresponding
anticommutator quadratic form. -/
theorem parentHamiltonianES_quadratic_form_of_finite_overlap_anticommutator
    (A : MPSTensor d D) (L N : ℕ) {γ : ℝ} (hγle : γ ≤ 1)
    (overlaps : Fin N → Fin N → Prop) [DecidableRel overlaps] {m : ℕ} (hm : 0 < m)
    (hRowCard : ∀ i : Fin N,
      ((Finset.univ.erase i).filter (fun j => overlaps i j)).card ≤ m)
    (hColCard : ∀ j : Fin N,
      ((Finset.univ.erase j).filter (fun i => overlaps i j)).card ≤ m)
    (hDisjointAnti : ∀ i j : Fin N, j ∈ Finset.univ.erase i → ¬ overlaps i j →
      ∀ v : EuclideanSpace ℂ (Cfg d N),
        0 ≤ (⟪localTermES A L i v, localTermES A L j v⟫_ℂ).re +
          (⟪localTermES A L j v, localTermES A L i v⟫_ℂ).re)
    (hAnti : ∀ i j : Fin N, j ∈ Finset.univ.erase i → overlaps i j →
      ∀ v : EuclideanSpace ℂ (Cfg d N),
        - (1 - γ) * ((m : ℝ)⁻¹) *
            ((⟪localTermES A L i v, v⟫_ℂ).re +
              (⟪localTermES A L j v, v⟫_ℂ).re) ≤
          (⟪localTermES A L i v, localTermES A L j v⟫_ℂ).re +
            (⟪localTermES A L j v, localTermES A L i v⟫_ℂ).re) :
    ∀ v : EuclideanSpace ℂ (Cfg d N),
      γ * (⟪parentHamiltonianES A L N v, v⟫_ℂ).re ≤
        (⟪parentHamiltonianES A L N v,
          parentHamiltonianES A L N v⟫_ℂ).re := by
  intro v
  simpa [parentHamiltonianES_eq_sum_localTermES A L N] using
    (ProjectionGeometry.quadraticForm_sum_projections_of_finite_overlap_anticommutator
      (ι := Fin N) (E := EuclideanSpace ℂ (Cfg d N)) hγle
      (fun i : Fin N => localTermES A L i)
      (fun i : Fin N => localTermES_isSymmetricProjection A L i) overlaps hm
      hRowCard hColCard hDisjointAnti hAnti v)

/-- Fixed-chain martingale quadratic-form estimate from finite-overlap ordered
cross-term hypotheses.

This is the local-window specialization of
`ProjectionGeometry.quadraticForm_sum_projections_of_finite_overlap`.  The
predicate `overlaps i j` marks the off-diagonal pairs for which a principal-angle
estimate is needed.  If each row has at most \(m\) such pairs, the non-overlap
cross terms are nonnegative, and every overlap obeys the ordered estimate with
coefficient \(1 / m\), then the Euclidean-space parent Hamiltonian satisfies
\(H² ≥ γ H\) as a quadratic form. -/
theorem parentHamiltonianES_quadratic_form_of_finite_overlap_ordered_cross_term
    (A : MPSTensor d D) (L N : ℕ) {γ : ℝ} (hγle : γ ≤ 1)
    (overlaps : Fin N → Fin N → Prop) [DecidableRel overlaps] {m : ℕ} (hm : 0 < m)
    (hProj : ∀ i : Fin N, (localTermES A L i).IsSymmetricProjection)
    (hCard : ∀ i : Fin N,
      ((Finset.univ.erase i).filter (fun j => overlaps i j)).card ≤ m)
    (hDisjoint : ∀ i j : Fin N, j ∈ Finset.univ.erase i → ¬ overlaps i j →
      ∀ v : EuclideanSpace ℂ (Cfg d N),
        0 ≤ (⟪localTermES A L i v, localTermES A L j v⟫_ℂ).re)
    (hCrossTerm : ∀ i j : Fin N, j ∈ Finset.univ.erase i → overlaps i j →
      ∀ v : EuclideanSpace ℂ (Cfg d N),
        - (1 - γ) * ((m : ℝ)⁻¹) * (⟪localTermES A L i v, v⟫_ℂ).re ≤
          (⟪localTermES A L i v, localTermES A L j v⟫_ℂ).re) :
    ∀ v : EuclideanSpace ℂ (Cfg d N),
      γ * (⟪parentHamiltonianES A L N v, v⟫_ℂ).re ≤
        (⟪parentHamiltonianES A L N v,
          parentHamiltonianES A L N v⟫_ℂ).re := by
  intro v
  simpa [parentHamiltonianES_eq_sum_localTermES A L N] using
    (ProjectionGeometry.quadraticForm_sum_projections_of_finite_overlap
      (ι := Fin N) (E := EuclideanSpace ℂ (Cfg d N)) hγle
      (fun i : Fin N => localTermES A L i) hProj overlaps hm hCard hDisjoint
      hCrossTerm v)

open Classical in
/-- Combined martingale criterion for a finite family of symmetric projections.

If the anticommutator forms satisfy row- and column-summable bounds with
constant \(γ\), then the sum \(H = \sum_i P_i\) of the projections satisfies
both the quadratic-form inequality
\(γ \operatorname{Re}\langle Hv, v\rangle \le \operatorname{Re}\langle Hv, Hv\rangle\)
for every \(v\), and the norm lower bound \(γ ‖v‖ ≤ ‖H v‖\) on
\((\ker H)^\perp\), because \(H\) is positive (a sum of positive maps). -/
theorem spectralGap_of_martingale_anticommutator_rowCol_of_finiteDimensional
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    {γ : ℝ} (hγpos : 0 < γ) (hγle : γ ≤ 1)
    (P : ι → E →ₗ[ℂ] E)
    (hP : ∀ i, (P i).IsSymmetricProjection)
    (c : ι → ι → ℝ)
    (hRow : ∀ i, (∑ j ∈ Finset.univ.erase i, c i j) ≤ 1)
    (hCol : ∀ j, (∑ i ∈ Finset.univ.erase j, c i j) ≤ 1)
    (hAnti : ∀ i j, j ∈ Finset.univ.erase i → ∀ v,
      -(1 - γ) * c i j *
          ((⟪P i v, v⟫_ℂ).re + (⟪P j v, v⟫_ℂ).re) ≤
        (⟪P i v, P j v⟫_ℂ).re + (⟪P j v, P i v⟫_ℂ).re) :
    (∀ v, γ * (⟪(∑ i, P i) v, v⟫_ℂ).re ≤ (⟪(∑ i, P i) v, (∑ i, P i) v⟫_ℂ).re) ∧
    ∀ v ∈ (LinearMap.ker (∑ i, P i))ᗮ, γ * ‖v‖ ≤ ‖(∑ i, P i) v‖ := by
  have hQuad : ∀ v,
      γ * (⟪(∑ i, P i) v, v⟫_ℂ).re ≤ (⟪(∑ i, P i) v, (∑ i, P i) v⟫_ℂ).re :=
    ProjectionGeometry.quadraticForm_sum_projections_of_anticommutator_rowCol
      hγle P hP c hRow hCol hAnti
  refine ⟨hQuad, fun v hv => ?_⟩
  exact FrustrationFree.spectralGap_of_martingale_of_finiteDimensional hγpos
    (LinearMap.isPositive_sum Finset.univ fun i _ => (hP i).isPositive)
    hQuad v hv

/-! ### The reduction for the parent interaction on the ring

The same reduction chain for the Hamiltonian of the parent interaction on the ring
(`parentRingInteraction`) on rings of \(N ≥ 2L\) sites. Statements about vectors take the
operators (`Matrix.toEuclideanLin`) of its terms \(h_i\) and of its Hamiltonian \(H\), and the
ground space is the kernel of \(H\). -/

section RingInteraction

private theorem sum_toEuclideanLin_parentRingInteraction_term (A : MPSTensor d D) {L N : ℕ}
    (hLN : L ≤ N) :
    ∑ i, Matrix.toEuclideanLin ((parentRingInteraction A hLN).term i) =
      Matrix.toEuclideanLin (parentRingInteraction A hLN).hamiltonian := by
  rw [ManyBody.Interaction.hamiltonian, map_sum]

/-- A uniform quadratic-form estimate \(γ\,\operatorname{Re}\langle Hv, v\rangle ≤
\operatorname{Re}\langle Hv, Hv\rangle\) for the Hamiltonians \(H\) of the parent interaction on
the rings of \(N ≥ 2L\) sites implies the norm lower bound \(γ‖v‖ ≤ ‖Hv‖\) on the orthogonal
complement of the kernel of \(H\), by positivity of \(H\) and the abstract spectral-theorem step
`FrustrationFree.spectralGap_of_martingale_of_finiteDimensional`. -/
theorem hamiltonian_parentRingInteraction_norm_bound_of_quadratic_form
    (A : MPSTensor d D) (L : ℕ) {γ : ℝ} (hγ : 0 < γ)
    (hQuad : ∀ (N : ℕ) (hLN : 2 * L ≤ N) (v : EuclideanSpace ℂ (Cfg d N)),
      let H := Matrix.toEuclideanLin (parentRingInteraction A (show L ≤ N by omega)).hamiltonian
      γ * (⟪H v, v⟫_ℂ).re ≤ (⟪H v, H v⟫_ℂ).re) :
    ∀ (N : ℕ) (hLN : 2 * L ≤ N) (v : EuclideanSpace ℂ (Cfg d N)),
      let H := Matrix.toEuclideanLin (parentRingInteraction A (show L ≤ N by omega)).hamiltonian
      v ∈ (LinearMap.ker H)ᗮ → γ * ‖v‖ ≤ ‖H v‖ := fun N hLN v ↦
  FrustrationFree.spectralGap_of_martingale_of_finiteDimensional hγ
    (Matrix.isPositive_toEuclideanLin_iff.mpr (posSemidef_hamiltonian_parentRingInteraction A _))
    (hQuad N hLN) v

/-- The explicit gap bound with constant \(1/(4L)\) for the Hamiltonians of the parent
interaction on the rings of \(N ≥ 2L\) sites follows from the corresponding uniform
quadratic-form estimate. -/
theorem hamiltonian_parentRingInteraction_gap_bound_of_quadratic_form
    (A : MPSTensor d D) (L : ℕ) (hL : 1 < L)
    (hQuad : ∀ (N : ℕ) (hLN : 2 * L ≤ N) (v : EuclideanSpace ℂ (Cfg d N)),
      let H := Matrix.toEuclideanLin (parentRingInteraction A (show L ≤ N by omega)).hamiltonian
      ((1 : ℝ) / (4 * (L : ℝ))) * (⟪H v, v⟫_ℂ).re ≤ (⟪H v, H v⟫_ℂ).re) :
    0 < (1 : ℝ) / (4 * (L : ℝ)) ∧
    ∀ (N : ℕ) (hLN : 2 * L ≤ N) (v : EuclideanSpace ℂ (Cfg d N)),
      let H := Matrix.toEuclideanLin (parentRingInteraction A (show L ≤ N by omega)).hamiltonian
      v ∈ (LinearMap.ker H)ᗮ → ((1 : ℝ) / (4 * (L : ℝ))) * ‖v‖ ≤ ‖H v‖ := by
  have hγ : 0 < (1 : ℝ) / (4 * (L : ℝ)) := by
    have hLpos : (0 : ℝ) < (L : ℝ) := by
      exact_mod_cast Nat.zero_lt_of_lt hL
    exact div_pos (by norm_num) (mul_pos (by norm_num) hLpos)
  exact ⟨hγ, hamiltonian_parentRingInteraction_norm_bound_of_quadratic_form A L hγ hQuad⟩

/-- Uniform explicit gap-bound reduction from ordered local cross-term row bounds: if for every
ring of \(N ≥ 2L\) sites the terms \(h_i\) of the parent interaction satisfy
\(\operatorname{Re}\langle h_i v, h_j v\rangle ≥
-(1 - γ)c_{ij}\operatorname{Re}\langle h_i v, v\rangle\) with \(γ = 1/(4L)\) and row sums of
\(c\) at most one, the Hamiltonian has the gap bound with constant \(1/(4L)\). -/
theorem hamiltonian_parentRingInteraction_gap_bound_of_ordered_local_term_bounds
    (A : MPSTensor d D) (L : ℕ) (hL : 1 < L)
    (c : ∀ N : ℕ, Fin N → Fin N → ℝ)
    (hRow : ∀ (N : ℕ) (_hLN : 2 * L ≤ N) (i : Fin N),
      (∑ j ∈ Finset.univ.erase i, c N i j) ≤ 1)
    (hCross : ∀ (N : ℕ) (hLN : 2 * L ≤ N) (i j : Fin N),
      j ∈ Finset.univ.erase i → ∀ v : EuclideanSpace ℂ (Cfg d N),
        let h (k : Fin N) :=
          Matrix.toEuclideanLin ((parentRingInteraction A (show L ≤ N by omega)).term k);
        - (1 - ((1 : ℝ) / (4 * (L : ℝ)))) * c N i j * (⟪h i v, v⟫_ℂ).re ≤
          (⟪h i v, h j v⟫_ℂ).re) :
    0 < (1 : ℝ) / (4 * (L : ℝ)) ∧
    ∀ (N : ℕ) (hLN : 2 * L ≤ N) (v : EuclideanSpace ℂ (Cfg d N)),
      let H := Matrix.toEuclideanLin (parentRingInteraction A (show L ≤ N by omega)).hamiltonian
      v ∈ (LinearMap.ker H)ᗮ → ((1 : ℝ) / (4 * (L : ℝ))) * ‖v‖ ≤ ‖H v‖ := by
  refine hamiltonian_parentRingInteraction_gap_bound_of_quadratic_form A L hL fun N hLN v ↦ ?_
  have hQuad := ProjectionGeometry.quadraticForm_sum_projections_of_ordered_rowSum
    (martingale_coefficient_le_one L hL)
    (fun i ↦ Matrix.toEuclideanLin ((parentRingInteraction A (show L ≤ N by omega)).term i))
    (isSymmetricProjection_toEuclideanLin_parentRingInteraction_term A (show L ≤ N by omega))
    (c N) (hRow N hLN)
    (hCross N hLN) v
  rwa [sum_toEuclideanLin_parentRingInteraction_term] at hQuad

/-- Uniform explicit gap-bound reduction from source anticommutator row bounds.

arXiv:2011.12127, Section IV.C, lines 2176-2179, state the martingale condition in the
anticommutator form
\[
  h_i h_j+h_jh_i\ge -c_{ij}(1-\gamma)(h_i+h_j).
\]
For the explicit choice \(\gamma=1/(4L)\), this theorem converts that condition for the terms of
the parent interaction on the rings of \(N ≥ 2L\) sites, with row and column coefficient sums
bounded by one for every ring, into the gap bound with constant \(1/(4L)\). -/
theorem hamiltonian_parentRingInteraction_gap_bound_of_anticommutator_local_term_bounds
    (A : MPSTensor d D) (L : ℕ) (hL : 1 < L)
    (c : ∀ N : ℕ, Fin N → Fin N → ℝ)
    (hRow : ∀ (N : ℕ) (_hLN : 2 * L ≤ N) (i : Fin N),
      (∑ j ∈ Finset.univ.erase i, c N i j) ≤ 1)
    (hCol : ∀ (N : ℕ) (_hLN : 2 * L ≤ N) (j : Fin N),
      (∑ i ∈ Finset.univ.erase j, c N i j) ≤ 1)
    (hAnti : ∀ (N : ℕ) (hLN : 2 * L ≤ N) (i j : Fin N),
      j ∈ Finset.univ.erase i → ∀ v : EuclideanSpace ℂ (Cfg d N),
        let h (k : Fin N) :=
          Matrix.toEuclideanLin ((parentRingInteraction A (show L ≤ N by omega)).term k);
        - (1 - ((1 : ℝ) / (4 * (L : ℝ)))) * c N i j * ((⟪h i v, v⟫_ℂ).re + (⟪h j v, v⟫_ℂ).re) ≤
          (⟪h i v, h j v⟫_ℂ).re + (⟪h j v, h i v⟫_ℂ).re) :
    0 < (1 : ℝ) / (4 * (L : ℝ)) ∧
    ∀ (N : ℕ) (hLN : 2 * L ≤ N) (v : EuclideanSpace ℂ (Cfg d N)),
      let H := Matrix.toEuclideanLin (parentRingInteraction A (show L ≤ N by omega)).hamiltonian
      v ∈ (LinearMap.ker H)ᗮ → ((1 : ℝ) / (4 * (L : ℝ))) * ‖v‖ ≤ ‖H v‖ := by
  refine hamiltonian_parentRingInteraction_gap_bound_of_quadratic_form A L hL fun N hLN v ↦ ?_
  have hQuad := ProjectionGeometry.quadraticForm_sum_projections_of_anticommutator_rowCol
    (martingale_coefficient_le_one L hL)
    (fun i ↦ Matrix.toEuclideanLin ((parentRingInteraction A (show L ≤ N by omega)).term i))
    (isSymmetricProjection_toEuclideanLin_parentRingInteraction_term A (show L ≤ N by omega))
    (c N) (hRow N hLN)
    (hCol N hLN) (hAnti N hLN) v
  rwa [sum_toEuclideanLin_parentRingInteraction_term] at hQuad

/-- Uniform explicit gap-bound reduction from a finite-overlap anticommutator martingale
estimate for the terms of the parent interaction on the rings of \(N ≥ 2L\) sites. With
\(m = 2(L-1)\): if the overlap relation has at most \(m\) off-diagonal neighbours in each row and
column, non-overlapping pairs have nonnegative anticommutator form, and overlapping pairs satisfy
the source anticommutator estimate (arXiv:2011.12127, Section IV.C, lines 2176-2179) with
coefficient \(1/m\), then the gap bound with constant \(1/(4L)\) follows. -/
theorem hamiltonian_parentRingInteraction_gap_bound_of_finite_overlap_anticommutator
    (A : MPSTensor d D) (L : ℕ) (hL : 1 < L)
    (overlaps : ∀ N : ℕ, Fin N → Fin N → Prop)
    [∀ N : ℕ, DecidableRel (overlaps N)]
    (hRowCard : ∀ (N : ℕ) (_hLN : 2 * L ≤ N) (i : Fin N),
      ((Finset.univ.erase i).filter (fun j => overlaps N i j)).card ≤ 2 * (L - 1))
    (hColCard : ∀ (N : ℕ) (_hLN : 2 * L ≤ N) (j : Fin N),
      ((Finset.univ.erase j).filter (fun i => overlaps N i j)).card ≤ 2 * (L - 1))
    (hDisjointAnti : ∀ (N : ℕ) (hLN : 2 * L ≤ N) (i j : Fin N),
      j ∈ Finset.univ.erase i → ¬ overlaps N i j → ∀ v : EuclideanSpace ℂ (Cfg d N),
        let h (k : Fin N) :=
          Matrix.toEuclideanLin ((parentRingInteraction A (show L ≤ N by omega)).term k)
        0 ≤ (⟪h i v, h j v⟫_ℂ).re + (⟪h j v, h i v⟫_ℂ).re)
    (hAnti : ∀ (N : ℕ) (hLN : 2 * L ≤ N) (i j : Fin N),
      j ∈ Finset.univ.erase i → overlaps N i j → ∀ v : EuclideanSpace ℂ (Cfg d N),
        let h (k : Fin N) :=
          Matrix.toEuclideanLin ((parentRingInteraction A (show L ≤ N by omega)).term k);
        - (1 - ((1 : ℝ) / (4 * (L : ℝ)))) * (((2 * (L - 1) : ℕ) : ℝ)⁻¹) *
            ((⟪h i v, v⟫_ℂ).re + (⟪h j v, v⟫_ℂ).re) ≤
          (⟪h i v, h j v⟫_ℂ).re + (⟪h j v, h i v⟫_ℂ).re) :
    0 < (1 : ℝ) / (4 * (L : ℝ)) ∧
    ∀ (N : ℕ) (hLN : 2 * L ≤ N) (v : EuclideanSpace ℂ (Cfg d N)),
      let H := Matrix.toEuclideanLin (parentRingInteraction A (show L ≤ N by omega)).hamiltonian
      v ∈ (LinearMap.ker H)ᗮ → ((1 : ℝ) / (4 * (L : ℝ))) * ‖v‖ ≤ ‖H v‖ := by
  refine hamiltonian_parentRingInteraction_gap_bound_of_quadratic_form A L hL fun N hLN v ↦ ?_
  have hQuad := ProjectionGeometry.quadraticForm_sum_projections_of_finite_overlap_anticommutator
    (martingale_coefficient_le_one L hL)
    (fun i ↦ Matrix.toEuclideanLin ((parentRingInteraction A (show L ≤ N by omega)).term i))
    (isSymmetricProjection_toEuclideanLin_parentRingInteraction_term A (show L ≤ N by omega))
    (overlaps N)
    (Nat.mul_pos (by decide) (Nat.sub_pos_of_lt hL)) (hRowCard N hLN) (hColCard N hLN)
    (hDisjointAnti N hLN) (hAnti N hLN) v
  rwa [sum_toEuclideanLin_parentRingInteraction_term] at hQuad

/-- Uniform explicit gap-bound reduction from finite-overlap ordered cross-term hypotheses for
the terms of the parent interaction on the rings of \(N ≥ 2L\) sites, with \(m = 2(L-1)\): the
terms are symmetric projections, each row has at most \(m\) overlapping off-diagonal pairs, the
non-overlap cross terms are nonnegative, and every overlap obeys the ordered estimate with
coefficient \(1/m\); then the gap bound with constant \(1/(4L)\) follows. -/
theorem hamiltonian_parentRingInteraction_gap_bound_of_finite_overlap_ordered_cross_term
    (A : MPSTensor d D) (L : ℕ) (hL : 1 < L)
    (overlaps : ∀ N : ℕ, Fin N → Fin N → Prop)
    [∀ N : ℕ, DecidableRel (overlaps N)]
    (hProj : ∀ (N : ℕ) (hLN : 2 * L ≤ N) (i : Fin N),
      (Matrix.toEuclideanLin
        ((parentRingInteraction A (show L ≤ N by omega)).term i)).IsSymmetricProjection)
    (hCard : ∀ (N : ℕ) (_hLN : 2 * L ≤ N) (i : Fin N),
      ((Finset.univ.erase i).filter (fun j => overlaps N i j)).card ≤ 2 * (L - 1))
    (hDisjoint : ∀ (N : ℕ) (hLN : 2 * L ≤ N) (i j : Fin N),
      j ∈ Finset.univ.erase i → ¬ overlaps N i j → ∀ v : EuclideanSpace ℂ (Cfg d N),
        let h (k : Fin N) :=
          Matrix.toEuclideanLin ((parentRingInteraction A (show L ≤ N by omega)).term k)
        0 ≤ (⟪h i v, h j v⟫_ℂ).re)
    (hCrossTerm : ∀ (N : ℕ) (hLN : 2 * L ≤ N) (i j : Fin N),
      j ∈ Finset.univ.erase i → overlaps N i j → ∀ v : EuclideanSpace ℂ (Cfg d N),
        let h (k : Fin N) :=
          Matrix.toEuclideanLin ((parentRingInteraction A (show L ≤ N by omega)).term k);
        - (1 - ((1 : ℝ) / (4 * (L : ℝ)))) * (((2 * (L - 1) : ℕ) : ℝ)⁻¹) * (⟪h i v, v⟫_ℂ).re ≤
          (⟪h i v, h j v⟫_ℂ).re) :
    0 < (1 : ℝ) / (4 * (L : ℝ)) ∧
    ∀ (N : ℕ) (hLN : 2 * L ≤ N) (v : EuclideanSpace ℂ (Cfg d N)),
      let H := Matrix.toEuclideanLin (parentRingInteraction A (show L ≤ N by omega)).hamiltonian
      v ∈ (LinearMap.ker H)ᗮ → ((1 : ℝ) / (4 * (L : ℝ))) * ‖v‖ ≤ ‖H v‖ := by
  refine hamiltonian_parentRingInteraction_gap_bound_of_quadratic_form A L hL fun N hLN v ↦ ?_
  have hQuad := ProjectionGeometry.quadraticForm_sum_projections_of_finite_overlap
    (martingale_coefficient_le_one L hL)
    (fun i ↦ Matrix.toEuclideanLin ((parentRingInteraction A (show L ≤ N by omega)).term i))
    (hProj N hLN) (overlaps N) (Nat.mul_pos (by decide) (Nat.sub_pos_of_lt hL)) (hCard N hLN)
    (hDisjoint N hLN) (hCrossTerm N hLN) v
  rwa [sum_toEuclideanLin_parentRingInteraction_term] at hQuad

/-- Uniform explicit gap-bound reduction using the concrete cyclic-window overlap predicate.
For rings of \(N ≥ 2L\) sites, the row-cardinality estimate is `cyclicWindowsOverlap_card_le`,
the projection structure of the terms of the parent interaction is
`isSymmetricProjection_toEuclideanLin_parentRingInteraction_term`, and non-overlap positivity is
`re_inner_parentRingInteraction_term_nonneg_of_not_cyclicWindowsOverlap`; the only remaining
hypothesis is the ordered cross-term estimate for overlapping pairs. -/
theorem hamiltonian_parentRingInteraction_gap_bound_of_cyclic_window_ordered_cross_term
    (A : MPSTensor d D) (L : ℕ) (hL : 1 < L)
    (hCrossTerm : ∀ (N : ℕ) (hLN : 2 * L ≤ N) (i j : Fin N),
      j ∈ Finset.univ.erase i → cyclicWindowsOverlap N L i j →
        ∀ v : EuclideanSpace ℂ (Cfg d N),
          let h (k : Fin N) :=
            Matrix.toEuclideanLin ((parentRingInteraction A (show L ≤ N by omega)).term k);
          - (1 - ((1 : ℝ) / (4 * (L : ℝ)))) * (((2 * (L - 1) : ℕ) : ℝ)⁻¹) *
              (⟪h i v, v⟫_ℂ).re ≤
            (⟪h i v, h j v⟫_ℂ).re) :
    0 < (1 : ℝ) / (4 * (L : ℝ)) ∧
    ∀ (N : ℕ) (hLN : 2 * L ≤ N) (v : EuclideanSpace ℂ (Cfg d N)),
      let H := Matrix.toEuclideanLin (parentRingInteraction A (show L ≤ N by omega)).hamiltonian
      v ∈ (LinearMap.ker H)ᗮ → ((1 : ℝ) / (4 * (L : ℝ))) * ‖v‖ ≤ ‖H v‖ :=
  hamiltonian_parentRingInteraction_gap_bound_of_finite_overlap_ordered_cross_term A L hL
    (fun N => cyclicWindowsOverlap N L)
    (fun _ _ i => isSymmetricProjection_toEuclideanLin_parentRingInteraction_term A _ i)
    (fun _ hLN i => cyclicWindowsOverlap_card_le hLN hL i)
    (fun _ _ _ _ _ hnot v =>
      re_inner_parentRingInteraction_term_nonneg_of_not_cyclicWindowsOverlap A _ hnot v)
    hCrossTerm

/-- Uniform explicit gap-bound reduction from the cyclic-window anticommutator martingale
estimate. For the terms \(h_i\) of the parent interaction on the rings of \(N ≥ 2L\) sites, the
overlap relation has at most \(2(L-1)\) off-diagonal neighbours in each row and column, so the
remaining analytic input is the source anticommutator form (arXiv:2011.12127, Section IV.C,
lines 2176-2179) on overlapping pairs:
\[
  h_i h_j+h_jh_i\ge
  -\Bigl(1-\frac{1}{4L}\Bigr)\frac{1}{2(L-1)}(h_i+h_j).
\]
Non-overlapping pairs are handled by the disjoint-window positivity. -/
theorem hamiltonian_parentRingInteraction_gap_bound_of_cyclic_window_overlap_anticommutator
    (A : MPSTensor d D) (L : ℕ) (hL : 1 < L)
    (hAnti : ∀ (N : ℕ) (hLN : 2 * L ≤ N) (i j : Fin N),
      j ∈ Finset.univ.erase i → cyclicWindowsOverlap N L i j →
        ∀ v : EuclideanSpace ℂ (Cfg d N),
          let h (k : Fin N) :=
            Matrix.toEuclideanLin ((parentRingInteraction A (show L ≤ N by omega)).term k);
          - (1 - ((1 : ℝ) / (4 * (L : ℝ)))) * (((2 * (L - 1) : ℕ) : ℝ)⁻¹) *
              ((⟪h i v, v⟫_ℂ).re + (⟪h j v, v⟫_ℂ).re) ≤
            (⟪h i v, h j v⟫_ℂ).re + (⟪h j v, h i v⟫_ℂ).re) :
    0 < (1 : ℝ) / (4 * (L : ℝ)) ∧
    ∀ (N : ℕ) (hLN : 2 * L ≤ N) (v : EuclideanSpace ℂ (Cfg d N)),
      let H := Matrix.toEuclideanLin (parentRingInteraction A (show L ≤ N by omega)).hamiltonian
      v ∈ (LinearMap.ker H)ᗮ → ((1 : ℝ) / (4 * (L : ℝ))) * ‖v‖ ≤ ‖H v‖ := by
  refine hamiltonian_parentRingInteraction_gap_bound_of_finite_overlap_anticommutator A L hL
    (fun N => cyclicWindowsOverlap N L) ?_ ?_ ?_ hAnti
  · intro N hLN i
    exact cyclicWindowsOverlap_card_le hLN hL i
  · intro N hLN j
    simpa only [cyclicWindowsOverlap_comm N L _ j] using cyclicWindowsOverlap_card_le hLN hL j
  · intro N hLN i j _hij hnot v
    exact add_nonneg
      (re_inner_parentRingInteraction_term_nonneg_of_not_cyclicWindowsOverlap A _ hnot v)
      (re_inner_parentRingInteraction_term_nonneg_of_not_cyclicWindowsOverlap A _
        (fun h => hnot ((cyclicWindowsOverlap_comm N L i j).mpr h)) v)

end RingInteraction

end MPSTensor
