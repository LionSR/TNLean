/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.Martingale.AbstractCriterion
import TNLean.MPS.ParentHamiltonian.Martingale.Transport
import TNLean.Analysis.ProjectionGeometry

/-!
# Martingale quadratic-form reduction chain

**Root-only.** This file contains the reduction theorems that convert
explicit local-projection bounds into the quadratic-form inequality
`H² ≥ γ H` for the transported parent Hamiltonian `parentHamiltonianES`
and then into the norm lower bound `γ ‖v‖ ≤ ‖H_ES v‖` on the orthogonal
complement of the ground space.

The chain proceeds from the most abstract (ordered row-sum of local
cross-term bounds) through finite-overlap reductions down to the
concrete cyclic-window overlap predicate and its row-cardinality bound
`2 * (L - 1)`. The final reduction theorems (`*_gap_bound_of_cyclic_window_*`)
supply all the already-proved structural input (local projection,
non-overlap positivity, and row cardinality) and leave only the
Friedrichs-angle estimate as a remaining hypothesis.

The abstract spectral-theorem step (`FrustrationFree.spectralGap_of_martingale`)
and the projection-geometry lemmas (`ProjectionGeometry.quadraticForm_sum_*`)
supply the reusable algebra, while the MPS-specific definitions and
structural theorems live in `Martingale.Transport`.
-/

open scoped BigOperators InnerProductSpace

namespace MPSTensor

variable {d D : ℕ}

/-! ### Martingale quadratic-form reduction -/

/-- A uniform quadratic-form estimate for the transported parent Hamiltonians
implies the corresponding norm lower bound on the orthogonal complement of the
transported ground space.

This theorem isolates the operator-theoretic part of the remaining
Friedrichs-angle route. The hypotheses already include the quantitative
martingale/Friedrichs estimate

`γ * re ⟪H_N v, v⟫ ≤ re ⟪H_N v, H_N v⟫`,

to be supplied later from the finite-overlap projection geometry. The proof
uses the established positivity of `parentHamiltonianES`, the kernel
identification `parentHamiltonianGroundSpaceES_eq_ker_parentHamiltonianES`, and
the abstract spectral-theorem step `FrustrationFree.spectralGap_of_martingale`. -/
theorem parentHamiltonianES_norm_bound_of_quadratic_form
    (A : MPSTensor d D) (L : ℕ) {γ : ℝ} (hγ : 0 < γ)
    (hQuad : ∀ (N : ℕ) (_hLN : 2 * L ≤ N)
      (v : EuclideanSpace ℂ (Cfg d N)),
        γ * (⟪parentHamiltonianES A L N v, v⟫_ℂ).re ≤
          (⟪parentHamiltonianES A L N v,
              parentHamiltonianES A L N v⟫_ℂ).re) :
    ∀ (N : ℕ) (_hLN : 2 * L ≤ N)
      (v : EuclideanSpace ℂ (Cfg d N)),
      v ∈ (parentHamiltonianGroundSpaceES A L N)ᗮ →
        γ * ‖v‖ ≤ ‖parentHamiltonianES A L N v‖ := by
  intro N hLN v hv
  have hvKer : v ∈ (LinearMap.ker (parentHamiltonianES A L N))ᗮ := by
    simpa [parentHamiltonianGroundSpaceES_eq_ker_parentHamiltonianES A L N] using hv
  exact FrustrationFree.spectralGap_of_martingale (ι := Cfg d N) hγ
    (parentHamiltonianES_isPositive A L N) (hQuad N hLN) v hvKer

/-- The exact explicit gap-bound reduction needed by
`parentHamiltonianES_gap_bound_of_friedrichs` follows from the corresponding
uniform quadratic-form estimate with constant `1 / (4 * L)`.

Thus the remaining MPS-specific content is precisely to prove the hypothesis
`hQuad` from the Friedrichs-angle / anti-commutator estimate and the finite
row-sum bound; the positivity, kernel transport, and spectral-theorem conversion
are already available here. -/
theorem parentHamiltonianES_gap_bound_of_quadratic_form
    (A : MPSTensor d D) (L : ℕ) (hL : 1 < L)
    (hQuad : ∀ (N : ℕ) (_hLN : 2 * L ≤ N)
      (v : EuclideanSpace ℂ (Cfg d N)),
        ((1 : ℝ) / (4 * (L : ℝ))) *
          (⟪parentHamiltonianES A L N v, v⟫_ℂ).re ≤
            (⟪parentHamiltonianES A L N v,
                parentHamiltonianES A L N v⟫_ℂ).re) :
    0 < (1 : ℝ) / (4 * (L : ℝ)) ∧
    ∀ (N : ℕ) (_hLN : 2 * L ≤ N)
      (v : EuclideanSpace ℂ (Cfg d N)),
      v ∈ (parentHamiltonianGroundSpaceES A L N)ᗮ →
        ((1 : ℝ) / (4 * (L : ℝ))) * ‖v‖ ≤
          ‖parentHamiltonianES A L N v‖ := by
  have hγ : 0 < (1 : ℝ) / (4 * (L : ℝ)) := by
    have hLpos : (0 : ℝ) < (L : ℝ) := by
      exact_mod_cast (Nat.zero_lt_of_lt hL)
    exact div_pos (by norm_num) (mul_pos (by norm_num) hLpos)
  exact ⟨hγ, parentHamiltonianES_norm_bound_of_quadratic_form A L hγ hQuad⟩

/-- Fixed-chain martingale quadratic-form estimate from ordered local
cross-term row bounds.

This theorem is the parent-Hamiltonian instantiation of the abstract projection
geometry in `ProjectionGeometry.quadraticForm_sum_projections_of_ordered_rowSum`.
The local projection input is supplied by `localTermES_isSymmetricProjection`, so
its hypotheses are only the ordered row-summable cross-term bounds

`Re ⟪hᵢ v, hⱼ v⟫ ≥ -(1 - γ) cᵢⱼ Re ⟪hᵢ v, v⟫`.

Under these hypotheses the transported Hamiltonian satisfies `H² ≥ γ H` as a
quadratic form, exactly in the shape consumed by
`parentHamiltonianES_norm_bound_of_quadratic_form`. -/
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

/-- Uniform explicit gap-bound reduction from ordered local cross-term row
bounds.

For every chain length `N ≥ 2L`, assume the transported local terms satisfy the
ordered row-summable cross-term estimate with constant `γ = 1 / (4L)`. The local
symmetric-projection input is already supplied by `localTermES_isSymmetricProjection`.
Then the existing quadratic-form-to-gap theorem applies and yields the explicit
norm lower bound. This exact reduction leaves proving the Friedrichs/row-sum
hypotheses for the concrete MPS local terms as the model-specific analytic task. -/
theorem parentHamiltonianES_gap_bound_of_ordered_local_term_bounds
    (A : MPSTensor d D) (L : ℕ) (hL : 1 < L)
    (c : ∀ N : ℕ, Fin N → Fin N → ℝ)
    (hRow : ∀ (N : ℕ) (_hLN : 2 * L ≤ N) (i : Fin N),
      (∑ j ∈ Finset.univ.erase i, c N i j) ≤ 1)
    (hCross : ∀ (N : ℕ) (_hLN : 2 * L ≤ N) (i j : Fin N),
      j ∈ Finset.univ.erase i → ∀ v : EuclideanSpace ℂ (Cfg d N),
        - (1 - ((1 : ℝ) / (4 * (L : ℝ)))) * c N i j *
            (⟪localTermES A L i v, v⟫_ℂ).re ≤
          (⟪localTermES A L i v, localTermES A L j v⟫_ℂ).re) :
    0 < (1 : ℝ) / (4 * (L : ℝ)) ∧
    ∀ (N : ℕ) (_hLN : 2 * L ≤ N)
      (v : EuclideanSpace ℂ (Cfg d N)),
      v ∈ (parentHamiltonianGroundSpaceES A L N)ᗮ →
        ((1 : ℝ) / (4 * (L : ℝ))) * ‖v‖ ≤
          ‖parentHamiltonianES A L N v‖ := by
  refine parentHamiltonianES_gap_bound_of_quadratic_form A L hL ?_
  intro N hLN v
  have hLpos : (0 : ℝ) < (L : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hL)
  have hLge_one : (1 : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast (Nat.le_of_lt hL)
  have hγle : ((1 : ℝ) / (4 * (L : ℝ))) ≤ 1 := by
    have hden : 0 < 4 * (L : ℝ) := mul_pos (by norm_num) hLpos
    rw [div_le_iff₀ hden]
    nlinarith [hLge_one]
  exact parentHamiltonianES_quadratic_form_of_ordered_local_term_bounds
    A L N hγle (c N) (hRow N hLN) (hCross N hLN) v

/-- Fixed-chain martingale quadratic-form estimate from finite-overlap
Friedrichs-angle hypotheses.

This is the local-window specialization of
`ProjectionGeometry.quadraticForm_sum_projections_of_finite_overlap`.  The
predicate `overlaps i j` marks the off-diagonal pairs for which a Friedrichs-angle
estimate is needed.  If each row has at most `m` such pairs, the non-overlap
cross terms are nonnegative, and every overlap obeys the ordered estimate with
coefficient `1 / m`, then the transported parent Hamiltonian satisfies
`H² ≥ γ H` as a quadratic form. -/
theorem parentHamiltonianES_quadratic_form_of_finite_overlap_friedrichs
    (A : MPSTensor d D) (L N : ℕ) {γ : ℝ} (hγle : γ ≤ 1)
    (overlaps : Fin N → Fin N → Prop) [DecidableRel overlaps] {m : ℕ} (hm : 0 < m)
    (hProj : ∀ i : Fin N, (localTermES A L i).IsSymmetricProjection)
    (hCard : ∀ i : Fin N,
      ((Finset.univ.erase i).filter (fun j => overlaps i j)).card ≤ m)
    (hDisjoint : ∀ i j : Fin N, j ∈ Finset.univ.erase i → ¬ overlaps i j →
      ∀ v : EuclideanSpace ℂ (Cfg d N),
        0 ≤ (⟪localTermES A L i v, localTermES A L j v⟫_ℂ).re)
    (hFriedrichs : ∀ i j : Fin N, j ∈ Finset.univ.erase i → overlaps i j →
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
      hFriedrichs v)

/-- Fixed-chain martingale quadratic-form estimate from finite-overlap
norm-compression Friedrichs-angle hypotheses.

For each overlapping pair, it is enough to bound the compressed product
`‖hᵢ (hⱼ v)‖` by `(1 - γ) / m` times `‖hᵢ v‖`.  The abstract projection-geometry
lemma converts this principal-angle style norm estimate into the ordered
cross-term bound consumed by the finite-overlap row-sum reduction. -/
theorem parentHamiltonianES_quadratic_form_of_finite_overlap_norm_bound
    (A : MPSTensor d D) (L N : ℕ) {γ : ℝ} (hγle : γ ≤ 1)
    (overlaps : Fin N → Fin N → Prop) [DecidableRel overlaps] {m : ℕ} (hm : 0 < m)
    (hCard : ∀ i : Fin N,
      ((Finset.univ.erase i).filter (fun j => overlaps i j)).card ≤ m)
    (hDisjoint : ∀ i j : Fin N, j ∈ Finset.univ.erase i → ¬ overlaps i j →
      ∀ v : EuclideanSpace ℂ (Cfg d N),
        0 ≤ (⟪localTermES A L i v, localTermES A L j v⟫_ℂ).re)
    (hOverlapNorm : ∀ i j : Fin N, j ∈ Finset.univ.erase i → overlaps i j →
      ∀ v : EuclideanSpace ℂ (Cfg d N),
        ‖localTermES A L i (localTermES A L j v)‖ ≤
          ((1 - γ) * ((m : ℝ)⁻¹)) * ‖localTermES A L i v‖) :
    ∀ v : EuclideanSpace ℂ (Cfg d N),
      γ * (⟪parentHamiltonianES A L N v, v⟫_ℂ).re ≤
        (⟪parentHamiltonianES A L N v,
          parentHamiltonianES A L N v⟫_ℂ).re := by
  intro v
  simpa [parentHamiltonianES_eq_sum_localTermES A L N] using
    (ProjectionGeometry.quadraticForm_sum_projections_of_finite_overlap_norm_bound
      (ι := Fin N) (E := EuclideanSpace ℂ (Cfg d N)) hγle
      (fun i : Fin N => localTermES A L i)
      (fun i : Fin N => localTermES_isSymmetricProjection A L i) overlaps hm hCard
      hDisjoint hOverlapNorm v)

/-- Fixed-chain finite-overlap quadratic-form estimate from a separate
norm-compression coefficient.

If the compressed products on overlapping pairs are bounded by `η`, and
`η ≤ (1 - γ) / m`, then the fixed-chain martingale quadratic form follows with
constant `γ`.  This version keeps the analytic overlap constant separate from the
gap parameter. -/
theorem parentHamiltonianES_quadratic_form_of_finite_overlap_norm_bound_of_le
    (A : MPSTensor d D) (L N : ℕ) {γ η : ℝ} (hγle : γ ≤ 1)
    (overlaps : Fin N → Fin N → Prop) [DecidableRel overlaps] {m : ℕ} (hm : 0 < m)
    (hCard : ∀ i : Fin N,
      ((Finset.univ.erase i).filter (fun j => overlaps i j)).card ≤ m)
    (hDisjoint : ∀ i j : Fin N, j ∈ Finset.univ.erase i → ¬ overlaps i j →
      ∀ v : EuclideanSpace ℂ (Cfg d N),
        0 ≤ (⟪localTermES A L i v, localTermES A L j v⟫_ℂ).re)
    (hηle : η ≤ (1 - γ) * ((m : ℝ)⁻¹))
    (hOverlapNorm : ∀ i j : Fin N, j ∈ Finset.univ.erase i → overlaps i j →
      ∀ v : EuclideanSpace ℂ (Cfg d N),
        ‖localTermES A L i (localTermES A L j v)‖ ≤
          η * ‖localTermES A L i v‖) :
    ∀ v : EuclideanSpace ℂ (Cfg d N),
      γ * (⟪parentHamiltonianES A L N v, v⟫_ℂ).re ≤
        (⟪parentHamiltonianES A L N v,
          parentHamiltonianES A L N v⟫_ℂ).re := by
  intro v
  simpa [parentHamiltonianES_eq_sum_localTermES A L N] using
    (ProjectionGeometry.quadraticForm_sum_projections_of_finite_overlap_norm_bound_of_le
      (ι := Fin N) (E := EuclideanSpace ℂ (Cfg d N)) hγle
      (fun i : Fin N => localTermES A L i)
      (fun i : Fin N => localTermES_isSymmetricProjection A L i) overlaps hm hCard
      hDisjoint hηle hOverlapNorm v)

/-- Uniform explicit gap-bound reduction from finite-overlap Friedrichs-angle
hypotheses.

For parent-Hamiltonian windows of length `L`, the expected finite-range bound is
`m = 2 * (L - 1)`: each local term overlaps at most that many other cyclic
translates when `N ≥ 2L`.  This theorem leaves the transported local projection
structure, the cyclic-window overlap predicate, non-overlap positivity, and the
Friedrichs-angle estimate as explicit hypotheses. It only performs the finite-overlap
row-sum reduction and the existing quadratic-form-to-gap conversion. -/
theorem parentHamiltonianES_gap_bound_of_finite_overlap_friedrichs
    (A : MPSTensor d D) (L : ℕ) (hL : 1 < L)
    (overlaps : ∀ N : ℕ, Fin N → Fin N → Prop)
    [∀ N : ℕ, DecidableRel (overlaps N)]
    (hProj : ∀ (N : ℕ) (_hLN : 2 * L ≤ N) (i : Fin N),
      (localTermES A L i).IsSymmetricProjection)
    (hCard : ∀ (N : ℕ) (_hLN : 2 * L ≤ N) (i : Fin N),
      ((Finset.univ.erase i).filter (fun j => overlaps N i j)).card ≤ 2 * (L - 1))
    (hDisjoint : ∀ (N : ℕ) (_hLN : 2 * L ≤ N) (i j : Fin N),
      j ∈ Finset.univ.erase i → ¬ overlaps N i j →
        ∀ v : EuclideanSpace ℂ (Cfg d N),
          0 ≤ (⟪localTermES A L i v, localTermES A L j v⟫_ℂ).re)
    (hFriedrichs : ∀ (N : ℕ) (_hLN : 2 * L ≤ N) (i j : Fin N),
      j ∈ Finset.univ.erase i → overlaps N i j →
        ∀ v : EuclideanSpace ℂ (Cfg d N),
          - (1 - ((1 : ℝ) / (4 * (L : ℝ)))) *
              (((2 * (L - 1) : ℕ) : ℝ)⁻¹) *
                (⟪localTermES A L i v, v⟫_ℂ).re ≤
            (⟪localTermES A L i v, localTermES A L j v⟫_ℂ).re) :
    0 < (1 : ℝ) / (4 * (L : ℝ)) ∧
    ∀ (N : ℕ) (_hLN : 2 * L ≤ N)
      (v : EuclideanSpace ℂ (Cfg d N)),
      v ∈ (parentHamiltonianGroundSpaceES A L N)ᗮ →
        ((1 : ℝ) / (4 * (L : ℝ))) * ‖v‖ ≤
          ‖parentHamiltonianES A L N v‖ := by
  refine parentHamiltonianES_gap_bound_of_quadratic_form A L hL ?_
  intro N hLN v
  have hLpos : (0 : ℝ) < (L : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hL)
  have hLge_one : (1 : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast (Nat.le_of_lt hL)
  have hγle : ((1 : ℝ) / (4 * (L : ℝ))) ≤ 1 := by
    have hden : 0 < 4 * (L : ℝ) := mul_pos (by norm_num) hLpos
    rw [div_le_iff₀ hden]
    nlinarith [hLge_one]
  have hm : 0 < 2 * (L - 1) :=
    Nat.mul_pos (by decide) (Nat.sub_pos_of_lt hL)
  exact parentHamiltonianES_quadratic_form_of_finite_overlap_friedrichs
    A L N hγle (overlaps N) hm (hProj N hLN) (hCard N hLN)
    (hDisjoint N hLN) (hFriedrichs N hLN) v

/-- Uniform explicit gap-bound reduction using the concrete cyclic-window overlap
predicate.

For chains with `N ≥ 2L`, the predicate `cyclicWindowsOverlap N L i j` marks the
cyclic translates whose length-`L` windows have the finite-range overlap relevant
to the martingale method.  The row-cardinality estimate is supplied by
`cyclicWindowsOverlap_card_le`, local projection structure is supplied by
`localTermES_isSymmetricProjection`, and non-overlap positivity is supplied by
`localTermES_re_inner_nonneg_of_not_cyclicWindowsOverlap`.  Consequently the
only remaining local hypothesis is the Friedrichs-angle estimate for pairs
marked by `cyclicWindowsOverlap`. -/
theorem parentHamiltonianES_gap_bound_of_cyclic_window_friedrichs
    (A : MPSTensor d D) (L : ℕ) (hL : 1 < L)
    (hFriedrichs : ∀ (N : ℕ) (_hLN : 2 * L ≤ N) (i j : Fin N),
      j ∈ Finset.univ.erase i → cyclicWindowsOverlap N L i j →
        ∀ v : EuclideanSpace ℂ (Cfg d N),
          - (1 - ((1 : ℝ) / (4 * (L : ℝ)))) *
              (((2 * (L - 1) : ℕ) : ℝ)⁻¹) *
                (⟪localTermES A L i v, v⟫_ℂ).re ≤
            (⟪localTermES A L i v, localTermES A L j v⟫_ℂ).re) :
    0 < (1 : ℝ) / (4 * (L : ℝ)) ∧
    ∀ (N : ℕ) (_hLN : 2 * L ≤ N)
      (v : EuclideanSpace ℂ (Cfg d N)),
      v ∈ (parentHamiltonianGroundSpaceES A L N)ᗮ →
        ((1 : ℝ) / (4 * (L : ℝ))) * ‖v‖ ≤
          ‖parentHamiltonianES A L N v‖ := by
  exact parentHamiltonianES_gap_bound_of_finite_overlap_friedrichs A L hL
    (fun N => cyclicWindowsOverlap N L)
    (fun N _hLN i => localTermES_isSymmetricProjection A L i)
    (fun N hLN i => cyclicWindowsOverlap_card_le hLN hL i)
    (fun N hLN i j _hij hnot v =>
      localTermES_re_inner_nonneg_of_not_cyclicWindowsOverlap A (by omega) hnot v)
    hFriedrichs

/-- Uniform explicit gap-bound reduction from the remaining overlapping-window
Friedrichs estimate.

The concrete cyclic-window row-cardinality bound, local symmetric-projection
structure, and non-overlap positivity are already proved.  Consequently it is
enough to assume the displayed ordered Friedrichs lower bound only for pairs whose
cyclic supports overlap. -/
theorem parentHamiltonianES_gap_bound_of_cyclic_window_overlap_friedrichs
    (A : MPSTensor d D) (L : ℕ) (hL : 1 < L)
    (hFriedrichs : ∀ (N : ℕ) (_hLN : 2 * L ≤ N) (i j : Fin N),
      j ∈ Finset.univ.erase i → cyclicWindowsOverlap N L i j →
        ∀ v : EuclideanSpace ℂ (Cfg d N),
          - (1 - ((1 : ℝ) / (4 * (L : ℝ)))) *
              (((2 * (L - 1) : ℕ) : ℝ)⁻¹) *
                (⟪localTermES A L i v, v⟫_ℂ).re ≤
            (⟪localTermES A L i v, localTermES A L j v⟫_ℂ).re) :
    0 < (1 : ℝ) / (4 * (L : ℝ)) ∧
    ∀ (N : ℕ) (_hLN : 2 * L ≤ N)
      (v : EuclideanSpace ℂ (Cfg d N)),
      v ∈ (parentHamiltonianGroundSpaceES A L N)ᗮ →
        ((1 : ℝ) / (4 * (L : ℝ))) * ‖v‖ ≤
          ‖parentHamiltonianES A L N v‖ := by
  exact parentHamiltonianES_gap_bound_of_cyclic_window_friedrichs A L hL hFriedrichs

/-- Uniform explicit gap-bound reduction from a norm-compression form of the
overlapping-window Friedrichs estimate.

It suffices to prove that for every overlapping off-diagonal pair the compressed
product of transported local projections satisfies
`‖hᵢ (hⱼ v)‖ ≤ (1 - 1/(4L)) / (2(L-1)) * ‖hᵢ v‖`.  The abstract projection
geometry converts this principal-angle style condition into the ordered
Friedrichs lower bound and then applies the finite-overlap martingale reduction. -/
theorem parentHamiltonianES_gap_bound_of_cyclic_window_overlap_norm_bound
    (A : MPSTensor d D) (L : ℕ) (hL : 1 < L)
    (hOverlapNorm : ∀ (N : ℕ) (_hLN : 2 * L ≤ N) (i j : Fin N),
      j ∈ Finset.univ.erase i → cyclicWindowsOverlap N L i j →
        ∀ v : EuclideanSpace ℂ (Cfg d N),
          ‖localTermES A L i (localTermES A L j v)‖ ≤
            ((1 - ((1 : ℝ) / (4 * (L : ℝ)))) *
              (((2 * (L - 1) : ℕ) : ℝ)⁻¹)) * ‖localTermES A L i v‖) :
    0 < (1 : ℝ) / (4 * (L : ℝ)) ∧
    ∀ (N : ℕ) (_hLN : 2 * L ≤ N)
      (v : EuclideanSpace ℂ (Cfg d N)),
      v ∈ (parentHamiltonianGroundSpaceES A L N)ᗮ →
        ((1 : ℝ) / (4 * (L : ℝ))) * ‖v‖ ≤
          ‖parentHamiltonianES A L N v‖ := by
  refine parentHamiltonianES_gap_bound_of_cyclic_window_overlap_friedrichs A L hL ?_
  intro N hLN i j hij hoverlap v
  have hCross :
      -((1 - ((1 : ℝ) / (4 * (L : ℝ)))) *
          (((2 * (L - 1) : ℕ) : ℝ)⁻¹)) *
        (⟪localTermES A L i v, v⟫_ℂ).re ≤
          (⟪localTermES A L i v, localTermES A L j v⟫_ℂ).re :=
    (localTermES_isSymmetricProjection A L i).re_inner_apply_apply_ge_neg_of_norm_apply_le
      (hOverlapNorm N hLN i j hij hoverlap) v
  convert hCross using 1
  ring

/-- Uniform gap-bound reduction from an overlap norm-compression estimate with a
separate coefficient.

For cyclic windows with at most `2 * (L - 1)` overlapping off-diagonal neighbours,
a compression estimate with coefficient `η` gives any positive gap parameter `γ`
satisfying `η ≤ (1 - γ) / (2 * (L - 1))`.  This is the constant-flexible form of
`parentHamiltonianES_gap_bound_of_cyclic_window_overlap_norm_bound`. -/
theorem parentHamiltonianES_gap_bound_of_cyclic_window_overlap_norm_bound_of_le
    (A : MPSTensor d D) (L : ℕ) (hL : 1 < L) {γ η : ℝ}
    (hγpos : 0 < γ) (hγle : γ ≤ 1)
    (hηle : η ≤ (1 - γ) * (((2 * (L - 1) : ℕ) : ℝ)⁻¹))
    (hOverlapNorm : ∀ (N : ℕ) (_hLN : 2 * L ≤ N) (i j : Fin N),
      j ∈ Finset.univ.erase i → cyclicWindowsOverlap N L i j →
        ∀ v : EuclideanSpace ℂ (Cfg d N),
          ‖localTermES A L i (localTermES A L j v)‖ ≤
            η * ‖localTermES A L i v‖) :
    0 < γ ∧
    ∀ (N : ℕ) (_hLN : 2 * L ≤ N)
      (v : EuclideanSpace ℂ (Cfg d N)),
      v ∈ (parentHamiltonianGroundSpaceES A L N)ᗮ →
        γ * ‖v‖ ≤ ‖parentHamiltonianES A L N v‖ := by
  refine ⟨hγpos, ?_⟩
  refine parentHamiltonianES_norm_bound_of_quadratic_form A L hγpos ?_
  intro N hLN v
  have hm : 0 < 2 * (L - 1) :=
    Nat.mul_pos (by decide) (Nat.sub_pos_of_lt hL)
  exact parentHamiltonianES_quadratic_form_of_finite_overlap_norm_bound_of_le
    A L N hγle (cyclicWindowsOverlap N L) hm
    (fun i => cyclicWindowsOverlap_card_le hLN hL i)
    (fun _i _j _hij hnot w =>
      localTermES_re_inner_nonneg_of_not_cyclicWindowsOverlap A (by omega) hnot w)
    hηle (fun i j hij hoverlap w => hOverlapNorm N hLN i j hij hoverlap w) v

/-- Uniform gap-bound reduction from a strict overlap norm-compression constant.

If every overlapping off-diagonal cyclic pair satisfies the compression estimate
with coefficient `η`, and `η * (2 * (L - 1)) < 1`, then the transported parent
Hamiltonians have gap constant `1 - η * (2 * (L - 1))`.  Thus any uniform
compression constant strictly below the reciprocal of the cyclic overlap degree
yields a positive gap. -/
theorem parentHamiltonianES_gap_bound_of_cyclic_window_overlap_norm_bound_of_lt
    (A : MPSTensor d D) (L : ℕ) (hL : 1 < L) {η : ℝ}
    (hηnonneg : 0 ≤ η)
    (hηlt : η * (((2 * (L - 1) : ℕ) : ℝ)) < 1)
    (hOverlapNorm : ∀ (N : ℕ) (_hLN : 2 * L ≤ N) (i j : Fin N),
      j ∈ Finset.univ.erase i → cyclicWindowsOverlap N L i j →
        ∀ v : EuclideanSpace ℂ (Cfg d N),
          ‖localTermES A L i (localTermES A L j v)‖ ≤
            η * ‖localTermES A L i v‖) :
    0 < 1 - η * (((2 * (L - 1) : ℕ) : ℝ)) ∧
    ∀ (N : ℕ) (_hLN : 2 * L ≤ N)
      (v : EuclideanSpace ℂ (Cfg d N)),
      v ∈ (parentHamiltonianGroundSpaceES A L N)ᗮ →
        (1 - η * (((2 * (L - 1) : ℕ) : ℝ))) * ‖v‖ ≤
          ‖parentHamiltonianES A L N v‖ := by
  have hm : 0 < 2 * (L - 1) :=
    Nat.mul_pos (by decide) (Nat.sub_pos_of_lt hL)
  have hmRpos : 0 < (((2 * (L - 1) : ℕ) : ℝ)) := by
    exact_mod_cast hm
  have hγpos : 0 < 1 - η * (((2 * (L - 1) : ℕ) : ℝ)) := by
    linarith
  have hγle : 1 - η * (((2 * (L - 1) : ℕ) : ℝ)) ≤ 1 := by
    have hmul_nonneg : 0 ≤ η * (((2 * (L - 1) : ℕ) : ℝ)) :=
      mul_nonneg hηnonneg hmRpos.le
    linarith
  have hηle :
      η ≤ (1 - (1 - η * (((2 * (L - 1) : ℕ) : ℝ)))) *
        (((2 * (L - 1) : ℕ) : ℝ)⁻¹) := by
    have hmne : (((2 * (L - 1) : ℕ) : ℝ)) ≠ 0 := ne_of_gt hmRpos
    have hηeq :
        η = (1 - (1 - η * (((2 * (L - 1) : ℕ) : ℝ)))) *
          (((2 * (L - 1) : ℕ) : ℝ)⁻¹) := by
      calc
        η = η * (((2 * (L - 1) : ℕ) : ℝ) *
            (((2 * (L - 1) : ℕ) : ℝ)⁻¹)) := by
              rw [mul_inv_cancel₀ hmne, mul_one]
        _ = (1 - (1 - η * (((2 * (L - 1) : ℕ) : ℝ)))) *
            (((2 * (L - 1) : ℕ) : ℝ)⁻¹) := by ring
    exact le_of_eq hηeq
  exact parentHamiltonianES_gap_bound_of_cyclic_window_overlap_norm_bound_of_le
    A L hL hγpos hγle hηle hOverlapNorm

end MPSTensor
