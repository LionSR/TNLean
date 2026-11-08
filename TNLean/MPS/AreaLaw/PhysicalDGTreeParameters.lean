/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalDGIntervalTree
import TNLean.MPS.AreaLaw.PolynomialFilterParameters
import TNLean.MPS.AreaLaw.SharpApproximationParameters

/-!
# Automatic parameters for the physical recursive viable tree

Universal constants are chosen before the chain and Hamiltonian. The
explicit enlarged count base is `m = max q 50`. The existing uniform
scalar theorem then chooses the degree and truncation scale and proves
all numerical tail and filter estimates required by the recursive physical
construction. No such numerical estimates are hypotheses of the result.
The actual parent families are chosen before every sampling size and child
space, and all recursive spaces remain viable for the original full ground
space.

**Scope restriction (block leaves, one final trim and capped gap):** This
is the recursive witness construction with full local spaces at leaves of
length at most `4 * ell`, one final trim at each long node, and
`g = min gamma 1`. The distinction from the printed algorithm is recorded
in `docs/paper-gaps/alvv16_approximation_parameters.tex`. No adaptive joint
probability, energy-estimation invariant, final spectral extraction or
running time is asserted. Rank bounds concern the recorded generators,
not every vector in their span.
-/

open Matrix
open scoped BigOperators TensorProduct ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- The original nearest-neighbour Hamiltonian determines an actual
recursive viable tree, with all numerical tail and filter conditions
derived from the displayed degree choice. The constants precede every
physical input, and each parent family precedes the sampling size and
child spaces. Supporting ALVV, arXiv:1602.08828v2, `t:alg1`,
lines 1777–1817, with the explicitly stated modified-tree scope. -/
theorem exists_physical_dg_interval_tree :
    ∃ C K : ℝ, 1 ≤ C ∧ 0 < K ∧ ∀ (L q : ℕ),
    ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
      (_hsupp : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
        (h i) (interval L i.val (i.val + 2)))
      (h0 : ∀ i, 0 ≤ h i) (_h1 : ∀ i, h i ≤ 1) (mu nu gamma : ℝ),
    0 < gamma →
    let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i, h i
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    mu ∈ spectrum ℝ H → nu ∈ spectrum ℝ H → mu < nu →
    (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
    let rG := Module.finrank ℂ G
    let g := min gamma 1
    let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
    let epsilonRef : ℝ := 1 / 10000
    let b := 16 + Real.log (1 / g) +
      Real.log (32 * (rG : ℝ) * ((L : ℝ) + 1) / epsilonRef)
    let m := max q 50
    let v := 1 + Real.log (m : ℝ) + Real.log (1 / g)
    let ell : ℕ := Nat.ceil (C * v ^ 2 / g)
    let D := (m * ell ^ 2) ^ (22 * ell)
    ∃ _hell : 21 ≤ ell,
    Real.log (D : ℝ) ≤ 22 * (C + 1) * (6 + 2 * Real.log (C + 1)) / g * v ^ 3 ∧
    ∃ B : ℕ, 1 ≤ B ∧
    Real.log (B : ℝ) ≤
      K * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) * u) *
        (1 + Real.log b) ∧
    let Dref := rG ^ 2 * B
    let xi := 1 / (1000 * (Dref : ℝ) * Real.sqrt ((L : ℝ) + 1))
    let width := 4 * ell
    let hwidth : 1 ≤ width := by omega
    ∃ (N : LongIntervalIndex L width → ℕ)
      (F : ∀ J : LongIntervalIndex L width,
        Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
          EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)),
      (∀ J, N J ≤ D ^ 2) ∧
      ∀ (beta : ℝ), 0 < beta → beta < 1 →
      let A := 1 + Real.log (rG : ℝ) + Real.log (D : ℝ) + Real.log (1 / beta)
      let s := Nat.ceil (4096 * (rG : ℝ) * A)
      let count := D ^ 6 * s ^ 3
      (s : ℝ) ≤ 4097 * (rG : ℝ) * A ∧
      ∃ operation : IntervalMergeOperation L q,
        (∀ (J : LongIntervalIndex L width) (k : ℕ) (hpk : J.val.1 ≤ k) (hkr : k ≤ J.val.2)
          (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 k → Fin q)))
          (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k J.val.2 → Fin q))),
          Submodule.IsViable (3 / 200 : ℝ) S1
            (G.map (Entropy.regionTensorCoordinates q
              (interval L J.val.1 k)).toLinearEquiv.toLinearMap) →
          Submodule.IsViable (3 / 200 : ℝ) S2
            (G.map (Entropy.regionTensorCoordinates q
              (interval L k J.val.2)).toLinearEquiv.toLinearMap) →
          Module.finrank ℂ S1 ≤ count → Module.finrank ℂ S2 ≤ count →
          ∃ U : Matrix.unitaryGroup
            (Fin (Module.finrank ℂ (adjacentIntervalMerge L q
              J.val.1 k J.val.2 hpk hkr S1 S2))) ℂ,
            operation J.val.1 k J.val.2 hpk hkr S1 S2 =
              sampledIntervalTrim L q J.val.1 J.val.2 (F J) (Nat.clog D (D ^ 2 * s)) s xi
                (adjacentIntervalMerge L q J.val.1 k J.val.2 hpk hkr S1 S2) U) ∧
        ∀ (p r : ℕ), p ≤ r → r ≤ L →
          let S := balancedIntervalSpace operation width hwidth p r
          Submodule.IsViable (3 / 200 : ℝ) S
            (G.map (Entropy.regionTensorCoordinates q
              (interval L p r)).toLinearEquiv.toLinearMap) ∧
          Module.finrank ℂ S ≤ count ∧
          ∃ n : ℕ, n ≤ count ∧
            ∃ u : Fin n → EuclideanSpace ℂ (interval L p r → Fin q),
              S = Submodule.span ℂ (Set.range u) ∧
              ∀ j : ℕ, j < r - p - 1 → ∀ i : Fin n,
                Matrix.schmidtRank (WithLp.ofLp
                  (Entropy.cutVector (n := fun _ : interval L p r ↦ q)
                    (intervalTrimCut L p r j) (u i))) ≤
                  1000000 * Dref ^ 2 * (L + 1) * count := by
  classical
  obtain ⟨C, hC, _hC21, _hCM, _hClog, hparameters⟩ :=
    Real.exists_dg_accuracy_scalar_parameters
  obtain ⟨K, hK, hconditional⟩ := exists_physical_dg_recursive_interval_spaces
  refine ⟨C, K, hC, hK, ?_⟩
  intro L q h hsupp h0 h1 mu nu gamma hgamma H hH hmu hnu hmunu hgap
    G rG g u epsilonRef b m v ell D
  have hm2 : 2 ≤ m := (by decide : 2 ≤ 50).trans (Nat.le_max_right q 50)
  have hqm : q ≤ m := Nat.le_max_left q 50
  have hm50 : 50 ≤ m := Nat.le_max_right q 50
  have hg : 0 < g := lt_min hgamma (by norm_num)
  have hg1 : g ≤ 1 := min_le_right gamma 1
  obtain ⟨hell, _hmD, hD, _hlower, _hupper, _hscale, _hcount,
    hlogD, htrade, htail⟩ := hparameters m g hm2 hg hg1
  refine ⟨hell, hlogD, ?_⟩
  obtain ⟨B, hB, hlogB, htree⟩ :=
    hconditional L q h hsupp h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
  refine ⟨B, hB, hlogB, ?_⟩
  intro Dref xi width hwidth
  have hDR : (0 : ℝ) < D := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < (2 : ℕ)) hD)
  have hpow : 0 < (D : ℝ) ^ 12 := pow_pos hDR 12
  let Delta : ℝ := (1 / 100000) / (D : ℝ) ^ 12
  have hbudget : (D : ℝ) ^ 12 * Delta = 1 / 100000 := by
    dsimp only [Delta]
    field_simp
  have hfilter : ∀ R : ℝ, 0 < R → R ≤ 3 * (ell : ℝ) + 4 * (ell : ℝ) →
      (2 * Real.exp (-2 * (ell : ℝ) ^ 2 * Real.sqrt ((4 * g / 5) / R))) ^ 2 ≤ Delta := by
    intro R hR hRbudget
    rw [Real.squared_chebyshev_error_eq]
    apply (le_div_iff₀ hpow).2
    have hR8 : R ≤ 8 * (ell : ℝ) := by
      linarith only [hRbudget, (Nat.cast_nonneg ell : (0 : ℝ) ≤ (ell : ℝ))]
    have hsmall : (D : ℝ) ^ 12 *
        (4 * Real.exp (-4 * (ell : ℝ) ^ 2 * Real.sqrt ((4 * g / 5) / R))) ≤
          1 / 100000 := by
      simpa only [neg_mul] using htrade R hR hR8
    nlinarith only [hsmall]
  have htail' : (288 * Real.exp (11 / 8)) *
      Real.exp (-((ell : ℝ) - g) / 8) ≤ (1 / (m : ℝ)) * g / 1000000 := by
    rw [div_mul_eq_mul_div, one_mul, div_div, mul_comm (m : ℝ) 1000000]
    exact htail
  exact htree m ell (ell : ℝ) Delta hqm hm50 (by omega) (by exact_mod_cast hell)
    htail' hfilter hbudget.le

end TNLean.MPS.AreaLaw
