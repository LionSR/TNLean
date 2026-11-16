/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.FullIntervalViability
import TNLean.MPS.AreaLaw.PhysicalDGTreeMPS
import QICLean.Analysis.ViableSubspaceUnitApproximation

/-!
# Normalized witnesses in the same recursively constructed root

The full-chain viable root gives, for each unit vector in the original
full ground space, its normalized orthogonal projection into that root.
The projection has squared overlap at least `197 / 200`, squared distance
at most `3 / 100`, and the native matrix product bound of the whole root.
The families, operations and recursive spaces are chosen before this vector.

**Scope restriction (a root projection, not final spectral extraction):**
The capped gap, block leaves and one final trim remain those of the
recursive witness theorem; see
`docs/paper-gaps/alvv16_approximation_parameters.tex`. The witness depends
on the chosen ground vector. No adaptive joint probability, Ritz extraction
or running-time bound is asserted.
-/

open Matrix
open scoped BigOperators TensorProduct ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open scoped InnerProductSpace

namespace TNLean.MPS.AreaLaw

/-- Every unit vector in the original full ground space has a normalized
projection into the same actual recursive root, with the displayed overlap,
distance and native MPS bounds. The complete recursive construction is
retained. Supporting ALVV, arXiv:1602.08828v2, `t:alg1`, lines 1777–1817,
and Definition `d:close`, lines 469–474. -/
theorem exists_physical_dg_interval_tree_unit_mps :
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
        (∀ (p r : ℕ), p ≤ r → r ≤ L →
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
                  1000000 * Dref ^ 2 * (L + 1) * count) ∧
        (∀ v : EuclideanSpace ℂ (interval L 0 L → Fin q),
          v ∈ balancedIntervalSpace operation width hwidth 0 L →
          IsOpenMPS L q (1000000 * Dref ^ 2 * (L + 1) * count ^ 2)
            (fullIntervalRead L q v)) ∧
        let root := balancedIntervalSpace operation width hwidth 0 L
        let nativeRoot := nativeFullIntervalSpace L q root
        Submodule.IsCloseTo (3 / 200 : ℝ) nativeRoot G ∧
        ∀ Γ : EuclideanSpace ℂ (Fin L → Fin q), Γ ∈ G → ‖Γ‖ = 1 →
          ∃ φ : EuclideanSpace ℂ (Fin L → Fin q),
            φ ∈ nativeRoot ∧ ‖φ‖ = 1 ∧
            (197 / 200 : ℝ) ≤ ‖⟪φ, Γ⟫_ℂ‖ ^ 2 ∧
            ⟪φ, Γ⟫_ℂ = ((‖nativeRoot.starProjection Γ‖ : ℝ) : ℂ) ∧
            ‖φ - Γ‖ ^ 2 ≤ (3 / 100 : ℝ) ∧
            φ = ((‖nativeRoot.starProjection Γ‖⁻¹ : ℝ) : ℂ) •
              nativeRoot.starProjection Γ ∧
            IsOpenMPS L q (1000000 * Dref ^ 2 * (L + 1) * count ^ 2)
              (WithLp.ofLp φ) := by
  classical
  obtain ⟨C, K, hC, hK, hphysical⟩ := exists_physical_dg_interval_tree_mps
  refine ⟨C, K, hC, hK, ?_⟩
  intro L q h hsupp h0 h1 mu nu gamma hgamma H hH hmu hnu hmunu hgap
    G rG g u epsilonRef b m v ell D
  obtain ⟨hell, hlogD, B, hB, hlogB, hfamilies⟩ :=
    hphysical L q h hsupp h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
  refine ⟨hell, hlogD, B, hB, hlogB, ?_⟩
  intro Dref xi width hwidth
  obtain ⟨N, F, hN, hparents⟩ := hfamilies
  refine ⟨N, F, hN, ?_⟩
  intro beta hbeta hbeta1 A s count
  obtain ⟨hscount, operation, hliteral, htree, hmps⟩ := hparents beta hbeta hbeta1
  refine ⟨hscount, operation, hliteral, htree, hmps, ?_⟩
  intro root nativeRoot
  have hroot := (htree 0 L (Nat.zero_le L) le_rfl).1
  have hclose : Submodule.IsCloseTo (3 / 200 : ℝ) nativeRoot G :=
    (isViable_fullInterval_iff_isCloseTo root G).mp hroot
  refine ⟨hclose, ?_⟩
  intro Γ hΓG hΓ
  obtain ⟨φ, hφroot, hφ, hoverlap, hphase, hdistance, hprojection⟩ :=
    hclose.exists_unit_mem_norm_inner_sq_ge (by norm_num) hΓG hΓ
  refine ⟨φ, hφroot, hφ, ?_, hphase, ?_, hprojection, ?_⟩
  · convert hoverlap using 1
    norm_num
  · convert hdistance using 1
    norm_num
  · obtain ⟨localVector, hlocal, rfl⟩ := hφroot
    change IsOpenMPS L q (1000000 * Dref ^ 2 * (L + 1) * count ^ 2)
      (WithLp.ofLp (fullIntervalEquiv L q localVector))
    simpa only [fullIntervalEquiv_apply] using hmps localVector hlocal

end TNLean.MPS.AreaLaw
