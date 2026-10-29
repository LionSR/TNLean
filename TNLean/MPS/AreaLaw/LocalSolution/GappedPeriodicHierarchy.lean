/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LocalSolution.PeriodicPhysicalHierarchy
import TNLean.Algebra.GappedGroundState

/-!
# The periodic hierarchy from a unique gapped ground state

The local ground-vector estimate is derived from the actual Gaussian
filters and the original projector gap. The filter parameter, decay rate
and norm allowance are chosen before the chain and its ground data.
The filters and pair assignment depend on the local operators and these
parameters; the spectral-window centres use expectations in the specified
ground vector. No ground-vector-free algorithm or running time is asserted.
This supplies the one-ground-state case of Hastings,
arXiv:cond-mat/0508554v3, lines 375–387 and 609–743.

**Scope restriction (unique ground state):** The degenerate-ground-space
basis construction is separate; see
`docs/paper-gaps/hastings05_two_dim_ground_basis.tex`.

**Local fix (periodic hierarchy):** the norm deficiency is measured against
the original ground vector, and a further window controls the closing edge.
See `docs/paper-gaps/hastings05_hierarchical_projection.tex` and
`docs/paper-gaps/hastings05_hierarchical_energy.tex`.
-/

open Matrix QuantumCircuit TNLean.Lattice
open scoped Matrix.Norms.L2Operator InnerProductSpace

namespace TNLean.MPS.AreaLaw.LocalSolution

/-- The actual truncated filters satisfy the local ground-vector estimate
with one common exponential rate. Hastings, arXiv:cond-mat/0508554v3,
eq. `low`, and the hierarchy construction in Section III. -/
private theorem exists_periodic_gapped_truncation_data {R J Δ : ℝ}
    (hR : 0 ≤ R) (hJ : 0 < J) (hΔ : 0 < Δ) :
    ∃ c₁ η C : ℝ, 0 < c₁ ∧ 0 < η ∧ 0 ≤ C ∧
      ∀ {M d : ℕ}, 0 < M →
        ∀ (g : Fin M → Matrix (Fin M → Fin d) (Fin M → Fin d) ℂ),
          (∀ i, (g i).IsHermitian) →
          (∀ i, g i ∈ supportedOperators d {v | (roundedPeriodicDistance i v : ℝ) ≤ R}) →
          (∀ i, ‖g i‖ ≤ J) →
          ∀ (Ω : EuclideanSpace ℂ (Fin M → Fin d)) (E₀ : ℝ),
            IsGappedGroundState (∑ i, g i) E₀ Ω Δ →
            ∀ (ℓ : ℕ), R ≤ (ℓ : ℝ) → ∀ i,
              let a := periodicPhysicalTruncatedTerm c₁ R Δ ℓ g i
              let Jb := 2 * max J (J * C)
              a ∈ supportedOperators d {v | roundedPeriodicDistance i v ≤ ℓ} ∧
                a.IsHermitian ∧ ‖a‖ ≤ Jb ∧
                ‖gaussianFilteredTerm (c₁ * (ℓ : ℝ) * Δ) Δ (∑ j, g j) (g i) - a‖ ≤
                  Jb * Real.exp (-(η * (ℓ : ℝ))) ∧
                ‖toEuclideanLin
                  (a - ((⟪Ω, toEuclideanLin a Ω⟫_ℂ).re : ℂ) • 1) Ω‖ ≤
                  Jb * Real.exp (-(η * (ℓ : ℝ))) := by
  obtain ⟨c₁, ηloc, C, hc₁, hηloc, hC, hloc⟩ :=
    exists_periodicPhysicalTruncatedTerm_localization hR hJ.le hΔ
  refine ⟨c₁, min ηloc (c₁ * Δ / 2), C, hc₁,
    lt_min hηloc (half_pos (mul_pos hc₁ hΔ)), hC, ?_⟩
  intro M d hM g hg hsupp hnorm Ω E₀ hgs ℓ hℓR i a Jb
  obtain ⟨haS, haH, haN, haE⟩ := hloc hM g hg hsupp hnorm ℓ hℓR i
  have hJb : J ≤ Jb := by
    dsimp only [Jb]
    linarith only [le_max_left J (J * C), hJ]
  have hlow := norm_apply_sub_inner_smul_le_of_gaussianFilteredTerm
    (by positivity : 0 ≤ c₁ * (ℓ : ℝ) * Δ) hΔ hgs (g i) a
  have hExpLoc : Real.exp (-(ηloc * (ℓ : ℝ))) ≤
      Real.exp (-(min ηloc (c₁ * Δ / 2) * (ℓ : ℝ))) :=
    Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right
      (min_le_left ηloc (c₁ * Δ / 2)) (Nat.cast_nonneg ℓ)))
  have hExpGap : Real.exp (-(c₁ * (ℓ : ℝ) * Δ) / 2) ≤
      Real.exp (-(min ηloc (c₁ * Δ / 2) * (ℓ : ℝ))) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div]
    apply neg_le_neg
    calc min ηloc (c₁ * Δ / 2) * (ℓ : ℝ) ≤ c₁ * Δ / 2 * (ℓ : ℝ) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg ℓ)
      _ = c₁ * (ℓ : ℝ) * Δ / 2 := by ring
  have hError : ‖gaussianFilteredTerm (c₁ * (ℓ : ℝ) * Δ) Δ (∑ j, g j) (g i) - a‖ ≤
      J * C * Real.exp (-(min ηloc (c₁ * Δ / 2) * (ℓ : ℝ))) :=
    haE.trans (mul_le_mul_of_nonneg_left hExpLoc (mul_nonneg hJ.le hC))
  have hbudget : J + J * C ≤ Jb := by
    dsimp only [Jb]
    linarith only [le_max_left J (J * C), le_max_right J (J * C)]
  have hJC : J * C ≤ Jb := (le_add_of_nonneg_left hJ.le).trans hbudget
  refine ⟨haS, haH, haN.trans hJb,
    hError.trans (mul_le_mul_of_nonneg_right hJC (Real.exp_pos _).le), ?_⟩
  have hreal : ((⟪Ω, toEuclideanLin a Ω⟫_ℂ).re : ℂ) =
      ⟪Ω, toEuclideanLin a Ω⟫_ℂ :=
    (isSymmetric_toEuclideanLin_iff.mpr haH).coe_re_inner_self_apply Ω
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    toLpLin_one, LinearMap.id_apply, hreal]
  calc _ ≤ ‖g i‖ * Real.exp (-(c₁ * (ℓ : ℝ) * Δ) / 2) +
        ‖gaussianFilteredTerm (c₁ * (ℓ : ℝ) * Δ) Δ (∑ j, g j) (g i) - a‖ := hlow
    _ ≤ J * Real.exp (-(min ηloc (c₁ * Δ / 2) * (ℓ : ℝ))) +
        J * C * Real.exp (-(min ηloc (c₁ * Δ / 2) * (ℓ : ℝ))) := by
      exact add_le_add (mul_le_mul (hnorm i) hExpGap (Real.exp_pos _).le hJ.le) hError
    _ = (J + J * C) * Real.exp (-(min ηloc (c₁ * Δ / 2) * (ℓ : ℝ))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hbudget (Real.exp_pos _).le

/-- Original Hermitian local interactions and a specified unique gapped ground state
give an actual periodic hierarchy, with no supplied local residual or pair family. The
constants are chosen before the chain, the Hamiltonian and its ground data.
Hastings, arXiv:cond-mat/0508554v3, eq. `low`, lines 375–387 and 609–743, with the
corrected deficiency recurrence and closing window documented in
`docs/paper-gaps/hastings05_hierarchical_projection.tex` and
`docs/paper-gaps/hastings05_hierarchical_energy.tex`. -/
theorem exists_periodicPhysicalHierarchy_of_isGappedGroundState {R J Δ : ℝ}
    (hR : 0 ≤ R) (hJ : 0 < J) (hΔ : 0 < Δ) :
    ∃ c₁ η C : ℝ, 0 < c₁ ∧ 0 < η ∧ 0 ≤ C ∧
      ∀ {M d : ℕ}, 0 < M →
        ∀ (g : Fin M → Matrix (Fin M → Fin d) (Fin M → Fin d) ℂ),
          (∀ i, (g i).IsHermitian) →
          (∀ i, g i ∈ supportedOperators d {v | (roundedPeriodicDistance i v : ℝ) ≤ R}) →
          (∀ i, ‖g i‖ ≤ J) →
          ∀ (Ω : EuclideanSpace ℂ (Fin M → Fin d)) (E₀ : ℝ),
            IsGappedGroundState (∑ i, g i) E₀ Ω Δ →
            let Jb := 2 * max J (J * C)
            let ℓ := physicalPeriodicProjectionRadius R M Jb η Δ
            let r := η * (ℓ : ℝ)
            let a := periodicPhysicalTruncatedTerm c₁ R Δ ℓ g
            let P := roundedPeriodicProjection ℓ a Ω Jb r
            let b := roundedPeriodicOperator ℓ a
            let h := finiteHierarchyDepth (roundedPeriodicBlockCount M ℓ)
            let K := 8 * (ℓ : ℝ) * Jb
            ∃ φ : EuclideanSpace ℂ (Fin M → Fin d), ‖φ‖ = 1 ∧
              toEuclideanLin P φ = φ ∧
              ‖φ - Ω‖ ≤ 2 * (((3 : ℝ) ^ (h + 1) - 1) * Real.exp (-r / 8)) ∧
              IsRetainedHierarchy
                (hierarchyProjection (hierarchyEdge (extendFiniteEdges b))
                  (fun m k ↦
                    (⟪Ω, toEuclideanLin (hierarchyEdge (extendFiniteEdges b) m k) Ω⟫_ℂ).re)
                  (hierarchyWindowRadius K r h)) h 0 φ ∧
              ∀ {n : ℕ} (Φ : Fin n → EuclideanSpace ℂ (Fin M → Fin d)), Orthonormal ℂ Φ →
                (∀ j, toEuclideanLin P (Φ j) = Φ j) → n ≤ 2 := by
  obtain ⟨c₁, η, C, hc₁, hη, hC, hdata⟩ :=
    exists_periodic_gapped_truncation_data hR hJ hΔ
  refine ⟨c₁, η, C, hc₁, hη, hC, ?_⟩
  intro M d hM g hg hsupp hnorm Ω E₀ hgs Jb ℓ r a P b h K
  have hJb : 0 < Jb := mul_pos (by norm_num) (hJ.trans_le (le_max_left _ _))
  obtain ⟨hℓ, hℓR⟩ := physicalPeriodicProjectionRadius_spec R M Jb Δ hη
  have hr := hierarchyProjectionLength_le_physicalPeriodicProjectionRadius hM R Jb Δ hη
  have ha (i : Fin M) := hdata hM g hg hsupp hnorm Ω E₀ hgs ℓ hℓR i
  have haSupp (i : Fin M) : a i ∈ supportedOperators d {v | roundedPeriodicDistance i v ≤ ℓ} :=
    (ha i).1
  have haHerm (i : Fin M) : (a i).IsHermitian := (ha i).2.1
  have haNorm (i : Fin M) : ‖a i‖ ≤ Jb := (ha i).2.2.1
  have haError (i : Fin M) :
      ‖gaussianFilteredTerm (c₁ * (ℓ : ℝ) * Δ) Δ (∑ j, g j) (g i) - a i‖ ≤
        Jb * Real.exp (-r) := (ha i).2.2.2.1
  obtain ⟨φ, hφ, hkeep, hnear, htree⟩ := exists_unit_mem_roundedPeriodicProjection hℓ a
    haSupp haHerm hgs.1 hJb hr (fun i ↦ (ha i).2.2.2.2) haNorm
  refine ⟨φ, hφ, hkeep, hnear, htree, ?_⟩
  let P₀ := vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))
  have hP₀ : IsStarProjection P₀ := by
    have heq : Matrix.toEuclideanCLM (n := Fin M → Fin d) (𝕜 := ℂ) P₀ =
        InnerProductSpace.rankOne ℂ Ω Ω := by
      apply ContinuousLinearMap.ext
      intro v
      change toEuclideanLin P₀ v = ⟪Ω, v⟫_ℂ • Ω
      exact toEuclideanLin_vecMulVec_star_self_apply Ω v
    have h := (InnerProductSpace.isStarProjection_rankOne_self (𝕜 := ℂ) hgs.1).map
      (Matrix.toEuclideanCLM (n := Fin M → Fin d) (𝕜 := ℂ)).symm.toStarAlgHom
    rw [← heq] at h
    change IsStarProjection ((Matrix.toEuclideanCLM (n := Fin M → Fin d) (𝕜 := ℂ)).symm
      (Matrix.toEuclideanCLM (n := Fin M → Fin d) (𝕜 := ℂ) P₀)) at h
    simpa only [StarAlgEquiv.symm_apply_apply] using h
  have hgap (v : EuclideanSpace ℂ (Fin M → Fin d)) :
      Δ * (‖v‖ ^ 2 - (⟪v, toEuclideanLin P₀ v⟫_ℂ).re) ≤
        (⟪v, toEuclideanLin (∑ i, g i) v⟫_ℂ).re - E₀ * ‖v‖ ^ 2 := by
    have hinner : (⟪v, toEuclideanLin P₀ v⟫_ℂ).re = ‖⟪Ω, v⟫_ℂ‖ ^ 2 := by
      change (⟪v, toEuclideanLin
        (vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) v⟫_ℂ).re = _
      rw [toEuclideanLin_vecMulVec_star_self_apply, inner_smul_right,
        ← inner_conj_symm v Ω, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
    simpa only [hinner] using hgs.2.2.gap_le v
  have hE₀ : (⟪Ω, toEuclideanLin (∑ i, g i) Ω⟫_ℂ).re = E₀ := by
    have heigen : toEuclideanLin (∑ i, g i) Ω = (E₀ : ℂ) • Ω := hgs.2.1
    rw [heigen, inner_smul_right, inner_self_eq_norm_sq_to_K, hgs.1]
    simp
  have htrace : (trace P₀).re = 1 := by
    change (trace (vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).re = 1
    rw [trace_vecMulVec, ← EuclideanSpace.inner_eq_star_dotProduct]
    rw [inner_self_eq_norm_sq_to_K, hgs.1]
    norm_num
  intro n Φ hΦ hfix
  have hc := card_le_two_mul_re_trace_of_roundedPeriodicProjection hℓ a g haSupp haHerm hg hgs.1
    hJb hη hΔ rfl hr haError hP₀ hgap hE₀ hΦ Finset.univ (fun j _ ↦ hfix j)
  have hc' : (n : ℝ) ≤ 2 := by simpa [htrace] using hc
  exact_mod_cast hc'

end TNLean.MPS.AreaLaw.LocalSolution
