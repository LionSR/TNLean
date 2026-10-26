/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.ViableLeadingVector
import TNLean.MPS.AreaLaw.ViableSet.GluingBounds

/-!
# Every minimizing boundary state and its top eigenvector

Fix a supported decomposition of the Hamiltonian before choosing the ground vector.
Viability then supplies witness data for which the energy and overlap bounds hold for every
feasible global minimizer of the left energy and every unit eigenvector associated with its
largest eigenvalue.

Source: Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`, equation `eq:conv`,
lines 472–476, Lemma `l:leading`, lines 493–505, and Lemma `l:within`, lines 509–515.

**Scope restriction (nontrivial chains and bond bound):** The theorem assumes `0 < L` and
`2 ≤ q` and uses the library bound `constantCutBond q 1 1 Δ c`, rather than the quantitative
AKLV bound; see `docs/paper-gaps/lvv13_constant_bond.tex`. Boundary points are quantified on
the actual bond space. No finite-net cardinality assertion is made.
-/

open Matrix
open scoped InnerProductSpace ComplexOrder Kronecker Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

variable {L q k : ℕ}

/-- Viability supplies cut data valid for every feasible global minimizer and every unit top
eigenvector. Auxiliary library-bond form of LVV13, `algo53.tex`, equation `eq:conv`,
lines 472–476, Lemma `l:leading`, lines 493–505, and Lemma `l:within`, lines 509–515. -/
theorem ChainHamiltonian.exists_uniform_leading_bounds_of_isViable
    (h : ChainHamiltonian L q 1 1) (hpos : ∀ X, (h.term X).PosSemidef)
    (hL : 0 < L) (hq : 2 ≤ q) {E₀ Δ : ℝ} (hΔ : 0 < Δ)
    (HL B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hsplit : h.operator = HL + B)
    (hHL : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) HL (leftBlock L k))
    (hBS : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) B (leftBlock L (k - 1))ᶜ)
    (hBn : ‖B‖ ≤ 2 * L)
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : IsGappedGroundState h.operator E₀ Γ Δ)
    {S : Set (LeftBlockVector L q k)}
    (hviable : IsViable Γ (((Δ / 169) ^ 2) / L) S) :
    let : NeZero q := ⟨by omega⟩
    let c : ℝ := (Δ / 169) ^ 2
    let D := constantCutBond q 1 1 Δ c
    let P := reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection S)
    ∃ (w : EuclideanSpace ℂ (Fin L → Fin q)) (m : ℕ)
      (W : Matrix (CutRight L q k) (Fin m) ℂ)
      (x : (CutLeft L q k × CutSite L q k) × Fin m → ℂ),
      ‖w‖ = 1 ∧ w ∈ leftSupportSubmodule S ∧
      (cutMatrix w k).rank ≤ D ∧
      (⟪w, toEuclideanLin h.operator w⟫_ℂ).re ≤ E₀ + 6 * √c ∧
      Wᴴ * W = 1 ∧ m ≤ D ∧
      WithLp.ofLp w ∘ (gluingCut L q k).symm =
        ((1 : Matrix (CutLeft L q k × CutSite L q k)
          (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ x ∧
      ‖WithLp.toLp 2 x‖ = 1 ∧ (P ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) *ᵥ x = x ∧
      ∀ X : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ,
        rectangularTraceNorm (partialTraceFirst (vecMulVec x (star x)) - X) ≤ c / (2 * L) →
        ∀ σ : Matrix ((CutLeft L q k × CutSite L q k) × Fin m)
            ((CutLeft L q k × CutSite L q k) × Fin m) ℂ,
          σ.PosSemidef → σ.trace = 1 →
          (P ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * σ = σ →
          rectangularTraceNorm (partialTraceFirst σ - X) ≤ c / (2 * L) →
          (∀ ρ : Matrix ((CutLeft L q k × CutSite L q k) × Fin m)
              ((CutLeft L q k × CutSite L q k) × Fin m) ℂ,
            ρ.PosSemidef → ρ.trace = 1 →
            (P ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * ρ = ρ →
            rectangularTraceNorm (partialTraceFirst ρ - X) ≤ c / (2 * L) →
            (σ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re ≤
              (ρ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re) →
          ∀ (u : EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m)) (μ : ℝ),
            ‖u‖ = 1 → σ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u →
            (∀ (ν : ℝ) (z : EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m)),
              z ≠ 0 → σ *ᵥ WithLp.ofLp z = (ν : ℂ) • WithLp.ofLp z → ν ≤ μ) →
            let v : EuclideanSpace ℂ (Fin L → Fin q) := WithLp.toLp 2
              ((((1 : Matrix (CutLeft L q k × CutSite L q k)
                (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) ∘ gluingCut L q k)
            1 / 2 < μ ∧
            (P ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) *ᵥ WithLp.ofLp u = WithLp.ofLp u ∧
            ‖v‖ = 1 ∧ v ∈ leftSupportSubmodule S ∧
            (⟪v, toEuclideanLin h.operator v⟫_ℂ).re ≤ E₀ + Δ / 12 ∧
            1 - 1 / 12 ≤ ‖⟪Γ, v⟫_ℂ‖ := by
  classical
  let : NeZero q := ⟨by omega⟩
  let c : ℝ := (Δ / 169) ^ 2
  let D := constantCutBond q 1 1 Δ c
  let P := reindex
    (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
    (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
    (spanProjection S)
  obtain ⟨_, _, w, m, W, x, -, -, -, -, hw, hwS, hwD, hwE, hW, hmD,
      hwx, hxnorm, hxP, -⟩ :=
    h.exists_boundary_minimizer_leading_vector_of_isViable hpos hL hq hΔ hgs hviable
  refine ⟨w, m, W, x, hw, hwS, hwD, hwE, hW, hmD,
    hwx, hxnorm, hxP, ?_⟩
  intro X hX σ hσ htr hσP hσX hmin u μ hu huσ hmax
  let ρx := vecMulVec x (star x)
  have hρxp : ρx.PosSemidef := posSemidef_vecMulVec_self_star x
  have hρxt : ρx.trace = 1 := by
    change (vecMulVec (WithLp.ofLp (WithLp.toLp 2 x))
      (star (WithLp.ofLp (WithLp.toLp 2 x)))).trace = 1
    rw [trace_vecMulVec, ← EuclideanSpace.inner_eq_star_dotProduct,
      inner_self_eq_norm_sq_to_K, hxnorm]
    norm_num
  have hρxP : (P ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * ρx = ρx := by
    dsimp only [ρx]
    rw [mul_vecMulVec, hxP]
  have hopt := hmin ρx hρxp hρxt hρxP hX
  let η := c / (2 * L)
  change rectangularTraceNorm (partialTraceFirst ρx - X) ≤ η at hX
  change rectangularTraceNorm (partialTraceFirst σ - X) ≤ η at hσX
  have hneg : rectangularTraceNorm (X - partialTraceFirst ρx) =
      rectangularTraceNorm (partialTraceFirst ρx - X) := by
    rw [show X - partialTraceFirst ρx = (-1 : ℂ) • (partialTraceFirst ρx - X) by
      simp, rectangularTraceNorm_smul]
    norm_num
  have hτ : rectangularTraceNorm (partialTraceFirst σ - partialTraceFirst ρx) ≤ 2 * η := by
    calc
      rectangularTraceNorm (partialTraceFirst σ - partialTraceFirst ρx) =
          rectangularTraceNorm ((partialTraceFirst σ - X) + (X - partialTraceFirst ρx)) := by
            rw [sub_add_sub_cancel]
      _ ≤ rectangularTraceNorm (partialTraceFirst σ - X) +
          rectangularTraceNorm (X - partialTraceFirst ρx) := rectangularTraceNorm_add_le _ _
      _ ≤ 2 * η := by rw [hneg]; linarith only [hσX, hX]
  have hΔ4 : Δ ≤ 4 := by
    simpa only [mul_one] using h.gap_le_four_mul_of_range_one hL hq hgs
  have hsqrt : √c = Δ / 169 := Real.sqrt_sq (div_nonneg hΔ.le (by norm_num))
  have hcr : 2 * c ≤ √c := by
    rw [hsqrt]
    dsimp only [c]
    nlinarith only [mul_nonneg hΔ.le (sub_nonneg.mpr hΔ4), hΔ]
  have hL0 : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hL.ne'
  have hηeq : 2 * η = c / L := by dsimp only [η]; field_simp [hL0]
  have hBτ : ‖B‖ * (2 * η) ≤ 2 * c := by
    rw [hηeq]
    calc
      ‖B‖ * (c / L) ≤ (2 * L) * (c / L) :=
        mul_le_mul_of_nonneg_right hBn (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
      _ = 2 * c := by field_simp [hL0]
  have htwo : 2 * (6 * √c + ‖B‖ * (2 * η)) ≤ 14 * √c := by
    linarith only [hBτ, hcr]
  have hgood : 14 * √c < Δ / 12 := by rw [hsqrt]; linarith only [hΔ]
  have h4 : 4 * (6 * √c + ‖B‖ * (2 * η)) < Δ := by
    linarith only [htwo, hgood, hΔ]
  have hgs' : IsGappedGroundState (HL + B) E₀ Γ Δ := by rw [← hsplit]; exact hgs
  have hwE' : (⟪w, toEuclideanLin (HL + B) w⟫_ℂ).re ≤ E₀ + 6 * √c := by
    rw [← hsplit]
    exact hwE
  obtain ⟨u₀, ν, hu₀, hu₀σ, hν, -, -⟩ :=
    exists_leading_eigenvector_chain (L := L) (q := q) (k := k) (e := 6 * √c) (τ := 2 * η)
      hHL hBS disjoint_compl_left hΔ hgs' W hW x hwx hwE' hσ htr hopt hτ h4
  have hu₀0 : u₀ ≠ 0 := by
    intro hz
    simp only [hz, norm_zero, zero_ne_one] at hu₀
  have hμ : 1 / 2 < μ := hν.trans_le (hmax ν u₀ hu₀0 hu₀σ)
  obtain ⟨huE, huov⟩ :=
    leading_eigenvector_bounds_chain (L := L) (q := q) (k := k) (e := 6 * √c) (τ := 2 * η)
      hHL hBS disjoint_compl_left hΔ hgs' W hW x hwx hwE' hσ htr hopt hτ h4 u μ hu huσ hμ
  have hμ0 : (μ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith only [hμ])
  have hQu : (P ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) *ᵥ WithLp.ofLp u =
      WithLp.ofLp u := by
    apply smul_right_injective _ hμ0
    simpa only [← mulVec_mulVec, huσ, mulVec_smul] using
      congrArg (fun A ↦ A *ᵥ WithLp.ofLp u) hσP
  let J := (1 : Matrix (CutLeft L q k × CutSite L q k)
    (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W
  have hJ : Jᴴ * J = 1 := by
    simp only [J, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
      Matrix.one_mul, hW, one_kronecker_one]
  let v := WithLp.toLp 2 ((J *ᵥ WithLp.ofLp u) ∘ gluingCut L q k)
  have hv : ‖v‖ = 1 :=
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (gluingCut L q k).symm).norm_map
      (WithLp.toLp 2 (J *ᵥ WithLp.ofLp u))).trans
        ((norm_toLp_mulVec_of_isometry J hJ u).trans hu)
  have hinter : (P ⊗ₖ (1 : Matrix (CutRight L q k) (CutRight L q k) ℂ)) * J =
      J * (P ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) := by
    simp only [J, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  have hvP : (P ⊗ₖ (1 : Matrix (CutRight L q k) (CutRight L q k) ℂ)) *ᵥ
      (J *ᵥ WithLp.ofLp u) = J *ᵥ WithLp.ofLp u := by
    rw [mulVec_mulVec, hinter, ← mulVec_mulVec, hQu]
  have hvS : v ∈ leftSupportSubmodule S :=
    mem_leftSupportSubmodule_of_gluingCut_fixed S (J *ᵥ WithLp.ofLp u) hvP
  refine ⟨hμ, hQu, hv, hvS, ?_, ?_⟩
  · rw [← hsplit] at huE
    exact huE.trans (add_le_add le_rfl (htwo.trans hgood.le))
  · have herr : 2 * (6 * √c + ‖B‖ * (2 * η)) / Δ ≤ 1 / 12 := by
      apply (div_le_iff₀ hΔ).mpr
      linarith only [htwo, hgood]
    linarith only [huov, herr]

end TNLean.MPS.AreaLaw
