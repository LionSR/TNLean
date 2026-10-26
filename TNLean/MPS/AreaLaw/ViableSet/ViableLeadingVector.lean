/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.GluingHamiltonian
import TNLean.MPS.AreaLaw.ViableSet.ViableTrimmedWitness
import QICLean.Channel.BoundaryDensityMinimizer

/-!
# A minimizing boundary state and its leading vector

A viable set supplies a low-energy trimmed witness and an isometry on its actual right
Schmidt space. Every boundary point close to this witness admits a density matrix minimizing
the left energy under the boundary and support constraints. Its eigenvector of eigenvalue
larger than one half extends to a unit chain vector in the viable span, with energy at most
`E₀ + Δ/12` and ground-state overlap at least `11/12`.

Source: Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`, equation `eq:conv`,
lines 472–476, and Lemma `l:leading`, lines 493–505, using Lemma `l:within`, lines 509–515.

**Scope restriction (nontrivial chains and bond bound):** The theorem assumes `0 < L` and
`2 ≤ q` and uses the library bound `constantCutBond q 1 1 Δ c`. Its dependence on dimension
and gap is documented in `docs/paper-gaps/lvv13_constant_bond.tex`; the source's quantitative
AKLV bound remains separate. The theorem concerns a point close to the actual boundary
state, without a finite-net or viable-set cardinality assertion.
-/

open Matrix
open scoped InnerProductSpace ComplexOrder Kronecker Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

variable {L q k : ℕ}

/-- The left support condition of LVV13, `algo53.tex`, lines 493–505, read from the
three-way cut coordinates back on the chain. -/
private theorem mem_leftSupportSubmodule_of_gluingCut_fixed
    (S : Set (LeftBlockVector L q k))
    (y : (CutLeft L q k × CutSite L q k) × CutRight L q k → ℂ)
    (hy : (reindex
        (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
        (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
        (spanProjection S) ⊗ₖ (1 : Matrix (CutRight L q k) (CutRight L q k) ℂ)) *ᵥ y = y) :
    WithLp.toLp 2 (y ∘ gluingCut L q k) ∈ leftSupportSubmodule S := by
  classical
  let e := Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (L := L) (Nat.sub_le k 1))
  let P := reindex e e (spanProjection S)
  let Y := Matrix.schmidtCoeffMatrix y
  have hleft : leftApply P (WithLp.toLp 2 y) = WithLp.toLp 2 y := by
    rw [← toEuclideanLin_kronecker_one_apply]
    apply WithLp.ofLp_injective 2
    simpa only [toLpLin_apply, WithLp.ofLp_toLp] using hy
  have hPY : P * Y = Y := by
    have h := congrArg (fun z ↦ schmidtCoeffMatrix (WithLp.ofLp z)) hleft
    simpa only [schmidtCoeffMatrix_ofLp_leftApply] using h
  have hcm : cutMatrix (WithLp.toLp 2 (y ∘ gluingCut L q k)) k = Y.submatrix e id := by
    ext p r
    rw [cutMatrix, Matrix.schmidtCoeffMatrix_apply]
    change y (gluingCut L q k ((Entropy.cutEquiv (fun _ : Fin L ↦ q)
      (leftBlock L k)).symm (p, r))) = y (e p, r)
    rw [gluingCut, Entropy.threeCutEquiv_eq_trans]
    simp [e]
  apply (spanProjection_mul_cutMatrix_eq_iff (S := S)).mp
  rw [hcm]
  have hP : P.submatrix e e = spanProjection S := by
    ext a b
    simp [P]
  have h := congrArg (fun M ↦ M.submatrix e id) hPY
  rw [← Matrix.submatrix_mul_equiv P Y e e id, hP] at h
  exact h

/-- A viable set supplies the feasible witness, a minimizing boundary state, and a dominant
low-energy vector. This is the library-bond form of LVV13, `algo53.tex`, equation `eq:conv`,
lines 472–476, and Lemma `l:leading`, lines 493–505. The boundary point is chosen after the
witness's actual bond space; no optimizer or witness energy bound is assumed. -/
theorem ChainHamiltonian.exists_boundary_minimizer_leading_vector_of_isViable
    (h : ChainHamiltonian L q 1 1) (hpos : ∀ X, (h.term X).PosSemidef)
    (hL : 0 < L) (hq : 2 ≤ q) {E₀ Δ : ℝ} (hΔ : 0 < Δ)
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
    ∃ (HL B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
      (w : EuclideanSpace ℂ (Fin L → Fin q)) (m : ℕ)
      (W : Matrix (CutRight L q k) (Fin m) ℂ)
      (x : (CutLeft L q k × CutSite L q k) × Fin m → ℂ),
      h.operator = HL + B ∧
      Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) HL (leftBlock L k) ∧
      Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) B (leftBlock L (k - 1))ᶜ ∧
      ‖B‖ ≤ 2 * L ∧ ‖w‖ = 1 ∧ w ∈ leftSupportSubmodule S ∧
      (cutMatrix w k).rank ≤ D ∧
      (⟪w, toEuclideanLin h.operator w⟫_ℂ).re ≤ E₀ + 6 * √c ∧
      Wᴴ * W = 1 ∧ m ≤ D ∧
      WithLp.ofLp w ∘ (gluingCut L q k).symm =
        ((1 : Matrix (CutLeft L q k × CutSite L q k)
          (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ x ∧
      ‖WithLp.toLp 2 x‖ = 1 ∧ (P ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) *ᵥ x = x ∧
      ∀ X : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ,
        rectangularTraceNorm (partialTraceFirst (vecMulVec x (star x)) - X) ≤ c / (2 * L) →
        ∃ (σ : Matrix ((CutLeft L q k × CutSite L q k) × Fin m)
            ((CutLeft L q k × CutSite L q k) × Fin m) ℂ)
          (u : EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m)) (μ : ℝ),
          let v : EuclideanSpace ℂ (Fin L → Fin q) := WithLp.toLp 2
            ((((1 : Matrix (CutLeft L q k × CutSite L q k)
              (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) ∘ gluingCut L q k)
          σ.PosSemidef ∧ σ.trace = 1 ∧
          (P ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * σ = σ ∧
          rectangularTraceNorm (partialTraceFirst σ - X) ≤ c / (2 * L) ∧
          (∀ ρ : Matrix ((CutLeft L q k × CutSite L q k) × Fin m)
              ((CutLeft L q k × CutSite L q k) × Fin m) ℂ,
            ρ.PosSemidef → ρ.trace = 1 →
            (P ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * ρ = ρ →
            rectangularTraceNorm (partialTraceFirst ρ - X) ≤ c / (2 * L) →
            (σ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re ≤
              (ρ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re) ∧
          ‖u‖ = 1 ∧ σ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u ∧ 1 / 2 < μ ∧
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
  obtain ⟨w, m, W, x, hw, hwS, hwD, hwE, hW, hmD, hwx, hxP⟩ :=
    h.exists_trimmed_witness_of_isViable hpos hL hq hΔ hgs hviable
  change (cutMatrix w k).rank ≤ D at hwD
  change m ≤ D at hmD
  obtain ⟨HL, B, hsplit, hHL, hBS, hBn⟩ := h.exists_gluing_decomposition_of_range_one k
  have hblock (i : ℕ) : interval L 0 i = leftBlock L i := by
    ext j
    simp [interval, leftBlock]
  rw [hblock k] at hHL
  rw [hblock (k - 1)] at hBS
  let J := (1 : Matrix (CutLeft L q k × CutSite L q k)
    (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W
  have hJ : Jᴴ * J = 1 := by
    simp only [J, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
      Matrix.one_mul, hW, one_kronecker_one]
  have hcoord : ‖WithLp.toLp 2 (WithLp.ofLp w ∘ (gluingCut L q k).symm)‖ = ‖w‖ := by
    have heq : (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (gluingCut L q k)) w =
        WithLp.toLp 2 (WithLp.ofLp w ∘ (gluingCut L q k).symm) := by
      ext i
      rfl
    rw [← heq]
    exact (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (gluingCut L q k)).norm_map w
  have hxnorm : ‖WithLp.toLp 2 x‖ = 1 := by
    have hn := norm_toLp_mulVec_of_isometry J hJ (WithLp.toLp 2 x)
    change ‖WithLp.toLp 2 (J *ᵥ x)‖ = ‖WithLp.toLp 2 x‖ at hn
    rw [← hwx] at hn
    exact hn.symm.trans (hcoord.trans hw)
  refine ⟨HL, B, w, m, W, x, hsplit, hHL, hBS, hBn, hw, hwS, hwD, hwE, hW, hmD,
    hwx, hxnorm, hxP, ?_⟩
  intro X hX
  let η := c / (2 * L)
  obtain ⟨σ, hσ, htr, hσP, hσX, hmin, hopt, hτ⟩ :=
    Matrix.exists_boundary_density_minimizer P (leftCutOperator k HL) X η
      (WithLp.toLp 2 x) hxnorm hxP hX
  have hΔ4 : Δ ≤ 4 := by
    simpa only [mul_one] using h.gap_le_four_mul_of_range_one hL hq hgs
  obtain ⟨hc0, hc, -, hnum, -⟩ := lvv_trimming_constant_bounds hΔ hΔ4
  change 0 < c at hc0
  change c ≤ 1 / 1600 at hc
  change 14 * √c / Δ < 1 / 12 at hnum
  have hcr : 2 * c ≤ √c := by
    have hr0 := Real.sqrt_nonneg c
    have hr2 := Real.sq_sqrt hc0.le
    have hr : √c ≤ 1 / 2 := by nlinarith only [hr0, hr2, hc]
    nlinarith only [hr2, mul_nonneg hr0 (sub_nonneg.mpr hr)]
  have hL0 : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hL.ne'
  have hηeq : 2 * η = c / L := by
    dsimp only [η]
    field_simp [hL0]
  have hBτ : ‖B‖ * (2 * η) ≤ 2 * c := by
    rw [hηeq]
    calc
      ‖B‖ * (c / L) ≤ (2 * L) * (c / L) :=
        mul_le_mul_of_nonneg_right hBn (div_nonneg hc0.le (Nat.cast_nonneg _))
      _ = 2 * c := by field_simp [hL0]
  have htwo : 2 * (6 * √c + ‖B‖ * (2 * η)) ≤ 14 * √c := by
    nlinarith only [hBτ, hcr]
  have hgood : 14 * √c < Δ / 12 := by
    have hh := (div_lt_iff₀ hΔ).mp hnum
    nlinarith only [hh]
  have h4 : 4 * (6 * √c + ‖B‖ * (2 * η)) < Δ := by
    nlinarith only [htwo, hgood, hΔ]
  have hgs' : IsGappedGroundState (HL + B) E₀ Γ Δ := by
    rw [← hsplit]
    exact hgs
  have hwE' : (⟪w, toEuclideanLin (HL + B) w⟫_ℂ).re ≤ E₀ + 6 * √c := by
    rw [← hsplit]
    exact hwE
  obtain ⟨u, μ, hu, hueig, hμ, huE, huov⟩ :=
    exists_leading_eigenvector_chain (L := L) (q := q) (k := k) (e := 6 * √c) (τ := 2 * η)
      hHL hBS disjoint_compl_left hΔ hgs' W hW x hwx hwE' hσ htr hopt hτ h4
  have hμ0 : (μ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith only [hμ])
  have hQu : (P ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) *ᵥ WithLp.ofLp u =
      WithLp.ofLp u := by
    have heig : (μ : ℂ) •
        ((P ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) *ᵥ WithLp.ofLp u) =
        (μ : ℂ) • WithLp.ofLp u := by
      rw [← mulVec_smul, ← hueig, mulVec_mulVec, hσP, hueig]
    have hh := congrArg (fun z ↦ (μ : ℂ)⁻¹ • z) heig
    simpa only [smul_smul, inv_mul_cancel₀ hμ0, one_smul] using hh
  let v := WithLp.toLp 2 ((J *ᵥ WithLp.ofLp u) ∘ gluingCut L q k)
  have hv : ‖v‖ = 1 := by
    have heq : (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (gluingCut L q k).symm)
        (WithLp.toLp 2 (J *ᵥ WithLp.ofLp u)) = v := by
      ext i
      rfl
    rw [← heq, LinearIsometryEquiv.norm_map]
    exact (norm_toLp_mulVec_of_isometry J hJ u).trans hu
  have hinter : (P ⊗ₖ (1 : Matrix (CutRight L q k) (CutRight L q k) ℂ)) * J =
      J * (P ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) := by
    simp only [J, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  have hvP : (P ⊗ₖ (1 : Matrix (CutRight L q k) (CutRight L q k) ℂ)) *ᵥ
      (J *ᵥ WithLp.ofLp u) = J *ᵥ WithLp.ofLp u := by
    rw [mulVec_mulVec, hinter, ← mulVec_mulVec, hQu]
  have hvS : v ∈ leftSupportSubmodule S :=
    mem_leftSupportSubmodule_of_gluingCut_fixed S (J *ᵥ WithLp.ofLp u) hvP
  refine ⟨σ, u, μ, hσ, htr, hσP, hσX, hmin, hu, hueig, hμ, hQu, hv, hvS, ?_, ?_⟩
  · rw [← hsplit] at huE
    exact huE.trans (add_le_add le_rfl (htwo.trans hgood.le))
  · have herr : 2 * (6 * √c + ‖B‖ * (2 * η)) / Δ ≤ 1 / 12 := by
      apply (div_le_iff₀ hΔ).mpr
      nlinarith only [htwo, hgood]
    linarith only [huov, herr]

end TNLean.MPS.AreaLaw
