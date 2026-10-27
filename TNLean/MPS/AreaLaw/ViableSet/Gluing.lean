/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.OpenMPS
import TNLean.Algebra.GappedGroundState
import QICLean.Channel.LeadingEigenvector
import QICLean.Entropy.ThreeWayCut
import QICLean.Entropy.RegionSplit
import QICLean.Analysis.RectangularTraceNormAlgebra

/-!
# Gluing a left state at a cut of the chain

Fix the cut after `k` sites of a chain of `L` sites. In the coordinates of the three-way cut
`A = leftBlock L (k - 1)`, `B = leftBlock L k`, a configuration is `((x, y), z)` with `x` on the
first `k - 1` sites, `y` on site `k - 1` and `z` on the remaining sites. A Hamiltonian
`H = H_L + K` with `H_L` supported on the first `k` sites and `K` supported off the first
`k - 1` sites is then `H_L' ⊗ 1 + 1 ⊗ K'`, the setting of the gluing lemma of Landau, Vazirani
and Vidick.

This file states Lemma `l:leading` on the chain: if a vector `w = (1 ⊗ W) x` has energy at most
`E₀ + e` and a density matrix `σ` on the left sites and the bond has left energy at most that of
`x` and boundary contraction within `τ` of that of `x`, then `σ` has a leading eigenvector `u`
whose extension `(1 ⊗ W) u`, read back on the chain, has energy at most `E₀ + 2 (e + ‖K‖ τ)` and
overlap at least `1 - 2 (e + ‖K‖ τ)/Δ` with the ground state.

## Main definitions

* `TNLean.MPS.AreaLaw.CutLeft`, `TNLean.MPS.AreaLaw.CutSite`,
  `TNLean.MPS.AreaLaw.CutRight`: configurations on the first `k - 1` sites, the intervening
  site when present, and the sites right of the cut, respectively.
* `TNLean.MPS.AreaLaw.gluingCut`: the three-way cut coordinates at the cut after `k` sites.
* `TNLean.MPS.AreaLaw.leftCutOperator`: the operator `H_L'` on the first `k` sites of a matrix
  supported there.
* `TNLean.MPS.AreaLaw.rightCutOperator`: the restriction of a matrix supported off the first
  `k - 1` sites to the intervening site, when present, and the sites right of the cut.

## Main results

* `TNLean.MPS.AreaLaw.reindex_gluingCut_eq`: `H_L + K` in the cut coordinates.
* `TNLean.MPS.AreaLaw.exists_leading_eigenvector_chain`: Lemma `l:leading` on the chain.

## References

* Z. Landau, U. Vazirani, T. Vidick, *A polynomial-time algorithm for the ground state of 1D
  gapped local Hamiltonians*, arXiv:1307.5143v1, `References/1307.5143/algo53.tex`: boundary
  contractions, lines 409–417; Lemma `l:gluing`, lines 421–447; Lemma `l:leading`,
  lines 493–505.
-/

open Matrix
open scoped Matrix Kronecker Matrix.Norms.L2Operator ComplexOrder InnerProductSpace

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ}

/-- The configurations of the first `k - 1` sites. -/
abbrev CutLeft (L q k : ℕ) := (v : {v // v ∈ leftBlock L (k - 1)}) → Fin q

/-- The configurations of site `k - 1`, the last site left of the cut. -/
abbrev CutSite (L q k : ℕ) := (v : {v // v ∈ leftBlock L k \ leftBlock L (k - 1)}) → Fin q

/-- The configurations of the sites right of the cut. -/
abbrev CutRight (L q k : ℕ) := (v : {v // v ∉ leftBlock L k}) → Fin q

/-- The three-way cut coordinates `((x, y), z)` at the cut after `k` sites. -/
abbrev gluingCut (L q k : ℕ) :
    (Fin L → Fin q) ≃ (CutLeft L q k × CutSite L q k) × CutRight L q k :=
  Entropy.threeCutEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1))

/-- The operator on the first `k` sites of a matrix supported there: its slice at the
configuration `0` of the remaining sites. -/
noncomputable def leftCutOperator [NeZero q] (k : ℕ)
    (X : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) :
    Matrix (CutLeft L q k × CutSite L q k) (CutLeft L q k × CutSite L q k) ℂ :=
  fun p p' ↦ reindex (gluingCut L q k) (gluingCut L q k) X (p, fun _ ↦ 0) (p', fun _ ↦ 0)

/-- The operator on site `k - 1` and the right of the cut of a matrix supported off the first
`k - 1` sites: its slice at the configuration `0` of the first `k - 1` sites. -/
noncomputable def rightCutOperator [NeZero q] (k : ℕ)
    (X : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) :
    Matrix (CutSite L q k × CutRight L q k) (CutSite L q k × CutRight L q k) ℂ :=
  fun r r' ↦ reindex (gluingCut L q k) (gluingCut L q k) X ((fun _ ↦ 0, r.1), r.2)
    ((fun _ ↦ 0, r'.1), r'.2)

/-- **`H_L + K` in the cut coordinates.** If `H_L` is supported on the first `k` sites and `K` is
supported off the first `k - 1` sites, then in the three-way cut coordinates
`H_L + K = H_L' ⊗ 1 + 1 ⊗ K'`. -/
theorem reindex_gluingCut_eq [NeZero q] {k : ℕ} {HL K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
    (hHL : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) HL (leftBlock L k)) {D : Finset (Fin L)}
    (hK : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) K D)
    (hDA : Disjoint D (leftBlock L (k - 1))) :
    reindex (gluingCut L q k) (gluingCut L q k) (HL + K) =
      leftCutOperator k HL ⊗ₖ (1 : Matrix (CutRight L q k) (CutRight L q k) ℂ) +
        reindex (Equiv.prodAssoc _ _ _).symm (Equiv.prodAssoc _ _ _).symm
          ((1 : Matrix (CutLeft L q k) (CutLeft L q k) ℂ) ⊗ₖ rightCutOperator k K) := by
  rw [show reindex (gluingCut L q k) (gluingCut L q k) (HL + K) =
      reindex (gluingCut L q k) (gluingCut L q k) HL +
        reindex (gluingCut L q k) (gluingCut L q k) K from by
    simp [reindex_apply, submatrix_add]]
  rw [hHL.reindex_threeCutEquiv_eq_kronecker_one _ subset_rfl (fun _ ↦ 0),
    hK.reindex_threeCutEquiv_eq_one_kronecker _ hDA (fun _ ↦ 0)]
  rfl

/-- Expectations are invariant under a change of coordinates. -/
private theorem inner_toEuclideanLin_reindex {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (e : X ≃ Y) (M : Matrix X X ℂ) (ψ : EuclideanSpace ℂ X) :
    ⟪WithLp.toLp 2 (WithLp.ofLp ψ ∘ e.symm),
        toEuclideanLin (reindex e e M) (WithLp.toLp 2 (WithLp.ofLp ψ ∘ e.symm))⟫_ℂ =
      ⟪ψ, toEuclideanLin M ψ⟫_ℂ := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, toLpLin_apply, reindex_apply]
  rw [dotProduct_comm, dotProduct_comm (M *ᵥ _)]
  exact Entropy.star_dotProduct_submatrix_mulVec e M (WithLp.ofLp ψ)

/-- Inner products are invariant under a change of coordinates. -/
private theorem inner_comp_symm {X Y : Type*} [Fintype X] [Fintype Y] (e : X ≃ Y)
    (φ ψ : EuclideanSpace ℂ X) :
    ⟪WithLp.toLp 2 (WithLp.ofLp φ ∘ e.symm), WithLp.toLp 2 (WithLp.ofLp ψ ∘ e.symm)⟫_ℂ =
      ⟪φ, ψ⟫_ℂ := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Function.comp_apply,
    Pi.star_apply]
  exact Fintype.sum_equiv e.symm _ _ fun _ ↦ rfl

/-- `‖K‖ ≤ ‖1 ⊗ K‖` when the first factor is nonempty: `K` is a corner of `1 ⊗ K`. -/
private theorem l2_opNorm_le_one_kronecker {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (x₀ : X) (K : Matrix Y Y ℂ) :
    ‖K‖ ≤ ‖(1 : Matrix X X ℂ) ⊗ₖ K‖ := by
  set V := Matrix.basisRegisterInjection (a := Y) x₀
  have hV : Vᴴ * V = 1 := Matrix.basisRegisterInjection_conjTranspose_mul_self x₀
  have hKV : (1 : Matrix X X ℂ) ⊗ₖ K * V = V * K := by
    ext ⟨x, i⟩ j
    simp [V, Matrix.basisRegisterInjection, Matrix.mul_apply, Fintype.sum_prod_type,
      one_apply]
  have hK : K = Vᴴ * ((1 : Matrix X X ℂ) ⊗ₖ K) * V := by
    rw [Matrix.mul_assoc, hKV, ← Matrix.mul_assoc, hV, Matrix.one_mul]
  have hVn : ‖V‖ ≤ 1 := l2_opNorm_le_one_of_conjTranspose_mul_self_eq_one hV
  have hVhn : ‖Vᴴ‖ ≤ 1 := by rwa [l2_opNorm_conjTranspose]
  calc ‖K‖ = ‖Vᴴ * ((1 : Matrix X X ℂ) ⊗ₖ K) * V‖ := by rw [← hK]
    _ ≤ ‖Vᴴ‖ * ‖(1 : Matrix X X ℂ) ⊗ₖ K‖ * ‖V‖ :=
        (l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _)
          (norm_nonneg _))
    _ ≤ 1 * ‖(1 : Matrix X X ℂ) ⊗ₖ K‖ * 1 := by gcongr
    _ = _ := by ring

/-- The energy of a rank-one matrix: `tr(|v⟩⟨v| M) = ⟨v, M v⟩`. -/
private theorem trace_vecMulVec_star_mul {X : Type*} [Fintype X] [DecidableEq X] (v : X → ℂ)
    (M : Matrix X X ℂ) :
    (vecMulVec v (star v) * M).trace =
      ⟪WithLp.toLp 2 v, toEuclideanLin M (WithLp.toLp 2 v)⟫_ℂ := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, toLpLin_apply, trace, diag, mul_apply,
    vecMulVec_apply, dotProduct, mulVec, Pi.star_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring

/-- **Lemma `l:leading` on the chain** (arXiv:1307.5143v1, `algo53.tex`, lines 493–505). Let
`H = H_L + K` with `H_L` supported on the first `k` sites and `K` supported off the first
`k - 1` sites, with gapped ground state `Γ`, energy `E₀` and gap `Δ`. Let `W` be an isometry
from the bond `ℂ^m` into the sites right of the cut and let `w = (1 ⊗ W) x` in the cut
coordinates have energy at most `E₀ + e`. Let `σ` be a density matrix on the first `k` sites and
the bond with left energy at most that of `x` and `‖tr_A σ - tr_A |x⟩⟨x|‖₁ ≤ τ`. If
`4 (e + ‖K‖ τ) < Δ`, then `σ` has a unit eigenvector `u` with eigenvalue larger than `1/2` whose
extension `(1 ⊗ W) u`, read on the chain, has energy at most `E₀ + 2 (e + ‖K‖ τ)` and overlap
at least `1 - 2 (e + ‖K‖ τ)/Δ` with `Γ`.

In the source `H_L = H_1 + ⋯ + H_{i-1}` and `K = H_i + H_R`, the vector `w` is the trimmed state
of Lemma `l:within`, `x` its left state and `σ` the solution of the size-trimming program; with
`‖K‖ ≤ n` and `τ = c_ε/n` the energy bound is `E₀ + 2 (e + c_ε)`. -/
theorem exists_leading_eigenvector_chain [NeZero q] {k : ℕ}
    {HL K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
    (hHL : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) HL (leftBlock L k)) {D : Finset (Fin L)}
    (hK : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) K D)
    (hDA : Disjoint D (leftBlock L (k - 1))) {E₀ Δ e τ : ℝ}
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hΔ : 0 < Δ)
    (hgs : IsGappedGroundState (HL + K) E₀ Γ Δ) {m : ℕ} (W : Matrix (CutRight L q k) (Fin m) ℂ)
    (hW : Wᴴ * W = 1) (x : (CutLeft L q k × CutSite L q k) × Fin m → ℂ)
    {w : EuclideanSpace ℂ (Fin L → Fin q)}
    (hwx : WithLp.ofLp w ∘ (gluingCut L q k).symm =
      ((1 : Matrix (CutLeft L q k × CutSite L q k) (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ x)
    (hwE : (⟪w, toEuclideanLin (HL + K) w⟫_ℂ).re ≤ E₀ + e)
    {σ : Matrix ((CutLeft L q k × CutSite L q k) × Fin m)
      ((CutLeft L q k × CutSite L q k) × Fin m) ℂ} (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    (hopt : (σ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re ≤
      (vecMulVec x (star x) * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re)
    (hτ : rectangularTraceNorm
      (partialTraceFirst σ - partialTraceFirst (vecMulVec x (star x))) ≤ τ)
    (h4 : 4 * (e + ‖K‖ * τ) < Δ) :
    ∃ (u : EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m)) (μ : ℝ), ‖u‖ = 1 ∧
      σ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u ∧ 1 / 2 < μ ∧
      (⟪WithLp.toLp 2 ((((1 : Matrix (CutLeft L q k × CutSite L q k)
            (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) ∘ gluingCut L q k),
          toEuclideanLin (HL + K) (WithLp.toLp 2 ((((1 : Matrix (CutLeft L q k × CutSite L q k)
            (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) ∘
              gluingCut L q k))⟫_ℂ).re ≤ E₀ + 2 * (e + ‖K‖ * τ) ∧
      1 - 2 * (e + ‖K‖ * τ) / Δ ≤
        ‖⟪Γ, WithLp.toLp 2 ((((1 : Matrix (CutLeft L q k × CutSite L q k)
            (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) ∘ gluingCut L q k)⟫_ℂ‖ := by
  classical
  set E := gluingCut L q k with hEdef
  set J := (1 : Matrix (CutLeft L q k × CutSite L q k) (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W
  set K' := rightCutOperator k K
  set Γ' : EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × CutRight L q k) :=
    WithLp.toLp 2 (WithLp.ofLp Γ ∘ E.symm)
  have hsplit := reindex_gluingCut_eq hHL hK hDA
  obtain ⟨hΓ, -, hgap⟩ := isGappedGroundState_iff.mp hgs
  -- The ground state and the gap in the cut coordinates.
  have hΓ' : ‖Γ'‖ = 1 := by
    have h := inner_comp_symm E Γ Γ
    have h' : ‖Γ'‖ ^ 2 = ‖Γ‖ ^ 2 := by
      rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, ← h]
    rw [hΓ, one_pow] at h'
    nlinarith [norm_nonneg Γ']
  have hgap' : (reindex E E (HL + K) - (E₀ : ℂ) • 1 -
      (Δ : ℂ) • (1 - vecMulVec (WithLp.ofLp Γ') (star (WithLp.ofLp Γ')))).PosSemidef := by
    have h := hgap.submatrix E.symm
    convert h using 1
    ext i j
    simp [reindex_apply, Γ', one_apply, vecMulVec_apply, E.symm.injective.eq_iff]
  rw [hsplit] at hgap'
  -- The energy of `w` in the cut coordinates.
  have hw' : (vecMulVec (J *ᵥ x) (star (J *ᵥ x)) *
      (leftCutOperator k HL ⊗ₖ (1 : Matrix (CutRight L q k) (CutRight L q k) ℂ) +
        reindex (Equiv.prodAssoc _ _ _).symm (Equiv.prodAssoc _ _ _).symm
          ((1 : Matrix (CutLeft L q k) (CutLeft L q k) ℂ) ⊗ₖ K'))).trace.re ≤ E₀ + e := by
    rw [← hsplit, ← hwx, trace_vecMulVec_star_mul]
    have h := inner_toEuclideanLin_reindex E (HL + K) w
    rw [h]
    exact hwE
  -- `‖K'‖ ≤ ‖K‖`.
  have hKK : ‖K'‖ ≤ ‖K‖ := by
    have hr := hK.reindex_threeCutEquiv_eq_one_kronecker (leftBlock_mono (Nat.sub_le k 1)) hDA
      (fun _ ↦ 0)
    have hn : ‖reindex E E K‖ = ‖K‖ := l2_opNorm_reindex_equiv E K
    rw [show reindex E E K = _ from hr, l2_opNorm_reindex_equiv] at hn
    exact (l2_opNorm_le_one_kronecker (fun _ ↦ 0) K').trans hn.le
  have hτ0 : 0 ≤ τ := (rectangularTraceNorm_nonneg _).trans hτ
  have he' : 4 * (e + ‖K'‖ * τ) < Δ := by nlinarith [mul_le_mul_of_nonneg_right hKK hτ0]
  obtain ⟨u, μ, hu1, hueig, hμ, huE, huov⟩ :=
    exists_leading_eigenvector_of_gluing W hW (leftCutOperator k HL) K' hgap' hΓ' hΔ hσ htr x
      hopt hτ hw' he'
  refine ⟨u, μ, hu1, hueig, hμ, ?_, ?_⟩
  · -- Read the energy back on the chain.
    have hback : WithLp.toLp 2 (WithLp.ofLp (WithLp.toLp 2 ((J *ᵥ WithLp.ofLp u) ∘ E)) ∘ E.symm) =
        toEuclideanLin J u := by
      simp [toLpLin_apply, Function.comp_assoc]
    have h := inner_toEuclideanLin_reindex E (HL + K) (WithLp.toLp 2 ((J *ᵥ WithLp.ofLp u) ∘ E))
    rw [hback, hsplit] at h
    rw [← h]
    exact huE.trans (by nlinarith [mul_le_mul_of_nonneg_right hKK hτ0])
  · have hback : WithLp.toLp 2 (WithLp.ofLp (WithLp.toLp 2 ((J *ᵥ WithLp.ofLp u) ∘ E)) ∘ E.symm) =
        toEuclideanLin J u := by
      simp [toLpLin_apply, Function.comp_assoc]
    have h := inner_comp_symm E Γ (WithLp.toLp 2 ((J *ᵥ WithLp.ofLp u) ∘ E))
    rw [hback] at h
    rw [← h]
    refine le_trans ?_ huov
    have : 2 * (e + ‖K'‖ * τ) ≤ 2 * (e + ‖K‖ * τ) := by
      nlinarith [mul_le_mul_of_nonneg_right hKK hτ0]
    have := div_le_div_of_nonneg_right this hΔ.le
    linarith

end TNLean.MPS.AreaLaw
