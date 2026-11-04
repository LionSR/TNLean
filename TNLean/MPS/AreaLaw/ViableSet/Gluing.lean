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
import QICLean.Analysis.EuclideanReindex
import QICLean.Analysis.KroneckerOperatorNorm

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
* `TNLean.MPS.AreaLaw.exists_leading_eigenvector_chain_with_objective_slack`: its stable form
  when the left-energy minimization has an additive error.

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

/-- Tensoring a square matrix with the identity on a nonempty finite space preserves its
Euclidean operator norm. This is the left-factor counterpart of
`Matrix.l2_opNorm_one_kronecker`. -/
theorem Matrix.l2_opNorm_kronecker_one {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] [Nonempty Y] (K : Matrix X X ℂ) :
    ‖K ⊗ₖ (1 : Matrix Y Y ℂ)‖ = ‖K‖ := by
  let e : X × Y ≃ Y × X := Equiv.prodComm X Y
  calc
    ‖K ⊗ₖ (1 : Matrix Y Y ℂ)‖ =
        ‖reindex e e (K ⊗ₖ (1 : Matrix Y Y ℂ))‖ :=
      (l2_opNorm_reindex_equiv e _).symm
    _ = ‖(1 : Matrix Y Y ℂ) ⊗ₖ K‖ := by
      congr 1
      apply Matrix.ext
      rintro ⟨y, x⟩ ⟨y', x'⟩
      simp [e, reindex_apply, kroneckerMap_apply, mul_comm]
    _ = ‖K‖ := l2_opNorm_one_kronecker K

/-- The configurations of the first `k - 1` sites. -/
abbrev CutLeft (L q k : ℕ) := (v : {v // v ∈ leftBlock L (k - 1)}) → Fin q

/-- The number of left configurations is the local dimension raised to the number of sites
strictly before the cut site. -/
@[simp]
theorem card_cutLeft (L q k : ℕ) :
    Fintype.card (CutLeft L q k) = q ^ min L (k - 1) := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
  simp

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

/-- Taking the left operator at a cut does not change the norm of an operator supported on
the left block. -/
theorem norm_leftCutOperator_eq [NeZero q] {k : ℕ}
    {X : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
    (hX : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) X (leftBlock L k)) :
    ‖leftCutOperator k X‖ = ‖X‖ := by
  classical
  have hform := hX.reindex_threeCutEquiv_eq_kronecker_one
    (leftBlock_mono (Nat.sub_le k 1)) subset_rfl (fun _ ↦ 0)
  have hn := l2_opNorm_reindex_equiv (gluingCut L q k) X
  rw [hform] at hn
  change ‖leftCutOperator k X ⊗ₖ
    (1 : Matrix (CutRight L q k) (CutRight L q k) ℂ)‖ = ‖X‖ at hn
  rw [Matrix.l2_opNorm_kronecker_one] at hn
  exact hn

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

/-- Numerical form of the LVV leading-vector lemma. If the supplied density has left
energy at most the comparison state plus `ξ`, the energy and overlap conclusions hold with
`e` replaced by `e + ξ`. This is the stability statement needed when the boundary convex
program is solved only to finite precision. -/
theorem exists_leading_eigenvector_of_gluing_with_objective_slack
    {a s r b : Type*} [Fintype a] [Fintype s] [Fintype r] [Fintype b]
    [DecidableEq a] [DecidableEq s] [DecidableEq r] [DecidableEq b]
    (W : Matrix r b ℂ) (hW : Wᴴ * W = 1)
    (HL : Matrix (a × s) (a × s) ℂ) (K : Matrix (s × r) (s × r) ℂ)
    {E₀ Δ e τ ξ : ℝ} {Γ : EuclideanSpace ℂ ((a × s) × r)}
    (hgap : (HL ⊗ₖ (1 : Matrix r r ℂ) +
        reindex (Equiv.prodAssoc a s r).symm (Equiv.prodAssoc a s r).symm
          ((1 : Matrix a a ℂ) ⊗ₖ K) - (E₀ : ℂ) • 1 -
      (Δ : ℂ) • (1 - vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ)))).PosSemidef)
    (hΓ : ‖Γ‖ = 1) (hΔ : 0 < Δ)
    {σ : Matrix ((a × s) × b) ((a × s) × b) ℂ} (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    (x : (a × s) × b → ℂ)
    (hopt : (σ * (HL ⊗ₖ (1 : Matrix b b ℂ))).trace.re ≤
      (vecMulVec x (star x) * (HL ⊗ₖ (1 : Matrix b b ℂ))).trace.re + ξ)
    (hτ : rectangularTraceNorm
      (partialTraceFirst σ - partialTraceFirst (vecMulVec x (star x))) ≤ τ)
    (hw : (vecMulVec (((1 : Matrix (a × s) (a × s) ℂ) ⊗ₖ W) *ᵥ x)
        (star (((1 : Matrix (a × s) (a × s) ℂ) ⊗ₖ W) *ᵥ x)) *
      (HL ⊗ₖ (1 : Matrix r r ℂ) +
        reindex (Equiv.prodAssoc a s r).symm (Equiv.prodAssoc a s r).symm
          ((1 : Matrix a a ℂ) ⊗ₖ K))).trace.re ≤ E₀ + e)
    (h4 : 4 * (e + ξ + ‖K‖ * τ) < Δ) :
    ∃ (u : EuclideanSpace ℂ ((a × s) × b)) (μ : ℝ), ‖u‖ = 1 ∧
      σ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u ∧ 1 / 2 < μ ∧
      (⟪toEuclideanLin ((1 : Matrix (a × s) (a × s) ℂ) ⊗ₖ W) u,
          toEuclideanLin (HL ⊗ₖ (1 : Matrix r r ℂ) +
            reindex (Equiv.prodAssoc a s r).symm (Equiv.prodAssoc a s r).symm
              ((1 : Matrix a a ℂ) ⊗ₖ K))
            (toEuclideanLin ((1 : Matrix (a × s) (a × s) ℂ) ⊗ₖ W) u)⟫_ℂ).re ≤
        E₀ + 2 * (e + ξ + ‖K‖ * τ) ∧
      1 - 2 * (e + ξ + ‖K‖ * τ) / Δ ≤
        ‖⟪Γ, toEuclideanLin ((1 : Matrix (a × s) (a × s) ℂ) ⊗ₖ W) u⟫_ℂ‖ := by
  classical
  set J := (1 : Matrix (a × s) (a × s) ℂ) ⊗ₖ W with hJdef
  set Hf := HL ⊗ₖ (1 : Matrix r r ℂ) +
    reindex (Equiv.prodAssoc a s r).symm (Equiv.prodAssoc a s r).symm
      ((1 : Matrix a a ℂ) ⊗ₖ K) with hHf
  set e' := e + ξ + ‖K‖ * τ
  have hJJ : Jᴴ * J = 1 := by
    rw [hJdef, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul,
      hW, one_kronecker_one]
  set σ' := J * σ * Jᴴ
  have hσ' : σ'.PosSemidef := hσ.mul_mul_conjTranspose_same J
  have htr' : σ'.trace = 1 := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hJJ, Matrix.one_mul, htr]
  have hglue := re_trace_gluing_le W hW σ x HL K
  have hK0 : 0 ≤ ‖K‖ := norm_nonneg K
  have hxv : (vecMulVec x (star x) * (HL ⊗ₖ (1 : Matrix b b ℂ))).trace =
      (vecMulVec (J *ᵥ x) (star (J *ᵥ x)) * (HL ⊗ₖ (1 : Matrix r r ℂ))).trace := by
    have hv : vecMulVec (J *ᵥ x) (star (J *ᵥ x)) = J * vecMulVec x (star x) * Jᴴ := by
      rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_conjTranspose, star_star]
    rw [hv, trace_gluing_mul_kronecker_one W hW]
  have henergy : (σ' * Hf).trace.re ≤ E₀ + e' := by
    have hsplit : (vecMulVec (J *ᵥ x) (star (J *ᵥ x)) * Hf).trace.re =
        (vecMulVec (J *ᵥ x) (star (J *ᵥ x)) * (HL ⊗ₖ (1 : Matrix r r ℂ))).trace.re +
          (vecMulVec (J *ᵥ x) (star (J *ᵥ x)) *
            reindex (Equiv.prodAssoc a s r).symm (Equiv.prodAssoc a s r).symm
              ((1 : Matrix a a ℂ) ⊗ₖ K)).trace.re := by
      rw [hHf, Matrix.mul_add, trace_add, Complex.add_re]
    rw [← hxv] at hsplit
    have := mul_le_mul_of_nonneg_left hτ hK0
    simp only [σ', e'] at hglue ⊢
    linarith
  obtain ⟨v', μ, hv'1, hv'eig, hμ, hv'E, hv'ov⟩ :=
    hσ'.exists_eigenvector_of_re_trace_mul_le htr' hgap hΓ hΔ henergy h4
  have hμ0 : (μ : ℂ) ≠ 0 := by exact_mod_cast (by linarith : μ ≠ 0)
  have heig : σ' *ᵥ WithLp.ofLp v' = (μ : ℂ) • WithLp.ofLp v' := by
    have h := congrArg WithLp.ofLp hv'eig
    simpa only [toLpLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_smul] using h
  set y := WithLp.ofLp v'
  have hrange : J *ᵥ (Jᴴ *ᵥ y) = y := by
    have hy : y = J *ᵥ ((μ : ℂ)⁻¹ • (σ *ᵥ (Jᴴ *ᵥ y))) := by
      rw [mulVec_smul, mulVec_mulVec, mulVec_mulVec]
      change y = (μ : ℂ)⁻¹ • (σ' *ᵥ y)
      rw [heig, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
    conv_rhs => rw [hy]
    conv_lhs => rw [hy]
    rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc, hJJ, Matrix.mul_one]
  set u : EuclideanSpace ℂ ((a × s) × b) := WithLp.toLp 2 (Jᴴ *ᵥ y)
  have hJu : toEuclideanLin J u = v' := by
    rw [← (WithLp.ofLp_injective 2).eq_iff]
    simp only [toLpLin_apply, WithLp.ofLp_toLp, u]
    exact hrange
  have hnorm : ‖toEuclideanLin J u‖ = ‖u‖ := by
    simpa only [toLpLin_apply] using norm_toLp_mulVec_of_isometry J hJJ u
  refine ⟨u, μ, ?_, ?_, hμ, ?_, ?_⟩
  · rw [← hnorm, hJu, hv'1]
  · have h : Jᴴ *ᵥ (σ' *ᵥ y) = σ *ᵥ (Jᴴ *ᵥ y) := by
      rw [mulVec_mulVec, mulVec_mulVec, show σ' = J * σ * Jᴴ from rfl, ← Matrix.mul_assoc,
        ← Matrix.mul_assoc, hJJ, Matrix.one_mul]
    simp only [u]
    rw [← h, heig, mulVec_smul]
  · rwa [hJu]
  · rwa [hJu]

/-- Numerical form of Lemma `l:leading` on the chain. If the left-energy objective of the
supplied density is within `ξ` of that of the comparison state, then the conclusion of the
leading-vector lemma holds with `e` replaced by `e + ξ`. This is the form used after solving
the size-trimming convex program to finite precision. -/
theorem exists_leading_eigenvector_chain_with_objective_slack [NeZero q] {k : ℕ}
    {HL K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
    (hHL : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) HL (leftBlock L k)) {D : Finset (Fin L)}
    (hK : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) K D)
    (hDA : Disjoint D (leftBlock L (k - 1))) {E₀ Δ e τ ξ : ℝ}
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
      (vecMulVec x (star x) *
        (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re + ξ)
    (hτ : rectangularTraceNorm
      (partialTraceFirst σ - partialTraceFirst (vecMulVec x (star x))) ≤ τ)
    (h4 : 4 * (e + ξ + ‖K‖ * τ) < Δ) :
    ∃ (u : EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m)) (μ : ℝ), ‖u‖ = 1 ∧
      σ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u ∧ 1 / 2 < μ ∧
      (⟪WithLp.toLp 2 ((((1 : Matrix (CutLeft L q k × CutSite L q k)
            (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) ∘ gluingCut L q k),
          toEuclideanLin (HL + K) (WithLp.toLp 2 ((((1 : Matrix (CutLeft L q k × CutSite L q k)
            (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) ∘
              gluingCut L q k))⟫_ℂ).re ≤ E₀ + 2 * (e + ξ + ‖K‖ * τ) ∧
      1 - 2 * (e + ξ + ‖K‖ * τ) / Δ ≤
        ‖⟪Γ, WithLp.toLp 2 ((((1 : Matrix (CutLeft L q k × CutSite L q k)
            (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) ∘ gluingCut L q k)⟫_ℂ‖ := by
  classical
  set E := gluingCut L q k
  set J := (1 : Matrix (CutLeft L q k × CutSite L q k) (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W
  set K' := rightCutOperator k K
  set Γ' : EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × CutRight L q k) :=
    WithLp.toLp 2 (WithLp.ofLp Γ ∘ E.symm)
  have hsplit := reindex_gluingCut_eq hHL hK hDA
  obtain ⟨hΓ, -, hgap⟩ := isGappedGroundState_iff.mp hgs
  have hΓ' : ‖Γ'‖ = 1 :=
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ E).norm_map Γ).trans hΓ
  have hgap' : (reindex E E (HL + K) - (E₀ : ℂ) • 1 -
      (Δ : ℂ) • (1 - vecMulVec (WithLp.ofLp Γ') (star (WithLp.ofLp Γ')))).PosSemidef := by
    have h := hgap.submatrix E.symm
    convert h using 1
    ext i j
    simp [reindex_apply, Γ', one_apply, vecMulVec_apply, E.symm.injective.eq_iff]
  rw [hsplit] at hgap'
  have hw' : (vecMulVec (J *ᵥ x) (star (J *ᵥ x)) *
      (leftCutOperator k HL ⊗ₖ (1 : Matrix (CutRight L q k) (CutRight L q k) ℂ) +
        reindex (Equiv.prodAssoc _ _ _).symm (Equiv.prodAssoc _ _ _).symm
          ((1 : Matrix (CutLeft L q k) (CutLeft L q k) ℂ) ⊗ₖ K'))).trace.re ≤ E₀ + e := by
    rw [← hsplit, ← hwx, trace_mul_comm, mul_vecMulVec, trace_vecMulVec]
    have h := inner_toEuclideanLin_reindex E (HL + K) w
    simp only [EuclideanSpace.inner_eq_star_dotProduct, toLpLin_apply] at h
    rw [h]
    exact hwE
  have hKK : ‖K'‖ ≤ ‖K‖ := by
    have hr := hK.reindex_threeCutEquiv_eq_one_kronecker (leftBlock_mono (Nat.sub_le k 1)) hDA
      (fun _ ↦ 0)
    have hn : ‖reindex E E K‖ = ‖K‖ := l2_opNorm_reindex_equiv E K
    rw [show reindex E E K = _ from hr, l2_opNorm_reindex_equiv] at hn
    exact (l2_opNorm_one_kronecker (X := CutLeft L q k) K').symm.le.trans hn.le
  have hτ0 : 0 ≤ τ := (rectangularTraceNorm_nonneg _).trans hτ
  have he' : 4 * (e + ξ + ‖K'‖ * τ) < Δ := by
    nlinarith [mul_le_mul_of_nonneg_right hKK hτ0]
  obtain ⟨u, μ, hu1, hueig, hμ, huE, huov⟩ :=
    exists_leading_eigenvector_of_gluing_with_objective_slack W hW (leftCutOperator k HL) K'
      hgap' hΓ' hΔ hσ htr x hopt hτ hw' he'
  refine ⟨u, μ, hu1, hueig, hμ, ?_, ?_⟩
  · have hback : WithLp.toLp 2 (WithLp.ofLp (WithLp.toLp 2 ((J *ᵥ WithLp.ofLp u) ∘ E)) ∘ E.symm) =
        toEuclideanLin J u := by
      simp [toLpLin_apply, Function.comp_assoc]
    have h := inner_toEuclideanLin_reindex E (HL + K) (WithLp.toLp 2 ((J *ᵥ WithLp.ofLp u) ∘ E))
    rw [hback, hsplit] at h
    rw [← h]
    exact huE.trans (by nlinarith [mul_le_mul_of_nonneg_right hKK hτ0])
  · have hback : WithLp.toLp 2 (WithLp.ofLp (WithLp.toLp 2 ((J *ᵥ WithLp.ofLp u) ∘ E)) ∘ E.symm) =
        toEuclideanLin J u := by
      simp [toLpLin_apply, Function.comp_assoc]
    have h := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ E).inner_map_map Γ
      (WithLp.toLp 2 ((J *ᵥ WithLp.ofLp u) ∘ E))
    change (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ E)
      (WithLp.toLp 2 ((J *ᵥ WithLp.ofLp u) ∘ E)) = toEuclideanLin J u at hback
    rw [hback] at h
    rw [← h]
    refine le_trans ?_ huov
    have : 2 * (e + ξ + ‖K'‖ * τ) ≤ 2 * (e + ξ + ‖K‖ * τ) := by
      nlinarith [mul_le_mul_of_nonneg_right hKK hτ0]
    have := div_le_div_of_nonneg_right this hΔ.le
    linarith

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
  have hΓ' : ‖Γ'‖ = 1 :=
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ E).norm_map Γ).trans hΓ
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
    rw [← hsplit, ← hwx, trace_mul_comm, mul_vecMulVec, trace_vecMulVec]
    have h := inner_toEuclideanLin_reindex E (HL + K) w
    simp only [EuclideanSpace.inner_eq_star_dotProduct, toLpLin_apply] at h
    rw [h]
    exact hwE
  -- `‖K'‖ ≤ ‖K‖`.
  have hKK : ‖K'‖ ≤ ‖K‖ := by
    have hr := hK.reindex_threeCutEquiv_eq_one_kronecker (leftBlock_mono (Nat.sub_le k 1)) hDA
      (fun _ ↦ 0)
    have hn : ‖reindex E E K‖ = ‖K‖ := l2_opNorm_reindex_equiv E K
    rw [show reindex E E K = _ from hr, l2_opNorm_reindex_equiv] at hn
    exact (l2_opNorm_one_kronecker (X := CutLeft L q k) K').symm.le.trans hn.le
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
    have h := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ E).inner_map_map Γ
      (WithLp.toLp 2 ((J *ᵥ WithLp.ofLp u) ∘ E))
    change (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ E)
      (WithLp.toLp 2 ((J *ᵥ WithLp.ofLp u) ∘ E)) = toEuclideanLin J u at hback
    rw [hback] at h
    rw [← h]
    refine le_trans ?_ huov
    have : 2 * (e + ‖K'‖ * τ) ≤ 2 * (e + ‖K‖ * τ) := by
      nlinarith [mul_le_mul_of_nonneg_right hKK hτ0]
    have := div_le_div_of_nonneg_right this hΔ.le
    linarith

end TNLean.MPS.AreaLaw
