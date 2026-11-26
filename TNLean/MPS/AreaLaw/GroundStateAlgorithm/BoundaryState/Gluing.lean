/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.VaryingBond.OpenMPS
import QICLean.Channel.Gluing.LeadingEigenvectorBounds
import QICLean.ManyBody.Sites.ThreeRegion.Cut
import QICLean.ManyBody.Entropy.Cut.RegionSplit
import QICLean.Analysis.TraceNorm.RectangularTraceNormAlgebra
import QICLean.Analysis.Isometry.EuclideanReindex
import QICLean.Analysis.Norm.KroneckerOperatorNorm
import QICLean.ManyBody.Hamiltonian.GroundSpace
import QICLean.Spectral.Eigenvalue.DominantEigenvectorUniqueness
import TNLean.MPS.AreaLaw.ViableSet.Basic
import QICLean.Channel.Schmidt.TrimmingEnergy
import TNLean.MPS.AreaLaw.GroundStateAlgorithm.BoundaryState.ConstantRankCut
import QICLean.Channel.Schmidt.TrimmedWitness

/-!
# Gluing a left state at a cut of the chain

Fix the cut after `k` sites of a chain of `L` sites. In the coordinates of the three-way cut
`A = interval L 0 (k - 1)`, `B = interval L 0 k`, a configuration is `((x, y), z)` with `x` on the
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

## Bounds for every dominant eigenvector on the chain

The energy and overlap estimates in chain gluing hold for every supplied unit eigenvector
of the left density matrix whose eigenvalue exceeds one half. The existing chain theorem
supplies one such vector, and phase uniqueness transfers its estimates to any other choice.
The physical extension through the right isometry and the cut coordinates is linear.

This is an auxiliary choice-independent form of Landau, Vazirani and Vidick,
arXiv:1307.5143v1, `algo53.tex`, Lemma `l:leading`, lines 493–505.

## Left support in three-way cut coordinates

A vector fixed by the left support projection in the three-way cut coordinates belongs to
the corresponding left-supported subspace when read on the chain. This is an auxiliary
coordinate statement for LVV13, arXiv:1307.5143v1, `algo53.tex`, Lemma `l:leading`,
lines 493–505.

## The trimmed witness at a cut of the chain

Fix the cut after `k` sites. Let `H = H_L + H_R + K` with `H_L` supported on the first `k`
sites, `H_R` on the others and `0 ≤ K ≤ 1`, and `H ≥ E₀`. Let `ψ` be a unit vector of energy at
most `E₀ + δ` whose left factor lies in the range of a matrix `P_V` on the first `k` sites,
`P_V C = C` for its cut matrix `C`, and let some unit vector of rank at most `D` across the cut
overlap `ψ` by at least `1 - η`, with `2η < 1`. Trimming `ψ` across the cut to its `D` largest
Schmidt terms and normalizing gives a unit vector `w` of rank at most `D` across the cut, with
energy at most `E₀ + (δ + 2√(2η))/(1 - 2η)` and left factor still in the range of `P_V`.
This `w` is `(1 ⊗ W) x` in the cut coordinates of `TNLean.MPS.AreaLaw.gluingCut` for an
isometry `W` from a bond `ℂ^m`, `m ≤ D`, into the sites right of the cut, and a left state `x`
whose left factor is again in the range of `P_V`. This is the input of Lemma `l:leading` on the
chain (`TNLean.MPS.AreaLaw.exists_leading_eigenvector_chain`).

This is Lemma `l:within` of Landau, Vazirani and Vidick on the chain. With `P_V` the projection
onto the span of a viable set `S`, the condition `P_V C = C` says that the left Schmidt vectors
of `ψ` lie in `Span(S)`.

**Local fix (energy after trimming):** the energy bound is the corrected one,
`E₀ + (δ + 2√(2η))/(1 - 2η)`; the printed `ε₀ + 6√c_ε` is not established by the printed
argument. Documented in the QICLean note
<https://sirui-lu.com/QICLean/paper-gaps/lvv13_trimming_energy.pdf>.

### Main results

* `TNLean.MPS.AreaLaw.exists_trimmed_witness_chain`: Lemma `l:within` on the chain.

### References

* Z. Landau, U. Vazirani, T. Vidick, *A polynomial-time algorithm for the ground state of 1D
  gapped local Hamiltonians*, arXiv:1307.5143v1, `References/1307.5143/algo53.tex`: Lemma
  `l:within`, lines 509–515.
-/

open ManyBody (interval interval_mono)

section

open Matrix
open scoped Matrix Kronecker Matrix.Norms.L2Operator ComplexOrder InnerProductSpace

open ManyBody (IsGapped groundSpace)

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
abbrev CutLeft (L q k : ℕ) := (v : {v // v ∈ interval L 0 (k - 1)}) → Fin q

/-- The number of left configurations is the local dimension raised to the number of sites
strictly before the cut site. -/
@[simp]
theorem card_cutLeft (L q k : ℕ) :
    Fintype.card (CutLeft L q k) = q ^ min L (k - 1) := by
  have hcard : (interval L 0 (k - 1)).card = min L (k - 1) := by
    rw [← Fin.card_filter_val_lt]
    simp [interval]
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, hcard]

/-- The configurations of site `k - 1`, the last site left of the cut. -/
abbrev CutSite (L q k : ℕ) := (v : {v // v ∈ interval L 0 k \ interval L 0 (k - 1)}) → Fin q

/-- The configurations of the sites right of the cut. -/
abbrev CutRight (L q k : ℕ) := (v : {v // v ∉ interval L 0 k}) → Fin q

/-- The three-way cut coordinates `((x, y), z)` at the cut after `k` sites. -/
abbrev gluingCut (L q k : ℕ) :
    (Fin L → Fin q) ≃ (CutLeft L q k × CutSite L q k) × CutRight L q k :=
  ManyBody.threeCutEquiv (fun _ : Fin L ↦ Fin q) (interval_mono (le_refl 0) (Nat.sub_le k 1))

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
    (hX : ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) X (interval L 0 k)) :
    ‖leftCutOperator k X‖ = ‖X‖ := by
  classical
  have hform := hX.reindex_threeCutEquiv_eq_kronecker_one
    (interval_mono (le_refl 0) (Nat.sub_le k 1)) subset_rfl (fun _ ↦ 0)
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
    (hHL : ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) HL (interval L 0 k)) {D : Finset (Fin L)}
    (hK : ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) K D)
    (hDA : Disjoint D (interval L 0 (k - 1))) :
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
    (hHL : ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) HL (interval L 0 k)) {D : Finset (Fin L)}
    (hK : ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) K D)
    (hDA : Disjoint D (interval L 0 (k - 1))) {E₀ Δ e τ ξ : ℝ}
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hΔ : 0 < Δ) (hH : (HL + K).IsHermitian)
    (hΩ : ‖Γ‖ = 1) (hgap : IsGapped (HL + K) E₀ Δ)
    (hspan : groundSpace (HL + K) E₀ = Submodule.span ℂ {Γ}) {m : ℕ}
    (W : Matrix (CutRight L q k) (Fin m) ℂ)
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
  have hΓ := hΩ
  have hgap := hgap.posSemidef_sub_smul_one hH hΩ hspan
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
    have hr := hK.reindex_threeCutEquiv_eq_one_kronecker
        (interval_mono (le_refl 0) (Nat.sub_le k 1)) hDA
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
    (hHL : ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) HL (interval L 0 k)) {D : Finset (Fin L)}
    (hK : ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) K D)
    (hDA : Disjoint D (interval L 0 (k - 1))) {E₀ Δ e τ : ℝ}
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hΔ : 0 < Δ) (hH : (HL + K).IsHermitian)
    (hΩ : ‖Γ‖ = 1) (hgap : IsGapped (HL + K) E₀ Δ)
    (hspan : groundSpace (HL + K) E₀ = Submodule.span ℂ {Γ}) {m : ℕ}
    (W : Matrix (CutRight L q k) (Fin m) ℂ)
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
  have hΓ := hΩ
  have hgap := hgap.posSemidef_sub_smul_one hH hΩ hspan
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
    have hr := hK.reindex_threeCutEquiv_eq_one_kronecker
        (interval_mono (le_refl 0) (Nat.sub_le k 1)) hDA
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

end

section

open Matrix
open scoped Matrix Kronecker Matrix.Norms.L2Operator ComplexOrder InnerProductSpace

open ManyBody (IsGapped groundSpace)

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ}

/-- Every supplied unit eigenvector of the left density matrix with eigenvalue larger than
one half satisfies the numerical chain-gluing bounds when the left-energy objective has
additive error `ξ`. This is the choice-independent finite-precision form of LVV13,
`algo53.tex`, Lemma `l:leading`, lines 493–505. -/
theorem leading_eigenvector_bounds_chain_with_objective_slack [NeZero q] {k : ℕ}
    {HL K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
    (hHL : ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) HL (interval L 0 k)) {D : Finset (Fin L)}
    (hK : ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) K D)
    (hDA : Disjoint D (interval L 0 (k - 1))) {E₀ Δ e τ ξ : ℝ}
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hΔ : 0 < Δ)
    (hH : (HL + K).IsHermitian) (hΩ : ‖Γ‖ = 1)
    (hgap : IsGapped (HL + K) E₀ Δ)
    (hspan : groundSpace (HL + K) E₀ = Submodule.span ℂ {Γ}) {m : ℕ}
    (W : Matrix (CutRight L q k) (Fin m) ℂ)
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
    (h4 : 4 * (e + ξ + ‖K‖ * τ) < Δ)
    (u : EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m))
    (μ : ℝ) (hu : ‖u‖ = 1)
    (huσ : σ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u) (hμ : 1 / 2 < μ) :
      (⟪WithLp.toLp 2 ((((1 : Matrix (CutLeft L q k × CutSite L q k)
            (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) ∘ gluingCut L q k),
          toEuclideanLin (HL + K) (WithLp.toLp 2 ((((1 : Matrix (CutLeft L q k × CutSite L q k)
            (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) ∘
              gluingCut L q k))⟫_ℂ).re ≤ E₀ + 2 * (e + ξ + ‖K‖ * τ) ∧
      1 - 2 * (e + ξ + ‖K‖ * τ) / Δ ≤
        ‖⟪Γ, WithLp.toLp 2 ((((1 : Matrix (CutLeft L q k × CutSite L q k)
            (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) ∘ gluingCut L q k)⟫_ℂ‖ := by
  classical
  obtain ⟨v, ν, hv, hvσ, hν, hvE, hvov⟩ :=
    exists_leading_eigenvector_chain_with_objective_slack
      hHL hK hDA hΔ hH hΩ hgap hspan W hW x hwx hwE hσ htr hopt hτ h4
  obtain ⟨-, z, hz, huz⟩ :=
    hσ.eigenvalue_eq_and_exists_unit_smul_of_gt_half htr hv hu hvσ huσ hν hμ
  let J := (1 : Matrix (CutLeft L q k × CutSite L q k)
    (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W
  have hphys : WithLp.toLp 2 ((J *ᵥ WithLp.ofLp u) ∘ gluingCut L q k) =
      z • WithLp.toLp 2 ((J *ᵥ WithLp.ofLp v) ∘ gluingCut L q k) := by
    apply WithLp.ofLp_injective 2
    ext i
    simp only [huz, WithLp.ofLp_smul, mulVec_smul,
      Function.comp_apply, Pi.smul_apply]
  have hphase : z * (starRingEnd ℂ) z = (1 : ℂ) := by
    simpa only [hz, one_pow, Complex.ofReal_one] using Complex.mul_conj' z
  dsimp only [J] at hphys
  rw [hphys]
  constructor
  · simpa only [map_smul, inner_smul_left, inner_smul_right, ← mul_assoc,
      hphase, one_mul] using hvE
  · simpa only [inner_smul_right, norm_mul, hz, one_mul] using hvov

/-- Every supplied unit eigenvector of the left density matrix with eigenvalue larger than
one half satisfies the chain gluing energy and overlap bounds. Auxiliary choice-independent
form of LVV13, `algo53.tex`, Lemma `l:leading`, lines 493–505. -/
theorem leading_eigenvector_bounds_chain [NeZero q] {k : ℕ}
    {HL K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
    (hHL : ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) HL (interval L 0 k)) {D : Finset (Fin L)}
    (hK : ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) K D)
    (hDA : Disjoint D (interval L 0 (k - 1))) {E₀ Δ e τ : ℝ}
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hΔ : 0 < Δ)
    (hH : (HL + K).IsHermitian) (hΩ : ‖Γ‖ = 1)
    (hgap : IsGapped (HL + K) E₀ Δ)
    (hspan : groundSpace (HL + K) E₀ = Submodule.span ℂ {Γ}) {m : ℕ}
    (W : Matrix (CutRight L q k) (Fin m) ℂ)
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
    (h4 : 4 * (e + ‖K‖ * τ) < Δ)
    (u : EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m))
    (μ : ℝ) (hu : ‖u‖ = 1)
    (huσ : σ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u) (hμ : 1 / 2 < μ) :
      (⟪WithLp.toLp 2 ((((1 : Matrix (CutLeft L q k × CutSite L q k)
            (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) ∘ gluingCut L q k),
          toEuclideanLin (HL + K) (WithLp.toLp 2 ((((1 : Matrix (CutLeft L q k × CutSite L q k)
            (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) ∘
              gluingCut L q k))⟫_ℂ).re ≤ E₀ + 2 * (e + ‖K‖ * τ) ∧
      1 - 2 * (e + ‖K‖ * τ) / Δ ≤
        ‖⟪Γ, WithLp.toLp 2 ((((1 : Matrix (CutLeft L q k × CutSite L q k)
            (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) ∘ gluingCut L q k)⟫_ℂ‖ := by
  simpa only [add_zero] using
    leading_eigenvector_bounds_chain_with_objective_slack
      (L := L) (q := q) (k := k) (ξ := 0) hHL hK hDA hΔ hH hΩ hgap hspan W hW x hwx hwE hσ htr
        (by simpa only [add_zero] using hopt) hτ (by simpa only [add_zero] using h4)
        u μ hu huσ hμ

end TNLean.MPS.AreaLaw

end

section

open Matrix
open scoped InnerProductSpace Kronecker

namespace TNLean.MPS.AreaLaw

variable {L q k : ℕ}

/-- The left support condition of LVV13, `algo53.tex`, lines 493–505, read from the
three-way cut coordinates back on the chain. -/
theorem mem_leftSupportSubmodule_of_gluingCut_fixed
    (S : Set (LeftBlockVector L q k))
    (y : (CutLeft L q k × CutSite L q k) × CutRight L q k → ℂ)
    (hy : (reindex
        (ManyBody.subsetSplitEquiv (fun _ : Fin L ↦ Fin q)
            (interval_mono (le_refl 0) (Nat.sub_le k 1)))
        (ManyBody.subsetSplitEquiv (fun _ : Fin L ↦ Fin q)
            (interval_mono (le_refl 0) (Nat.sub_le k 1)))
        (spanProjection S) ⊗ₖ (1 : Matrix (CutRight L q k) (CutRight L q k) ℂ)) *ᵥ y = y) :
    WithLp.toLp 2 (y ∘ gluingCut L q k) ∈ leftSupportSubmodule S := by
  classical
  let e :=
    ManyBody.subsetSplitEquiv (fun _ : Fin L ↦ Fin q)
      (interval_mono (L := L) (le_refl 0) (Nat.sub_le k 1))
  let P := reindex e e (spanProjection S)
  let Y := Matrix.schmidtCoeffMatrix y
  have hleft : leftApply P (WithLp.toLp 2 y) = WithLp.toLp 2 y := by
    rw [← toEuclideanLin_kronecker_one_apply]
    apply WithLp.ofLp_injective 2
    simpa only [toLpLin_apply, WithLp.ofLp_toLp] using hy
  have hPY : P * Y = Y := by
    have h := congrArg (fun z ↦ schmidtCoeffMatrix (WithLp.ofLp z)) hleft
    simpa only [schmidtCoeffMatrix_ofLp_leftApply] using h
  have hcm : ManyBody.cutMatrix (interval L 0 k) (WithLp.toLp 2 (y ∘ gluingCut L q k)) =
      Y.submatrix e id := by
    ext p r
    rw [ManyBody.cutMatrix_apply]
    change y (gluingCut L q k ((ManyBody.cutEquiv (fun _ ↦ Fin q)
      (interval L 0 k)).symm (p, r))) = y (e p, r)
    rw [gluingCut, ManyBody.threeCutEquiv_eq_trans]
    simp [e]
  apply (spanProjection_mul_cutMatrix_eq_iff (S := S)).mp
  rw [hcm]
  have hP : P.submatrix e e = spanProjection S := by
    ext a b
    simp [P]
  have h := congrArg (fun M ↦ M.submatrix e id) hPY
  rw [← Matrix.submatrix_mul_equiv P Y e e id, hP] at h
  exact h

end TNLean.MPS.AreaLaw

end

section

open Matrix
open scoped Matrix Kronecker ComplexOrder InnerProductSpace

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ}

/-- **Lemma `l:within` on the chain** (arXiv:1307.5143v1, `algo53.tex`, lines 509–515), with
the corrected energy bound. Let `H = H_L + H_R + K` with `H_L` supported on the first `k`
sites, `H_R` on the others, `0 ≤ K ≤ 1` and `H ≥ E₀`. Let `ψ` be a unit vector with
`Re ⟨ψ, H ψ⟩ ≤ E₀ + δ` and `P_V C = C` for its cut matrix `C`, and let a unit vector `u` of rank
at most `D` across the cut satisfy `|⟨u, ψ⟩| ≥ 1 - η` with `2η < 1`. Then there are a unit
vector `w` of rank at most `D` across the cut, with
`Re ⟨w, H w⟩ ≤ E₀ + (δ + 2√(2η))/(1 - 2η)` and `P_V C_w = C_w`, an isometry `W` from `ℂ^m`,
`m ≤ D`, into the sites right of the cut, and `x` with `w = (1 ⊗ W) x` in the coordinates of
`gluingCut L q k`, whose left factor is in the range of `P_V`. -/
theorem exists_trimmed_witness_chain {k : ℕ}
    {H HL HR K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ} (hsplit : H = HL + HR + K)
    (hHL : ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) HL (interval L 0 k))
    (hHR : ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) HR (interval L 0 k)ᶜ)
    (hK0 : K.PosSemidef) (hK1 : (1 - K).PosSemidef) {E₀ δ : ℝ}
    (hH0 : (H - (E₀ : ℂ) • 1).PosSemidef) {ψ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hψ : ‖ψ‖ = 1) (hE : (⟪ψ, toEuclideanLin H ψ⟫_ℂ).re ≤ E₀ + δ) {D : ℕ}
    {u : EuclideanSpace ℂ (Fin L → Fin q)} (hu : ‖u‖ = 1)
    (huD : (ManyBody.cutMatrix (interval L 0 k) u).rank ≤ D)
    {η : ℝ} (hη : 1 - η ≤ ‖⟪u, ψ⟫_ℂ‖) (hη2 : 2 * η < 1) {PV : LeftBlockMatrix L q k}
    (hPV : PV * ManyBody.cutMatrix (interval L 0 k) ψ = ManyBody.cutMatrix (interval L 0 k) ψ) :
    ∃ (w : EuclideanSpace ℂ (Fin L → Fin q)) (m : ℕ) (W : Matrix (CutRight L q k) (Fin m) ℂ)
      (x : (CutLeft L q k × CutSite L q k) × Fin m → ℂ),
      ‖w‖ = 1 ∧ (ManyBody.cutMatrix (interval L 0 k) w).rank ≤ D ∧
      (⟪w, toEuclideanLin H w⟫_ℂ).re ≤ E₀ + (δ + 2 * √(2 * η)) / (1 - 2 * η) ∧
      PV * ManyBody.cutMatrix (interval L 0 k) w = ManyBody.cutMatrix (interval L 0 k) w ∧
      Wᴴ * W = 1 ∧ m ≤ D ∧
      WithLp.ofLp w ∘ (gluingCut L q k).symm =
        ((1 : Matrix (CutLeft L q k × CutSite L q k) (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ
          x ∧
      (reindex (ManyBody.subsetSplitEquiv (fun _ : Fin L ↦ Fin q)
          (interval_mono (le_refl 0) (Nat.sub_le k 1)))
          (ManyBody.subsetSplitEquiv (fun _ : Fin L ↦ Fin q) (interval_mono (le_refl 0)
            (Nat.sub_le k 1))) PV ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ)) *ᵥ x = x := by
  classical
  rcases isEmpty_or_nonempty (Fin L → Fin q) with hσ | ⟨⟨σ⟩⟩
  · exfalso
    have h0 : ψ = 0 := Subsingleton.elim _ _
    simp [h0] at hψ
  set e := ManyBody.cutEquiv (fun _ ↦ Fin q) (interval L 0 k)
  set ψc := ManyBody.cutVector (X := fun _ ↦ Fin q) (interval L 0 k) ψ
  set uc := ManyBody.cutVector (X := fun _ ↦ Fin q) (interval L 0 k) u
  -- The Hamiltonian in the cut coordinates.
  have hL := hHL.cutOperator_eq_kronecker_one (B := interval L 0 k) subset_rfl (e σ).2
  have hR := hHR.cutOperator_eq_one_kronecker (B := interval L 0 k) disjoint_compl_left (e σ).1
  obtain ⟨A, A', hHc⟩ : ∃ (A : LeftBlockMatrix L q k)
      (A' : Matrix (CutRight L q k) (CutRight L q k) ℂ),
      ManyBody.cutOperator (X := fun _ ↦ Fin q) (interval L 0 k) H =
        A ⊗ₖ (1 : Matrix (CutRight L q k) (CutRight L q k) ℂ) +
          (1 : LeftBlockMatrix L q k) ⊗ₖ A' +
          ManyBody.cutOperator (X := fun _ ↦ Fin q) (interval L 0 k) K :=
    ⟨fun x x' ↦ ManyBody.cutOperator (X := fun _ ↦ Fin q) (interval L 0 k) HL
        (x, (e σ).2) (x', (e σ).2),
      fun y y' ↦ ManyBody.cutOperator (X := fun _ ↦ Fin q) (interval L 0 k) HR
        ((e σ).1, y) ((e σ).1, y'),
      by rw [hsplit, cutOperator_add, cutOperator_add, ← hL, ← hR]⟩
  have hK1c : (1 - ManyBody.cutOperator (X := fun _ ↦ Fin q) (interval L 0 k) K).PosSemidef := by
    have : (ManyBody.cutOperator (X := fun _ ↦ Fin q) (interval L 0 k)
        (1 - K)).PosSemidef := hK1.submatrix _
    have h1 : ManyBody.cutOperator (X := fun _ ↦ Fin q) (interval L 0 k) (1 - K) =
        1 - ManyBody.cutOperator (X := fun _ ↦ Fin q) (interval L 0 k) K := by
      ext a b
      simp [one_apply]
    rwa [h1] at this
  have hHc0 : (ManyBody.cutOperator (X := fun _ ↦ Fin q) (interval L 0 k) H -
      (E₀ : ℂ) • 1).PosSemidef := by
    rw [← cutOperator_sub_smul_one]
    exact hH0.submatrix _
  have hEc := hE
  rw [← Entropy.inner_cutOperator (interval L 0 k)] at hEc
  have hψc : ‖ψc‖ = 1 := by rw [Entropy.norm_cutVector, hψ]
  have huc : ‖uc‖ = 1 := by rw [Entropy.norm_cutVector, hu]
  have hucD : HasSchmidtRankLE D (WithLp.ofLp uc) := huD
  have hη' : 1 - η ≤ ‖⟪uc, ψc⟫_ℂ‖ := by rw [inner_cutVector]; exact hη
  have hPVc : leftApply PV ψc = ψc := by
    change toEuclid (PV * ManyBody.cutMatrix (interval L 0 k) ψ) =
      toEuclid (ManyBody.cutMatrix (interval L 0 k) ψ)
    rw [hPV]
  obtain ⟨wc, m, W, xc, hwc1, hwcD, hwcE, hwcPV, hW, hmD, hwx, hxPV⟩ :=
    IsTrimmingProjection.exists_trimmed_witness hHc hHc0 (hK0.submatrix _) hK1c hψc hEc huc
      hucD hη' hη2 hPVc
  -- Back to the chain.
  set w : EuclideanSpace ℂ (Fin L → Fin q) := WithLp.toLp 2 (WithLp.ofLp wc ∘ e)
  have hwcw : ManyBody.cutVector (X := fun _ ↦ Fin q) (interval L 0 k) w = wc := by
    ext x
    simp [w, e]
  have hcm : ManyBody.cutMatrix (interval L 0 k) w = schmidtCoeffMatrix (WithLp.ofLp wc) := by
    change schmidtCoeffMatrix (WithLp.ofLp
      (ManyBody.cutVector (X := fun _ ↦ Fin q) (interval L 0 k) w)) = _
    rw [hwcw]
  set Ssplit :=
    ManyBody.subsetSplitEquiv (fun _ : Fin L ↦ Fin q)
      (interval_mono (L := L) (le_refl 0) (Nat.sub_le k 1))
  refine ⟨w, m, W, fun p ↦ WithLp.ofLp xc (Ssplit.symm p.1, p.2), ?_, ?_, ?_, ?_, hW, hmD, ?_, ?_⟩
  · rw [← Entropy.norm_cutVector (interval L 0 k), hwcw, hwc1]
  · rw [hcm]; exact hwcD
  · rw [← Entropy.inner_cutOperator (interval L 0 k), hwcw]; exact hwcE
  · rw [hcm]
    have h := congrArg (fun v ↦ schmidtCoeffMatrix (WithLp.ofLp v)) hwcPV
    simpa only [schmidtCoeffMatrix_ofLp_leftApply] using h
  · funext ⟨p, z⟩
    have h := congrFun hwx (Ssplit.symm p, z)
    have hg : (gluingCut L q k).symm (p, z) = e.symm (Ssplit.symm p, z) := by
      rw [gluingCut, ManyBody.threeCutEquiv_eq_trans]
      rfl
    simp only [Function.comp_apply, hg, w, Equiv.apply_symm_apply]
    rw [h]
    simp [mulVec, dotProduct, Fintype.sum_prod_type, one_apply]
  · have h := congrArg (fun v ↦ schmidtCoeffMatrix (WithLp.ofLp v)) hxPV
    simp only [schmidtCoeffMatrix_ofLp_leftApply] at h
    funext ⟨p, j⟩
    have hpj := congrFun (congrFun h (Ssplit.symm p)) j
    simp only [schmidtCoeffMatrix_apply, mul_apply] at hpj
    simp only [mulVec, dotProduct, Fintype.sum_prod_type, kroneckerMap_apply, one_apply,
      reindex_apply, submatrix_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    rw [← hpj, ← Fintype.sum_prod_type']
    exact Fintype.sum_equiv Ssplit.symm _ _ fun _ ↦ rfl

end TNLean.MPS.AreaLaw

end
