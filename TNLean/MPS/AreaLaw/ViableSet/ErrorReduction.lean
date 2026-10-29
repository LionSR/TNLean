/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.Basic
import TNLean.MPS.AreaLaw.ViableSet.OperatorAction
import TNLean.MPS.AreaLaw.SupportedCutRank
import QICLean.Entropy.ModularExpectation
import Mathlib.Analysis.Matrix.Hermitian

/-!
# The error-reduction step for viable sets

Fix the cut after `i` sites of a chain of `L` sites. Let `K` be an operator on the chain that in
the coordinates of the cut is `∑_{j ∈ J} A_j ⊗ B_j`, with `A_j` acting on the first `i` sites
and `B_j` on the remaining ones. The error-reduction step of Landau, Vazirani and Vidick
replaces a viable set `S` by `S' = {A_j s : j ∈ J, s ∈ S}`.

This file proves the deterministic part of Claim `c:errorreduction`.

* If `ψ ∈ Span(S) ⊗ H_R`, then `K ψ ∈ Span(S') ⊗ H_R`, and `|S'| ≤ |J| |S|`.
* If `v` is a unit witness for `S`, `A₀` is an operator with `‖A₀ v‖ ≥ c > 0` and
  `|⟨Γ, A₀ v⟩| ≥ (1 - ε) ‖A₀ v‖`, and `‖K - A₀‖ ≤ η < c`, then `K v / ‖K v‖` is a witness for
  `S'` with overlap at least `1 - ε - 2 η / c`.
* For the source's operator `A₀` (Hermitian with `A₀ Γ = Γ`), every witness of a
  `1/2`-viable set has `‖A₀ v‖ ≥ 1/2`, so `S'` is `(i, ε + 4 η)`-viable.

**Local fix (norm of `A v`):** the source passes from `|⟨Γ, A v / ‖A v‖⟩| ≥ 1 - δ` and
`‖K - A‖ ≤ δ` to `|⟨Γ, K v / ‖K v‖⟩| ≥ 1 - 2 δ` (algo53.tex, line 589). Without a lower bound
on `‖A v‖` this step is false: in `ℂ²` with `Γ = v = e₁`, `A = δ · 1` and `K = A + δ |e₂⟩⟨e₁|`,
the first two bounds hold while `|⟨Γ, K v / ‖K v‖⟩| = 1/√2 < 1 - 2 δ` for `0 < δ < 1/8`.
The source's `A` is Hermitian and fixes `Γ` (line 602), so that
`‖A v‖ ≥ |⟨Γ, v⟩| ≥ 1/2`; the triangle inequality then gives `1 - δ - 4 ‖K - A‖` in place of
`1 - 2 δ`, a change of the constant absorbed by applying Corollary `c:agsp` with a larger
polynomial denominator. The marker covers `IsViable.errorReduction` and
`IsViableMPS.errorReduction`, which
conclude `(i, δ + 4 η)`-viability where the source states `(i, 2 δ)` for `η = δ`. Documented in
`docs/paper-gaps/lvv13_error_reduction_witness_norm.tex`.

The operator-Schmidt ranks of each `A_j` at the internal cuts of the first `i` sites bound
the MPS bond dimensions of its images. The theorem
`IsViableMPS.errorReduction_of_norm_sub_groundProjection_le` derives these output bounds
from the input MPS bounds and combines them with viability and cardinality. The theorem
`IsViableMPS.errorReduction` also applies when MPS bounds for the images are already known.

## Main definitions

* `TNLean.MPS.AreaLaw.RightBlockMatrix`: matrices on the configurations right of a cut.
* `TNLean.MPS.AreaLaw.errorReductionSet`: the set `{A_j s : j ∈ J, s ∈ S}`.

## Main results

* `TNLean.MPS.AreaLaw.cutMatrix_toEuclideanLin_eq_sum`: the cut matrix of `K ψ` is
  `∑_j A_j M (B_j)ᵀ` for the cut matrix `M` of `ψ`.
* `TNLean.MPS.AreaLaw.card_errorReductionSet_le`: `|S'| ≤ |J| |S|`.
* `TNLean.MPS.AreaLaw.toEuclideanLin_mem_leftSupportSubmodule_errorReductionSet`: `K` maps
  `Span(S) ⊗ H_R` into `Span(S') ⊗ H_R`.
* `TNLean.MPS.AreaLaw.mul_norm_le_norm_inner_of_norm_sub_le`: the overlap estimate under a
  perturbation.
* `TNLean.MPS.AreaLaw.isViable_errorReductionSet_of_witness`,
  `TNLean.MPS.AreaLaw.IsViable.errorReduction`, `TNLean.MPS.AreaLaw.IsViableMPS.errorReduction`:
  the deterministic part of Claim `c:errorreduction`.
* `TNLean.MPS.AreaLaw.IsViable.errorReduction_of_norm_sub_groundProjection_le`,
  `TNLean.MPS.AreaLaw.IsViableMPS.errorReduction_of_norm_sub_groundProjection_le`: viability
  from the ground-projection approximation, with output MPS bounds derived in the second form.

## References

* Z. Landau, U. Vazirani, T. Vidick, *A polynomial-time algorithm for the ground state of 1D
  gapped local Hamiltonians*, arXiv:1307.5143v1, `References/1307.5143/algo53.tex`: algorithm
  step 4, lines 568–575; Claim `c:errorreduction`, lines 580–581, and its proof, lines 583–592;
  the properties of `A` and the bound `e:cutdown`, lines 602–604.
-/

open Matrix
open scoped InnerProductSpace Kronecker Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ} {ι : Type*} {i : ℕ}

/-- Matrices on the configurations of the sites right of the cut after `k` sites. -/
abbrev RightBlockMatrix (L q k : ℕ) : Type :=
  Matrix ((v : {v : Fin L // v ∉ leftBlock L k}) → Fin q)
    ((v : {v : Fin L // v ∉ leftBlock L k}) → Fin q) ℂ

/-! ### The cut matrix of `K ψ` -/

/-- The coefficient matrix of `(A ⊗ B) ψ` is `A C Bᵀ` for the coefficient matrix `C` of `ψ`. -/
private theorem schmidtCoeffMatrix_kronecker_mulVec_eq {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) (ψ : m × n → ℂ) :
    schmidtCoeffMatrix ((A ⊗ₖ B) *ᵥ ψ) = A * schmidtCoeffMatrix ψ * Bᵀ := by
  classical
  have h : A ⊗ₖ B = (A ⊗ₖ (1 : Matrix n n ℂ)) * ((1 : Matrix m m ℂ) ⊗ₖ B) := by
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  rw [h, ← Matrix.mulVec_mulVec, Matrix.schmidtCoeffMatrix_kronecker_one_mulVec,
    Matrix.schmidtCoeffMatrix_one_kronecker_mulVec, Matrix.mul_assoc]

/-- **The cut matrix of `K ψ`.** If `K = ∑_{j ∈ J} A_j ⊗ B_j` in the coordinates of the cut after
`i` sites, the cut matrix of `K ψ` is `∑_j A_j M (B_j)ᵀ` for the cut matrix `M` of `ψ`
(arXiv:1307.5143v1, algo53.tex, decomposition `e:decomp`, lines 584–588). -/
theorem cutMatrix_toEuclideanLin_eq_sum {J : Finset ι} {A : ι → LeftBlockMatrix L q i}
    {B : ι → RightBlockMatrix L q i} {K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
    (hK : Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L i) K =
      ∑ j ∈ J, A j ⊗ₖ B j)
    (ψ : EuclideanSpace ℂ (Fin L → Fin q)) :
    cutMatrix (toEuclideanLin K ψ) i = ∑ j ∈ J, A j * cutMatrix ψ i * (B j)ᵀ := by
  rw [cutMatrix_toEuclideanLin, hK, Matrix.sum_mulVec]
  ext a b
  simp only [schmidtCoeffMatrix_apply, Finset.sum_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  exact congrFun (congrFun (schmidtCoeffMatrix_kronecker_mulVec_eq (A j) (B j)
    (WithLp.ofLp (Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L i) ψ))) a) b

/-! ### The new set and its support -/

/-- **The error-reduced set** `S' = {A_j s : j ∈ J, s ∈ S}` of algorithm step 4
(arXiv:1307.5143v1, algo53.tex, line 572, and the proof of Claim `c:errorreduction`,
line 588). -/
noncomputable def errorReductionSet (J : Finset ι) (A : ι → LeftBlockMatrix L q i)
    (S : Finset (LeftBlockVector L q i)) : Finset (LeftBlockVector L q i) :=
  open Classical in Finset.image₂ (fun j s ↦ toEuclideanLin (A j) s) J S

/-- Every `A_j s` with `j ∈ J` and `s ∈ S` belongs to the error-reduced set. -/
theorem toEuclideanLin_mem_errorReductionSet {J : Finset ι} {A : ι → LeftBlockMatrix L q i}
    {S : Finset (LeftBlockVector L q i)} {j : ι} (hj : j ∈ J) {s : LeftBlockVector L q i}
    (hs : s ∈ S) : toEuclideanLin (A j) s ∈ errorReductionSet J A S := by
  unfold errorReductionSet
  exact Finset.mem_image₂.mpr ⟨j, hj, s, hs, rfl⟩

/-- **Size of the error-reduced set** (arXiv:1307.5143v1, algo53.tex, line 591):
`|S'| ≤ |J| |S|`. -/
theorem card_errorReductionSet_le (J : Finset ι) (A : ι → LeftBlockMatrix L q i)
    (S : Finset (LeftBlockVector L q i)) :
    (errorReductionSet J A S).card ≤ J.card * S.card := by
  unfold errorReductionSet
  exact Finset.card_image₂_le _ _ _

/-- `A_j` maps `Span(S)` into `Span(S')` for every `j ∈ J`. -/
theorem toEuclideanLin_mem_span_errorReductionSet {J : Finset ι}
    {A : ι → LeftBlockMatrix L q i} {S : Finset (LeftBlockVector L q i)} {j : ι} (hj : j ∈ J)
    {w : LeftBlockVector L q i} (hw : w ∈ Submodule.span ℂ (S : Set (LeftBlockVector L q i))) :
    toEuclideanLin (A j) w ∈
      Submodule.span ℂ (errorReductionSet J A S : Set (LeftBlockVector L q i)) := by
  have h := Submodule.mem_map_of_mem (f := toEuclideanLin (A j)) hw
  rw [Submodule.map_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨s, hs, rfl⟩
  exact toEuclideanLin_mem_errorReductionSet hj hs

/-- **The support survives the error reduction** (arXiv:1307.5143v1, algo53.tex, lines
588–589). If `K = ∑_{j ∈ J} A_j ⊗ B_j` across the cut after `i` sites and
`ψ ∈ Span(S) ⊗ H_R`, then `K ψ ∈ Span(S') ⊗ H_R` for `S' = {A_j s : j ∈ J, s ∈ S}`. -/
theorem toEuclideanLin_mem_leftSupportSubmodule_errorReductionSet {J : Finset ι}
    {A : ι → LeftBlockMatrix L q i} {B : ι → RightBlockMatrix L q i}
    {K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
    (hK : Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L i) K =
      ∑ j ∈ J, A j ⊗ₖ B j)
    {S : Finset (LeftBlockVector L q i)} {ψ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hψ : ψ ∈ leftSupportSubmodule (S : Set (LeftBlockVector L q i))) :
    toEuclideanLin K ψ ∈
      leftSupportSubmodule (errorReductionSet J A S : Set (LeftBlockVector L q i)) := by
  refine mem_leftSupportSubmodule.mpr fun b ↦ ?_
  have hcol : cutColumn (toEuclideanLin K ψ) i b =
      ∑ j ∈ J, ∑ b', B j b b' • toEuclideanLin (A j) (cutColumn ψ i b') := by
    ext a
    rw [cutColumn_apply, cutMatrix_toEuclideanLin_eq_sum hK]
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.transpose_apply,
      WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      toLpLin_apply, cutColumn_apply, mulVec, dotProduct]
    simp only [mul_comm]
  rw [hcol]
  refine Submodule.sum_mem _ fun j hj ↦ Submodule.sum_mem _ fun b' _ ↦
    Submodule.smul_mem _ _ ?_
  exact toEuclideanLin_mem_span_errorReductionSet hj (hψ b')

/-! ### The witness -/

/-- **Overlap under a perturbation.** Let `Γ` be a unit vector and `x` a vector with
`‖x‖ ≥ c > 0` and `|⟨Γ, x⟩| ≥ (1 - ε) ‖x‖`, `ε ≥ 0`. If `‖y - x‖ ≤ η`, then
`|⟨Γ, y⟩| ≥ (1 - ε - 2 η / c) ‖y‖`. This is the step from `A v` to `K v` in the proof of Claim
`c:errorreduction` (arXiv:1307.5143v1, algo53.tex, line 589), with the lower bound `c` on
`‖A v‖` that the step needs; see the module docstring. -/
theorem mul_norm_le_norm_inner_of_norm_sub_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {Γ x y : E} {ε η c : ℝ} (hΓ : ‖Γ‖ = 1) (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (hc : 0 < c) (hcx : c ≤ ‖x‖) (hx : (1 - ε) * ‖x‖ ≤ ‖⟪Γ, x⟫_ℂ‖) (hxy : ‖y - x‖ ≤ η) :
    (1 - ε - 2 * η / c) * ‖y‖ ≤ ‖⟪Γ, y⟫_ℂ‖ := by
  have hin : ‖⟪Γ, x⟫_ℂ‖ - η ≤ ‖⟪Γ, y⟫_ℂ‖ := by
    have h1 : ‖⟪Γ, y - x⟫_ℂ‖ ≤ η := by
      refine (norm_inner_le_norm (𝕜 := ℂ) Γ (y - x)).trans ?_
      rw [hΓ, one_mul]
      exact hxy
    have h2 : ⟪Γ, x⟫_ℂ = ⟪Γ, y⟫_ℂ - ⟪Γ, y - x⟫_ℂ := by
      rw [inner_sub_right]
      ring
    have h3 := norm_sub_le ⟪Γ, y⟫_ℂ ⟪Γ, y - x⟫_ℂ
    rw [← h2] at h3
    linarith
  have hy : ‖y‖ ≤ ‖x‖ + η := by
    have e : x + (y - x) = y := by abel
    have h := norm_add_le x (y - x)
    rw [e] at h
    linarith
  rcases le_or_gt (1 - ε - 2 * η / c) 0 with ht | ht
  · have h0 := mul_le_mul_of_nonneg_right ht (norm_nonneg y)
    rw [zero_mul] at h0
    exact h0.trans (norm_nonneg _)
  · have hq : 2 * η ≤ 2 * η / c * ‖x‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hc]
      nlinarith [mul_le_mul_of_nonneg_left hcx hη]
    have hq2 : 0 ≤ 2 * η / c * η := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hy ht.le, mul_nonneg hε hη]

/-- **The witness of the error-reduced set** (arXiv:1307.5143v1, algo53.tex, line 589). Let
`K = ∑_{j ∈ J} A_j ⊗ B_j` across the cut after `i` sites, let `v` be a unit vector in
`Span(S) ⊗ H_R` and let `A₀` satisfy `‖A₀ v‖ ≥ c > 0` and `|⟨Γ, A₀ v⟩| ≥ (1 - ε) ‖A₀ v‖`.
If `‖K - A₀‖ ≤ η < c`, then `S' = {A_j s}` is `(i, ε + 2 η / c)`-viable for the unit vector
`Γ`, with witness `K v / ‖K v‖`. -/
theorem isViable_errorReductionSet_of_witness {J : Finset ι} {A : ι → LeftBlockMatrix L q i}
    {B : ι → RightBlockMatrix L q i} {K A₀ : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hΓ : ‖Γ‖ = 1)
    (hK : Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L i) K =
      ∑ j ∈ J, A j ⊗ₖ B j)
    {S : Finset (LeftBlockVector L q i)} {v : EuclideanSpace ℂ (Fin L → Fin q)} (hv1 : ‖v‖ = 1)
    (hvS : v ∈ leftSupportSubmodule (S : Set (LeftBlockVector L q i))) {ε η c : ℝ}
    (hε : 0 ≤ ε) (hc : 0 < c) (hcv : c ≤ ‖toEuclideanLin A₀ v‖)
    (hA₀v : (1 - ε) * ‖toEuclideanLin A₀ v‖ ≤ ‖⟪Γ, toEuclideanLin A₀ v⟫_ℂ‖)
    (hKA : ‖K - A₀‖ ≤ η) (hηc : η < c) :
    IsViable Γ (ε + 2 * η / c) (errorReductionSet J A S : Set (LeftBlockVector L q i)) := by
  set x := toEuclideanLin A₀ v with hx
  set y := toEuclideanLin K v with hy
  have hxy : ‖y - x‖ ≤ η := by
    have h1 : y - x = toEuclideanLin (K - A₀) v := by
      rw [hx, hy, map_sub, LinearMap.sub_apply]
    rw [h1]
    calc ‖toEuclideanLin (K - A₀) v‖ ≤ ‖K - A₀‖ * ‖v‖ := Entropy.norm_toEuclideanLin_le _ _
      _ ≤ η := by rw [hv1, mul_one]; exact hKA
  have hη0 : 0 ≤ η := (norm_nonneg _).trans hKA
  have hy0 : 0 < ‖y‖ := by
    have e : y - (y - x) = x := by abel
    have h2 := norm_sub_le y (y - x)
    rw [e] at h2
    linarith
  have habs := mul_norm_le_norm_inner_of_norm_sub_le hΓ hε hη0 hc hcv hA₀v hxy
  refine ⟨((‖y‖⁻¹ : ℝ) : ℂ) • y, ?_, ?_, ?_⟩
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hy0,
      inv_mul_cancel₀ hy0.ne']
  · rw [norm_inner_symm, inner_smul_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_inv, abs_of_pos hy0, inv_mul_eq_div, le_div_iff₀ hy0]
    calc (1 - (ε + 2 * η / c)) * ‖y‖ = (1 - ε - 2 * η / c) * ‖y‖ := by ring
      _ ≤ ‖⟪Γ, y⟫_ℂ‖ := habs
  · exact (leftSupportSubmodule _).smul_mem _
      (toEuclideanLin_mem_leftSupportSubmodule_errorReductionSet hK hvS)

/-- An operator that is Hermitian and fixes the unit vector `Γ` does not shrink the overlap with
`Γ`: `‖A₀ v‖ ≥ |⟨v, Γ⟩|`. The source's operator `A` has these properties (arXiv:1307.5143v1,
algo53.tex, line 602). -/
theorem norm_inner_le_norm_toEuclideanLin_of_fixed {m : Type*} [Fintype m] [DecidableEq m]
    {A₀ : Matrix m m ℂ} (hA₀ : A₀.IsHermitian) {Γ : EuclideanSpace ℂ m} (hΓ : ‖Γ‖ = 1)
    (hfix : toEuclideanLin A₀ Γ = Γ) (v : EuclideanSpace ℂ m) :
    ‖⟪v, Γ⟫_ℂ‖ ≤ ‖toEuclideanLin A₀ v‖ := by
  have hsym := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA₀
  have h1 : ⟪Γ, toEuclideanLin A₀ v⟫_ℂ = ⟪Γ, v⟫_ℂ := by
    rw [← hsym Γ v, hfix]
  calc ‖⟪v, Γ⟫_ℂ‖ = ‖⟪Γ, toEuclideanLin A₀ v⟫_ℂ‖ := by rw [h1, norm_inner_symm]
    _ ≤ ‖Γ‖ * ‖toEuclideanLin A₀ v‖ := norm_inner_le_norm (𝕜 := ℂ) _ _
    _ = ‖toEuclideanLin A₀ v‖ := by rw [hΓ, one_mul]

/-- **Claim `c:errorreduction`, viability** (arXiv:1307.5143v1, algo53.tex, lines 580–589). Let
`Γ` be a unit vector, `A₀` a Hermitian operator with `A₀ Γ = Γ` and `K = ∑_{j ∈ J} A_j ⊗ B_j`
across the cut after `i` sites. Let `S` be `(i, 1/2)`-viable for `Γ` and suppose that every
witness `v` of `S` has `|⟨Γ, A₀ v⟩| ≥ (1 - δ) ‖A₀ v‖`, as the bound `e:cutdown` gives for the
source's operator `A`. If `‖K - A₀‖ ≤ η < 1/2`, then `S' = {A_j s}` is `(i, δ + 4 η)`-viable;
the source states `(i, 2 δ)` for `η = δ`, see the module docstring. -/
theorem IsViable.errorReduction {J : Finset ι} {A : ι → LeftBlockMatrix L q i}
    {B : ι → RightBlockMatrix L q i} {K A₀ : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {S : Finset (LeftBlockVector L q i)}
    (hS : IsViable Γ (1 / 2) (S : Set (LeftBlockVector L q i))) (hΓ : ‖Γ‖ = 1)
    (hK : Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L i) K =
      ∑ j ∈ J, A j ⊗ₖ B j)
    (hA₀ : A₀.IsHermitian) (hfix : toEuclideanLin A₀ Γ = Γ) {δ η : ℝ} (hδ : 0 ≤ δ)
    (hcut : ∀ v : EuclideanSpace ℂ (Fin L → Fin q), ‖v‖ = 1 →
      v ∈ leftSupportSubmodule (S : Set (LeftBlockVector L q i)) → 1 / 2 ≤ ‖⟪v, Γ⟫_ℂ‖ →
        (1 - δ) * ‖toEuclideanLin A₀ v‖ ≤ ‖⟪Γ, toEuclideanLin A₀ v⟫_ℂ‖)
    (hKA : ‖K - A₀‖ ≤ η) (hη : η < 1 / 2) :
    IsViable Γ (δ + 4 * η) (errorReductionSet J A S : Set (LeftBlockVector L q i)) := by
  obtain ⟨v, hv1, hvΓ, hvS⟩ := hS
  have hvΓ' : 1 / 2 ≤ ‖⟪v, Γ⟫_ℂ‖ := by linarith
  have hcv : 1 / 2 ≤ ‖toEuclideanLin A₀ v‖ :=
    hvΓ'.trans (norm_inner_le_norm_toEuclideanLin_of_fixed hA₀ hΓ hfix v)
  have h := isViable_errorReductionSet_of_witness hΓ hK hv1 hvS hδ (by norm_num) hcv
    (hcut v hv1 hvS hvΓ') hKA hη
  have e : δ + 2 * η / (1 / 2) = δ + 4 * η := by ring
  rwa [e] at h

/-- **Claim `c:errorreduction`** (arXiv:1307.5143v1, algo53.tex, lines 580–591), deterministic
part, under the hypotheses of `IsViable.errorReduction`. If `S` is `(i, s, b, 1/2)`-viable and
every `A_j t` with `j ∈ J`, `t ∈ S` is a matrix product state of bond dimension at most `b'`,
then `S'` is `(i, |J| s, b', δ + 4 η)`-viable. The bound `b'` stands for the source's bond
dimension of `A_j t` (line 591); a bound in terms of the bond dimensions of `A_j` and `t` needs
matrix product operators on the first `i` sites, which this file does not define. -/
theorem IsViableMPS.errorReduction {J : Finset ι} {A : ι → LeftBlockMatrix L q i}
    {B : ι → RightBlockMatrix L q i} {K A₀ : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {s b b' : ℕ} {S : Finset (LeftBlockVector L q i)}
    (hS : IsViableMPS Γ s b (1 / 2) S) (hΓ : ‖Γ‖ = 1)
    (hK : Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L i) K =
      ∑ j ∈ J, A j ⊗ₖ B j)
    (hA₀ : A₀.IsHermitian) (hfix : toEuclideanLin A₀ Γ = Γ) {δ η : ℝ} (hδ : 0 ≤ δ)
    (hcut : ∀ v : EuclideanSpace ℂ (Fin L → Fin q), ‖v‖ = 1 →
      v ∈ leftSupportSubmodule (S : Set (LeftBlockVector L q i)) → 1 / 2 ≤ ‖⟪v, Γ⟫_ℂ‖ →
        (1 - δ) * ‖toEuclideanLin A₀ v‖ ≤ ‖⟪Γ, toEuclideanLin A₀ v⟫_ℂ‖)
    (hKA : ‖K - A₀‖ ≤ η) (hη : η < 1 / 2)
    (hmps : ∀ j ∈ J, ∀ t ∈ S, IsLeftOpenMPS b' (toEuclideanLin (A j) t)) :
    IsViableMPS Γ (J.card * s) b' (δ + 4 * η) (errorReductionSet J A S) := by
  obtain ⟨hs, -, hv⟩ := hS
  refine ⟨(card_errorReductionSet_le J A S).trans (Nat.mul_le_mul_left _ hs), fun w hw ↦ ?_,
    hv.errorReduction hΓ hK hA₀ hfix hδ hcut hKA hη⟩
  unfold errorReductionSet at hw
  obtain ⟨j, hj, t, ht, rfl⟩ := Finset.mem_image₂.mp hw
  exact hmps j hj t ht

/-- A sampled operator close to the ground projection improves a half-viable set.
LVV, arXiv:1307.5143v1, Claim `c:errorreduction`, lines 580–592. The operator-norm
estimate supplies the overlap bound; no separate condition on its output witness is needed. -/
theorem IsViable.errorReduction_of_norm_sub_groundProjection_le
    {J : Finset ι} {A : ι → LeftBlockMatrix L q i}
    {B : ι → RightBlockMatrix L q i}
    {K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {S : Finset (LeftBlockVector L q i)}
    (hS : IsViable Γ (1 / 2) (S : Set (LeftBlockVector L q i))) (hΓ : ‖Γ‖ = 1)
    (hK : Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L i) K =
      ∑ j ∈ J, A j ⊗ₖ B j)
    {η : ℝ} (hKP : ‖K - vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ))‖ ≤ η)
    (hη : η < 1 / 2) :
    IsViable Γ (4 * η) (errorReductionSet J A S : Set (LeftBlockVector L q i)) := by
  obtain ⟨v, hv1, hvΓ, hvS⟩ := hS
  have hcv : (1 / 2 : ℝ) ≤
      ‖toEuclideanLin (vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ))) v‖ := by
    rw [toEuclideanLin_vecMulVec_star_self_apply, norm_smul, hΓ, mul_one, norm_inner_symm]
    linarith
  have hPv : (1 - (0 : ℝ)) *
      ‖toEuclideanLin (vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ))) v‖ ≤
      ‖⟪Γ, toEuclideanLin (vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ))) v⟫_ℂ‖ := by
    simp [toEuclideanLin_vecMulVec_star_self_apply, inner_smul_right,
      inner_self_eq_norm_sq_to_K, hΓ, norm_smul]
  have h := isViable_errorReductionSet_of_witness hΓ hK hv1 hvS (by norm_num)
    (by norm_num) hcv hPv hKP hη
  convert h using 1
  ring

/-- The deterministic LVV error-reduction step with derived MPS bond bounds.
LVV, arXiv:1307.5143v1, `algo53.tex`, Claim `c:errorreduction`, lines 580–592.
The hypotheses are the product decomposition, operator-Schmidt-rank bounds and approximation
estimate that the sampling construction must supply; the witness and output MPS bounds
are conclusions. This does not assert existence of a sampled operator. -/
theorem IsViableMPS.errorReduction_of_norm_sub_groundProjection_le
    {J : Finset ι} {A : ι → LeftBlockMatrix L q i}
    {B : ι → RightBlockMatrix L q i}
    {K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {s b D : ℕ}
    {S : Finset (LeftBlockVector L q i)} (hi : i ≤ L)
    (hS : IsViableMPS Γ s b (1 / 2) S) (hΓ : ‖Γ‖ = 1)
    (hK : Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L i) K =
      ∑ j ∈ J, A j ⊗ₖ B j)
    (hA : ∀ j ∈ J, ∀ k : ℕ, 0 < k → k < i →
      operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin i ↦ q) (leftBlock i k)
        ((A j).submatrix leftConfigOfFin leftConfigOfFin)) ≤ D)
    {η : ℝ} (hKP : ‖K - vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ))‖ ≤ η)
    (hη : η < 1 / 2) :
    IsViableMPS Γ (J.card * s) (D * max 1 b) (4 * η) (errorReductionSet J A S) := by
  refine ⟨(card_errorReductionSet_le J A S).trans (Nat.mul_le_mul_left _ hS.1), ?_,
    hS.2.2.errorReduction_of_norm_sub_groundProjection_le hΓ hK hKP hη⟩
  intro w hw
  unfold errorReductionSet at hw
  obtain ⟨j, hj, t, ht, rfl⟩ := Finset.mem_image₂.mp hw
  exact IsLeftOpenMPS.toEuclideanLin hi (hS.2.1 t ht) (A j) (hA j hj)

end TNLean.MPS.AreaLaw
