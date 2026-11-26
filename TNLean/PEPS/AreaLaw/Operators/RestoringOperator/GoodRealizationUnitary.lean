/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.Isometry.PolarUnitaryCorrection
import QICLean.ManyBody.Sites.PlacedConfiguration
import QICLean.Analysis.Norm.MatrixKroneckerContraction

/-!
# From a good clock realization to a local unitary

In the proof of the amplification proposition, one clock realization is
selected on which the excited component, the omitted events and the radius
truncation are all small. This module carries out the deterministic steps
that follow that selection. The truncated product `L'` applied to the
restoring vector `ζ = R₀ φ` has norm at most `1 + 3ε`, and its adjoint almost
fixes every vector fixed by the adjoint of the retained product. An adjoint
error `a` and a direct norm bound `1 + b` for a square operator `R'` between
unit vectors `φ` and `η` bound `‖R' φ - η‖²` by `2a + 2b + b²`. Finally the
unitary polar factor of a local `R'`, tensored with the identity on the
remaining systems, moves `φ` to within `a + √(2a + 2b + b²)` of `η`.

All vectors may be entangled with the remaining systems, and no invertibility
of `R'` is assumed. The probabilistic selection of the realization, the
restoring operator and the final entropy comparison are not formalized here.

## Main statements

* `norm_truncated_restoring_le`: the first estimate of
  `eq:amplification-before-polar`.
* `norm_truncated_adjoint_sub_le`: the second estimate of
  `eq:amplification-before-polar`.
* `norm_sub_sq_le_of_adjoint_error`: `eq:amplification-direct-error`.
* `exists_unitary_kronecker_sub_le`: `eq:amplification-unitary-error`.
* `exists_unitary_kronecker_sub_le_of_good_realization`: the three steps
  composed, with `b = 3ε`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `09-amplification.tex`, lines 501–545, equations
  `eq:amplification-before-polar`, `eq:amplification-direct-error` and
  `eq:amplification-unitary-error`.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.

## The local unitary of a good realization, on a set of sites

The deterministic steps after the choice of a good clock realization produce a unitary
`U` on a local factor `n` of a product `n × m` with `‖(U ⊗ 1) φ - η‖` small. On a
finite set of sites `ι` with local dimension `q`, the local factor is the set of
configurations of a region `S`. This module restates the result in that form: if the
restoring operator `R₀` and the truncated product `L'` act on `S`, the unitary acts on
`S` as well.

### Main statements

* `TNLean.PEPS.AreaLaw.exists_supported_unitary_of_good_realization`: the unitary of
  `eq:amplification-unitary-error`, acting on `S`.

The entropy comparison for a unitary acting away from both regions,
`ManyBody.regionMutualInformation_le_inv_pow_of_supported_unitary`, does not depend on the
geometry of the sites and is stated in `QICLean.ManyBody.Entropy.MutualInformationPerturbation`.

### References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  `09-amplification.tex`, lines 501–545, equations `eq:amplification-before-polar`,
  `eq:amplification-direct-error` and `eq:amplification-unitary-error`: the operator `R'`
  is supported on `s'` and `N_{2r}(S₀)`, and its polar unitary is tensored with the
  identity elsewhere.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open ManyBody (toEuclideanCLM_conjTranspose)
open Matrix (exists_unitary_kronecker_sub_le)

section

open Matrix
open scoped Kronecker

namespace TNLean.PEPS.AreaLaw

section SameSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "L" => toEuclideanCLM (n := ι) (𝕜 := ℂ)

/-- **First estimate of `eq:amplification-before-polar`.** Let `g` be the ground
component of the restoring vector `ζ`, fixed by the full product `D` and of norm at
most one. If the excited component, the omitted events and the radius truncation
contribute at most `ε` each on the chosen realization, with `‖ζ‖ ≤ M₀`, then the
truncated product `L'` satisfies `‖L' ζ‖ ≤ 1 + 3ε`.
Source: `09-amplification.tex`, lines 493–508, `eq:amplification-good-trajectory`
and `eq:amplification-before-polar`. -/
theorem norm_truncated_restoring_le {D Dret L' : Matrix ι ι ℂ}
    {ζ g : EuclideanSpace ℂ ι} {M₀ ε : ℝ}
    (hg : L D g = g) (hgn : ‖g‖ ≤ 1)
    (hexc : ‖L D (ζ - g)‖ ≤ ε) (hret : ‖L (D - Dret) ζ‖ ≤ ε)
    (htrunc : M₀ * ‖L (Dret - L')‖ ≤ ε) (hζ : ‖ζ‖ ≤ M₀) :
    ‖L L' ζ‖ ≤ 1 + 3 * ε := by
  have htr : ‖L (Dret - L') ζ‖ ≤ ε :=
    calc ‖L (Dret - L') ζ‖ ≤ ‖L (Dret - L')‖ * ‖ζ‖ := (L (Dret - L')).le_opNorm ζ
      _ ≤ ‖L (Dret - L')‖ * M₀ := mul_le_mul_of_nonneg_left hζ (norm_nonneg _)
      _ ≤ ε := by rw [mul_comm]; exact htrunc
  have hsplit : L L' ζ =
      g + L D (ζ - g) - L (D - Dret) ζ - L (Dret - L') ζ := by
    simp only [map_sub, _root_.sub_apply, hg]
    abel
  rw [hsplit]
  calc ‖g + L D (ζ - g) - L (D - Dret) ζ - L (Dret - L') ζ‖
      ≤ ‖g‖ + ‖L D (ζ - g)‖ + ‖L (D - Dret) ζ‖ + ‖L (Dret - L') ζ‖ :=
        (norm_sub_le _ _).trans (add_le_add_left
          ((norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _)) _)
    _ ≤ 1 + 3 * ε := by linarith only [hgn, hexc, hret, htr]

/-- **Second estimate of `eq:amplification-before-polar`.** If the adjoint of
the retained product fixes a vector `w` of norm at most one, then the adjoint of
the truncated product moves `w` by at most `ε`, provided `M₀ ≥ 1`.
Source: `09-amplification.tex`, lines 501–508. -/
theorem norm_truncated_adjoint_sub_le {Dret L' : Matrix ι ι ℂ}
    {w : EuclideanSpace ℂ ι} {M₀ ε : ℝ}
    (hfix : L Dretᴴ w = w) (hw : ‖w‖ ≤ 1) (hM₀ : 1 ≤ M₀)
    (htrunc : M₀ * ‖L (Dret - L')‖ ≤ ε) :
    ‖L L'ᴴ w - w‖ ≤ ε := by
  have hdiff : L L'ᴴ w - w = L (L' - Dret)ᴴ w := by
    simp only [conjTranspose_sub, map_sub, _root_.sub_apply, hfix]
  have hnorm : ‖L (L' - Dret)ᴴ‖ = ‖L (Dret - L')‖ := by
    rw [toEuclideanCLM_conjTranspose, ContinuousLinearMap.adjoint.norm_map, ← norm_neg,
      ← map_neg, neg_sub]
  have hle : ‖L (Dret - L')‖ ≤ ε :=
    (le_mul_of_one_le_left (norm_nonneg _) hM₀).trans htrunc
  rw [hdiff]
  calc ‖L (L' - Dret)ᴴ w‖ ≤ ‖L (L' - Dret)ᴴ‖ * ‖w‖ := (L (L' - Dret)ᴴ).le_opNorm w
    _ ≤ ‖L (L' - Dret)ᴴ‖ * 1 := mul_le_mul_of_nonneg_left hw (norm_nonneg _)
    _ ≤ ε := by rw [mul_one, hnorm]; exact hle

end SameSpace

section Spectator

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {m : Type*} [Fintype m] [DecidableEq m]

local notation "L₂" => toEuclideanCLM (n := n × m) (𝕜 := ℂ)

/-- **The deterministic steps after the choice of a good realization**
(`eq:amplification-before-polar` through `eq:amplification-unitary-error`). Let
`R₀` and `L'` be local operators on `n`, with `M₀ ≥ 1` bounding the restoring vector
`ζ = (R₀ ⊗ I) φ`. Suppose the full product `D` fixes the ground component `g` of `ζ`,
`‖g‖ ≤ 1`, and on the chosen realization the excited component, the omitted events
and `M₀` times the truncation error are at most `ε`. If the adjoint error of
`R' = L' R₀` is at most `a`, then some unitary `U` on `n` alone satisfies
`‖(U ⊗ I) φ - η‖ ≤ a + √(2a + 6ε + 9ε²)`.
Source: `09-amplification.tex`, lines 493–545. -/
theorem exists_unitary_kronecker_sub_le_of_good_realization
    (R₀ L' : Matrix n n ℂ) {D Dret : Matrix (n × m) (n × m) ℂ}
    {φ η g : EuclideanSpace ℂ (n × m)} (hφ : ‖φ‖ = 1) (hη : ‖η‖ = 1)
    {M₀ ε a : ℝ}
    (hζ : ‖L₂ (R₀ ⊗ₖ (1 : Matrix m m ℂ)) φ‖ ≤ M₀)
    (hg : L₂ D g = g) (hgn : ‖g‖ ≤ 1)
    (hexc : ‖L₂ D (L₂ (R₀ ⊗ₖ (1 : Matrix m m ℂ)) φ - g)‖ ≤ ε)
    (hret : ‖L₂ (D - Dret) (L₂ (R₀ ⊗ₖ (1 : Matrix m m ℂ)) φ)‖ ≤ ε)
    (htrunc : M₀ * ‖L₂ (Dret - L' ⊗ₖ (1 : Matrix m m ℂ))‖ ≤ ε)
    (hadj : ‖L₂ ((L' * R₀) ⊗ₖ (1 : Matrix m m ℂ))ᴴ η - φ‖ ≤ a) :
    ∃ U : unitaryGroup n ℂ,
      ‖L₂ ((U : Matrix n n ℂ) ⊗ₖ (1 : Matrix m m ℂ)) φ - η‖ ≤
        a + √(2 * a + 6 * ε + 9 * ε ^ 2) := by
  have hdir := norm_truncated_restoring_le hg hgn hexc hret htrunc hζ
  have hprod : L₂ ((L' * R₀) ⊗ₖ (1 : Matrix m m ℂ)) φ =
      L₂ (L' ⊗ₖ (1 : Matrix m m ℂ)) (L₂ (R₀ ⊗ₖ (1 : Matrix m m ℂ)) φ) := by
    rw [← mul_apply_eq_comp, ← map_mul, ← mul_kronecker_mul, one_mul]
  rw [← hprod] at hdir
  obtain ⟨U, hU⟩ := exists_unitary_kronecker_sub_le (L' * R₀) hφ hη hadj hdir
  refine ⟨U, hU.trans_eq ?_⟩
  congr 2
  ring

end Spectator

end TNLean.PEPS.AreaLaw

end

section

open Matrix QuantumCircuit
open scoped Kronecker Matrix.Norms.L2Operator

namespace TNLean.PEPS.AreaLaw

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}

/-- **The local unitary of a good realization, on a set of sites.** Let `R₀` and `L'` act on
a region `S`, and let `D, D_ret` be arbitrary. For unit vectors `φ, η`, suppose the ground
component `g` of `ζ = R₀ φ` is fixed by `D` with `‖g‖ ≤ 1`, `‖ζ‖ ≤ M₀`, the excited
component, the omitted events and `M₀` times the truncation error are at most `ε`, and the
adjoint error of `L' R₀` is at most `a`. Then some unitary `U` acting on `S` satisfies
`‖U φ - η‖ ≤ a + √(2a + 6ε + 9ε²)`.
Source: `09-amplification.tex`, lines 501–545. -/
theorem exists_supported_unitary_of_good_realization (S : Finset ι)
    {R₀ L' D Dret : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hR₀ : R₀ ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) S)
    (hL : L' ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) S)
    {φ η g : (ι → Fin q) → ℂ} (hφ : ‖WithLp.toLp 2 φ‖ = 1) (hη : ‖WithLp.toLp 2 η‖ = 1)
    {M₀ ε a : ℝ} (hζ : ‖WithLp.toLp 2 (R₀ *ᵥ φ)‖ ≤ M₀) (hg : D *ᵥ g = g)
    (hgn : ‖WithLp.toLp 2 g‖ ≤ 1) (hexc : ‖WithLp.toLp 2 (D *ᵥ (R₀ *ᵥ φ - g))‖ ≤ ε)
    (hret : ‖WithLp.toLp 2 ((D - Dret) *ᵥ (R₀ *ᵥ φ))‖ ≤ ε) (htrunc : M₀ * ‖Dret - L'‖ ≤ ε)
    (hadj : ‖WithLp.toLp 2 ((L' * R₀)ᴴ *ᵥ η) - WithLp.toLp 2 φ‖ ≤ a) :
    ∃ U : Matrix (ι → Fin q) (ι → Fin q) ℂ, U ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) S ∧
      Uᴴ * U = 1 ∧ ‖WithLp.toLp 2 (U *ᵥ φ) - WithLp.toLp 2 η‖ ≤
        a + √(2 * a + 6 * ε + 9 * ε ^ 2) := by
  set e := ManyBody.cutEquiv (fun _ : ι => Fin q) S with he
  obtain ⟨R', hR'⟩ : ∃ R' : Matrix (S → Fin q) (S → Fin q) ℂ, R₀.submatrix e.symm e.symm =
      R' ⊗ₖ (1 : Matrix ({v // v ∉ S} → Fin q) ({v // v ∉ S} → Fin q) ℂ) := by
    obtain ⟨K, rfl⟩ := ManyBody.exists_eq_place_of_mem_supportedOperators hR₀
    exact ⟨K, ManyBody.cutOperator_place K⟩
  obtain ⟨L'', hL''⟩ : ∃ L'' : Matrix (S → Fin q) (S → Fin q) ℂ, L'.submatrix e.symm e.symm =
      L'' ⊗ₖ (1 : Matrix ({v // v ∉ S} → Fin q) ({v // v ∉ S} → Fin q) ℂ) := by
    obtain ⟨K, rfl⟩ := ManyBody.exists_eq_place_of_mem_supportedOperators hL
    exact ⟨K, ManyBody.cutOperator_place K⟩
  -- Transport of vectors and matrices to the coordinates `S × Sᶜ`.
  have hvec (A : Matrix (ι → Fin q) (ι → Fin q) ℂ) (v : (ι → Fin q) → ℂ) :
      A.submatrix e.symm e.symm *ᵥ (v ∘ e.symm) = (A *ᵥ v) ∘ e.symm := by
    rw [submatrix_mulVec_equiv, Equiv.symm_symm]
    congr 2
    ext x
    simp
  have hnorm (v : (ι → Fin q) → ℂ) : ‖WithLp.toLp 2 (v ∘ e.symm)‖ = ‖WithLp.toLp 2 v‖ :=
    EuclideanSpace.norm_toLp_comp_equiv e.symm v
  have hcomp (f h : (ι → Fin q) → ℂ) : (f - h) ∘ e.symm = f ∘ e.symm - h ∘ e.symm := rfl
  have hsubS (A B : Matrix (ι → Fin q) (ι → Fin q) ℂ) :
      A.submatrix e.symm e.symm - B.submatrix e.symm e.symm = (A - B).submatrix e.symm e.symm :=
    rfl
  have hR'e : R₀.submatrix e.symm e.symm =
      R' ⊗ₖ (1 : Matrix ({v // v ∉ S} → Fin q) ({v // v ∉ S} → Fin q) ℂ) :=
    hR'
  have hL''e : L'.submatrix e.symm e.symm =
      L'' ⊗ₖ (1 : Matrix ({v // v ∉ S} → Fin q) ({v // v ∉ S} → Fin q) ℂ) := hL''
  have hRφ : (R' ⊗ₖ (1 : Matrix ({v // v ∉ S} → Fin q) ({v // v ∉ S} → Fin q) ℂ)) *ᵥ (φ ∘ e.symm) =
      (R₀ *ᵥ φ) ∘ e.symm := by rw [← hR'e, hvec]
  have hprod : (L'' * R') ⊗ₖ (1 : Matrix ({v // v ∉ S} → Fin q) ({v // v ∉ S} → Fin q) ℂ) =
      (L' * R₀).submatrix e.symm e.symm := by
    rw [← submatrix_mul_equiv _ _ _ e.symm, hR'e, hL''e, ← mul_kronecker_mul, Matrix.one_mul]
  obtain ⟨U, hU⟩ := exists_unitary_kronecker_sub_le_of_good_realization
    (φ := WithLp.toLp 2 (φ ∘ e.symm)) (η := WithLp.toLp 2 (η ∘ e.symm))
    (g := WithLp.toLp 2 (g ∘ e.symm)) (D := D.submatrix e.symm e.symm)
    (Dret := Dret.submatrix e.symm e.symm) (M₀ := M₀) (ε := ε) (a := a) R' L''
    (by rw [hnorm]; exact hφ) (by rw [hnorm]; exact hη)
    (by rw [toEuclideanCLM_toLp, hRφ, hnorm]; exact hζ)
    (by rw [toEuclideanCLM_toLp, hvec, hg])
    (by rw [hnorm]; exact hgn)
    (by
      have e1 : toEuclideanCLM (𝕜 := ℂ) (D.submatrix e.symm e.symm) (toEuclideanCLM (𝕜 := ℂ)
          (R' ⊗ₖ (1 : Matrix ({v // v ∉ S} → Fin q) ({v // v ∉ S} → Fin q) ℂ))
            (WithLp.toLp 2 (φ ∘ e.symm)) -
            WithLp.toLp 2 (g ∘ e.symm)) = WithLp.toLp 2 ((D *ᵥ (R₀ *ᵥ φ - g)) ∘ e.symm) := by
        apply WithLp.ofLp_injective 2
        simp only [ofLp_toEuclideanCLM, WithLp.ofLp_sub, hRφ, ← hcomp, hvec]
      rw [e1, hnorm]
      exact hexc)
    (by
      have e1 : toEuclideanCLM (𝕜 := ℂ) (D.submatrix e.symm e.symm - Dret.submatrix e.symm e.symm)
          (toEuclideanCLM (𝕜 := ℂ)
            (R' ⊗ₖ (1 : Matrix ({v // v ∉ S} → Fin q) ({v // v ∉ S} → Fin q) ℂ))
            (WithLp.toLp 2 (φ ∘ e.symm))) =
          WithLp.toLp 2 (((D - Dret) *ᵥ (R₀ *ᵥ φ)) ∘ e.symm) := by
        apply WithLp.ofLp_injective 2
        simp only [ofLp_toEuclideanCLM, hRφ, hsubS, hvec]
      rw [e1, hnorm]
      exact hret)
    (by
      rw [← hL''e, hsubS, l2_opNorm_toEuclideanCLM]
      exact (mul_le_mul_of_nonneg_left (norm_submatrix_equiv_le _ _)
        ((norm_nonneg _).trans hζ)).trans htrunc)
    (by
      rw [hprod, conjTranspose_submatrix, toEuclideanCLM_toLp, hvec, ← WithLp.toLp_sub,
        ← hcomp, hnorm, WithLp.toLp_sub]
      exact hadj)
  have hu : (U : Matrix (S → Fin q) (S → Fin q) ℂ)ᴴ * U = 1 := by
    rw [← star_eq_conjTranspose]
    exact Unitary.coe_star_mul_self U
  refine ⟨((U : Matrix (S → Fin q) (S → Fin q) ℂ) ⊗ₖ
    (1 : Matrix ({v // v ∉ S} → Fin q) ({v // v ∉ S} → Fin q) ℂ)).submatrix e e,
    by
      have h := ManyBody.place_mem_supportedOperators (X := fun _ : ι ↦ Fin q) (D := S)
        (U : Matrix (S → Fin q) (S → Fin q) ℂ)
      rwa [ManyBody.place, Matrix.reindex_apply, Equiv.symm_symm, ← he] at h, ?_, ?_⟩
  · rw [conjTranspose_submatrix, submatrix_mul_equiv _ _ _ e, conjTranspose_kronecker,
      ← mul_kronecker_mul, hu, conjTranspose_one, Matrix.one_mul, one_kronecker_one,
      submatrix_one_equiv]
  · have hUe : (((U : Matrix (S → Fin q) (S → Fin q) ℂ) ⊗ₖ
        (1 : Matrix ({v // v ∉ S} → Fin q) ({v // v ∉ S} → Fin q) ℂ)).submatrix e e).submatrix
          e.symm e.symm =
          (U : Matrix (S → Fin q) (S → Fin q) ℂ) ⊗ₖ
            (1 : Matrix ({v // v ∉ S} → Fin q) ({v // v ∉ S} → Fin q) ℂ) := by
      simp
    rw [← WithLp.toLp_sub, ← hnorm, hcomp, ← hvec, hUe, WithLp.toLp_sub]
    simpa only [toEuclideanCLM_toLp] using hU

end TNLean.PEPS.AreaLaw

end
