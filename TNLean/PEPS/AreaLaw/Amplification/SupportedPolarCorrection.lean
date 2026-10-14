/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Amplification.GoodRealizationUnitary
import TNLean.PEPS.Approximation.SheetSplitting
import TNLean.Circuit.SiteEmbedding
import TNLean.Algebra.MatrixKroneckerContraction
import TNLean.PEPS.AreaLaw.Amplification.EntropyComparison

/-!
# The local unitary of a good realization, on a set of sites

The deterministic steps after the choice of a good clock realization produce a unitary
`U` on a local factor `n` of a product `n × m` with `‖(U ⊗ 1) φ - η‖` small. On a
finite set of sites `ι` with local dimension `q`, the local factor is the set of
configurations of a region `S`. This module restates the result in that form: if the
restoring operator `R₀` and the truncated product `L'` act on `S`, the unitary acts on
`S` as well.

## Main statements

* `QuantumCircuit.embedOp_val_eq_kronecker_one_submatrix`: a local matrix placed on `S`
  is `K ⊗ 1` in the coordinates of `S` and its complement.
* `TNLean.PEPS.AreaLaw.exists_supported_unitary_of_good_realization`: the unitary of
  `eq:amplification-unitary-error`, acting on `S`.
* `TNLean.PEPS.AreaLaw.mutualInformation_le_inv_pow_of_supported_unitary`: the entropy
  comparison of `eq:amplification-output` for a unitary acting away from both regions.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  `09-amplification.tex`, lines 501–545, equations `eq:amplification-before-polar`,
  `eq:amplification-direct-error` and `eq:amplification-unitary-error`: the operator `R'`
  is supported on `s'` and `N_{2r}(S₀)`, and its polar unitary is tensored with the
  identity elsewhere.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open Matrix QuantumCircuit
open scoped Kronecker Matrix.Norms.L2Operator

namespace QuantumCircuit

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}

/-- A local matrix placed on a region `S` is `K ⊗ 1` in the coordinates of `S` and its
complement. -/
theorem embedOp_val_eq_kronecker_one_submatrix (S : Finset ι)
    (K : Matrix (S → Fin q) (S → Fin q) ℂ) :
    embedOp (fun x : S => x.val) K = (K ⊗ₖ (1 : Matrix (↥Sᶜ → Fin q) (↥Sᶜ → Fin q) ℂ)).submatrix
      (FiniteProduct.splitEquiv (fun _ : ι => Fin q) S)
      (FiniteProduct.splitEquiv (fun _ : ι => Fin q) S) := by
  ext c c'
  simp only [embedOp_apply, submatrix_apply, kroneckerMap_apply, one_apply]
  have hagree : AgreeOff (fun x : S => x.val) c c' ↔
      (FiniteProduct.splitEquiv (fun _ : ι => Fin q) S c).2 =
        (FiniteProduct.splitEquiv (fun _ : ι => Fin q) S c').2 := by
    constructor
    · intro h
      funext v
      exact h v fun j hj => (Finset.mem_compl.mp v.2) (hj ▸ j.2)
    · intro h i hi
      have hiS : i ∉ S := fun hiS => hi ⟨i, hiS⟩ rfl
      exact congrFun h ⟨i, Finset.mem_compl.mpr hiS⟩
  by_cases h : AgreeOff (fun x : S => x.val) c c'
  · simp only [h, hagree.mp h, ite_true, mul_one]
    rfl
  · simp only [h, hagree.not.mp h, ite_false, mul_zero]

/-- A matrix of the form `K ⊗ 1` in the coordinates of `S` acts on `S`. -/
theorem kronecker_one_submatrix_mem_supportedOperators (S : Finset ι)
    (K : Matrix (S → Fin q) (S → Fin q) ℂ) :
    (K ⊗ₖ (1 : Matrix (↥Sᶜ → Fin q) (↥Sᶜ → Fin q) ℂ)).submatrix
        (FiniteProduct.splitEquiv (fun _ : ι => Fin q) S)
        (FiniteProduct.splitEquiv (fun _ : ι => Fin q) S) ∈
      supportedOperators q (S : Set ι) := by
  rw [← embedOp_val_eq_kronecker_one_submatrix]
  simpa using embedOp_mem_supportedOperators (e := fun x : S => x.val) Subtype.val_injective K

end QuantumCircuit

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
    (hR₀ : R₀ ∈ supportedOperators q (S : Set ι)) (hL : L' ∈ supportedOperators q (S : Set ι))
    {φ η g : (ι → Fin q) → ℂ} (hφ : ‖WithLp.toLp 2 φ‖ = 1) (hη : ‖WithLp.toLp 2 η‖ = 1)
    {M₀ ε a : ℝ} (hζ : ‖WithLp.toLp 2 (R₀ *ᵥ φ)‖ ≤ M₀) (hg : D *ᵥ g = g)
    (hgn : ‖WithLp.toLp 2 g‖ ≤ 1) (hexc : ‖WithLp.toLp 2 (D *ᵥ (R₀ *ᵥ φ - g))‖ ≤ ε)
    (hret : ‖WithLp.toLp 2 ((D - Dret) *ᵥ (R₀ *ᵥ φ))‖ ≤ ε) (htrunc : M₀ * ‖Dret - L'‖ ≤ ε)
    (hadj : ‖WithLp.toLp 2 ((L' * R₀)ᴴ *ᵥ η) - WithLp.toLp 2 φ‖ ≤ a) :
    ∃ U : Matrix (ι → Fin q) (ι → Fin q) ℂ, U ∈ supportedOperators q (S : Set ι) ∧
      Uᴴ * U = 1 ∧ ‖WithLp.toLp 2 (U *ᵥ φ) - WithLp.toLp 2 η‖ ≤
        a + √(2 * a + 6 * ε + 9 * ε ^ 2) := by
  set e := FiniteProduct.splitEquiv (fun _ : ι => Fin q) S with he
  obtain ⟨R', hR'⟩ := EncodedFrame.exists_kronecker_one_of_mem_supportedOperators hR₀
  obtain ⟨L'', hL''⟩ := EncodedFrame.exists_kronecker_one_of_mem_supportedOperators hL
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
  have hR'e : R₀.submatrix e.symm e.symm = R' ⊗ₖ (1 : Matrix (↥Sᶜ → Fin q) (↥Sᶜ → Fin q) ℂ) :=
    hR'
  have hL''e : L'.submatrix e.symm e.symm =
      L'' ⊗ₖ (1 : Matrix (↥Sᶜ → Fin q) (↥Sᶜ → Fin q) ℂ) := hL''
  have hRφ : (R' ⊗ₖ (1 : Matrix (↥Sᶜ → Fin q) (↥Sᶜ → Fin q) ℂ)) *ᵥ (φ ∘ e.symm) =
      (R₀ *ᵥ φ) ∘ e.symm := by rw [← hR'e, hvec]
  have hprod : (L'' * R') ⊗ₖ (1 : Matrix (↥Sᶜ → Fin q) (↥Sᶜ → Fin q) ℂ) =
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
          (R' ⊗ₖ (1 : Matrix (↥Sᶜ → Fin q) (↥Sᶜ → Fin q) ℂ)) (WithLp.toLp 2 (φ ∘ e.symm)) -
            WithLp.toLp 2 (g ∘ e.symm)) = WithLp.toLp 2 ((D *ᵥ (R₀ *ᵥ φ - g)) ∘ e.symm) := by
        apply WithLp.ofLp_injective 2
        simp only [ofLp_toEuclideanCLM, WithLp.ofLp_sub, hRφ, ← hcomp, hvec]
      rw [e1, hnorm]
      exact hexc)
    (by
      have e1 : toEuclideanCLM (𝕜 := ℂ) (D.submatrix e.symm e.symm - Dret.submatrix e.symm e.symm)
          (toEuclideanCLM (𝕜 := ℂ) (R' ⊗ₖ (1 : Matrix (↥Sᶜ → Fin q) (↥Sᶜ → Fin q) ℂ))
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
    (1 : Matrix (↥Sᶜ → Fin q) (↥Sᶜ → Fin q) ℂ)).submatrix e e,
    kronecker_one_submatrix_mem_supportedOperators S _, ?_, ?_⟩
  · rw [conjTranspose_submatrix, submatrix_mul_equiv _ _ _ e, conjTranspose_kronecker,
      ← mul_kronecker_mul, hu, conjTranspose_one, Matrix.one_mul, one_kronecker_one,
      submatrix_one_equiv]
  · have hUe : (((U : Matrix (S → Fin q) (S → Fin q) ℂ) ⊗ₖ
        (1 : Matrix (↥Sᶜ → Fin q) (↥Sᶜ → Fin q) ℂ)).submatrix e e).submatrix e.symm e.symm =
          (U : Matrix (S → Fin q) (S → Fin q) ℂ) ⊗ₖ
            (1 : Matrix (↥Sᶜ → Fin q) (↥Sᶜ → Fin q) ℂ) := by
      simp
    rw [← WithLp.toLp_sub, ← hnorm, hcomp, ← hvec, hUe, WithLp.toLp_sub]
    simpa only [toEuclideanCLM_toLp] using hU

/-- **The entropy comparison for a unitary acting away from both regions.** Let `U` be a
unitary acting on a region `S` disjoint from `X ∪ J`, and let `η` be a unit vector with
`I_η(X : J) = 0`. If `‖U φ - η‖ ≤ C₁ n^(-K/2)` with `K ≥ 4(M + 2)` and `log dim X ≤ C₂ n²`,
then every part of `X` has mutual information at most `8 √C₁ (1 + C₂) n^(-M)` with `J` in
the unit vector `φ`. Source: `09-amplification.tex`, lines 547–561. -/
theorem mutualInformation_le_inv_pow_of_supported_unitary
    {φ η : EuclideanSpace ℂ (ι → Fin q)} (hφ : ‖φ‖ = 1) (hη : ‖η‖ = 1)
    {X J S : Finset ι} (hXJ : Disjoint X J) (hS : Disjoint (S : Set ι) ((X ∪ J : Finset ι) :
      Set ι)) {U : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hU : U ∈ supportedOperators q (S : Set ι))
    (hUu : Uᴴ * U = 1)
    (hprod : FiniteProduct.mutualInformation (fun _ : ι => Fin q) η X J = 0)
    {C₁ C₂ : ℝ} {n M K : ℕ} (hn : 1 ≤ n) (hK : 4 * (M + 2) ≤ K)
    (hδ : ‖WithLp.toLp 2 (U *ᵥ WithLp.ofLp φ) - η‖ ≤ C₁ * (n : ℝ) ^ (-(K : ℝ) / 2))
    (hdim : Real.log (Fintype.card (FiniteProduct.Configuration (fun _ : ι => Fin q) X)) ≤
      C₂ * (n : ℝ) ^ 2) :
    ∀ X' ⊆ X, FiniteProduct.mutualInformation (fun _ : ι => Fin q) φ X' J ≤
      8 * √C₁ * (1 + C₂) * ((n : ℝ) ^ M)⁻¹ := by
  obtain ⟨U₂, hU₂⟩ := EncodedFrame.exists_one_kronecker_of_mem_supportedOperators hS hU
  set e := FiniteProduct.splitEquiv (fun _ : ι => Fin q) (X ∪ J) with he
  have hUeq : U = ((1 : Matrix (FiniteProduct.Configuration (fun _ : ι => Fin q) (X ∪ J))
      (FiniteProduct.Configuration (fun _ : ι => Fin q) (X ∪ J)) ℂ)
      ⊗ₖ U₂).submatrix e e := by
    rw [← hU₂]
    simp [e]
  have hU₂u : U₂ᴴ * U₂ = 1 := by
    have h1 : ((1 : Matrix (FiniteProduct.Configuration (fun _ : ι => Fin q) (X ∪ J))
      (FiniteProduct.Configuration (fun _ : ι => Fin q) (X ∪ J)) ℂ) ⊗ₖ
        (U₂ᴴ * U₂)).submatrix e e = 1 := by
      rw [← hUu, hUeq, conjTranspose_submatrix, submatrix_mul_equiv, conjTranspose_kronecker,
        conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul]
    have h2 : (1 : Matrix (FiniteProduct.Configuration (fun _ : ι => Fin q) (X ∪ J))
      (FiniteProduct.Configuration (fun _ : ι => Fin q) (X ∪ J)) ℂ) ⊗ₖ
        (U₂ᴴ * U₂) = 1 := by
      have := congrArg (fun A => A.submatrix e.symm e.symm) h1
      simpa using this
    have hne : Nonempty (ι → Fin q) := by
      by_contra hne
      rw [not_nonempty_iff] at hne
      have hz : φ = 0 := by
        ext c
        exact (IsEmpty.false c).elim
      rw [hz, norm_zero] at hφ
      exact zero_ne_one hφ
    obtain ⟨c⟩ := hne
    ext i j
    have hij := congrFun (congrFun h2 ((e c).1, i)) ((e c).1, j)
    simpa [kroneckerMap_apply, one_apply] using hij
  have t1 := FiniteProduct.mutualInformation_le_inv_pow_of_unitary_sub_le (fun _ : ι => Fin q) hφ hη
    hXJ U₂
  have t2 := t1 hU₂u hprod (C₁ := C₁) (C₂ := C₂) hn hK
  have t3 := t2 ?_ hdim
  · exact t3
  · rw [← hUeq]
    exact hδ

end TNLean.PEPS.AreaLaw
