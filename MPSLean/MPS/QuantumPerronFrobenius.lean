/-
Copyright (c) 2025 MPSLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MPSLean.MPS.PositiveMapSpectral

import Mathlib.Tactic.NoncommRing

/-!
# Quantum Perron–Frobenius Theory for MPS Transfer Operators

This file proves the quantum Perron–Frobenius theorem for transfer operators
of injective MPS tensors:

1. **Positive definiteness** of PSD fixed points (under injectivity)
2. **Uniqueness** of PSD fixed points (up to scalar)
3. **Existence** of PSD fixed points

## References

- Evans, Høegh-Krohn (1978): "Frobenius theory for positive maps"
- Wolf (2012): "Quantum Channels & Operations: Guided Tour"
-/

open scoped Matrix ComplexOrder BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-! ### Shared spectral decomposition helpers -/

private lemma eig_conj_mul [DecidableEq (Fin D)]
    {M : Matrix (Fin D) (Fin D) ℂ} (hM : M.IsHermitian) :
    (↑hM.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℂ)ᴴ *
      (↑hM.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℂ) = 1 := by
  rw [← Matrix.star_eq_conjTranspose]
  exact Matrix.UnitaryGroup.star_mul_self hM.eigenvectorUnitary

private lemma eig_mul_conj [DecidableEq (Fin D)]
    {M : Matrix (Fin D) (Fin D) ℂ} (hM : M.IsHermitian) :
    (↑hM.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℂ) *
      (↑hM.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℂ)ᴴ = 1 := by
  rw [← Matrix.star_eq_conjTranspose]
  exact Unitary.mul_star_self_of_mem hM.eigenvectorUnitary.prop

private lemma spectral_decomp_eq [DecidableEq (Fin D)]
    {M : Matrix (Fin D) (Fin D) ℂ} (hM : M.IsHermitian) :
    M = (↑hM.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℂ) *
      Matrix.diagonal (fun j => (↑(hM.eigenvalues j) : ℂ)) *
      (↑hM.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℂ)ᴴ := by
  have h := hM.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] at h
  convert h using 2

/-! ## Part 1: Positive definiteness from injectivity

**Key Insight:** If `A` is injective (i.e., `{A_i}` spans `M_D(ℂ)`) and
`ρ` is a nonzero PSD fixed point of `E_A(X) = ∑ A_i X A_i†`, then `ρ`
is positive definite.

The proof uses a vector-level argument:
1. If `x ∈ ker(ρ)`, then `A_i† x ∈ ker(ρ)` for all `i`
   (from the fixed point equation and positivity)
2. By injectivity, `{A_i}` spans `M_D`, so `{A_i†}` spans `M_D`
3. Hence `M x ∈ ker(ρ)` for all `M`, forcing `ker(ρ) = ℂ^D`
4. But `ρ ≠ 0` gives `ker(ρ) ≠ ℂ^D`, contradiction

This bypasses the need for spectral projections entirely.
-/

section PosDef

/-- Adjoint identity for dot product: `star x ⬝ᵥ (M *ᵥ y) = star (Mᴴ *ᵥ x) ⬝ᵥ y`. -/
private lemma dotProduct_mulVec_conjTranspose
    (M : Matrix (Fin D) (Fin D) ℂ)
    (x y : Fin D → ℂ) :
    star x ⬝ᵥ (M *ᵥ y) = star (Mᴴ *ᵥ x) ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]

/-- For a PSD matrix `ρ`, if `star x ⬝ᵥ (ρ *ᵥ x) = 0` then `ρ *ᵥ x = 0`.

This follows from the fact that `ρ = S† S` for some `S`, so
`star x ⬝ᵥ (ρ *ᵥ x) = ‖S x‖² = 0` implies `S x = 0` and hence `ρ x = 0`. -/
private lemma mulVec_eq_zero_of_quadForm_eq_zero
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosSemidef)
    (x : Fin D → ℂ) (hx : star x ⬝ᵥ (ρ *ᵥ x) = 0) :
    ρ *ᵥ x = 0 := by
  classical
  exact (hρ.dotProduct_mulVec_zero_iff x).mp hx

/-- From the transfer map fixed point equation, if `ρ *ᵥ x = 0` then
`ρ *ᵥ (Aᵢᴴ *ᵥ x) = 0` for all Kraus operators `Aᵢ`.

**Proof:** From `ρ = ∑ Aᵢ ρ Aᵢ†`, we get
`0 = star x ⬝ᵥ (ρ *ᵥ x) = ∑ᵢ star(Aᵢ† x) ⬝ᵥ (ρ *ᵥ (Aᵢ† x))`.
Each term is ≥ 0 (ρ PSD), so each = 0, hence `ρ *ᵥ (Aᵢ† x) = 0`. -/
private lemma ker_invariant_under_adjoint
    (A : MPSTensor d D)
    (ρ : Matrix (Fin D) (Fin D) ℂ)
    (hρ_psd : ρ.PosSemidef)
    (hρ_fix : transferMap (d := d) (D := D) A ρ = ρ)
    (x : Fin D → ℂ) (hx : ρ *ᵥ x = 0) :
    ∀ i : Fin d, ρ *ᵥ ((A i)ᴴ *ᵥ x) = 0 := by
  classical
  -- Step 1: star x ⬝ᵥ (ρ *ᵥ x) = 0
  have hqf : star x ⬝ᵥ (ρ *ᵥ x) = 0 := by simp [hx]
  -- Step 2: Rewrite using fixed point equation
  have hsum : star x ⬝ᵥ (ρ *ᵥ x) =
      ∑ i : Fin d, star ((A i)ᴴ *ᵥ x) ⬝ᵥ (ρ *ᵥ ((A i)ᴴ *ᵥ x)) := by
    conv_lhs => rw [show ρ *ᵥ x = (transferMap (d := d) (D := D) A ρ) *ᵥ x from by rw [hρ_fix]]
    simp only [transferMap_apply, Matrix.sum_mulVec]
    rw [dotProduct_sum]
    congr 1; ext i
    rw [show (A i * ρ * (A i)ᴴ) *ᵥ x = A i *ᵥ (ρ *ᵥ ((A i)ᴴ *ᵥ x)) from by
      simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]]
    rw [dotProduct_mulVec_conjTranspose]
  -- Step 3: Each term is nonneg, sum is 0
  have h_each_zero : ∀ i : Fin d,
      star ((A i)ᴴ *ᵥ x) ⬝ᵥ (ρ *ᵥ ((A i)ᴴ *ᵥ x)) = 0 := by
    intro i
    have h_nonneg : ∀ j : Fin d,
        0 ≤ star ((A j)ᴴ *ᵥ x) ⬝ᵥ (ρ *ᵥ ((A j)ᴴ *ᵥ x)) :=
      fun j => hρ_psd.dotProduct_mulVec_nonneg _
    have h_sum_zero : ∑ j : Fin d,
        star ((A j)ᴴ *ᵥ x) ⬝ᵥ (ρ *ᵥ ((A j)ᴴ *ᵥ x)) = 0 := by
      rw [← hsum, hqf]
    -- Use dotProduct_mulVec_zero_iff: 0 = quadratic form ↔ mulVec = 0
    -- Strategy: show quadratic form = 0 for each i
    -- All terms are nonneg (PSD), their sum is 0, each is ≤ sum of rest
    -- We'll show this by proving the real part is 0 using Finset.sum_eq_zero_iff_of_nonneg
    --
    -- The key issue: ρ *ᵥ (Aᴴ *ᵥ x) reduces to (ρ * Aᴴ) *ᵥ x definitionally.
    -- So we work with a single function g that captures the real part.
    have hg_nonneg : ∀ j, (0 : ℝ) ≤ RCLike.re (star ((A j)ᴴ *ᵥ x) ⬝ᵥ (ρ *ᵥ ((A j)ᴴ *ᵥ x))) :=
      fun j => hρ_psd.re_dotProduct_nonneg _
    have hg_sum : ∑ j : Fin d, RCLike.re (star ((A j)ᴴ *ᵥ x) ⬝ᵥ (ρ *ᵥ ((A j)ᴴ *ᵥ x))) = 0 := by
      rw [← map_sum]
      rw [h_sum_zero]; simp
    have hg_zero : RCLike.re (star ((A i)ᴴ *ᵥ x) ⬝ᵥ (ρ *ᵥ ((A i)ᴴ *ᵥ x))) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hg_nonneg j)).mp
        hg_sum i (Finset.mem_univ _)
    have him_zero : RCLike.im (star ((A i)ᴴ *ᵥ x) ⬝ᵥ (ρ *ᵥ ((A i)ᴴ *ᵥ x))) = 0 :=
      hρ_psd.isHermitian.im_star_dotProduct_mulVec_self _
    -- The hypotheses use RCLike.re/im which are defeq to Complex.re/im
    -- Both re and im are zero, so the complex number is zero
    have hre : (star ((A i)ᴴ *ᵥ x) ⬝ᵥ (ρ *ᵥ ((A i)ᴴ *ᵥ x))).re = 0 := hg_zero
    have him : (star ((A i)ᴴ *ᵥ x) ⬝ᵥ (ρ *ᵥ ((A i)ᴴ *ᵥ x))).im = 0 := him_zero
    exact Complex.ext hre him
  -- Step 4: Conclude ρ *ᵥ (Aᵢ† x) = 0
  intro i
  exact mulVec_eq_zero_of_quadForm_eq_zero ρ hρ_psd _ (h_each_zero i)

/-- From the span condition `{A_i†}` spans `M_D`, if `ker(ρ)` contains
`A_i† *ᵥ x` for all `i`, then `ker(ρ)` contains `M *ᵥ x` for all `M`. -/
private lemma ker_contains_all_of_span
    (A : MPSTensor d D) (hA : IsInjective A)
    (ρ : Matrix (Fin D) (Fin D) ℂ)
    (x : Fin D → ℂ)
    (h : ∀ i : Fin d, ρ *ᵥ ((A i)ᴴ *ᵥ x) = 0) :
    ∀ M : Matrix (Fin D) (Fin D) ℂ, ρ *ᵥ (M *ᵥ x) = 0 := by
  -- {A_i} spans M_D, so {A_i†} also spans M_D
  -- (since ᴴ is a linear bijection)
  intro M
  -- Write Mᴴ ∈ span {A_i}  (since span {A_i} = ⊤)
  have hMH : Mᴴ ∈ Submodule.span ℂ (Set.range A) := hA ▸ Submodule.mem_top
  -- So M = (Mᴴ)ᴴ ∈ span {A_i†}
  -- ρ *ᵥ (M *ᵥ x) = ρ *ᵥ ((Mᴴ)ᴴ *ᵥ x) and this is a linear combination of
  -- ρ *ᵥ ((A_i)ᴴ *ᵥ x) = 0
  -- Actually, we need to work with Mᴴ = ∑ c_j A_j, then M = ∑ conj(c_j) A_j†
  -- and M *ᵥ x = ∑ conj(c_j) A_j† *ᵥ x, so ρ *ᵥ (M *ᵥ x) = ∑ conj(c_j) ρ *ᵥ (A_j† *ᵥ x) = 0
  -- More directly: use linearity of ρ *ᵥ (- *ᵥ x)
  -- The map M ↦ ρ *ᵥ (Mᴴ *ᵥ x) is linear in M and vanishes on {A_i}
  suffices ∀ N : Matrix (Fin D) (Fin D) ℂ, ρ *ᵥ (Nᴴ *ᵥ x) = 0 by
    specialize this Mᴴ; rwa [Matrix.conjTranspose_conjTranspose] at this
  intro N
  -- N ∈ span {A_i}
  have hN : N ∈ Submodule.span ℂ (Set.range A) := hA ▸ Submodule.mem_top
  induction hN using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact h i
  | zero => simp
  | add a b _ _ ha hb =>
    simp [Matrix.add_mulVec, Matrix.mulVec_add, ha, hb]
  | smul c a _ ha =>
    simp [Matrix.conjTranspose_smul, Matrix.smul_mulVec, Matrix.mulVec_smul, ha]

/-- **Positive definiteness from injectivity**: If `A` is injective and `ρ`
is a nonzero PSD fixed point of the transfer map, then `ρ` is PD.

This is the key step of the quantum Perron–Frobenius theorem for MPS.
It bypasses the abstract notion of irreducibility by using the spanning
property of injective tensors directly. -/
theorem posSemidef_fixedPoint_isPosDef
    (A : MPSTensor d D) (hA : IsInjective A)
    (ρ : Matrix (Fin D) (Fin D) ℂ)
    (hρ_psd : ρ.PosSemidef) (hρ_ne : ρ ≠ 0)
    (hρ_fix : transferMap (d := d) (D := D) A ρ = ρ) :
    ρ.PosDef := by
  classical
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨hρ_psd.isHermitian, fun x hx => ?_⟩
  -- Show 0 < star x ⬝ᵥ (ρ *ᵥ x) by showing it's ≥ 0 and ≠ 0
  have h_nonneg := hρ_psd.dotProduct_mulVec_nonneg x
  suffices h_ne : star x ⬝ᵥ (ρ *ᵥ x) ≠ 0 from
    lt_of_le_of_ne h_nonneg (Ne.symm h_ne)
  intro h_zero
  -- Then ρ *ᵥ x = 0
  have h_ker := mulVec_eq_zero_of_quadForm_eq_zero ρ hρ_psd x h_zero
  -- Ker(ρ) is invariant under A_i†
  have h_inv := ker_invariant_under_adjoint A ρ hρ_psd hρ_fix x h_ker
  -- By injectivity, ker(ρ) contains M *ᵥ x for all M
  have h_all := ker_contains_all_of_span A hA ρ x h_inv
  -- Since x ≠ 0, the map M ↦ M *ᵥ x is surjective, so ρ *ᵥ v = 0 for all v
  have h_surj : ∀ v : Fin D → ℂ, ρ *ᵥ v = 0 := by
    intro v
    -- Pick k with x k ≠ 0
    have ⟨k, hk⟩ : ∃ k, x k ≠ 0 := by
      by_contra h_all_zero; push_neg at h_all_zero
      exact hx (funext h_all_zero)
    -- Construct M with M *ᵥ x = v
    let M : Matrix (Fin D) (Fin D) ℂ := Matrix.of (fun i j => if j = k then v i * (x k)⁻¹ else 0)
    have hMx : M *ᵥ x = v := by
      ext i
      simp only [M, Matrix.mulVec, dotProduct, Matrix.of_apply]
      rw [Finset.sum_eq_single k]
      · simp [hk]
      · intro j _ hj; simp [hj]
      · exact absurd (Finset.mem_univ k) -- unreachable
    rw [← hMx]; exact h_all M
  -- ρ *ᵥ v = 0 for all v implies ρ = 0
  have h_rho_zero : ρ = 0 := by
    ext i j
    have h := congr_fun (h_surj (Pi.single j 1)) i
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply, Pi.zero_apply] at h
    simpa [Finset.sum_ite_eq, Finset.mem_univ] using h
  exact hρ_ne h_rho_zero

-- Corollary for the irreducibility-based formulation
theorem posSemidef_fixedPoint_isPosDef_of_irreducible
    (A : MPSTensor d D)
    (hIrr : IsIrreducibleCP (transferMap (d := d) (D := D) A))
    (ρ : Matrix (Fin D) (Fin D) ℂ)
    (hρ_psd : ρ.PosSemidef) (hρ_ne : ρ ≠ 0)
    (hρ_fix : transferMap (d := d) (D := D) A ρ = ρ) :
    ρ.PosDef := by
  classical
  -- Proof by contradiction: assume ρ is PSD but not PD
  by_contra hρ_not_pd
  -- ρ PSD but not PD means some eigenvalue is zero
  have hH := hρ_psd.isHermitian
  have h_not_all_pos : ¬∀ i, 0 < hH.eigenvalues i := by
    intro h_all_pos
    exact hρ_not_pd (hH.posDef_iff_eigenvalues_pos.mpr h_all_pos)
  push_neg at h_not_all_pos
  obtain ⟨j₀, hj₀⟩ := h_not_all_pos
  have hj₀_eq : hH.eigenvalues j₀ = 0 :=
    le_antisymm hj₀ (hH.posSemidef_iff_eigenvalues_nonneg.mp hρ_psd j₀)
  -- Define the support projection Q = U * diag(sign(λ)) * U†
  set U : Matrix (Fin D) (Fin D) ℂ := ↑hH.eigenvectorUnitary
  set sgnEig : Fin D → ℂ := fun i => if 0 < hH.eigenvalues i then 1 else 0
  set Q := U * Matrix.diagonal sgnEig * Uᴴ with hQ_def
  -- Useful: U† U = 1 and U U† = 1
  have hUU : Uᴴ * U = 1 := eig_conj_mul hH
  have hUU' : U * Uᴴ = 1 := eig_mul_conj hH
  -- sgnEig is real-valued (star-fixed)
  have hsgnEig_star : star sgnEig = sgnEig := by
    ext i; simp only [sgnEig, Pi.star_apply]; split <;> simp
  -- sgnEig is idempotent (pointwise)
  have hsgnEig_sq : ∀ i, sgnEig i * sgnEig i = sgnEig i := by
    intro i; simp only [sgnEig]; split <;> simp
  -- sgnEig * eigenvalues = eigenvalues
  have hsign_mul_eig : sgnEig * (fun j => (↑(hH.eigenvalues j) : ℂ)) =
      (fun j => (↑(hH.eigenvalues j) : ℂ)) := by
    ext i; simp only [sgnEig, Pi.mul_apply]; split
    · simp
    · rename_i h; push_neg at h
      simp [le_antisymm h (hH.posSemidef_iff_eigenvalues_nonneg.mp hρ_psd i)]
  -- Q is hermitian
  have hQ_herm : Q.IsHermitian := by
    change (U * Matrix.diagonal sgnEig * Uᴴ)ᴴ = U * Matrix.diagonal sgnEig * Uᴴ
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, Matrix.diagonal_conjTranspose, hsgnEig_star]
    rw [Matrix.mul_assoc]
  -- Q is idempotent
  have hQ_idem : Q * Q = Q := by
    change U * Matrix.diagonal sgnEig * Uᴴ * (U * Matrix.diagonal sgnEig * Uᴴ) =
         U * Matrix.diagonal sgnEig * Uᴴ
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
        ← Matrix.mul_assoc Uᴴ U, hUU, Matrix.one_mul,
        ← Matrix.mul_assoc (Matrix.diagonal sgnEig), Matrix.diagonal_mul_diagonal,
        show (fun i => sgnEig i * sgnEig i) = sgnEig from funext hsgnEig_sq]
  -- Q * (1 - Q) = 0 and (1 - Q) * Q = 0
  have hQ1Q : Q * (1 - Q) = 0 := by
    rw [mul_sub, mul_one, hQ_idem, sub_self]
  have h1QQ : (1 - Q) * Q = 0 := by
    rw [sub_mul, one_mul, hQ_idem, sub_self]
  -- Q is an orthogonal projection
  have hQ_proj : IsOrthogonalProjection Q := ⟨hQ_herm, hQ_idem⟩
  -- Q * ρ = ρ
  have hQρ : Q * ρ = ρ := by
    have hρ_spectral : ρ = U * Matrix.diagonal (fun j => (↑(hH.eigenvalues j) : ℂ)) * Uᴴ :=
      spectral_decomp_eq hH
    rw [hρ_spectral, hQ_def]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
        ← Matrix.mul_assoc Uᴴ U, hUU, Matrix.one_mul,
        ← Matrix.mul_assoc (Matrix.diagonal sgnEig), Matrix.diagonal_mul_diagonal]
    rw [show (fun i => sgnEig i * ↑(hH.eigenvalues i)) =
            (fun j => (↑(hH.eigenvalues j) : ℂ)) from hsign_mul_eig]
  -- ρ * Q = ρ
  have hρQ : ρ * Q = ρ := by
    have : (Q * ρ)ᴴ = ρᴴ := congr_arg Matrix.conjTranspose hQρ
    rwa [Matrix.conjTranspose_mul, hQ_herm.eq, hH.eq] at this
  -- ρ = Q * ρ * Q
  have hQρQ : Q * ρ * Q = ρ := by rw [hQρ, hρQ]
  -- ker(Q) ⊆ ker(ρ)
  have ker_Q_sub_ker_ρ : ∀ v, Q *ᵥ v = 0 → ρ *ᵥ v = 0 := by
    intro v hv
    calc ρ *ᵥ v = (Q * ρ * Q) *ᵥ v := by rw [hQρQ]
      _ = Q *ᵥ (ρ *ᵥ (Q *ᵥ v)) := by rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ = 0 := by rw [hv]; simp
  -- ker(ρ) ⊆ ker(Q) via spectral argument
  have ker_ρ_sub_ker_Q : ∀ v, ρ *ᵥ v = 0 → Q *ᵥ v = 0 := by
    intro v hv
    set w := Uᴴ *ᵥ v
    -- ρ v = 0 ⟹ U Λ U† v = 0 ⟹ Λ w = 0 (multiply by U†)
    have hΛw : Matrix.diagonal (fun j => (↑(hH.eigenvalues j) : ℂ)) *ᵥ w = 0 := by
      have hρv : (U * Matrix.diagonal (fun j => (↑(hH.eigenvalues j) : ℂ)) * Uᴴ) *ᵥ v = 0 := by
        rwa [spectral_decomp_eq hH] at hv
      -- (U * Λ * U†) v = 0 ⟹ U (Λ (U† v)) = 0 ⟹ Λ w = 0
      set Λ := Matrix.diagonal (fun j => (↑(hH.eigenvalues j) : ℂ)) with hΛ_def
      have hUΛw : U *ᵥ (Λ *ᵥ w) = 0 := by
        rw [Matrix.mulVec_mulVec]
        -- goal: (U * Λ) *ᵥ w = 0, where w = Uᴴ *ᵥ v
        -- (U * Λ) *ᵥ (Uᴴ *ᵥ v) = ((U * Λ) * Uᴴ) *ᵥ v = (U * Λ * Uᴴ) *ᵥ v
        rw [show w = Uᴴ *ᵥ v from rfl, Matrix.mulVec_mulVec]
        exact hρv
      -- Multiply by U† on left
      have : Uᴴ *ᵥ (U *ᵥ (Λ *ᵥ w)) = 0 := by rw [hUΛw]; simp
      rwa [Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec] at this
    -- Component-wise: λ_j * w_j = 0
    have h_comp : ∀ j, (↑(hH.eigenvalues j) : ℂ) * w j = 0 := by
      intro j
      have := congr_fun hΛw j
      simp only [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, Pi.zero_apply] at this
      -- this : ∑ x, (if j = x then ↑(hH.eigenvalues j) else 0) * w x = 0
      -- Simplify the sum: only x = j contributes
      -- The sum simplifies to (↑eigenvalues j) * w j
      simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at this
      exact this
    -- diag(sgnEig) * w = 0
    have hSw : Matrix.diagonal sgnEig *ᵥ w = 0 := by
      ext j
      simp only [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, Pi.zero_apply]
      simp only [sgnEig]
      split
      · -- λ_j > 0 so w_j = 0
        rename_i hpos
        have hwj : w j = 0 := by
          have := h_comp j
          have hne : (↑(hH.eigenvalues j) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hpos
          exact (mul_eq_zero.mp this).resolve_left hne
        simp [hwj]
      · -- sgnEig j = 0
        simp
    -- Q v = U (diag(sgnEig) w) = 0
    change (U * Matrix.diagonal sgnEig * Uᴴ) *ᵥ v = 0
    have : (U * Matrix.diagonal sgnEig * Uᴴ) *ᵥ v =
           U *ᵥ (Matrix.diagonal sgnEig *ᵥ w) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    rw [this, hSw]; simp
  -- Key: (1-Q) * A_i * Q = 0 for all i
  -- Via: Q * A_i† * (1-Q) = 0 (then take conj transpose)
  have h_complement_zero : ∀ i : Fin d, (1 - Q) * A i * Q = 0 := by
    intro i
    -- First show Q * (A i)ᴴ * (1 - Q) = 0 by showing every column is zero
    suffices h : Q * (A i)ᴴ * (1 - Q) = 0 by
      have h1 : ((Q * (A i)ᴴ * (1 - Q))ᴴ) = 0ᴴ := congr_arg _ h
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
        Matrix.conjTranspose_one, Matrix.conjTranspose_conjTranspose,
        hQ_herm.eq, Matrix.conjTranspose_zero] at h1
      -- h1 : (1 - Q) * (A i * Q) = 0, need (1 - Q) * A i * Q = 0
      rwa [← Matrix.mul_assoc] at h1
    -- Show (Q * A_i† * (1-Q)) *ᵥ v = 0 for all v, then conclude matrix is 0
    suffices h_vec : ∀ v, (Q * (A i)ᴴ * (1 - Q)) *ᵥ v = 0 by
      ext a b; simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_ite_eq'] using
        congr_fun (h_vec (Pi.single b 1)) a
    intro v
    -- (Q * (A i)ᴴ * (1-Q)) *ᵥ v = Q *ᵥ ((A i)ᴴ *ᵥ ((1-Q) *ᵥ v))
    have key : (Q * (A i)ᴴ * (1 - Q)) *ᵥ v = Q *ᵥ ((A i)ᴴ *ᵥ ((1 - Q) *ᵥ v)) := by
      simp only [Matrix.mul_assoc, Matrix.mulVec_mulVec]
    rw [key]
    apply ker_ρ_sub_ker_Q
    apply ker_invariant_under_adjoint A ρ hρ_psd hρ_fix
    apply ker_Q_sub_ker_ρ
    -- Q *ᵥ ((1-Q) *ᵥ v) = (Q * (1-Q)) *ᵥ v = 0
    rw [Matrix.mulVec_mulVec, hQ1Q]; simp
  -- From h_complement_zero: A_i Q = Q A_i Q and Q A_i† = Q A_i† Q
  have h_AQ : ∀ i : Fin d, A i * Q = Q * A i * Q := by
    intro i
    have h := h_complement_zero i
    -- (1-Q) A_i Q = 0 means A_i Q - Q A_i Q = 0
    have : A i * Q - Q * A i * Q = 0 := by
      calc A i * Q - Q * A i * Q
          = (1 - Q) * A i * Q := by noncomm_ring
        _ = 0 := h
    exact sub_eq_zero.mp this
  have h_QA : ∀ i : Fin d, Q * (A i)ᴴ = Q * (A i)ᴴ * Q := by
    intro i
    have h := h_AQ i  -- A i * Q = Q * A i * Q
    -- Take conjTranspose of both sides
    have h1 : (A i * Q)ᴴ = (Q * A i * Q)ᴴ := congr_arg _ h
    simp only [Matrix.conjTranspose_mul, hQ_herm.eq] at h1
    -- h1 : Q * (A i)ᴴ = Q * ((A i)ᴴ * Q)
    rwa [← Matrix.mul_assoc] at h1
  -- Q satisfies the invariance condition for irreducibility
  have hQ_inv : ∀ X, Q * transferMap (d := d) (D := D) A (Q * X * Q) * Q =
      transferMap (d := d) (D := D) A (Q * X * Q) := by
    intro X
    simp only [transferMap_apply]
    -- Show Q * (∑ ...) * Q = ∑ ... by showing each term is fixed
    have h_term : ∀ i : Fin d,
        Q * (A i * (Q * X * Q) * (A i)ᴴ) * Q = A i * (Q * X * Q) * (A i)ᴴ := by
      intro i
      calc Q * (A i * (Q * X * Q) * (A i)ᴴ) * Q
          = (Q * A i) * (Q * X * Q) * ((A i)ᴴ * Q) := by noncomm_ring
        _ = (Q * A i * Q) * X * (Q * (A i)ᴴ * Q) := by noncomm_ring
        _ = (A i * Q) * X * (Q * (A i)ᴴ) := by rw [← h_AQ i, ← h_QA i]
        _ = A i * (Q * X * Q) * (A i)ᴴ := by noncomm_ring
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => h_term i)
  -- Apply irreducibility: Q = 0 or Q = 1
  have hQ_zero_or_one := hIrr Q hQ_proj hQ_inv
  -- Q ≠ 0 (since Qρ = ρ and ρ ≠ 0)
  have hQ_ne_zero : Q ≠ 0 := by
    intro hQ_zero; apply hρ_ne; rw [← hQρ, hQ_zero]; simp
  -- Q ≠ 1 (since sgnEig j₀ = 0, but 1 would require sgnEig = 1)
  have hQ_ne_one : Q ≠ 1 := by
    intro hQ_one
    -- Q = 1 implies diag(sgnEig) = 1
    have hdiag_one : Matrix.diagonal sgnEig = 1 := by
      calc Matrix.diagonal sgnEig
          = (Uᴴ * U) * Matrix.diagonal sgnEig * (Uᴴ * U) := by rw [hUU]; simp
        _ = Uᴴ * (U * Matrix.diagonal sgnEig * Uᴴ) * U := by noncomm_ring
        _ = Uᴴ * 1 * U := by rw [show U * Matrix.diagonal sgnEig * Uᴴ = Q from rfl, hQ_one]
        _ = 1 := by rw [Matrix.mul_one, hUU]
    -- sgnEig j₀ = 0 but diagonal sgnEig = 1 means sgnEig j₀ = 1, contradiction
    have : sgnEig j₀ = 1 := by
      have := congr_fun (Matrix.diagonal_injective (hdiag_one.trans Matrix.diagonal_one.symm)) j₀
      simpa using this
    simp [sgnEig, hj₀_eq] at this
  -- Contradiction
  rcases hQ_zero_or_one with h | h
  · exact hQ_ne_zero h
  · exact hQ_ne_one (by convert h)

end PosDef

/-! ## Part 2: Uniqueness of PSD fixed point

Under injectivity, any two nonzero PSD fixed points are proportional.
-/

section Uniqueness

private lemma eigenvectorUnitary_isUnit' [DecidableEq (Fin D)]
    {A : Matrix (Fin D) (Fin D) ℂ} (hA : A.IsHermitian) :
    IsUnit (↑hA.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℂ) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  exact Matrix.UnitaryGroup.det_isUnit hA.eigenvectorUnitary

/-! ### Square root diagonal functions -/

private noncomputable def sqrtΛ' [DecidableEq (Fin D)]
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.IsHermitian) : Fin D → ℂ :=
  fun i => ↑(Real.sqrt (hρ.eigenvalues i))

private noncomputable def sqrtInvΛ' [DecidableEq (Fin D)]
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.IsHermitian) (_ : ρ.PosDef) : Fin D → ℂ :=
  fun i => ↑(1 / Real.sqrt (hρ.eigenvalues i))

private lemma star_sqrtΛ'' [DecidableEq (Fin D)]
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.IsHermitian) :
    star (sqrtΛ' hρ) = sqrtΛ' hρ := by
  ext i; simp [sqrtΛ', Pi.star_apply, Complex.conj_ofReal]

private lemma star_sqrtInvΛ'' [DecidableEq (Fin D)]
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.IsHermitian) (hPD : ρ.PosDef) :
    star (sqrtInvΛ' hρ hPD) = sqrtInvΛ' hρ hPD := by
  ext i; simp [sqrtInvΛ', Pi.star_apply, Complex.conj_ofReal]

private lemma sqrtΛ_mul_sqrtΛ' [DecidableEq (Fin D)]
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.IsHermitian) (hPSD : ρ.PosSemidef) :
    Matrix.diagonal (sqrtΛ' hρ) * Matrix.diagonal (sqrtΛ' hρ) =
      Matrix.diagonal (fun j => (↑(hρ.eigenvalues j) : ℂ)) := by
  rw [Matrix.diagonal_mul_diagonal]
  congr 1; ext j; simp only [sqrtΛ']
  rw [← Complex.ofReal_mul]; congr 1
  exact Real.mul_self_sqrt ((hρ.posSemidef_iff_eigenvalues_nonneg.mp hPSD) j)

private lemma sqrtΛ_mul_sqrtInvΛ' [DecidableEq (Fin D)]
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.IsHermitian) (hPD : ρ.PosDef) :
    Matrix.diagonal (sqrtΛ' hρ) * Matrix.diagonal (sqrtInvΛ' hρ hPD) = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; ext j
  simp only [sqrtInvΛ', sqrtΛ', ← Complex.ofReal_mul]
  congr 1
  exact mul_div_cancel₀ _ (Real.sqrt_ne_zero'.mpr (hρ.posDef_iff_eigenvalues_pos.mp hPD j))

private lemma sqrtInvΛ_mul_sqrtΛ' [DecidableEq (Fin D)]
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.IsHermitian) (hPD : ρ.PosDef) :
    Matrix.diagonal (sqrtInvΛ' hρ hPD) * Matrix.diagonal (sqrtΛ' hρ) = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; ext j
  simp only [sqrtInvΛ', sqrtΛ', ← Complex.ofReal_mul]
  congr 1
  exact div_mul_cancel₀ 1 (Real.sqrt_ne_zero'.mpr (hρ.posDef_iff_eigenvalues_pos.mp hPD j))

/-! ### Key factorization identities -/

-- S * Sᴴ = ρ
private lemma sqrtFactor_mul_conjTranspose' [DecidableEq (Fin D)]
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.IsHermitian) (hρ_pd : ρ.PosDef) :
    let U : Matrix (Fin D) (Fin D) ℂ := ↑hρ.eigenvectorUnitary
    let S := U * Matrix.diagonal (sqrtΛ' hρ)
    S * Sᴴ = ρ := by
  intro U S
  change U * Matrix.diagonal (sqrtΛ' hρ) * (U * Matrix.diagonal (sqrtΛ' hρ))ᴴ = ρ
  rw [Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose, star_sqrtΛ'' hρ]
  calc U * Matrix.diagonal (sqrtΛ' hρ) * (Matrix.diagonal (sqrtΛ' hρ) * Uᴴ)
      = U * (Matrix.diagonal (sqrtΛ' hρ) * Matrix.diagonal (sqrtΛ' hρ)) * Uᴴ := by noncomm_ring
    _ = U * Matrix.diagonal (fun j => (↑(hρ.eigenvalues j) : ℂ)) * Uᴴ := by
        rw [sqrtΛ_mul_sqrtΛ' hρ hρ_pd.posSemidef]
    _ = ρ := (spectral_decomp_eq hρ).symm

-- S * Bᴴ = 1
private lemma sqrtFactor_mul_invFactor_conj' [DecidableEq (Fin D)]
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.IsHermitian) (hρ_pd : ρ.PosDef) :
    let U : Matrix (Fin D) (Fin D) ℂ := ↑hρ.eigenvectorUnitary
    let S := U * Matrix.diagonal (sqrtΛ' hρ)
    let B := U * Matrix.diagonal (sqrtInvΛ' hρ hρ_pd)
    S * Bᴴ = 1 := by
  intro U S B
  change U * Matrix.diagonal (sqrtΛ' hρ) * (U * Matrix.diagonal (sqrtInvΛ' hρ hρ_pd))ᴴ = 1
  rw [Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose, star_sqrtInvΛ'' hρ hρ_pd]
  calc U * Matrix.diagonal (sqrtΛ' hρ) * (Matrix.diagonal (sqrtInvΛ' hρ hρ_pd) * Uᴴ)
      = U * (Matrix.diagonal (sqrtΛ' hρ) * Matrix.diagonal (sqrtInvΛ' hρ hρ_pd)) * Uᴴ := by
        noncomm_ring
    _ = U * 1 * Uᴴ := by rw [sqrtΛ_mul_sqrtInvΛ' hρ hρ_pd]
    _ = 1 := by rw [Matrix.mul_one]; exact eig_mul_conj hρ

-- B * Sᴴ = 1
private lemma invFactor_mul_sqrtFactor_conj' [DecidableEq (Fin D)]
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.IsHermitian) (hρ_pd : ρ.PosDef) :
    let U : Matrix (Fin D) (Fin D) ℂ := ↑hρ.eigenvectorUnitary
    let S := U * Matrix.diagonal (sqrtΛ' hρ)
    let B := U * Matrix.diagonal (sqrtInvΛ' hρ hρ_pd)
    B * Sᴴ = 1 := by
  intro U S B
  change U * Matrix.diagonal (sqrtInvΛ' hρ hρ_pd) * (U * Matrix.diagonal (sqrtΛ' hρ))ᴴ = 1
  rw [Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose, star_sqrtΛ'' hρ]
  calc U * Matrix.diagonal (sqrtInvΛ' hρ hρ_pd) * (Matrix.diagonal (sqrtΛ' hρ) * Uᴴ)
      = U * (Matrix.diagonal (sqrtInvΛ' hρ hρ_pd) * Matrix.diagonal (sqrtΛ' hρ)) * Uᴴ := by
        noncomm_ring
    _ = U * 1 * Uᴴ := by rw [sqrtInvΛ_mul_sqrtΛ' hρ hρ_pd]
    _ = 1 := by rw [Matrix.mul_one]; exact eig_mul_conj hρ

-- S is a unit
private lemma sqrtFactor_isUnit' [DecidableEq (Fin D)]
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.IsHermitian) (hρ_pd : ρ.PosDef) :
    let U : Matrix (Fin D) (Fin D) ℂ := ↑hρ.eigenvectorUnitary
    let S := U * Matrix.diagonal (sqrtΛ' hρ)
    IsUnit S := by
  intro U S
  rw [Matrix.isUnit_iff_isUnit_det]
  have h1 := sqrtFactor_mul_invFactor_conj' hρ hρ_pd
  have h2 := invFactor_mul_sqrtFactor_conj' hρ hρ_pd
  -- S has a right inverse (Bᴴ), hence its det is a unit
  set B := U * Matrix.diagonal (sqrtInvΛ' hρ hρ_pd)
  have : S * Bᴴ = 1 := h1
  rw [isUnit_iff_exists_inv]
  exact ⟨(Bᴴ).det, by rw [← Matrix.det_mul, this, Matrix.det_one]⟩

/-! ### Diagonal subtraction and spectral shift -/

private lemma diagonal_sub_smul_one' [DecidableEq (Fin D)] (v : Fin D → ℝ) (c : ℝ) :
    Matrix.diagonal (fun j => (↑(v j) : ℂ)) - (↑c : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ) =
      Matrix.diagonal (fun j => (↑(v j - c) : ℂ)) := by
  ext i j
  simp [Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply]
  split
  · simp
  · simp

-- A - c•I = U diag(λ - c) Uᴴ
private lemma hermitian_sub_scalar_spectral [DecidableEq (Fin D)]
    {A : Matrix (Fin D) (Fin D) ℂ} (hA : A.IsHermitian) (c : ℝ) :
    A - (↑c : ℂ) • 1 =
      (↑hA.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℂ) *
      Matrix.diagonal (fun j => (↑(hA.eigenvalues j - c) : ℂ)) *
      (↑hA.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℂ)ᴴ := by
  set U : Matrix (Fin D) (Fin D) ℂ := ↑hA.eigenvectorUnitary
  have hUUt : U * Uᴴ = 1 := eig_mul_conj hA
  have hA_spec := spectral_decomp_eq hA
  have h_cI : (↑c : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ) =
      U * ((↑c : ℂ) • 1) * Uᴴ := by
    calc (↑c : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ)
        = (↑c : ℂ) • (U * Uᴴ) := by rw [hUUt]
      _ = U * ((↑c : ℂ) • 1) * Uᴴ := by
          rw [Matrix.mul_smul, Matrix.mul_one, smul_mul_assoc]
  calc A - (↑c : ℂ) • 1
      = U * Matrix.diagonal (fun j => ↑(hA.eigenvalues j)) * Uᴴ -
        U * ((↑c : ℂ) • 1) * Uᴴ := by
        conv_lhs => rw [hA_spec]; rw [h_cI]
    _ = U * (Matrix.diagonal (fun j => ↑(hA.eigenvalues j)) - (↑c : ℂ) • 1) * Uᴴ := by
        noncomm_ring
    _ = U * Matrix.diagonal (fun j => ↑(hA.eigenvalues j - c)) * Uᴴ := by
        congr 1; congr 1; exact diagonal_sub_smul_one' hA.eigenvalues c

/-! ### Min eigenvalue -/

private noncomputable def minEigenvalue' [DecidableEq (Fin D)] [Nonempty (Fin D)]
    {A : Matrix (Fin D) (Fin D) ℂ} (hA : A.IsHermitian) : ℝ :=
  (Finset.univ.image hA.eigenvalues).min' (Finset.Nonempty.image Finset.univ_nonempty _)

private lemma minEigenvalue_le' [DecidableEq (Fin D)] [Nonempty (Fin D)]
    {A : Matrix (Fin D) (Fin D) ℂ} (hA : A.IsHermitian) (i : Fin D) :
    minEigenvalue' hA ≤ hA.eigenvalues i := by
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

private lemma minEigenvalue_achieved' [DecidableEq (Fin D)] [Nonempty (Fin D)]
    {A : Matrix (Fin D) (Fin D) ℂ} (hA : A.IsHermitian) :
    ∃ i : Fin D, hA.eigenvalues i = minEigenvalue' hA := by
  have hne := Finset.Nonempty.image Finset.univ_nonempty hA.eigenvalues
  have h := Finset.min'_mem _ hne
  rw [Finset.mem_image] at h
  obtain ⟨i, _, hi⟩ := h
  exact ⟨i, hi⟩

private lemma minEigenvalue_pos' [DecidableEq (Fin D)] [Nonempty (Fin D)]
    {A : Matrix (Fin D) (Fin D) ℂ} (hA : A.IsHermitian) (hPD : A.PosDef) :
    0 < minEigenvalue' hA := by
  unfold minEigenvalue'
  rw [Finset.lt_min'_iff]
  intro x hx
  rw [Finset.mem_image] at hx
  obtain ⟨i, _, rfl⟩ := hx
  exact hA.posDef_iff_eigenvalues_pos.mp hPD i

/-! ### The key identity and critical scalar lemma -/

-- σ - c₀ρ = S (H - c₀I) Sᴴ
private lemma key_identity' [DecidableEq (Fin D)]
    {ρ σ : Matrix (Fin D) (Fin D) ℂ}
    (hρ : ρ.IsHermitian) (hρ_pd : ρ.PosDef) (c₀ : ℝ) :
    let U : Matrix (Fin D) (Fin D) ℂ := ↑hρ.eigenvectorUnitary
    let S := U * Matrix.diagonal (sqrtΛ' hρ)
    let B := U * Matrix.diagonal (sqrtInvΛ' hρ hρ_pd)
    let H := Bᴴ * σ * B
    σ - (↑c₀ : ℂ) • ρ = S * (H - (↑c₀ : ℂ) • 1) * Sᴴ := by
  intro U S B H
  have h_expand : S * (H - (↑c₀ : ℂ) • 1) * Sᴴ = S * H * Sᴴ - (↑c₀ : ℂ) • (S * Sᴴ) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
               Matrix.mul_one]
  rw [h_expand]
  have hSS := sqrtFactor_mul_conjTranspose' hρ hρ_pd
  have hSBt := sqrtFactor_mul_invFactor_conj' hρ hρ_pd
  have hBSt := invFactor_mul_sqrtFactor_conj' hρ hρ_pd
  have hSHS : S * H * Sᴴ = σ := by
    calc S * (Bᴴ * σ * B) * Sᴴ
        = (S * Bᴴ) * σ * (B * Sᴴ) := by noncomm_ring
      _ = 1 * σ * 1 := by rw [hSBt, hBSt]
      _ = σ := by rw [Matrix.one_mul, Matrix.mul_one]
  rw [hSHS, hSS]

/-- **Critical scalar lemma.** For positive definite `ρ` and `σ`, there exists
`c₀ > 0` such that `σ - c₀ • ρ` is PSD but not PD.

Uses the conjugation `H = ρ^{-1/2} σ ρ^{-1/2}` (via spectral decomposition)
and takes `c₀ = min eigenvalue of H`. -/
private lemma exists_critical_scalar [Nonempty (Fin D)]
    {ρ σ : Matrix (Fin D) (Fin D) ℂ}
    (hρ_pd : ρ.PosDef) (hσ_pd : σ.PosDef) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ (σ - (↑c₀ : ℂ) • ρ).PosSemidef ∧
      ¬(σ - (↑c₀ : ℂ) • ρ).PosDef := by
  classical
  set hρ := hρ_pd.isHermitian
  set hσ := hσ_pd.isHermitian
  set U : Matrix (Fin D) (Fin D) ℂ := ↑hρ.eigenvectorUnitary
  set S := U * Matrix.diagonal (sqrtΛ' hρ) with hS_def
  set B := U * Matrix.diagonal (sqrtInvΛ' hρ hρ_pd) with hB_def
  set H := Bᴴ * σ * B with hH_def
  -- H is Hermitian
  have hH_herm : H.IsHermitian := by
    change Hᴴ = H
    simp only [hH_def, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hσ.eq]
    noncomm_ring
  -- H is PD (Bᴴ σ B with B invertible and σ PD)
  -- Use star = conjTranspose, and the fact that B is a unit
  have hB_unit : IsUnit B := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have h := invFactor_mul_sqrtFactor_conj' hρ hρ_pd  -- B * Sᴴ = 1
    have h_det := congr_arg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_one] at h_det
    rw [Matrix.det_conjTranspose] at h_det
    -- h_det : B.det * star S.det = 1
    exact IsUnit.of_mul_eq_one _ h_det
  have hH_pd : H.PosDef := by
    rw [show H = star B * σ * B from by simp [hH_def, Matrix.star_eq_conjTranspose]]
    exact (Matrix.IsUnit.posDef_star_left_conjugate_iff hB_unit).mpr hσ_pd
  -- c₀ = min eigenvalue of H > 0
  set c₀ := minEigenvalue' hH_herm with hc₀_def
  have hc₀_pos : 0 < c₀ := minEigenvalue_pos' hH_herm hH_pd
  -- H - c₀I has spectral decomposition: V diag(μ - c₀) Vᴴ
  -- where μ_i are eigenvalues of H and V is H's eigenvector unitary
  set V : Matrix (Fin D) (Fin D) ℂ := ↑hH_herm.eigenvectorUnitary with hV_def
  have hV_unit : IsUnit V := eigenvectorUnitary_isUnit' hH_herm
  -- H - c₀I = V diag(μ - c₀) Vᴴ
  have h_shift := hermitian_sub_scalar_spectral hH_herm c₀
  -- H - c₀I is PSD: diag(μ - c₀) has nonneg entries (since μ_i ≥ c₀)
  have hHc_psd : (H - (↑c₀ : ℂ) • 1).PosSemidef := by
    rw [h_shift]
    rw [show V * Matrix.diagonal (fun j => ↑(hH_herm.eigenvalues j - c₀)) * Vᴴ =
          V * Matrix.diagonal (fun j => ↑(hH_herm.eigenvalues j - c₀)) * star V from by
        simp [Matrix.star_eq_conjTranspose]]
    exact (Matrix.IsUnit.posSemidef_star_right_conjugate_iff hV_unit).mpr
      (Matrix.posSemidef_diagonal_iff.mpr (fun i => by
        simp only [Complex.nonneg_iff]
        constructor
        · exact_mod_cast sub_nonneg.mpr (minEigenvalue_le' hH_herm i)
        · simp [Complex.ofReal_im]))
  -- H - c₀I is not PD: some μ_i = c₀ (the minimizer)
  have hHc_not_pd : ¬(H - (↑c₀ : ℂ) • 1).PosDef := by
    rw [h_shift]
    rw [show V * Matrix.diagonal (fun j => ↑(hH_herm.eigenvalues j - c₀)) * Vᴴ =
          V * Matrix.diagonal (fun j => ↑(hH_herm.eigenvalues j - c₀)) * star V from by
        simp [Matrix.star_eq_conjTranspose]]
    intro h_pd
    have h_pd' := (Matrix.IsUnit.posDef_star_right_conjugate_iff hV_unit).mp h_pd
    rw [Matrix.posDef_diagonal_iff] at h_pd'
    obtain ⟨i₀, hi₀⟩ := minEigenvalue_achieved' hH_herm
    have := h_pd' i₀
    simp only at this
    rw [show (↑(hH_herm.eigenvalues i₀ - c₀) : ℂ) = ↑(hH_herm.eigenvalues i₀ - c₀) from rfl,
        hi₀, sub_self] at this
    simp at this
  -- σ - c₀ρ = S (H - c₀I) Sᴴ
  have h_key := key_identity' (σ := σ) hρ hρ_pd c₀
  -- S is a unit
  have hS_unit := sqrtFactor_isUnit' hρ hρ_pd
  -- Transfer PSD/not PD via conjugation
  refine ⟨c₀, hc₀_pos, ?_, ?_⟩
  · -- PSD
    rw [h_key, show S * (H - (↑c₀ : ℂ) • 1) * Sᴴ =
      S * (H - (↑c₀ : ℂ) • 1) * star S from by simp [Matrix.star_eq_conjTranspose]]
    exact (Matrix.IsUnit.posSemidef_star_right_conjugate_iff hS_unit).mpr hHc_psd
  · -- Not PD
    rw [h_key, show S * (H - (↑c₀ : ℂ) • 1) * Sᴴ =
      S * (H - (↑c₀ : ℂ) • 1) * star S from by simp [Matrix.star_eq_conjTranspose]]
    intro h_pd
    exact hHc_not_pd ((Matrix.IsUnit.posDef_star_right_conjugate_iff hS_unit).mp h_pd)

/-- **Uniqueness**: any two nonzero PSD fixed points of an injective
transfer map are proportional.

**Proof.** Both ρ and σ are PD (by `posSemidef_fixedPoint_isPosDef`).
The critical scalar lemma gives `c₀ > 0` with `τ := σ - c₀ρ` PSD but
not PD. By linearity, `τ` is a fixed point. If `τ ≠ 0`, the PD theorem
forces `τ` to be PD — contradiction. So `τ = 0`, giving `σ = c₀ • ρ`. -/
theorem posSemidef_fixedPoint_unique
    (A : MPSTensor d D) (hA : IsInjective A)
    (ρ σ : Matrix (Fin D) (Fin D) ℂ)
    (hρ_psd : ρ.PosSemidef) (hρ_ne : ρ ≠ 0)
    (hσ_psd : σ.PosSemidef) (hσ_ne : σ ≠ 0)
    (hρ_fix : transferMap (d := d) (D := D) A ρ = ρ)
    (hσ_fix : transferMap (d := d) (D := D) A σ = σ) :
    ∃ c : ℂ, σ = c • ρ := by
  classical
  -- Step 1: Both ρ and σ are PD
  have hρ_pd := posSemidef_fixedPoint_isPosDef A hA ρ hρ_psd hρ_ne hρ_fix
  have hσ_pd := posSemidef_fixedPoint_isPosDef A hA σ hσ_psd hσ_ne hσ_fix
  -- Step 2: Handle D = 0 case
  by_cases hD : D = 0
  · exact ⟨1, by ext i; exact (Fin.elim0 (hD ▸ i))⟩
  · haveI : Nonempty (Fin D) := ⟨⟨0, Nat.pos_of_ne_zero hD⟩⟩
    -- Step 3: Get critical scalar c₀
    obtain ⟨c₀, _, hτ_psd, hτ_not_pd⟩ := exists_critical_scalar hρ_pd hσ_pd
    -- Step 4: τ = σ - c₀•ρ is a fixed point
    set τ := σ - (↑c₀ : ℂ) • ρ with hτ_def
    have hτ_fix : transferMap (d := d) (D := D) A τ = τ := by
      simp only [hτ_def, map_sub, LinearMap.map_smul, hρ_fix, hσ_fix]
    -- Step 5: τ = 0 or contradiction
    by_cases hτ_ne : τ = 0
    · exact ⟨↑c₀, sub_eq_zero.mp hτ_ne⟩
    · exfalso
      exact hτ_not_pd (posSemidef_fixedPoint_isPosDef A hA τ hτ_psd hτ_ne hτ_fix)

end Uniqueness

/-! ## Part 3: Existence of PSD fixed point -/

section Existence

/-- Existence of a PSD fixed point for the transfer map of an injective
MPS tensor.

**Mathematical content**: By the Krein-Rutman theorem (finite-dimensional version),
the transfer map `E_A`, which preserves the PSD cone, has a PSD eigenvector for its
spectral radius `r`. After rescaling `A ↦ A/√r`, this eigenvector becomes a fixed
point of the rescaled transfer map.

**Status**: This requires either Brouwer's fixed point theorem or the
finite-dimensional Krein-Rutman theorem, neither of which is currently in Mathlib.

**Note**: Requires normalization `∑ Aᵢ† Aᵢ = 1`, which ensures the transfer map
is trace-preserving. For a general injective tensor, the conclusion should be
`∃ ρ c, ρ.PosSemidef ∧ ρ ≠ 0 ∧ 0 < c ∧ E(ρ) = c • ρ`. The fixed-point version
follows after rescaling so that the spectral radius equals 1. -/
theorem exists_posSemidef_fixedPoint
    (A : MPSTensor d D) (_hA : IsInjective A)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hD : 0 < D) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ, ρ.PosSemidef ∧ ρ ≠ 0 ∧
      transferMap (d := d) (D := D) A ρ = ρ := by
  have hCh := MPSTensor.transferMap_isChannel A hNorm
  exact hCh.exists_posSemidef_fixedPoint (E := transferMap A) hD

end Existence

/-! ## Part 4: Assembling the quantum PF theorem -/

section Assembly

/-- **The quantum Perron–Frobenius theorem for MPS transfer operators.**

The transfer map of an injective MPS tensor has a unique PSD fixed point
(up to scalar), and it is positive definite. -/
theorem quantum_perron_frobenius [DecidableEq (Fin D)]
    (A : MPSTensor d D) (hA : IsInjective A)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hD : 0 < D) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ,
      HasUniqueFixedPoint (transferMap (d := d) (D := D) A) ρ := by
  obtain ⟨ρ, hρ_psd, hρ_ne, hρ_fix⟩ := exists_posSemidef_fixedPoint A hA (by convert hNorm) hD
  have hρ_pd := posSemidef_fixedPoint_isPosDef A hA ρ hρ_psd hρ_ne hρ_fix
  exact ⟨ρ, {
    fixed := hρ_fix
    pos_def := hρ_pd
    unique := fun σ hσ_psd hσ_fix => by
      by_cases hσ : σ = 0
      · exact ⟨0, by simp [hσ]⟩
      · exact posSemidef_fixedPoint_unique A hA ρ σ hρ_psd hρ_ne hσ_psd hσ hρ_fix hσ_fix
  }⟩

/-! ### Bridge: handle the `D = 0` edge case

`quantum_perron_frobenius` requires `0 < D`. The theorem below lifts this restriction. -/

/-- For D = 0, the zero matrix is vacuously positive definite. -/
private lemma posDef_zero_fin0 : (0 : Matrix (Fin 0) (Fin 0) ℂ).PosDef :=
  Matrix.PosDef.of_dotProduct_mulVec_pos Matrix.isHermitian_zero
    (fun x hx => absurd (Subsingleton.elim x 0) hx)

/-- **Injectivity implies unique fixed point** (without the `0 < D` hypothesis).
Wraps `quantum_perron_frobenius` with a vacuous case for `D = 0`. -/
theorem injective_transfer_unique_fixed_point' [DecidableEq (Fin D)]
    (A : MPSTensor d D) (hA : IsInjective A)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ,
      HasUniqueFixedPoint (transferMap (d := d) (D := D) A) ρ := by
  by_cases hD : 0 < D
  · exact quantum_perron_frobenius A hA hNorm hD
  · push_neg at hD
    interval_cases D
    exact ⟨0, {
      fixed := by ext i; exact Fin.elim0 i
      pos_def := posDef_zero_fin0
      unique := fun σ _ _ => ⟨0, by ext i; exact Fin.elim0 i⟩
    }⟩

end Assembly

end MPSTensor
