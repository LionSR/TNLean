/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- Keep these dependencies explicit here for readability:
-- • `TNLean.Channel.PositiveMap` for the positive-definiteness API
-- • `TNLean.Channel.Irreducible` for irreducibility/projection lemmas
-- Both are already transitively available through `TNLean.MPS.CPPrimitive`,
-- but listing them directly makes the local proof dependencies honest.
import TNLean.Channel.PositiveMap
import TNLean.Channel.Irreducible
import TNLean.MPS.CPPrimitive

import Mathlib.Tactic.NoncommRing

/-!
# Quantum Perron–Frobenius: Positive Definiteness

If `A` is injective (i.e., `{A_i}` spans `M_D(ℂ)`) and `ρ` is a nonzero
PSD fixed point of `E_A(X) = ∑ A_i X A_i†`, then `ρ` is positive definite.

This formalizes the positive-definiteness part of **Wolf Theorem 6.3**
(Spectral radius of irreducible maps), item 2: the eigenvector corresponding to
the spectral radius is strictly positive (`T(X) = rX > 0`). In our setting the
spectral radius has already been normalized to 1 (i.e., the map is TP), so the
eigenvalue equation becomes a fixed-point equation.

The irreducibility-based variant `posSemidef_fixedPoint_isPosDef_of_irreducible`
follows the same strategy but under the weaker hypothesis `IsIrreducibleMap E`
instead of `IsInjective A`.

## Main results

* `posSemidef_fixedPoint_isPosDef`: PSD fixed point → PD under injectivity
* `posSemidef_fixedPoint_isPosDef_of_irreducible`: same under irreducibility

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, §6.2, Thm 6.3 item 2][Wolf2012QChannels]
* [Evans, Høegh-Krohn, *Spectral properties of positive maps*, 1978][Evans1978Spectral]
-/

open scoped Matrix ComplexOrder BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-! ### Shared spectral decomposition helpers

These are non-private so that `QPF.Uniqueness` can reuse them. -/

lemma eig_conj_mul [DecidableEq (Fin D)]
    {M : Matrix (Fin D) (Fin D) ℂ} (hM : M.IsHermitian) :
    (↑hM.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℂ)ᴴ *
      (↑hM.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℂ) = 1 := by
  rw [← Matrix.star_eq_conjTranspose]
  exact Matrix.UnitaryGroup.star_mul_self hM.eigenvectorUnitary

lemma eig_mul_conj [DecidableEq (Fin D)]
    {M : Matrix (Fin D) (Fin D) ℂ} (hM : M.IsHermitian) :
    (↑hM.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℂ) *
      (↑hM.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℂ)ᴴ = 1 := by
  rw [← Matrix.star_eq_conjTranspose]
  exact Unitary.mul_star_self_of_mem hM.eigenvectorUnitary.prop

lemma spectral_decomp_eq [DecidableEq (Fin D)]
    {M : Matrix (Fin D) (Fin D) ℂ} (hM : M.IsHermitian) :
    M = (↑hM.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℂ) *
      Matrix.diagonal (fun j => (↑(hM.eigenvalues j) : ℂ)) *
      (↑hM.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℂ)ᴴ := by
  have h := hM.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] at h
  convert h using 2

/-! ## Positive definiteness from injectivity -/

section PosDef

/-- Adjoint identity for dot product: `star x ⬝ᵥ (M *ᵥ y) = star (Mᴴ *ᵥ x) ⬝ᵥ y`. -/
private lemma dotProduct_mulVec_conjTranspose
    (M : Matrix (Fin D) (Fin D) ℂ)
    (x y : Fin D → ℂ) :
    star x ⬝ᵥ (M *ᵥ y) = star (Mᴴ *ᵥ x) ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]

private lemma mulVec_eq_zero_of_quadForm_eq_zero
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosSemidef)
    (x : Fin D → ℂ) (hx : star x ⬝ᵥ (ρ *ᵥ x) = 0) :
    ρ *ᵥ x = 0 := by
  classical
  exact (hρ.dotProduct_mulVec_zero_iff x).mp hx

private lemma ker_invariant_under_adjoint
    (A : MPSTensor d D)
    (ρ : Matrix (Fin D) (Fin D) ℂ)
    (hρ_psd : ρ.PosSemidef)
    (hρ_fix : transferMap (d := d) (D := D) A ρ = ρ)
    (x : Fin D → ℂ) (hx : ρ *ᵥ x = 0) :
    ∀ i : Fin d, ρ *ᵥ ((A i)ᴴ *ᵥ x) = 0 := by
  classical
  have hqf : star x ⬝ᵥ (ρ *ᵥ x) = 0 := by simp [hx]
  have hsum : star x ⬝ᵥ (ρ *ᵥ x) =
      ∑ i : Fin d, star ((A i)ᴴ *ᵥ x) ⬝ᵥ (ρ *ᵥ ((A i)ᴴ *ᵥ x)) := by
    conv_lhs => rw [show ρ *ᵥ x = (transferMap (d := d) (D := D) A ρ) *ᵥ x from by rw [hρ_fix]]
    simp only [transferMap_apply, Matrix.sum_mulVec]
    rw [dotProduct_sum]
    congr 1; ext i
    rw [show (A i * ρ * (A i)ᴴ) *ᵥ x = A i *ᵥ (ρ *ᵥ ((A i)ᴴ *ᵥ x)) from by
      simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]]
    rw [dotProduct_mulVec_conjTranspose]
  have h_each_zero : ∀ i : Fin d,
      star ((A i)ᴴ *ᵥ x) ⬝ᵥ (ρ *ᵥ ((A i)ᴴ *ᵥ x)) = 0 := by
    intro i
    have h_sum_zero : ∑ j, RCLike.re (star ((A j)ᴴ *ᵥ x) ⬝ᵥ (ρ *ᵥ ((A j)ᴴ *ᵥ x))) = 0 := by
      rw [← map_sum, ← hsum, hqf]; simp
    have hre := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hρ_psd.re_dotProduct_nonneg _)).mp
      h_sum_zero i (Finset.mem_univ _)
    exact Complex.ext hre (hρ_psd.isHermitian.im_star_dotProduct_mulVec_self _)
  intro i
  exact mulVec_eq_zero_of_quadForm_eq_zero ρ hρ_psd _ (h_each_zero i)

private lemma ker_contains_all_of_span
    (A : MPSTensor d D) (hA : IsInjective A)
    (ρ : Matrix (Fin D) (Fin D) ℂ)
    (x : Fin D → ℂ)
    (h : ∀ i : Fin d, ρ *ᵥ ((A i)ᴴ *ᵥ x) = 0) :
    ∀ M : Matrix (Fin D) (Fin D) ℂ, ρ *ᵥ (M *ᵥ x) = 0 := by
  intro M
  suffices ∀ N : Matrix (Fin D) (Fin D) ℂ, ρ *ᵥ (Nᴴ *ᵥ x) = 0 by
    specialize this Mᴴ; rwa [Matrix.conjTranspose_conjTranspose] at this
  intro N
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

/-- **Positive definiteness from injectivity** (Wolf Thm 6.3(2)):
If `A` is injective and `ρ` is a nonzero PSD fixed point of the transfer map,
then `ρ` is positive definite. -/
theorem posSemidef_fixedPoint_isPosDef
    (A : MPSTensor d D) (hA : IsInjective A)
    (ρ : Matrix (Fin D) (Fin D) ℂ)
    (hρ_psd : ρ.PosSemidef) (hρ_ne : ρ ≠ 0)
    (hρ_fix : transferMap (d := d) (D := D) A ρ = ρ) :
    ρ.PosDef := by
  classical
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨hρ_psd.isHermitian, fun x hx => ?_⟩
  have h_nonneg := hρ_psd.dotProduct_mulVec_nonneg x
  suffices h_ne : star x ⬝ᵥ (ρ *ᵥ x) ≠ 0 from
    lt_of_le_of_ne h_nonneg (Ne.symm h_ne)
  intro h_zero
  have h_ker := mulVec_eq_zero_of_quadForm_eq_zero ρ hρ_psd x h_zero
  have h_inv := ker_invariant_under_adjoint A ρ hρ_psd hρ_fix x h_ker
  have h_all := ker_contains_all_of_span A hA ρ x h_inv
  have h_surj : ∀ v : Fin D → ℂ, ρ *ᵥ v = 0 := by
    intro v
    have ⟨k, hk⟩ : ∃ k, x k ≠ 0 := by
      by_contra h_all_zero; push_neg at h_all_zero
      exact hx (funext h_all_zero)
    let M : Matrix (Fin D) (Fin D) ℂ := Matrix.of (fun i j => if j = k then v i * (x k)⁻¹ else 0)
    have hMx : M *ᵥ x = v := by
      ext i
      simp only [M, Matrix.mulVec, dotProduct, Matrix.of_apply]
      rw [Finset.sum_eq_single k]
      · simp [hk]
      · intro j _ hj; simp [hj]
      · exact absurd (Finset.mem_univ k)
    rw [← hMx]; exact h_all M
  have h_rho_zero : ρ = 0 := by
    ext i j
    have h := congr_fun (h_surj (Pi.single j 1)) i
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply, Pi.zero_apply] at h
    simpa [Finset.sum_ite_eq, Finset.mem_univ] using h
  exact hρ_ne h_rho_zero

/-- Corollary for the irreducibility-based formulation (still Wolf Thm 6.3(2),
but with `IsIrreducibleMap E` instead of `IsInjective A`). -/
theorem posSemidef_fixedPoint_isPosDef_of_irreducible
    (A : MPSTensor d D)
    (hIrr : IsIrreducibleMap (transferMap (d := d) (D := D) A))
    (ρ : Matrix (Fin D) (Fin D) ℂ)
    (hρ_psd : ρ.PosSemidef) (hρ_ne : ρ ≠ 0)
    (hρ_fix : transferMap (d := d) (D := D) A ρ = ρ) :
    ρ.PosDef := by
  classical
  by_contra hρ_not_pd
  have hH := hρ_psd.isHermitian
  have h_not_all_pos : ¬∀ i, 0 < hH.eigenvalues i :=
    fun h => hρ_not_pd (hH.posDef_iff_eigenvalues_pos.mpr h)
  push_neg at h_not_all_pos
  obtain ⟨j₀, hj₀⟩ := h_not_all_pos
  have hj₀_eq : hH.eigenvalues j₀ = 0 :=
    le_antisymm hj₀ (hH.posSemidef_iff_eigenvalues_nonneg.mp hρ_psd j₀)
  set U : Matrix (Fin D) (Fin D) ℂ := ↑hH.eigenvectorUnitary
  set sgnEig : Fin D → ℂ := fun i => if 0 < hH.eigenvalues i then 1 else 0
  set Q := U * Matrix.diagonal sgnEig * Uᴴ with hQ_def
  have hUU : Uᴴ * U = 1 := eig_conj_mul hH
  have hUU' : U * Uᴴ = 1 := eig_mul_conj hH
  have hsgnEig_star : star sgnEig = sgnEig := by
    ext i; simp only [sgnEig, Pi.star_apply]; split <;> simp
  have hsgnEig_sq : ∀ i, sgnEig i * sgnEig i = sgnEig i := by
    intro i; simp only [sgnEig]; split <;> simp
  have hsign_mul_eig : sgnEig * (fun j => (↑(hH.eigenvalues j) : ℂ)) =
      (fun j => (↑(hH.eigenvalues j) : ℂ)) := by
    ext i; simp only [sgnEig, Pi.mul_apply]; split
    · simp
    · rename_i h; push_neg at h
      simp [le_antisymm h (hH.posSemidef_iff_eigenvalues_nonneg.mp hρ_psd i)]
  have hQ_herm : Q.IsHermitian := by
    change (U * Matrix.diagonal sgnEig * Uᴴ)ᴴ = U * Matrix.diagonal sgnEig * Uᴴ
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, Matrix.diagonal_conjTranspose, hsgnEig_star,
        Matrix.mul_assoc]
  have hQ_idem : Q * Q = Q := by
    change U * Matrix.diagonal sgnEig * Uᴴ * (U * Matrix.diagonal sgnEig * Uᴴ) =
         U * Matrix.diagonal sgnEig * Uᴴ
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
        ← Matrix.mul_assoc Uᴴ U, hUU, Matrix.one_mul,
        ← Matrix.mul_assoc (Matrix.diagonal sgnEig), Matrix.diagonal_mul_diagonal,
        show (fun i => sgnEig i * sgnEig i) = sgnEig from funext hsgnEig_sq]
  have hQ1Q : Q * (1 - Q) = 0 := by rw [mul_sub, mul_one, hQ_idem, sub_self]
  have h1QQ : (1 - Q) * Q = 0 := by rw [sub_mul, one_mul, hQ_idem, sub_self]
  have hQ_proj : IsOrthogonalProjection Q := ⟨hQ_herm, hQ_idem⟩
  have hQρ : Q * ρ = ρ := by
    have hρ_spectral := spectral_decomp_eq hH
    rw [hρ_spectral, hQ_def,
        Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
        ← Matrix.mul_assoc Uᴴ U, hUU, Matrix.one_mul,
        ← Matrix.mul_assoc (Matrix.diagonal sgnEig), Matrix.diagonal_mul_diagonal,
        show (fun i => sgnEig i * ↑(hH.eigenvalues i)) =
            (fun j => (↑(hH.eigenvalues j) : ℂ)) from hsign_mul_eig]
  have hρQ : ρ * Q = ρ := by
    have : (Q * ρ)ᴴ = ρᴴ := congr_arg Matrix.conjTranspose hQρ
    rwa [Matrix.conjTranspose_mul, hQ_herm.eq, hH.eq] at this
  have hQρQ : Q * ρ * Q = ρ := by rw [hQρ, hρQ]
  have ker_Q_sub_ker_ρ : ∀ v, Q *ᵥ v = 0 → ρ *ᵥ v = 0 := by
    intro v hv
    calc ρ *ᵥ v = (Q * ρ * Q) *ᵥ v := by rw [hQρQ]
      _ = Q *ᵥ (ρ *ᵥ (Q *ᵥ v)) := by rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ = 0 := by rw [hv]; simp
  have ker_ρ_sub_ker_Q : ∀ v, ρ *ᵥ v = 0 → Q *ᵥ v = 0 := by
    intro v hv
    set w := Uᴴ *ᵥ v
    have hΛw : Matrix.diagonal (fun j => (↑(hH.eigenvalues j) : ℂ)) *ᵥ w = 0 := by
      have hρv : (U * Matrix.diagonal (fun j => (↑(hH.eigenvalues j) : ℂ)) * Uᴴ) *ᵥ v = 0 :=
        spectral_decomp_eq hH ▸ hv
      set Λ := Matrix.diagonal (fun j => (↑(hH.eigenvalues j) : ℂ))
      have hUΛw : U *ᵥ (Λ *ᵥ w) = 0 := by
        rw [Matrix.mulVec_mulVec, show w = Uᴴ *ᵥ v from rfl, Matrix.mulVec_mulVec]; exact hρv
      have : Uᴴ *ᵥ (U *ᵥ (Λ *ᵥ w)) = 0 := by rw [hUΛw]; simp
      rwa [Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec] at this
    have h_comp : ∀ j, (↑(hH.eigenvalues j) : ℂ) * w j = 0 := fun j => by
      have := congr_fun hΛw j
      simp only [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, Pi.zero_apply,
        ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at this
      exact this
    have hSw : Matrix.diagonal sgnEig *ᵥ w = 0 := by
      ext j; simp only [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, Pi.zero_apply, sgnEig]
      split
      · simp [(mul_eq_zero.mp (h_comp j)).resolve_left (by exact_mod_cast ne_of_gt ‹_›)]
      · simp
    change (U * Matrix.diagonal sgnEig * Uᴴ) *ᵥ v = 0
    have : (U * Matrix.diagonal sgnEig * Uᴴ) *ᵥ v =
           U *ᵥ (Matrix.diagonal sgnEig *ᵥ w) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    rw [this, hSw]; simp
  have h_complement_zero : ∀ i : Fin d, (1 - Q) * A i * Q = 0 := by
    intro i
    suffices h : Q * (A i)ᴴ * (1 - Q) = 0 by
      have := congr_arg Matrix.conjTranspose h
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
        Matrix.conjTranspose_one, Matrix.conjTranspose_conjTranspose,
        hQ_herm.eq, Matrix.conjTranspose_zero] at this
      rwa [← Matrix.mul_assoc] at this
    suffices h_vec : ∀ v, (Q * (A i)ᴴ * (1 - Q)) *ᵥ v = 0 by
      ext a b; simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_ite_eq'] using
        congr_fun (h_vec (Pi.single b 1)) a
    intro v
    rw [show (Q * (A i)ᴴ * (1 - Q)) *ᵥ v = Q *ᵥ ((A i)ᴴ *ᵥ ((1 - Q) *ᵥ v)) from by
      simp only [Matrix.mul_assoc, Matrix.mulVec_mulVec]]
    apply ker_ρ_sub_ker_Q
    apply ker_invariant_under_adjoint A ρ hρ_psd hρ_fix
    apply ker_Q_sub_ker_ρ
    rw [Matrix.mulVec_mulVec, hQ1Q]; simp
  have h_AQ : ∀ i : Fin d, A i * Q = Q * A i * Q := by
    intro i
    exact sub_eq_zero.mp (show A i * Q - Q * A i * Q = 0 by
      calc _ = (1 - Q) * A i * Q := by noncomm_ring
           _ = 0 := h_complement_zero i)
  have h_QA : ∀ i : Fin d, Q * (A i)ᴴ = Q * (A i)ᴴ * Q := by
    intro i
    have := congr_arg Matrix.conjTranspose (h_AQ i)
    simp only [Matrix.conjTranspose_mul, hQ_herm.eq] at this
    rwa [← Matrix.mul_assoc] at this
  have hQ_inv : ∀ X, Q * transferMap (d := d) (D := D) A (Q * X * Q) * Q =
      transferMap (d := d) (D := D) A (Q * X * Q) := by
    intro X; simp only [transferMap_apply, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by
      calc Q * (A i * (Q * X * Q) * (A i)ᴴ) * Q
          = (Q * A i * Q) * X * (Q * (A i)ᴴ * Q) := by noncomm_ring
        _ = (A i * Q) * X * (Q * (A i)ᴴ) := by rw [← h_AQ i, ← h_QA i]
        _ = A i * (Q * X * Q) * (A i)ᴴ := by noncomm_ring
  have hQ_zero_or_one := hIrr Q hQ_proj hQ_inv
  have hQ_ne_zero : Q ≠ 0 := by
    intro hQ_zero; apply hρ_ne; rw [← hQρ, hQ_zero]; simp
  have hQ_ne_one : Q ≠ 1 := by
    intro hQ_one
    have hdiag_one : Matrix.diagonal sgnEig = 1 :=
      calc Matrix.diagonal sgnEig
          = (Uᴴ * U) * Matrix.diagonal sgnEig * (Uᴴ * U) := by rw [hUU]; simp
        _ = Uᴴ * (U * Matrix.diagonal sgnEig * Uᴴ) * U := by noncomm_ring
        _ = Uᴴ * 1 * U := by rw [show U * Matrix.diagonal sgnEig * Uᴴ = Q from rfl, hQ_one]
        _ = 1 := by rw [Matrix.mul_one, hUU]
    have : sgnEig j₀ = 1 := by
      simpa using congr_fun (Matrix.diagonal_injective
        (hdiag_one.trans Matrix.diagonal_one.symm)) j₀
    simp [sgnEig, hj₀_eq] at this
  rcases hQ_zero_or_one with h | h
  · exact hQ_ne_zero h
  · exact hQ_ne_one (by convert h)

end PosDef

end MPSTensor
