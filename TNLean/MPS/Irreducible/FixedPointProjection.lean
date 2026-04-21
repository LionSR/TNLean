/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Core.Transfer
import TNLean.Channel.Irreducible.Basic
import TNLean.Channel.Basic

import Mathlib.Analysis.Matrix.Spectrum

import Mathlib.Tactic.NoncommRing

-- For FixedPointSplit theorems (exists_twoBlock_decomp_of_lowerZero etc.)
import TNLean.MPS.Structure.InvariantSubspaceDecomp

/-!
# Fixed point ⇒ invariant support projection (MPS transfer map)

This module implements the standard “support projection argument” used in canonical-form
existence proofs for matrix product states.

If $\rho \succeq 0$ is a fixed point of the transfer map
$$E_A(X) = \sum_i A_i X A_i^\dagger,$$
then the support projection $P = \mathrm{supp}(\rho)$ is invariant under each Kraus operator:
$$(1-P) A_i P = 0.$$

References:
* Perez-Garcia et al., quant-ph/0608197, Thm. 3 (support projector argument)
* Cirac et al., arXiv:1606.00608, §2.3
-/

open scoped Matrix ComplexOrder BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-! ## Support projection of a PSD matrix -/

/-- The (orthogonal) projection onto the support of a PSD matrix.

We construct this using a unitary diagonalization `ρ = U * diag(λ) * Uᴴ` and then set
`P = U * diag(1_{λ>0}) * Uᴴ`.

This is the matrix-algebra version of the range projection of a positive operator.
-/
noncomputable def supportProj (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosSemidef) :
    Matrix (Fin D) (Fin D) ℂ :=
  let hH : ρ.IsHermitian := hρ.isHermitian
  let U : Matrix (Fin D) (Fin D) ℂ := ↑hH.eigenvectorUnitary
  let sgnEig : Fin D → ℂ := fun i => if 0 < hH.eigenvalues i then 1 else 0
  U * Matrix.diagonal sgnEig * Uᴴ

section SupportProjLemmas

variable (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosSemidef)

private noncomputable def supportU : Matrix (Fin D) (Fin D) ℂ :=
  (↑(hρ.isHermitian.eigenvectorUnitary) : Matrix (Fin D) (Fin D) ℂ)

private noncomputable def sgnEig : Fin D → ℂ :=
  fun i => if 0 < (hρ.isHermitian.eigenvalues i) then 1 else 0

private lemma supportProj_eq : supportProj (D := D) ρ hρ = supportU (D := D) ρ hρ *
    Matrix.diagonal (sgnEig (D := D) ρ hρ) * (supportU (D := D) ρ hρ)ᴴ := by
  rfl

private lemma supportU_star_mul_self : (supportU (D := D) ρ hρ)ᴴ * supportU (D := D) ρ hρ = 1 := by
  -- `Uᴴ * U = 1` for a unitary matrix.
  classical
  -- rewrite `ᴴ` as `star` to use the `UnitaryGroup` lemma.
  rw [← Matrix.star_eq_conjTranspose]
  simp [supportU]

private lemma supportU_mul_star_self : supportU (D := D) ρ hρ * (supportU (D := D) ρ hρ)ᴴ = 1 := by
  classical
  -- The unitary group lemma is phrased with `star`.
  have : (supportU (D := D) ρ hρ) * star (supportU (D := D) ρ hρ) = 1 := by
    -- `U * star U = 1` for a unitary.
    simp [supportU]
  simpa [Matrix.star_eq_conjTranspose] using this

private lemma sgnEig_star : star (sgnEig (D := D) ρ hρ) = sgnEig (D := D) ρ hρ := by
  classical
  ext i
  simp [sgnEig]

private lemma sgnEig_sq :
    ∀ i, sgnEig (D := D) ρ hρ i * sgnEig (D := D) ρ hρ i = sgnEig (D := D) ρ hρ i := by
  classical
  intro i
  simp [sgnEig]

/-- `supportProj ρ` is Hermitian. -/
lemma supportProj_isHermitian : (supportProj (D := D) ρ hρ).IsHermitian := by
  classical
  -- Reduce to the explicit form `P = U * diag(s) * Uᴴ`.
  rw [supportProj_eq (D := D) (ρ := ρ) (hρ := hρ)]
  have hsgn : star (sgnEig (D := D) ρ hρ) = sgnEig (D := D) ρ hρ :=
    sgnEig_star (D := D) ρ hρ
  change (supportU (D := D) ρ hρ * Matrix.diagonal (sgnEig (D := D) ρ hρ) *
      (supportU (D := D) ρ hρ)ᴴ)ᴴ =
    supportU (D := D) ρ hρ * Matrix.diagonal (sgnEig (D := D) ρ hρ) *
      (supportU (D := D) ρ hρ)ᴴ
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.diagonal_conjTranspose, hsgn,
    Matrix.mul_assoc]

/-- `supportProj ρ` is idempotent. -/
lemma supportProj_idem :
    supportProj (D := D) ρ hρ * supportProj (D := D) ρ hρ = supportProj (D := D) ρ hρ := by
  classical
  -- Write `P = U * diag(s) * Uᴴ`.
  have hUU : (supportU (D := D) ρ hρ)ᴴ * supportU (D := D) ρ hρ = 1 :=
    supportU_star_mul_self (D := D) (ρ := ρ) (hρ := hρ)
  rw [supportProj_eq (D := D) (ρ := ρ) (hρ := hρ)]
  -- Expand `P * P` using `Uᴴ * U = 1` and `diag(s) * diag(s) = diag(s)`.
  change supportU (D := D) ρ hρ * Matrix.diagonal (sgnEig (D := D) ρ hρ) *
        (supportU (D := D) ρ hρ)ᴴ *
        (supportU (D := D) ρ hρ * Matrix.diagonal (sgnEig (D := D) ρ hρ) *
          (supportU (D := D) ρ hρ)ᴴ)
      =
      supportU (D := D) ρ hρ * Matrix.diagonal (sgnEig (D := D) ρ hρ) *
        (supportU (D := D) ρ hρ)ᴴ
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
    ← Matrix.mul_assoc ((supportU (D := D) ρ hρ)ᴴ) (supportU (D := D) ρ hρ), hUU, Matrix.one_mul,
    ← Matrix.mul_assoc (Matrix.diagonal (sgnEig (D := D) ρ hρ)), Matrix.diagonal_mul_diagonal,
    show (fun i => sgnEig (D := D) ρ hρ i * sgnEig (D := D) ρ hρ i) = sgnEig (D := D) ρ hρ from
      funext (sgnEig_sq (D := D) (ρ := ρ) (hρ := hρ))]

/-- `supportProj ρ` is an orthogonal projection. -/
lemma isOrthogonalProjection_supportProj :
    IsOrthogonalProjection (supportProj (D := D) ρ hρ) := by
  exact ⟨supportProj_isHermitian (D := D) (ρ := ρ) (hρ := hρ),
    supportProj_idem (D := D) (ρ := ρ) (hρ := hρ)⟩

/-- Spectral decomposition for a Hermitian matrix, in matrix form.

We provide a local helper (to avoid importing `TNLean.QPF.PosDef`).
-/
private lemma spectral_decomp_eq
    (M : Matrix (Fin D) (Fin D) ℂ) (hM : M.IsHermitian) :
    M = (↑hM.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℂ) *
      Matrix.diagonal (fun j => (↑(hM.eigenvalues j) : ℂ)) *
      (↑hM.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℂ)ᴴ := by
  classical
  have h := hM.spectral_theorem
  -- Rewrite the conjugation automorphism into matrix multiplication.
  -- `conjStarAlgAut` acts as `U * X * Uᴴ`.
  rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] at h
  -- The statement matches after rewriting.
  simpa using h

/-- `supportProj ρ` satisfies `P * ρ = ρ`. -/
lemma supportProj_mul (hρ_psd : ρ.PosSemidef) :
    supportProj (D := D) ρ hρ_psd * ρ = ρ := by
  classical
  -- Work in an eigenbasis `ρ = U * diag(λ) * Uᴴ`.
  let hH : ρ.IsHermitian := hρ_psd.isHermitian
  set U : Matrix (Fin D) (Fin D) ℂ := ↑hH.eigenvectorUnitary
  set sgn : Fin D → ℂ := fun i => if 0 < hH.eigenvalues i then 1 else 0
  have hUU : Uᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    simp [U]
  have hsign_mul_eig : sgn * (fun j => (↑(hH.eigenvalues j) : ℂ)) =
      (fun j => (↑(hH.eigenvalues j) : ℂ)) := by
    ext i
    simp only [sgn, Pi.mul_apply]
    split
    · simp only [one_mul]
    · rename_i hi
      push Not at hi
      -- PSD implies eigenvalues are nonnegative, so `¬(0 < λ)` forces `λ = 0`.
      have hnonneg : 0 ≤ hH.eigenvalues i :=
        (hH.posSemidef_iff_eigenvalues_nonneg.mp hρ_psd) i
      simp [le_antisymm hi hnonneg]
  have hρ_spec : ρ = U * Matrix.diagonal (fun j => (↑(hH.eigenvalues j) : ℂ)) * Uᴴ := by
    simpa [U] using (spectral_decomp_eq (D := D) ρ hH)
  have hP_def : supportProj (D := D) ρ hρ_psd = U * Matrix.diagonal sgn * Uᴴ := by
    simp [supportProj, U, sgn]
  -- Compute `P * ρ`.
  rw [hP_def, hρ_spec, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
    ← Matrix.mul_assoc Uᴴ U, hUU, Matrix.one_mul,
    ← Matrix.mul_assoc (Matrix.diagonal sgn), Matrix.diagonal_mul_diagonal,
    show (fun i => sgn i * ↑(hH.eigenvalues i)) = (fun j => (↑(hH.eigenvalues j) : ℂ)) from
      hsign_mul_eig]

/-- `supportProj ρ` satisfies `ρ * P = ρ`. -/
lemma mul_supportProj (hρ_psd : ρ.PosSemidef) :
    ρ * supportProj (D := D) ρ hρ_psd = ρ := by
  classical
  -- Take conjugate transpose of the `P * ρ = ρ` identity.
  have hPρ : supportProj (D := D) ρ hρ_psd * ρ = ρ :=
    supportProj_mul (D := D) (ρ := ρ) hρ_psd
  have hHermP : (supportProj (D := D) ρ hρ_psd).IsHermitian :=
    (isOrthogonalProjection_supportProj (D := D) (ρ := ρ) (hρ := hρ_psd)).1
  have hHermρ : ρ.IsHermitian := hρ_psd.isHermitian
  have : (supportProj (D := D) ρ hρ_psd * ρ)ᴴ = ρᴴ := congrArg Matrix.conjTranspose hPρ
  -- Rewrite.
  simpa [Matrix.conjTranspose_mul, hHermP.eq, hHermρ.eq] using this

end SupportProjLemmas


/-! ## Fixed point ⇒ invariant support projection -/

section FixedPointInvariant

/-- Adjoint identity for dot product: `star x ⬝ᵥ (M *ᵥ y) = star (Mᴴ *ᵥ x) ⬝ᵥ y`.

This helper is intentionally kept local to this file: unlike
`orthogonalProjection_posSemidef` in `Irreducible/Basic`, this is a small linear-algebra
rewrite used only in the fixed-point support-projection argument below, and exporting it
would add API surface without a second in-repo call site.
-/
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

/-- If `ρ` is PSD and `E_A(ρ)=ρ`, then `ker ρ` is invariant under each adjoint Kraus operator.

Formally, `ρ *ᵥ x = 0` implies `ρ *ᵥ ((A i)ᴴ *ᵥ x) = 0`.
-/
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
    conv_lhs =>
      rw [show ρ *ᵥ x = (transferMap (d := d) (D := D) A ρ) *ᵥ x by rw [hρ_fix]]
    simp only [transferMap_apply, Matrix.sum_mulVec]
    rw [dotProduct_sum]
    congr 1
    ext i
    -- reassociate and use the adjoint identity
    have : (A i * ρ * (A i)ᴴ) *ᵥ x = A i *ᵥ (ρ *ᵥ ((A i)ᴴ *ᵥ x)) := by
      simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [this, dotProduct_mulVec_conjTranspose]
  have h_each_zero : ∀ i : Fin d,
      star ((A i)ᴴ *ᵥ x) ⬝ᵥ (ρ *ᵥ ((A i)ᴴ *ᵥ x)) = 0 := by
    intro i
    have h_sum_zero :
        ∑ j : Fin d,
            RCLike.re (star ((A j)ᴴ *ᵥ x) ⬝ᵥ (ρ *ᵥ ((A j)ᴴ *ᵥ x))) = 0 := by
      rw [← map_sum, ← hsum, hqf]
      exact Complex.zero_re
    have hre :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hρ_psd.re_dotProduct_nonneg _)).mp
          h_sum_zero i (Finset.mem_univ _)
    exact Complex.ext hre (hρ_psd.isHermitian.im_star_dotProduct_mulVec_self _)
  intro i
  exact mulVec_eq_zero_of_quadForm_eq_zero ρ hρ_psd _ (h_each_zero i)


/-- If `ρ` is a PSD fixed point of the transfer map, then its support projection is invariant:
`(1 - P) * A i * P = 0` for all Kraus operators `A i`.
-/
theorem lowerZero_of_posSemidef_fixedPoint
    (A : MPSTensor d D)
    (ρ : Matrix (Fin D) (Fin D) ℂ)
    (hρ_psd : ρ.PosSemidef)
    (hρ_fix : transferMap (d := d) (D := D) A ρ = ρ) :
    let P := supportProj (D := D) ρ hρ_psd
    IsOrthogonalProjection P ∧ (∀ i : Fin d, (1 - P) * A i * P = 0) := by
  classical
  -- Notation for the support projection.
  let P : Matrix (Fin D) (Fin D) ℂ := supportProj (D := D) ρ hρ_psd
  have hP_proj : IsOrthogonalProjection P :=
    isOrthogonalProjection_supportProj (D := D) (ρ := ρ) (hρ := hρ_psd)
  have hP_herm : P.IsHermitian := hP_proj.1
  have hP_idem : P * P = P := hP_proj.2
  have hP1P : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP_idem, sub_self]
  have h1PP : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP_idem, sub_self]
  -- Multiplication identities `P*ρ=ρ` and `ρ*P=ρ`.
  have hPρ : P * ρ = ρ := supportProj_mul (D := D) (ρ := ρ) hρ_psd
  have hρP : ρ * P = ρ := mul_supportProj (D := D) (ρ := ρ) hρ_psd
  have hPρP : P * ρ * P = ρ := by simp [hPρ, hρP]
  -- Kernel inclusion: `ker P ⊆ ker ρ`.
  have ker_P_sub_ker_ρ : ∀ v, P *ᵥ v = 0 → ρ *ᵥ v = 0 := by
    intro v hv
    calc
      ρ *ᵥ v = (P * ρ * P) *ᵥ v := by rw [hPρP]
      _ = P *ᵥ (ρ *ᵥ (P *ᵥ v)) := by
            simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = 0 := by
            rw [hv]
            simp only [Matrix.mulVec_zero]
  -- Kernel inclusion: `ker ρ ⊆ ker P` (spectral argument).
  have ker_ρ_sub_ker_P : ∀ v, ρ *ᵥ v = 0 → P *ᵥ v = 0 := by
    intro v hv
    -- Expand the definition of the support projector.
    let hH : ρ.IsHermitian := hρ_psd.isHermitian
    set U : Matrix (Fin D) (Fin D) ℂ := ↑hH.eigenvectorUnitary
    set s : Fin D → ℂ := fun i => if 0 < hH.eigenvalues i then 1 else 0
    have hUU : Uᴴ * U = 1 := by
      rw [← Matrix.star_eq_conjTranspose]
      simp [U]
    -- Work in the eigenbasis: `w := Uᴴ *ᵥ v`.
    set w : Fin D → ℂ := Uᴴ *ᵥ v
    have hΛw : Matrix.diagonal (fun j => (↑(hH.eigenvalues j) : ℂ)) *ᵥ w = 0 := by
      have hρv : (U * Matrix.diagonal (fun j => (↑(hH.eigenvalues j) : ℂ)) * Uᴴ) *ᵥ v = 0 :=
        spectral_decomp_eq (D := D) ρ hH ▸ hv
      set Λ : Matrix (Fin D) (Fin D) ℂ := Matrix.diagonal (fun j => (↑(hH.eigenvalues j) : ℂ))
      have hUΛw : U *ᵥ (Λ *ᵥ w) = 0 := by
        rw [Matrix.mulVec_mulVec, show w = Uᴴ *ᵥ v from rfl, Matrix.mulVec_mulVec]
        exact hρv
      have : Uᴴ *ᵥ (U *ᵥ (Λ *ᵥ w)) = 0 := by
        rw [hUΛw]
        simp only [Matrix.mulVec_zero]
      rwa [Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec] at this
    have h_comp : ∀ j, (↑(hH.eigenvalues j) : ℂ) * w j = 0 := fun j => by
      have := congrFun hΛw j
      simp only [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, Pi.zero_apply,
        ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at this
      exact this
    have hSw : Matrix.diagonal s *ᵥ w = 0 := by
      ext j
      -- Entrywise, multiplying by a diagonal matrix scales each coordinate.
      rw [Matrix.mulVec_diagonal]
      by_cases hjpos : 0 < hH.eigenvalues j
      · have : w j = 0 := by
          have hEig_ne : (↑(hH.eigenvalues j) : ℂ) ≠ 0 := by
            exact_mod_cast (ne_of_gt hjpos)
          exact (mul_eq_zero.mp (h_comp j)).resolve_left hEig_ne
        simp [s, hjpos, this]
      · simp [s, hjpos]
    -- Finish: compute `P *ᵥ v` in the `U` eigenbasis.
    have hP_def : P = U * Matrix.diagonal s * Uᴴ := by
      simp [P, supportProj, U, s]
    change (U * Matrix.diagonal s * Uᴴ) *ᵥ v = 0
    have : (U * Matrix.diagonal s * Uᴴ) *ᵥ v = U *ᵥ (Matrix.diagonal s *ᵥ w) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    rw [this, hSw]
    simp only [Matrix.mulVec_zero]
  -- Complement-zero (invariance) statement.
  have h_complement_zero : ∀ i : Fin d, (1 - P) * A i * P = 0 := by
    intro i
    -- It suffices to prove the adjoint statement and then take `conjTranspose`.
    suffices h : P * (A i)ᴴ * (1 - P) = 0 by
      have := congrArg Matrix.conjTranspose h
      -- rewrite `conjTranspose` and use Hermiticity of `P`.
      simp [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
        Matrix.conjTranspose_conjTranspose, hP_herm.eq] at this
      -- reassociate
      simpa [Matrix.mul_assoc] using this
    -- Show the matrix is zero by testing on all vectors.
    suffices h_vec : ∀ v, (P * (A i)ᴴ * (1 - P)) *ᵥ v = 0 by
      ext a b
      -- evaluate on the standard basis vector `e_b`.
      simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_ite_eq'] using
        congrFun (h_vec (Pi.single b 1)) a
    intro v
    -- Rewrite as `P *ᵥ ((A i)ᴴ *ᵥ ((1-P) *ᵥ v))`.
    have : (P * (A i)ᴴ * (1 - P)) *ᵥ v = P *ᵥ ((A i)ᴴ *ᵥ ((1 - P) *ᵥ v)) := by
      simp [Matrix.mul_assoc, Matrix.mulVec_mulVec]
    rw [this]
    -- Use `ker ρ ⊆ ker P` and the kernel invariance lemma.
    apply ker_ρ_sub_ker_P
    -- reduce to `ρ *ᵥ ((A i)ᴴ *ᵥ ((1-P) *ᵥ v)) = 0`.
    -- Apply invariance under adjoint with `x = (1-P) *ᵥ v`.
    have hker : ρ *ᵥ ((1 - P) *ᵥ v) = 0 := by
      -- First show `(1-P)*ᵥ v` is in `ker P`.
      have : P *ᵥ ((1 - P) *ᵥ v) = 0 := by
        -- because `P*(1-P)=0`
        simp [Matrix.mulVec_mulVec, hP1P]
      exact ker_P_sub_ker_ρ _ this
    -- Now apply the invariance lemma.
    simpa using (ker_invariant_under_adjoint (d := d) (D := D) A ρ hρ_psd hρ_fix
      ((1 - P) *ᵥ v) hker i)
  -- Package the result.
  refine ?_
  -- unfold `let P := ...`
  simp [P, hP_proj, h_complement_zero]

end FixedPointInvariant


/-! ## Nontriviality lemmas for the support projection

These lemmas connect the support projection to the nondegeneracy of the original
matrix, and are essential for the "strict dimension decrease" argument used when
iterating the canonical-form splitting step.

References:
* Perez-Garcia et al., quant-ph/0608197, Thm. 3 (lines 769–803): the recursion terminates
  because each irreducible block has strictly smaller bond dimension.
* Cirac et al., arXiv:1606.00608, §2.3: the same argument in a slightly different presentation.
-/

section SupportProjNontriviality

variable {d D : ℕ}

/-- The support projection of a nonzero PSD matrix is nonzero.

If `supportProj ρ hρ` were zero, then `supportProj_mul` would give `0 * ρ = ρ`, i.e., `ρ = 0`.
-/
theorem supportProj_ne_zero_of_ne_zero
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosSemidef) (hne : ρ ≠ 0) :
    supportProj (D := D) ρ hρ ≠ 0 := by
  intro habs
  apply hne
  have h := supportProj_mul (D := D) (ρ := ρ) hρ
  rw [habs, Matrix.zero_mul] at h
  exact h.symm

/-- The support projection of a PSD-but-not-PosDef matrix is not the identity.

If `supportProj ρ hρ = 1`, then every eigenvalue of `ρ` is strictly positive,
hence `ρ` is positive definite — contradicting `¬ ρ.PosDef`.
-/
theorem supportProj_ne_one_of_not_posDef
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosSemidef) (hnotPD : ¬ ρ.PosDef) :
    supportProj (D := D) ρ hρ ≠ 1 := by
  classical
  intro habs
  apply hnotPD
  -- Use the spectral characterization: PSD + all eigenvalues positive ⟹ PosDef.
  let hH : ρ.IsHermitian := hρ.isHermitian
  rw [hH.posDef_iff_eigenvalues_pos]
  -- It suffices to show all eigenvalues are positive.
  intro i
  -- Expand the support projection definition and use `habs`.
  set U : Matrix (Fin D) (Fin D) ℂ := ↑hH.eigenvectorUnitary
  set sgn : Fin D → ℂ := fun j => if 0 < hH.eigenvalues j then 1 else 0
  have hP_def : supportProj (D := D) ρ hρ = U * Matrix.diagonal sgn * Uᴴ := by
    simp [supportProj, U, sgn]
  -- From `P = 1`, deduce `diag(sgn) = 1`.
  have hUU : Uᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    simp [U]
  have hSgn1 : Matrix.diagonal sgn = 1 := by
    have h : U * Matrix.diagonal sgn * Uᴴ = 1 := hP_def ▸ habs
    -- Multiply on the left by `Uᴴ` and on the right by `U`.
    have step1 : Uᴴ * (U * Matrix.diagonal sgn * Uᴴ) * U = Uᴴ * 1 * U := by
      -- Apply the congruence `M ↦ Uᴴ * M * U` to the equality `h`.
      simpa using congrArg (fun M => Uᴴ * M * U) h
    -- Reassociate to expose the unitary cancellations.
    have step2 : (Uᴴ * U) * Matrix.diagonal sgn * (Uᴴ * U) = Uᴴ * U := by
      -- LHS: rewrite `Uᴴ * (U * diag(sgn) * Uᴴ) * U`.
      -- RHS: rewrite `Uᴴ * 1 * U`.
      simpa [Matrix.mul_assoc] using step1
    -- Now cancel `Uᴴ * U = 1`.
    simpa [hUU] using step2
  -- Extract `sgn i = 1` from the diagonal-entry equality.
  have hSgn_i : sgn i = 1 := by
    have hentry := congrArg (fun M => M i i) hSgn1
    simpa [Matrix.diagonal_apply] using hentry
  -- `sgn i = 1` means `0 < eigenvalues i`.
  by_cases hi : 0 < hH.eigenvalues i
  · exact hi
  · -- Otherwise `sgn i = 0`, contradicting `sgn i = 1`.
    have : (if 0 < hH.eigenvalues i then (1 : ℂ) else 0) = 1 := by simpa [sgn] using hSgn_i
    simp [hi] at this

end SupportProjNontriviality

/-!
## Fixed point → 2-block decomposition

This section covers the canonical-form reduction step

> PSD fixed point → invariant support projection → two-block direct sum.

Concretely, if $\rho \succeq 0$ satisfies $E_A(\rho)=\rho$, then the support
projection $P := \mathrm{supp}(\rho)$ is invariant under the Kraus operators `(A i)`, i.e.
`(1 - P) * A i * P = 0`. Applying `exists_twoBlock_decomp_of_lowerZero`, we obtain an
explicit two-block block-diagonal tensor which is MPV-equivalent to `A`.

References:
* Perez-Garcia et al., quant-ph/0608197, Thm. 3 (support projection argument)
* Cirac et al., arXiv:1606.00608, §2.3
-/

/-- If `ρ` is a PSD fixed point of the transfer map, then `A` is MPV-equivalent to a
2-block block-diagonal tensor.

This is just the composition
`lowerZero_of_posSemidef_fixedPoint` + `exists_twoBlock_decomp_of_lowerZero`.
-/
theorem exists_twoBlock_decomp_of_posSemidef_fixedPoint
    (A : MPSTensor d D)
    (ρ : Matrix (Fin D) (Fin D) ℂ)
    (hρ_psd : ρ.PosSemidef)
    (hρ_fix : transferMap (d := d) (D := D) A ρ = ρ) :
    ∃ (n m : ℕ) (_ : n + m = D)
      (A₁ : MPSTensor d n) (A₂ : MPSTensor d m),
      SameMPV₂ A (twoBlockTensor (d := d) (n := n) (m := m) A₁ A₂) := by
  classical
  let P : Matrix (Fin D) (Fin D) ℂ := supportProj (D := D) ρ hρ_psd
  have hP : IsOrthogonalProjection P ∧ (∀ i : Fin d, (1 - P) * A i * P = 0) := by
    simpa [P] using
      (lowerZero_of_posSemidef_fixedPoint (d := d) (D := D) A ρ hρ_psd hρ_fix)
  exact exists_twoBlock_decomp_of_lowerZero (d := d) (D := D) A P hP.1 hP.2

/-- **Strict dimension decrease**: If `ρ` is a PSD fixed point of the transfer map,
`ρ ≠ 0`, and `ρ` is not positive definite, then `A` is MPV-equivalent to a
two-block block-diagonal tensor where **both** block bond dimensions are
strictly less than `D`.

This is the key recursion step in the canonical form existence proof:
each iteration strictly reduces the bond dimension.

The proof composes:
1. `lowerZero_of_posSemidef_fixedPoint` — support projection is invariant,
2. `supportProj_ne_zero_of_ne_zero` — `P ≠ 0` from `ρ ≠ 0`,
3. `supportProj_ne_one_of_not_posDef` — `P ≠ 1` from `¬ρ.PosDef`,
4. `exists_twoBlock_decomp_of_lowerZero_strict` — strict dimension bounds.

References:
* Perez-Garcia et al., quant-ph/0608197, Thm. 3
* Cirac et al., arXiv:1606.00608, §2.3
-/
theorem exists_twoBlock_decomp_of_posSemidef_fixedPoint_strict
    (A : MPSTensor d D)
    (ρ : Matrix (Fin D) (Fin D) ℂ)
    (hρ_psd : ρ.PosSemidef)
    (hρ_fix : transferMap (d := d) (D := D) A ρ = ρ)
    (hρ_ne : ρ ≠ 0)
    (hρ_not_pd : ¬ ρ.PosDef) :
    ∃ n m : ℕ, ∃ _ : n + m = D, n < D ∧ m < D ∧
      ∃ (A₁ : MPSTensor d n) (A₂ : MPSTensor d m),
        SameMPV₂ A (twoBlockTensor (d := d) (n := n) (m := m) A₁ A₂) := by
  -- Step 1: obtain the invariant support projection
  let P : Matrix (Fin D) (Fin D) ℂ := supportProj (D := D) ρ hρ_psd
  have hP_inv : IsOrthogonalProjection P ∧ (∀ i : Fin d, (1 - P) * A i * P = 0) := by
    simpa [P] using
      (lowerZero_of_posSemidef_fixedPoint (d := d) (D := D) A ρ hρ_psd hρ_fix)
  -- Step 2: P ≠ 0 from ρ ≠ 0
  have hP0 : P ≠ 0 := supportProj_ne_zero_of_ne_zero ρ hρ_psd hρ_ne
  -- Step 3: P ≠ 1 from ¬ρ.PosDef
  have hP1 : P ≠ 1 := supportProj_ne_one_of_not_posDef ρ hρ_psd hρ_not_pd
  -- Step 4: apply strict decomposition
  exact exists_twoBlock_decomp_of_lowerZero_strict A P hP_inv.1 hP_inv.2 hP0 hP1

end MPSTensor
