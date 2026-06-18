/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Core.Transfer
import TNLean.Algebra.HermitianHelpers
import TNLean.Channel.Irreducible.Basic
import TNLean.Channel.Basic

import Mathlib.Analysis.Matrix.Spectrum

import Mathlib.Tactic.NoncommRing

-- For FixedPointSplit theorems (exists_twoBlock_decomp_of_lowerZero etc.)
import TNLean.MPS.Structure.InvariantSubspaceDecomp

/-!
# Fixed point ⇒ invariant support projection (MPS transfer map)

This module implements the fixed-point-to-support-projection step used in
canonical-form existence proofs for matrix product states.

If $\rho \succeq 0$ is a fixed point of the transfer map
$$E_A(X) = \sum_i A_i X A_i^\dagger,$$
then the support projection $P = \mathrm{supp}(\rho)$ is invariant under each Kraus operator:
$$(1-P) A_i P = 0.$$

In Pérez-García, Verstraete, Wolf, and Cirac, this is the first half of the
singular-fixed-point case in the proof of Theorem Th:TIcanonical: lines 771–774
introduce the spectral support projection $P_R$, and lines 775–783 prove the
invariant relation by a positivity contradiction.  The finite-ring trace split
is the subsequent step, lines 785–815, and is handled by the
invariant-subspace decomposition results.  Thus the results here should be used
before, not instead of, the source trace-splitting argument.

References:
* Pérez-García, Verstraete, Wolf, and Cirac, Theorem Th:TIcanonical,
  proof lines 771–783 (singular positive fixed point gives an invariant
  support projection)
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
    IsOrthogonalProjection (supportProj (D := D) ρ hρ) :=
  ⟨supportProj_isHermitian (D := D) (ρ := ρ) (hρ := hρ),
    supportProj_idem (D := D) (ρ := ρ) (hρ := hρ)⟩

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
    simpa [U] using (spectral_decomp_eq (D := D) (M := ρ) hH)
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

/-- Kernel inclusion `ker ρ ≤ ker (supportProj ρ)`: if `ρ *ᵥ v = 0`, then the support
projection also annihilates `v`. -/
theorem supportProj_mulVec_eq_zero_of_mulVec_eq_zero
    (v : Fin D → ℂ) (hv : ρ *ᵥ v = 0) :
    supportProj (D := D) ρ hρ *ᵥ v = 0 := by
  classical
  let hH : ρ.IsHermitian := hρ.isHermitian
  set U : Matrix (Fin D) (Fin D) ℂ := ↑hH.eigenvectorUnitary
  set s : Fin D → ℂ := fun i => if 0 < hH.eigenvalues i then 1 else 0
  have hUU : Uᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    simp [U]
  set w : Fin D → ℂ := Uᴴ *ᵥ v
  have hρ_spec : ρ = U * Matrix.diagonal (fun j => (↑(hH.eigenvalues j) : ℂ)) * Uᴴ := by
    simpa [U] using (spectral_decomp_eq (D := D) (M := ρ) hH)
  have hΛw : Matrix.diagonal (fun j => (↑(hH.eigenvalues j) : ℂ)) *ᵥ w = 0 := by
    have hρv : (U * Matrix.diagonal (fun j => (↑(hH.eigenvalues j) : ℂ)) * Uᴴ) *ᵥ v = 0 := by
      rw [← hρ_spec]; exact hv
    have hUΛw : U *ᵥ (Matrix.diagonal (fun j => (↑(hH.eigenvalues j) : ℂ)) *ᵥ w) = 0 := by
      simpa [w, Matrix.mulVec_mulVec, Matrix.mul_assoc] using hρv
    have hUΛw' : Uᴴ *ᵥ (U *ᵥ (Matrix.diagonal (fun j => (↑(hH.eigenvalues j) : ℂ)) *ᵥ w)) = 0 := by
      simp [hUΛw]
    have : (Uᴴ * U) *ᵥ (Matrix.diagonal (fun j => (↑(hH.eigenvalues j) : ℂ)) *ᵥ w) = 0 := by
      simpa [Matrix.mulVec_mulVec, Matrix.mul_assoc] using hUΛw'
    simpa [Matrix.mulVec_mulVec, hUU] using this
  have h_comp : ∀ j, (↑(hH.eigenvalues j) : ℂ) * w j = 0 := fun j => by
    have := congrFun hΛw j
    simpa [Matrix.mulVec, dotProduct, Matrix.diagonal_apply] using this
  have hSw : Matrix.diagonal s *ᵥ w = 0 := by
    ext j
    rw [Matrix.mulVec_diagonal]
    by_cases hjpos : 0 < hH.eigenvalues j
    · have hwj : w j = 0 := by
        have hEig_ne : (↑(hH.eigenvalues j) : ℂ) ≠ 0 := by
          exact_mod_cast (ne_of_gt hjpos)
        exact (mul_eq_zero.mp (h_comp j)).resolve_left hEig_ne
      simp [s, hjpos, hwj]
    · simp [s, hjpos]
  have hP_def : supportProj (D := D) ρ hρ = U * Matrix.diagonal s * Uᴴ := by rfl
  have hPeval : (U * Matrix.diagonal s * Uᴴ) *ᵥ v = U *ᵥ (Matrix.diagonal s *ᵥ w) := by
    simp [w, U, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  simp [hP_def, hPeval, hSw]

end SupportProjLemmas


/-! ## Fixed point ⇒ invariant support projection -/

section FixedPointInvariant

/-- Adjoint identity for dot product: `star x ⬝ᵥ (M *ᵥ y) = star (Mᴴ *ᵥ x) ⬝ᵥ y`.

This auxiliary lemma is intentionally kept local to this file: unlike
`orthogonalProjection_posSemidef` in `Irreducible/Basic`, this is a small linear-algebra
rewrite used only in the fixed-point support-projection argument below, and there is no
second in-repo call site.
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

This proves the support-projection assertion in Pérez-García, Verstraete, Wolf,
and Cirac, Theorem Th:TIcanonical, proof lines 771–783.  The source writes the
fixed point as $X = \sum_\alpha \lambda_\alpha |\alpha\rangle\langle\alpha|$,
lets $P_R$ be its support projection, and proves $A_i P_R = P_R A_i P_R$ by
the positivity contradiction in lines 775–783.
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
  have ker_ρ_sub_ker_P : ∀ v, ρ *ᵥ v = 0 → P *ᵥ v = 0 := fun v hv =>
    supportProj_mulVec_eq_zero_of_mulVec_eq_zero (D := D) ρ hρ_psd v hv
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
  -- Conclude.
  refine ?_
  -- unfold `let P := ...`
  simp [P, hP_proj, h_complement_zero]

end FixedPointInvariant


/-! ## Nontriviality lemmas for the support projection

These lemmas connect the support projection to the nondegeneracy of the original
matrix, and are essential for the "strict dimension decrease" argument used when
iterating the canonical-form splitting step.

References:
* Pérez-García, Verstraete, Wolf, and Cirac, Theorem Th:TIcanonical,
  proof lines 771–783 for the support projection and lines 785–815 for the
  finite-ring trace split whose recursive blocks have smaller dimensions.
* Cirac, Pérez-García, Schuch, and Verstraete, arXiv:1606.00608,
  lines 201–217: invariant subspaces are split into diagonal blocks in the
  canonical-form construction.
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
## Non-scalar fixed point → singular positive fixed point

The next lemma isolates the second fixed-point split in the proof of
PGVWC07 Theorem `Th:TIcanonical`, lines 819--826.  After a block has been
put in the unital normalization, a non-scalar Hermitian fixed point can be
shifted by its largest eigenvalue to give a positive fixed point which is
singular and nonzero.  The preceding support-projection theorem can then split
the block further.
-/

section NonScalarFixedPoint

variable {d D : ℕ}

private lemma max_shift_posSemidef [Nonempty (Fin D)]
    {X : Matrix (Fin D) (Fin D) ℂ} (hX : X.IsHermitian) :
    ((↑(maxEigenvalue hX) : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ) - X).PosSemidef := by
  classical
  set U : Matrix (Fin D) (Fin D) ℂ := ↑hX.eigenvectorUnitary
  have hU_unit : IsUnit U := by
    rw [Matrix.isUnit_iff_isUnit_det]
    simpa [U] using Matrix.UnitaryGroup.det_isUnit hX.eigenvectorUnitary
  rw [smul_one_sub_hermitian_spectral hX (maxEigenvalue hX)]
  rw [show Uᴴ = star U by simp [Matrix.star_eq_conjTranspose]]
  exact (Matrix.IsUnit.posSemidef_star_right_conjugate_iff hU_unit).mpr
    (Matrix.posSemidef_diagonal_iff.mpr (fun i => by
      simp only [Complex.nonneg_iff]
      constructor
      · exact_mod_cast sub_nonneg.mpr (le_maxEigenvalue hX i)
      · simp [Complex.ofReal_im]))

private lemma max_shift_not_posDef [Nonempty (Fin D)]
    {X : Matrix (Fin D) (Fin D) ℂ} (hX : X.IsHermitian) :
    ¬ ((↑(maxEigenvalue hX) : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ) - X).PosDef := by
  classical
  intro h_pd
  set U : Matrix (Fin D) (Fin D) ℂ := ↑hX.eigenvectorUnitary
  have hU_unit : IsUnit U := by
    rw [Matrix.isUnit_iff_isUnit_det]
    simpa [U] using Matrix.UnitaryGroup.det_isUnit hX.eigenvectorUnitary
  have h_diag_pd :
      (Matrix.diagonal (fun j => (↑(maxEigenvalue hX - hX.eigenvalues j) : ℂ)) :
        Matrix (Fin D) (Fin D) ℂ).PosDef := by
    have h_pd' := h_pd
    rw [smul_one_sub_hermitian_spectral hX (maxEigenvalue hX)] at h_pd'
    rw [show Uᴴ = star U by simp [Matrix.star_eq_conjTranspose]] at h_pd'
    exact (Matrix.IsUnit.posDef_star_right_conjugate_iff hU_unit).mp h_pd'
  rw [Matrix.posDef_diagonal_iff] at h_diag_pd
  obtain ⟨i₀, hi₀⟩ := maxEigenvalue_achieved hX
  have := h_diag_pd i₀
  have hzero : maxEigenvalue hX - hX.eigenvalues i₀ = 0 := by
    exact sub_eq_zero.mpr hi₀.symm
  simp [hzero] at this

/-- A non-scalar Hermitian fixed point of a unital MPS transfer map yields a
nonzero singular positive fixed point.

This is the formal fixed-point shift used in Pérez-García, Verstraete, Wolf,
and Cirac, Theorem `Th:TIcanonical`, proof lines 819--826.  The paper writes
`I - λ₁⁻¹ X`; the equivalent scalar-free form used here is
`λ_max I - X`, which avoids a separate sign assumption on the largest
eigenvalue. -/
theorem exists_singular_posSemidef_fixedPoint_of_unital_nonScalar_fixedPoint
    [Nonempty (Fin D)]
    (A : MPSTensor d D) (X : Matrix (Fin D) (Fin D) ℂ)
    (h_unital : transferMap (d := d) (D := D) A 1 = 1)
    (hX_herm : X.IsHermitian)
    (hX_fix : transferMap (d := d) (D := D) A X = X)
    (hX_nonscalar : ¬ ∃ c : ℂ, X = c • (1 : Matrix (Fin D) (Fin D) ℂ)) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ,
      ρ.PosSemidef ∧ transferMap (d := d) (D := D) A ρ = ρ ∧
        ρ ≠ 0 ∧ ¬ ρ.PosDef := by
  classical
  let c : ℝ := maxEigenvalue hX_herm
  let ρ : Matrix (Fin D) (Fin D) ℂ := (↑c : ℂ) • 1 - X
  have hρ_psd : ρ.PosSemidef := by
    simpa [ρ, c] using max_shift_posSemidef (D := D) hX_herm
  have hρ_not_pd : ¬ ρ.PosDef := by
    simpa [ρ, c] using max_shift_not_posDef (D := D) hX_herm
  have hρ_fix : transferMap (d := d) (D := D) A ρ = ρ := by
    change transferMap (d := d) (D := D) A ((↑c : ℂ) • 1 - X) = (↑c : ℂ) • 1 - X
    rw [map_sub, map_smul, h_unital, hX_fix]
  have hρ_ne : ρ ≠ 0 := by
    intro hρ_zero
    apply hX_nonscalar
    refine ⟨(↑c : ℂ), ?_⟩
    have hsub : (↑c : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ) - X = 0 := by
      simpa [ρ] using hρ_zero
    exact (sub_eq_zero.mp hsub).symm
  exact ⟨ρ, hρ_psd, hρ_fix, hρ_ne, hρ_not_pd⟩

end NonScalarFixedPoint

/-!
## Fixed point → 2-block decomposition

This section covers the canonical-form reduction step

> PSD fixed point → invariant support projection → two-block direct sum.

Concretely, if $\rho \succeq 0$ satisfies $E_A(\rho)=\rho$, then the support
projection $P := \mathrm{supp}(\rho)$ is invariant under the Kraus operators `(A i)`, i.e.
`(1 - P) * A i * P = 0`. Applying `exists_twoBlock_decomp_of_lowerZero`, we obtain an
explicit two-block block-diagonal tensor which is MPV-equivalent to `A`.

References:
* Pérez-García, Verstraete, Wolf, and Cirac, Theorem Th:TIcanonical,
  proof lines 771–783 for the support projection and lines 785–815 for the
  finite-ring trace split.
* Cirac, Pérez-García, Schuch, and Verstraete, arXiv:1606.00608,
  lines 201–217 for the corresponding
  invariant-subspace block splitting in the canonical-form construction.
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
* Pérez-García, Verstraete, Wolf, and Cirac, Theorem Th:TIcanonical,
  proof lines 771–783 for deriving the invariant support projection and
  lines 785–815 for the trace split into two smaller blocks.
* Cirac, Pérez-García, Schuch, and Verstraete, arXiv:1606.00608,
  lines 201–217 for the invariant-subspace direct-sum step in the
  canonical-form construction.
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

/-- A non-scalar Hermitian fixed point of a unital transfer map gives a strict
two-block decomposition.

This composes the fixed-point shift from PGVWC07 Theorem `Th:TIcanonical`,
lines 819--826, with the support-projection split from lines 771--815.  The
source phrase "fixed point different from the identity" is implemented here as
"non-scalar fixed point", since scalar multiples of the identity are fixed by
every unital linear map and do not produce a nontrivial support projection. -/
theorem exists_twoBlock_decomp_of_unital_nonScalar_fixedPoint
    [Nonempty (Fin D)]
    (A : MPSTensor d D) (X : Matrix (Fin D) (Fin D) ℂ)
    (h_unital : transferMap (d := d) (D := D) A 1 = 1)
    (hX_herm : X.IsHermitian)
    (hX_fix : transferMap (d := d) (D := D) A X = X)
    (hX_nonscalar : ¬ ∃ c : ℂ, X = c • (1 : Matrix (Fin D) (Fin D) ℂ)) :
    ∃ n m : ℕ, ∃ _ : n + m = D, n < D ∧ m < D ∧
      ∃ (A₁ : MPSTensor d n) (A₂ : MPSTensor d m),
        SameMPV₂ A (twoBlockTensor (d := d) (n := n) (m := m) A₁ A₂) := by
  obtain ⟨ρ, hρ_psd, hρ_fix, hρ_ne, hρ_not_pd⟩ :=
    exists_singular_posSemidef_fixedPoint_of_unital_nonScalar_fixedPoint
      (d := d) (D := D) A X h_unital hX_herm hX_fix hX_nonscalar
  exact exists_twoBlock_decomp_of_posSemidef_fixedPoint_strict
    (d := d) (D := D) A ρ hρ_psd hρ_fix hρ_ne hρ_not_pd

end MPSTensor
