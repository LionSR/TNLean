/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.SkolemNoetherUnitary
import TNLean.Algebra.CornerCompression

/-!
# Spatial implementation of isomorphisms between matrix corners

This file proves that a multiplicative, adjoint-preserving linear equivalence
between two corners of a full complex matrix algebra is implemented by an
ambient partial isometry.

## Main results

* `exists_partial_isometry_implementing_corner_linearEquiv`
* `exists_partial_isometry_transporting_compressions`
-/

open scoped Matrix ComplexOrder

namespace MPSTensor

/-- A unitary conjugation between two compressed matrix algebras extends to an
ambient partial isometry, and conjugation by this partial isometry transports
the two compression maps.

Source: arXiv:1708.00029, Appendix A, lines 985–1002. -/
theorem exists_partial_isometry_transporting_compressions
    {D n : ℕ} (P Q : MatrixAlg D)
    (φP : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ] cornerSubmodule P)
    (φQ : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ] cornerSubmodule Q)
    (VP VQ : Matrix (Fin D) (Fin n) ℂ)
    (hVP_iso : VPᴴ * VP = 1) (hVP_range : VP * VPᴴ = P)
    (hVQ_iso : VQᴴ * VQ = 1) (hVQ_range : VQ * VQᴴ = Q)
    (hφP : ∀ X : Matrix (Fin n) (Fin n) ℂ, (φP X).1 = VP * X * VPᴴ)
    (hφQ : ∀ X : Matrix (Fin n) (Fin n) ℂ, (φQ X).1 = VQ * X * VQᴴ)
    (W : Matrix.unitaryGroup (Fin n) ℂ) :
    ∃ U : MatrixAlg D,
      U = P * U * Q ∧
      Uᴴ * U = Q ∧
      U * Uᴴ = P ∧
      ∀ X : Matrix (Fin n) (Fin n) ℂ,
        (φP ((W : Matrix (Fin n) (Fin n) ℂ) * X *
          (W : Matrix (Fin n) (Fin n) ℂ)ᴴ)).1 =
            U * (φQ X).1 * Uᴴ := by
  let Wmat : Matrix (Fin n) (Fin n) ℂ := W
  let U : MatrixAlg D := VP * Wmat * VQᴴ
  have hWstarW : Wmatᴴ * Wmat = 1 := by
    simpa [Wmat, Matrix.star_eq_conjTranspose] using Matrix.UnitaryGroup.star_mul_self W
  have hWWstar : Wmat * Wmatᴴ = 1 := by
    simpa [Wmat, Matrix.star_eq_conjTranspose] using Unitary.mul_star_self_of_mem W.prop
  have hPVP : P * VP = VP := by
    rw [← hVP_range, Matrix.mul_assoc, hVP_iso, Matrix.mul_one]
  have hVQstarQ : VQᴴ * Q = VQᴴ := by
    rw [← hVQ_range, ← Matrix.mul_assoc, hVQ_iso, Matrix.one_mul]
  have hU_eq : U = VP * Wmat * VQᴴ := rfl
  have htemp_Ueq_PUQ : VP * Wmat * VQᴴ = P * (VP * Wmat * VQᴴ) * Q := by
    calc
      VP * Wmat * VQᴴ = (VP * Wmat) * VQᴴ := rfl
      _ = (VP * Wmat) * (VQᴴ * Q) := by rw [hVQstarQ]
      _ = ((VP * Wmat) * VQᴴ) * Q := by simp [Matrix.mul_assoc]
      _ = (((P * VP) * Wmat) * VQᴴ) * Q := by rw [hPVP]
      _ = P * (VP * Wmat * VQᴴ) * Q := by simp [Matrix.mul_assoc]
  refine ⟨U, ?_, ?_, ?_, ?_⟩
  · -- Goal: U = P * U * Q
    rw [hU_eq]
    exact htemp_Ueq_PUQ
  · -- Goal: Uᴴ * U = Q
    dsimp [U]
    calc
      (VP * Wmat * VQᴴ)ᴴ * (VP * Wmat * VQᴴ)
          = (VQ * Wmatᴴ * VPᴴ) * (VP * Wmat * VQᴴ) := by
            simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      _ = VQ * Wmatᴴ * VPᴴ * VP * Wmat * VQᴴ := by repeat' rw [Matrix.mul_assoc]
      _ = VQ * Wmatᴴ * (VPᴴ * VP) * Wmat * VQᴴ := by repeat' rw [Matrix.mul_assoc]
      _ = VQ * Wmatᴴ * 1 * Wmat * VQᴴ := by rw [hVP_iso]
      _ = VQ * (Wmatᴴ * Wmat) * VQᴴ := by repeat' rw [Matrix.mul_assoc]
      _ = VQ * 1 * VQᴴ := by rw [hWstarW]
      _ = VQ * VQᴴ := by rw [Matrix.mul_one]
      _ = Q := hVQ_range
  · -- Goal: U * Uᴴ = P
    dsimp [U]
    calc
      (VP * Wmat * VQᴴ) * (VP * Wmat * VQᴴ)ᴴ
          = (VP * Wmat * VQᴴ) * (VQ * Wmatᴴ * VPᴴ) := by
            simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      _ = VP * Wmat * VQᴴ * VQ * Wmatᴴ * VPᴴ := by repeat' rw [Matrix.mul_assoc]
      _ = VP * Wmat * (VQᴴ * VQ) * Wmatᴴ * VPᴴ := by repeat' rw [Matrix.mul_assoc]
      _ = VP * Wmat * 1 * Wmatᴴ * VPᴴ := by rw [hVQ_iso]
      _ = VP * (Wmat * Wmatᴴ) * VPᴴ := by repeat' rw [Matrix.mul_assoc]
      _ = VP * 1 * VPᴴ := by rw [hWWstar]
      _ = VP * VPᴴ := by rw [Matrix.mul_one]
      _ = P := hVP_range
  · -- Goal: ∀ X, (φP (W * X * Wᴴ)).1 = U * (φQ X).1 * Uᴴ
    dsimp [U]
    intro X
    rw [hφP, hφQ]
    simp only [Wmat, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    repeat' rw [Matrix.mul_assoc]
    rw [hVQ_iso]
    simp

/-- A multiplicative, adjoint-preserving linear equivalence between two
corners of a full complex matrix algebra is implemented by an ambient partial
isometry whose initial and final projections are the corner units.

Source: arXiv:1708.00029, Appendix A, lines 985–1002. -/
theorem exists_partial_isometry_implementing_corner_linearEquiv
    {D : ℕ} (P Q : MatrixAlg D)
    (hP : IsOrthogonalProjection P) (hQ : IsOrthogonalProjection Q)
    [Fact (P * P = P)] [Fact (Q * Q = Q)]
    (f : cornerSubmodule Q ≃ₗ[ℂ] cornerSubmodule P)
    (hMul : ∀ X Y : cornerSubmodule Q, f (X * Y) = f X * f Y)
    (hStar : ∀ X : cornerSubmodule Q, (f ⟨X.1ᴴ, by
      simpa [cornerSubmodule, hQ.1.eq, Matrix.conjTranspose_mul, Matrix.mul_assoc]
        using congrArg (·ᴴ) X.2⟩).1 = (f X).1ᴴ) :
    ∃ U : MatrixAlg D,
      U = P * U * Q ∧
      Uᴴ * U = Q ∧
      U * Uᴴ = P ∧
      ∀ X : cornerSubmodule Q, (f X).1 = U * X.1 * Uᴴ := by
  classical
  obtain ⟨UP, SP, TP, nP, -, eSTP, eSP, hUPUP, hUPstarUP, hPdiag_std,
    hP_decomp, hPdiag_back, htraceP, -⟩ :=
    ProjectionSpectralSplit.ofOrthogonalProjection P hP
  obtain ⟨UQ, SQ, TQ, nQ, -, eSTQ, eSQ, hUQUQ, hUQstarUQ, hQdiag_std,
    hQ_decomp, hQdiag_back, htraceQ, -⟩ :=
    ProjectionSpectralSplit.ofOrthogonalProjection Q hQ
  let P0 : Matrix (SP ⊕ TP) (SP ⊕ TP) ℂ :=
    Matrix.fromBlocks (1 : Matrix SP SP ℂ) 0 0 (0 : Matrix TP TP ℂ)
  let Q0 : Matrix (SQ ⊕ TQ) (SQ ⊕ TQ) ℂ :=
    Matrix.fromBlocks (1 : Matrix SQ SQ ℂ) 0 0 (0 : Matrix TQ TQ ℂ)
  let φP : Matrix (Fin nP) (Fin nP) ℂ ≃ₗ[ℂ] cornerSubmodule P :=
    cornerCompressionLinearEquiv (P := P) (Pdiag := UPᴴ * P * UP) UP eSTP eSP
      P0 rfl hP_decomp rfl hPdiag_std hPdiag_back hUPstarUP hUPUP
  let φQ : Matrix (Fin nQ) (Fin nQ) ℂ ≃ₗ[ℂ] cornerSubmodule Q :=
    cornerCompressionLinearEquiv (P := Q) (Pdiag := UQᴴ * Q * UQ) UQ eSTQ eSQ
      Q0 rfl hQ_decomp rfl hQdiag_std hQdiag_back hUQstarUQ hUQUQ
  let VP : Matrix (Fin D) (Fin nP) ℂ := cornerCompressionIsometry UP eSTP eSP
  let VQ : Matrix (Fin D) (Fin nQ) ℂ := cornerCompressionIsometry UQ eSTQ eSQ
  let gLinear : Matrix (Fin nQ) (Fin nQ) ℂ ≃ₗ[ℂ]
      Matrix (Fin nP) (Fin nP) ℂ :=
    φQ.trans (f.trans φP.symm)
  have hfinrank := LinearEquiv.finrank_eq gLinear
  have hsq : nQ ^ 2 = nP ^ 2 := by
    simpa [Module.finrank_matrix, Fintype.card_fin, pow_two] using hfinrank
  have hRank : nQ = nP := Nat.pow_left_injective (by norm_num) hsq
  subst nP
  have hφP_mul (X Y : Matrix (Fin nQ) (Fin nQ) ℂ) :
      (φP (X * Y)).1 = (φP X).1 * (φP Y).1 := by
    exact cornerCompressionExpand_mul UP eSTP eSP hUPstarUP X Y
  have hφQ_mul (X Y : Matrix (Fin nQ) (Fin nQ) ℂ) :
      (φQ (X * Y)).1 = (φQ X).1 * (φQ Y).1 := by
    exact cornerCompressionExpand_mul UQ eSTQ eSQ hUQstarUQ X Y
  have hφP_star (X : Matrix (Fin nQ) (Fin nQ) ℂ) :
      (φP Xᴴ).1 = (φP X).1ᴴ := by
    exact (cornerCompressionExpand_conjTranspose UP eSTP eSP X).symm
  have hφQ_star (X : Matrix (Fin nQ) (Fin nQ) ℂ) :
      (φQ Xᴴ).1 = (φQ X).1ᴴ := by
    exact (cornerCompressionExpand_conjTranspose UQ eSTQ eSQ X).symm
  let g : Matrix (Fin nQ) (Fin nQ) ℂ →⋆ₙₐ[ℂ]
      Matrix (Fin nQ) (Fin nQ) ℂ :=
    { toFun := gLinear
      map_zero' := gLinear.map_zero
      map_add' := gLinear.map_add
      map_smul' := gLinear.map_smul
      map_mul' := by
        intro X Y
        apply φP.injective
        -- Goal: φP (gLinear (X * Y)) = φP (gLinear X * gLinear Y)
        simp [gLinear, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
        -- Goal: f (φQ (X * Y)) = φP (φP.symm (f (φQ X)) * φP.symm (f (φQ Y)))
        have hφP_mul_subtype (A B : Matrix (Fin nQ) (Fin nQ) ℂ) :
            φP (A * B) = φP A * φP B := Subtype.ext (hφP_mul A B)
        have hφQ_mul_subtype (A B : Matrix (Fin nQ) (Fin nQ) ℂ) :
            φQ (A * B) = φQ A * φQ B := Subtype.ext (hφQ_mul A B)
        calc
          f (φQ (X * Y)) = f (φQ X * φQ Y) := by rw [hφQ_mul_subtype X Y]
          _ = f (φQ X) * f (φQ Y) := hMul (φQ X) (φQ Y)
          _ = φP (φP.symm (f (φQ X))) * φP (φP.symm (f (φQ Y))) := by
            simp [LinearEquiv.apply_symm_apply]
          _ = φP (φP.symm (f (φQ X)) * φP.symm (f (φQ Y))) := by
            rw [← hφP_mul_subtype]
      map_star' := by
        intro X
        apply φP.injective
        -- Goal: φP (gLinear Xᴴ) = φP ((gLinear X)ᴴ)
        simp [gLinear, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, hφP_star]
        -- Goal: f (φQ Xᴴ) = (f (φQ X))ᴴ where ᴴ is adjoint in corner
        apply Subtype.ext
        -- Goal: f (φQ Xᴴ).1 = (f (φQ X)).1ᴴ
        convert hStar (φQ X) using 1
        apply Subtype.ext
        simpa using hφQ_star X }
  let gEquiv : Matrix (Fin nQ) (Fin nQ) ℂ ≃⋆ₐ[ℂ]
      Matrix (Fin nQ) (Fin nQ) ℂ :=
    StarAlgEquiv.ofBijective g gLinear.bijective
  cases nQ with
  | zero =>
      have hQzero : Q = 0 := by
        apply (isOrthogonalProjection_posSemidef hQ).trace_eq_zero_iff.mp
        rw [← htraceQ]
        simp
      have hPzero : P = 0 := by
        apply (isOrthogonalProjection_posSemidef hP).trace_eq_zero_iff.mp
        rw [← htraceP]
        -- Goal: (nP : ℂ) = (0 : ℂ). After subst nP, nP = nQ = 0
        simp
      refine ⟨0, by simp [hPzero, hQzero], by simp [hQzero],
        by simp [hPzero], ?_⟩
      intro X
      have hXzero : X.1 = 0 := by simpa [hQzero] using X.2.symm
      have hfXzero : (f X).1 = 0 := by simpa [hPzero] using (f X).2.symm
      simp [hXzero, hfXzero]
  | succ n =>
      obtain ⟨W, hW⟩ := exists_unitary_conj_of_starAlgEquiv_matrix gEquiv
      have hVP_iso : VPᴴ * VP = 1 :=
        cornerCompressionIsometry_conjTranspose_mul UP eSTP eSP hUPstarUP
      have hVQ_iso : VQᴴ * VQ = 1 :=
        cornerCompressionIsometry_conjTranspose_mul UQ eSTQ eSQ hUQstarUQ
      have hVP_range : VP * VPᴴ = P := by
        rw [show VP * VPᴴ =
          cornerCompressionExpand UP eSTP eSP 1 by
            simpa [VP] using
              (cornerCompressionExpand_eq_isometry UP eSTP eSP
                (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).symm]
        exact cornerCompressionExpand_one P (UPᴴ * P * UP) UP eSTP eSP P0 rfl
          hP_decomp hPdiag_back
      have hVQ_range : VQ * VQᴴ = Q := by
        rw [show VQ * VQᴴ =
          cornerCompressionExpand UQ eSTQ eSQ 1 by
            simpa [VQ] using
              (cornerCompressionExpand_eq_isometry UQ eSTQ eSQ
                (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).symm]
        exact cornerCompressionExpand_one Q (UQᴴ * Q * UQ) UQ eSTQ eSQ Q0 rfl
          hQ_decomp hQdiag_back
      have hφP_apply (X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
          (φP X).1 = VP * X * VPᴴ := by
        exact cornerCompressionExpand_eq_isometry UP eSTP eSP X
      have hφQ_apply (X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
          (φQ X).1 = VQ * X * VQᴴ := by
        exact cornerCompressionExpand_eq_isometry UQ eSTQ eSQ X
      obtain ⟨U, hUsupp, hUstarU, hUUstar, hTransport⟩ :=
        exists_partial_isometry_transporting_compressions P Q φP φQ VP VQ
          hVP_iso hVP_range hVQ_iso hVQ_range hφP_apply hφQ_apply W
      refine ⟨U, hUsupp, hUstarU, hUUstar, ?_⟩
      intro X
      let M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := φQ.symm X
      have hφQM : φQ M = X := LinearEquiv.apply_symm_apply φQ X
      have hgM : gEquiv M = (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) * M *
          (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ᴴ := hW M
      have hfX :
          f X = φP ((W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) * M *
            (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ᴴ) := by
        calc
          f X = f (φQ M) := by rw [hφQM]
          _ = φP (φP.symm (f (φQ M))) :=
            (LinearEquiv.apply_symm_apply φP (f (φQ M))).symm
          _ = φP (gLinear M) := rfl
          _ = φP (gEquiv M) := rfl
          _ = φP ((W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) * M *
            (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ᴴ) := by rw [hgM]
      rw [congrArg Subtype.val hfX, hTransport M, congrArg Subtype.val hφQM]

end MPSTensor
