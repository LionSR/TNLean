/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.BlockPermutation
import TNLean.Algebra.MatrixGramUnitary
import TNLean.Algebra.SkolemNoether

import Mathlib.Algebra.Central.Matrix
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Unitary Skolem--Noether theorem for complex matrices

A star-algebra automorphism of a nonzero full complex matrix algebra is
conjugation by a unitary matrix.  This is the simple-summand implementation
step used in CPSV16, arXiv:1606.00608, Appendix C.4, line 1997, following
Wolf--Perez-Garcia, arXiv:1005.4545, Theorem 8, source lines 322--324.
-/

open scoped Matrix ComplexOrder

namespace MPSTensor

/-- A star-algebra automorphism of a nonzero full complex matrix algebra is
implemented by unitary conjugation.

Source: CPSV16, arXiv:1606.00608, Appendix C.4, line 1997; the argument cited
there is Wolf--Perez-Garcia, arXiv:1005.4545, Theorem 8, source lines
322--324. -/
theorem exists_unitary_conj_of_starAlgEquiv_matrix
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (f : Matrix n n ℂ ≃⋆ₐ[ℂ] Matrix n n ℂ) :
    ∃ U : Matrix.unitaryGroup n ℂ, ∀ M : Matrix n n ℂ,
      f M = (U : Matrix n n ℂ) * M * (U : Matrix n n ℂ)ᴴ := by
  classical
  obtain ⟨P, hP⟩ := skolemNoether_matrix f.toAlgEquiv
  have hPinvP :
      (↑(P⁻¹ : GL n ℂ) : Matrix n n ℂ) * (↑P : Matrix n n ℂ) = 1 :=
    congrArg Units.val (inv_mul_cancel P)
  have hPPinv :
      (↑P : Matrix n n ℂ) * (↑(P⁻¹ : GL n ℂ) : Matrix n n ℂ) = 1 :=
    congrArg Units.val (mul_inv_cancel P)
  have hstar_inner : ∀ X : Matrix n n ℂ,
      (↑P : Matrix n n ℂ) * Xᴴ * (↑(P⁻¹ : GL n ℂ) : Matrix n n ℂ) =
        (↑(P⁻¹ : GL n ℂ) : Matrix n n ℂ)ᴴ * Xᴴ * (↑P : Matrix n n ℂ)ᴴ := by
    intro X
    have h := map_star f X
    rw [Matrix.star_eq_conjTranspose,
      show f Xᴴ = (↑P : Matrix n n ℂ) * Xᴴ *
        (↑(P⁻¹ : GL n ℂ) : Matrix n n ℂ) from hP Xᴴ,
      show f X = (↑P : Matrix n n ℂ) * X *
        (↑(P⁻¹ : GL n ℂ) : Matrix n n ℂ) from hP X] at h
    simpa only [Matrix.star_eq_conjTranspose, Matrix.mul_assoc, Matrix.conjTranspose_mul] using h
  have hPstarPinvstar :
      (↑P : Matrix n n ℂ)ᴴ * (↑(P⁻¹ : GL n ℂ) : Matrix n n ℂ)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hPinvP, Matrix.conjTranspose_one]
  have hP_star_comm : ∀ Y : Matrix n n ℂ,
      (↑P : Matrix n n ℂ)ᴴ * (↑P : Matrix n n ℂ) * Y =
        Y * ((↑P : Matrix n n ℂ)ᴴ * (↑P : Matrix n n ℂ)) := by
    intro Y
    specialize hstar_inner Yᴴ
    simp only [Matrix.conjTranspose_conjTranspose] at hstar_inner
    calc
      (↑P : Matrix n n ℂ)ᴴ * (↑P : Matrix n n ℂ) * Y
          = (↑P : Matrix n n ℂ)ᴴ *
              ((↑P : Matrix n n ℂ) * Y * (↑(P⁻¹ : GL n ℂ) : Matrix n n ℂ)) *
              (↑P : Matrix n n ℂ) := by
            simp only [Matrix.mul_assoc, hPinvP, Matrix.mul_one]
      _ = (↑P : Matrix n n ℂ)ᴴ *
            ((↑(P⁻¹ : GL n ℂ) : Matrix n n ℂ)ᴴ * Y *
              (↑P : Matrix n n ℂ)ᴴ) *
            (↑P : Matrix n n ℂ) := by
            exact congrArg (fun Z : Matrix n n ℂ ↦
              (↑P : Matrix n n ℂ)ᴴ * Z * (↑P : Matrix n n ℂ)) hstar_inner
      _ = ((↑P : Matrix n n ℂ)ᴴ *
              (↑(P⁻¹ : GL n ℂ) : Matrix n n ℂ)ᴴ) * Y *
            ((↑P : Matrix n n ℂ)ᴴ * (↑P : Matrix n n ℂ)) := by
            simp only [Matrix.mul_assoc]
      _ = Y * ((↑P : Matrix n n ℂ)ᴴ * (↑P : Matrix n n ℂ)) := by
            rw [Matrix.mul_assoc, hPstarPinvstar, Matrix.one_mul]
  have hPHP_center :
      (↑P : Matrix n n ℂ)ᴴ * (↑P : Matrix n n ℂ) ∈
        Set.range (Matrix.scalar n : ℂ →+* Matrix n n ℂ) := by
    rw [← Matrix.center_eq_range, Semigroup.mem_center_iff]
    exact fun Y ↦ (hP_star_comm Y).symm
  obtain ⟨c, hc_eq⟩ := hPHP_center
  rw [Matrix.scalar_apply] at hc_eq
  have hPHP_smul :
      (↑P : Matrix n n ℂ)ᴴ * (↑P : Matrix n n ℂ) = c • (1 : Matrix n n ℂ) := by
    rw [← hc_eq, ← Matrix.smul_one_eq_diagonal]
  have hPHP_psd :
      ((↑P : Matrix n n ℂ)ᴴ * (↑P : Matrix n n ℂ)).PosSemidef :=
    Matrix.posSemidef_conjTranspose_mul_self _
  let i : n := Classical.choice (inferInstance : Nonempty n)
  have hc_nonneg : 0 ≤ c := by
    have hdiag :
        ((↑P : Matrix n n ℂ)ᴴ * (↑P : Matrix n n ℂ)) i i = c := by
      rw [hPHP_smul]
      simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    simpa only [hdiag] using hPHP_psd.diag_nonneg (i := i)
  have hc_ne : c ≠ 0 := by
    intro hc0
    have h0 : (↑P : Matrix n n ℂ)ᴴ * (↑P : Matrix n n ℂ) = 0 := by
      rw [hPHP_smul, hc0, zero_smul]
    have hPH_zero : (↑P : Matrix n n ℂ)ᴴ = 0 := by
      have h := congrArg (· * (↑(P⁻¹ : GL n ℂ) : Matrix n n ℂ)) h0
      simp only [Matrix.zero_mul, Matrix.mul_assoc] at h
      rwa [hPPinv, Matrix.mul_one] at h
    have hP_zero : (↑P : Matrix n n ℂ) = 0 := by
      rw [← Matrix.conjTranspose_conjTranspose (↑P : Matrix n n ℂ),
        hPH_zero, Matrix.conjTranspose_zero]
    exact one_ne_zero (show (1 : Matrix n n ℂ) = 0 by
      rw [← hPPinv, hP_zero, Matrix.zero_mul])
  have hc_re_nonneg : 0 ≤ c.re := (RCLike.nonneg_iff.mp hc_nonneg).1
  have hc_im_zero : c.im = 0 := (RCLike.nonneg_iff.mp hc_nonneg).2
  have hc_re_pos : 0 < c.re := by
    rcases lt_or_eq_of_le hc_re_nonneg with h | h
    · exact h
    · exact absurd (Complex.ext h.symm (by simpa using hc_im_zero)) hc_ne
  have hc_eq_re : (c.re : ℂ) = c :=
    Complex.ext (Complex.ofReal_re _) (by simpa using hc_im_zero.symm)
  let V : Matrix n n ℂ := ((Real.sqrt c.re : ℂ))⁻¹ • (↑P : Matrix n n ℂ)
  have hV_mem : V ∈ Matrix.unitaryGroup n ℂ := by
    apply Matrix.smul_mem_unitaryGroup_of_conjTranspose_mul_self_eq_smul_one hc_re_pos
    rw [hc_eq_re, hPHP_smul]
  have hVHV : Vᴴ * V = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff'.mp hV_mem)
  have hr_ne : (Real.sqrt c.re : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hc_re_pos).ne'
  have hPm_eq :
      (↑P : Matrix n n ℂ) = (Real.sqrt c.re : ℂ) • V := by
    simp only [V, smul_smul, mul_inv_cancel₀ hr_ne, one_smul]
  have hVPinv :
      V * (↑(P⁻¹ : GL n ℂ) : Matrix n n ℂ) =
        (Real.sqrt c.re : ℂ)⁻¹ • (1 : Matrix n n ℂ) := by
    rw [show V = (Real.sqrt c.re : ℂ)⁻¹ • (↑P : Matrix n n ℂ) from rfl,
      smul_mul_assoc, hPPinv]
  have hPinvm_eq :
      (↑(P⁻¹ : GL n ℂ) : Matrix n n ℂ) =
        (Real.sqrt c.re : ℂ)⁻¹ • Vᴴ := by
    calc
      (↑(P⁻¹ : GL n ℂ) : Matrix n n ℂ)
          = 1 * (↑(P⁻¹ : GL n ℂ) : Matrix n n ℂ) :=
              (Matrix.one_mul _).symm
      _ = (Vᴴ * V) * (↑(P⁻¹ : GL n ℂ) : Matrix n n ℂ) := by rw [hVHV]
      _ = Vᴴ * (V * (↑(P⁻¹ : GL n ℂ) : Matrix n n ℂ)) := by
            rw [Matrix.mul_assoc]
      _ = Vᴴ * ((Real.sqrt c.re : ℂ)⁻¹ • (1 : Matrix n n ℂ)) := by
            rw [hVPinv]
      _ = (Real.sqrt c.re : ℂ)⁻¹ • Vᴴ := by
            rw [mul_smul_comm, Matrix.mul_one]
  refine ⟨⟨V, hV_mem⟩, fun M ↦ ?_⟩
  change f M = V * M * Vᴴ
  rw [show f M = (↑P : Matrix n n ℂ) * M *
      (↑(P⁻¹ : GL n ℂ) : Matrix n n ℂ) from hP M,
    hPm_eq, hPinvm_eq, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, smul_smul,
    inv_mul_cancel₀ hr_ne, one_smul]

section PairedBlocks

variable {I J : Type*} [Finite I] [DecidableEq I] [Finite J] [DecidableEq J]
variable {d : I → ℕ} {e : J → ℕ}
variable [∀ i, NeZero (d i)] [∀ j, NeZero (e j)]

noncomputable local instance sourceMatrix_isSimpleRing (i : I) :
    IsSimpleRing (Matrix (Fin (d i)) (Fin (d i)) ℂ) := by
  have : Nonempty (Fin (d i)) := Fin.pos_iff_nonempty.mp (NeZero.pos (d i))
  exact IsSimpleRing.matrix (Fin (d i)) ℂ

noncomputable local instance targetMatrix_isSimpleRing (j : J) :
    IsSimpleRing (Matrix (Fin (e j)) (Fin (e j)) ℂ) := by
  have : Nonempty (Fin (e j)) := Fin.pos_iff_nonempty.mp (NeZero.pos (e j))
  exact IsSimpleRing.matrix (Fin (e j)) ℂ

/-- The star-algebra equivalence obtained by restricting a product equivalence
to a supplied pair of simple matrix summands.

The supplied pairing is the relabeling fixed in arXiv:1606.00608,
Appendix C.4, line 1997. -/
noncomputable def blockComponentStarAlgEquiv
    (T : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) ≃⋆ₐ[ℂ]
      (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ))
    (sigma : I ≃ J)
    (hsigma : ∀ i, T.toRingEquiv.mapTwoSidedIdeal
      (blockIdeal (fun k ↦ Matrix (Fin (d k)) (Fin (d k)) ℂ) i) =
        blockIdeal (fun k ↦ Matrix (Fin (e k)) (Fin (e k)) ℂ) (sigma i))
    (i : I) :
    Matrix (Fin (d i)) (Fin (d i)) ℂ ≃⋆ₐ[ℂ]
      Matrix (Fin (e (sigma i))) (Fin (e (sigma i))) ℂ := by
  classical
  let phi : Matrix (Fin (d i)) (Fin (d i)) ℂ →⋆ₙₐ[ℂ]
      Matrix (Fin (e (sigma i))) (Fin (e (sigma i))) ℂ :=
    { toFun := fun M ↦ T (Pi.single i M) (sigma i)
      map_zero' := by simp only [Pi.single_zero, map_zero, Pi.zero_apply]
      map_add' := by
        intro M N
        simp only [Pi.single_add, map_add, Pi.add_apply]
      map_mul' := by
        intro M N
        simp only [Pi.single_mul, map_mul, Pi.mul_apply]
      map_smul' := by
        intro c M
        simp only [Pi.single_smul, map_smul, Pi.smul_apply, MonoidHom.id_apply]
      map_star' := by
        intro M
        rw [Pi.single_star, map_star, Pi.star_apply] }
  exact StarAlgEquiv.ofBijective phi
    (blockComponentMap_bijective T.toRingEquiv sigma hsigma i)

/-- Reindexing both matrix indices along the same equivalence is a
star-algebra equivalence. -/
noncomputable def matrixReindexStarAlgEquiv
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (p : m ≃ n) : Matrix m m ℂ ≃⋆ₐ[ℂ] Matrix n n ℂ :=
  StarAlgEquiv.ofAlgEquiv (Matrix.reindexAlgEquiv ℂ ℂ p) fun M ↦ by
    change Matrix.reindex p p (star M) = star (Matrix.reindex p p M)
    rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_reindex]

/-- The restriction of a product star-algebra equivalence to each supplied
pair of equally sized simple matrix summands is implemented by a unitary.

This is the unitary implementation step in arXiv:1606.00608,
Appendix C.4, line 1997. The statement retains the supplied summand pairing
and dimension equalities rather than selecting new witnesses. -/
theorem exists_unitary_block_implementers_of_starAlgEquiv_pi_matrix
    (T : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) ≃⋆ₐ[ℂ]
      (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ))
    (sigma : I ≃ J)
    (hsigma : ∀ i, T.toRingEquiv.mapTwoSidedIdeal
      (blockIdeal (fun k ↦ Matrix (Fin (d k)) (Fin (d k)) ℂ) i) =
        blockIdeal (fun k ↦ Matrix (Fin (e k)) (Fin (e k)) ℂ) (sigma i))
    (hDim : ∀ i, d i = e (sigma i)) :
    ∃ U : ∀ i, Matrix.unitaryGroup (Fin (e (sigma i))) ℂ,
      ∀ (i : I) (M : Matrix (Fin (d i)) (Fin (d i)) ℂ),
        T (Pi.single i M) (sigma i) =
          (U i : Matrix (Fin (e (sigma i))) (Fin (e (sigma i))) ℂ) *
            Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDim i)) M *
              (U i : Matrix (Fin (e (sigma i))) (Fin (e (sigma i))) ℂ)ᴴ := by
  classical
  have hImplementer (i : I) :
      ∃ U : Matrix.unitaryGroup (Fin (e (sigma i))) ℂ,
        ∀ M : Matrix (Fin (d i)) (Fin (d i)) ℂ,
          T (Pi.single i M) (sigma i) =
            (U : Matrix (Fin (e (sigma i))) (Fin (e (sigma i))) ℂ) *
              Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDim i)) M *
                (U : Matrix (Fin (e (sigma i))) (Fin (e (sigma i))) ℂ)ᴴ := by
    let reindexEquiv := matrixReindexStarAlgEquiv (finCongr (hDim i))
    let componentEquiv := blockComponentStarAlgEquiv T sigma hsigma i
    let automorphism := reindexEquiv.symm.trans componentEquiv
    obtain ⟨U, hU⟩ := exists_unitary_conj_of_starAlgEquiv_matrix automorphism
    refine ⟨U, fun M ↦ ?_⟩
    change componentEquiv M =
      (U : Matrix (Fin (e (sigma i))) (Fin (e (sigma i))) ℂ) *
        reindexEquiv M *
          (U : Matrix (Fin (e (sigma i))) (Fin (e (sigma i))) ℂ)ᴴ
    have hComponent : componentEquiv M = automorphism (reindexEquiv M) := by
      simp only [automorphism, StarAlgEquiv.trans_apply, StarAlgEquiv.symm_apply_apply]
    rw [hComponent, hU]
  exact ⟨fun i ↦ (hImplementer i).choose,
    fun i ↦ (hImplementer i).choose_spec⟩

end PairedBlocks

end MPSTensor
