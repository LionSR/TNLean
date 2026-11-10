/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.KroneckerLeastEigenvalue
import TNLean.Circuit.EntropySupport
import QICLean.Analysis.GroundEnergyBounds

/-!
# Ground-energy shifts on disjoint regions

Two Hermitian operators with disjoint site supports have compatible regional
ground vectors. Their least energies add. This supplies the regional scalar
normalization in AKLV, arXiv:1301.1162v1, Section 6.1, lines 901–925.
-/

open scoped Matrix ComplexOrder MatrixOrder Kronecker

noncomputable section

namespace TNLean.MPS.AreaLaw.AKLV

/-- Disjoint supported Hermitian operators admit scalar shifts making each
positive and a common normalized vector annihilated by both shifts.
AKLV, Section 6.1, the product of the regional ground vectors. -/
theorem exists_common_ground_shifts_of_disjoint_support
    {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}
    (S T : Finset V) (hST : Disjoint S T)
    (X Y : Matrix (Entropy.SiteConfig n) (Entropy.SiteConfig n) ℂ)
    (hsX : Entropy.IsSupportedOn X S) (hsY : Entropy.IsSupportedOn Y T)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) (σ₀ : Entropy.SiteConfig n) :
    ∃ (x y : ℝ) (w : Entropy.SiteConfig n → ℂ),
      (X - (x : ℂ) • 1).PosSemidef ∧ (Y - (y : ℂ) • 1).PosSemidef ∧
      star w ⬝ᵥ w = 1 ∧ X *ᵥ w = (x : ℂ) • w ∧ Y *ᵥ w = (y : ℂ) • w := by
  classical
  let e := Entropy.cutEquiv n S
  let A := Entropy.RegionConfig n S
  let B := (v : {v // v ∉ S}) → Fin (n v)
  let a₀ : A := (e σ₀).1
  let b₀ : B := (e σ₀).2
  let M : Matrix A A ℂ := fun a a' ↦ X (e.symm (a, b₀)) (e.symm (a', b₀))
  let N : Matrix B B ℂ := fun b b' ↦ Y (e.symm (a₀, b)) (e.symm (a₀, b'))
  have hM : M.IsHermitian := hX.submatrix (fun a ↦ e.symm (a, b₀))
  have hN : N.IsHermitian := hY.submatrix (fun b ↦ e.symm (a₀, b))
  let : Nonempty A := ⟨a₀⟩
  let : Nonempty B := ⟨b₀⟩
  obtain ⟨x, u, hu, hunitu, hMlow⟩ := hM.exists_unit_eigenvector_le
  obtain ⟨y, v, hv, hunitv, hNlow⟩ := hN.exists_unit_eigenvector_le
  have hXcut : X.submatrix e.symm e.symm = M ⊗ₖ (1 : Matrix B B ℂ) :=
    hsX.cutOperator_eq_kronecker_one (B := S) subset_rfl b₀
  have hYcut : Y.submatrix e.symm e.symm = (1 : Matrix A A ℂ) ⊗ₖ N :=
    hsY.cutOperator_eq_one_kronecker (B := S) hST.symm a₀
  let z : A × B → ℂ := fun p ↦ u p.1 * v p.2
  let w : Entropy.SiteConfig n → ℂ := z ∘ e
  have hunitz : star z ⬝ᵥ z = 1 := by
    rw [Matrix.star_mul_dotProduct_mul u u v v, hunitu, hunitv, mul_one]
  have hunitw : star w ⬝ᵥ w = 1 := by
    change (∑ σ, star (z (e σ)) * z (e σ)) = 1
    calc
      _ = ∑ p : A × B, star (z p) * z p := e.sum_comp _
      _ = 1 := hunitz
  have hXeig : X *ᵥ w = (x : ℂ) • w := by
    have hh : X.submatrix e.symm e.symm *ᵥ z = (x : ℂ) • z := by
      rw [hXcut, Matrix.kronecker_mulVec_mul, hu, Matrix.one_mulVec]
      ext p
      simp only [z, Pi.smul_apply, smul_eq_mul]
      ring
    rw [Matrix.submatrix_mulVec_equiv] at hh
    ext σ
    simpa only [w, Function.comp_apply, e.symm_apply_apply, Equiv.symm_symm, Pi.smul_apply,
      smul_eq_mul] using congrFun hh (e σ)
  have hYeig : Y *ᵥ w = (y : ℂ) • w := by
    have hh : Y.submatrix e.symm e.symm *ᵥ z = (y : ℂ) • z := by
      rw [hYcut, Matrix.kronecker_mulVec_mul, hv, Matrix.one_mulVec]
      ext p
      simp only [z, Pi.smul_apply, smul_eq_mul]
      ring
    rw [Matrix.submatrix_mulVec_equiv] at hh
    ext σ
    simpa only [w, Function.comp_apply, e.symm_apply_apply, Equiv.symm_symm, Pi.smul_apply,
      smul_eq_mul] using congrFun hh (e σ)
  have hXlow : (X - (x : ℂ) • 1).PosSemidef := by
    have hp := (hMlow.kronecker (Matrix.PosSemidef.one : (1 : Matrix B B ℂ).PosSemidef)).submatrix e
    have heq : (M - (x : ℂ) • 1) ⊗ₖ (1 : Matrix B B ℂ) =
        X.submatrix e.symm e.symm - (x : ℂ) • 1 := by
      rw [hXcut, sub_eq_add_neg, ← neg_smul, Matrix.add_kronecker,
        Matrix.smul_kronecker, Matrix.one_kronecker_one]
      simp only [neg_smul, sub_eq_add_neg]
    rw [heq] at hp
    have hback : (X.submatrix e.symm e.symm - (x : ℂ) • 1).submatrix e e =
        X - (x : ℂ) • 1 := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply,
        e.symm_apply_apply, Matrix.one_apply, e.apply_eq_iff_eq]
    rw [hback] at hp
    exact hp
  have hYlow : (Y - (y : ℂ) • 1).PosSemidef := by
    have hp := ((Matrix.PosSemidef.one : (1 : Matrix A A ℂ).PosSemidef).kronecker hNlow).submatrix e
    have heq : (1 : Matrix A A ℂ) ⊗ₖ (N - (y : ℂ) • 1) =
        Y.submatrix e.symm e.symm - (y : ℂ) • 1 := by
      rw [hYcut, sub_eq_add_neg, ← neg_smul, Matrix.kronecker_add,
        Matrix.kronecker_smul, Matrix.one_kronecker_one]
      simp only [neg_smul, sub_eq_add_neg]
    rw [heq] at hp
    have hback : (Y.submatrix e.symm e.symm - (y : ℂ) • 1).submatrix e e =
        Y - (y : ℂ) • 1 := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply,
        e.symm_apply_apply, Matrix.one_apply, e.apply_eq_iff_eq]
    rw [hback] at hp
    exact hp
  exact ⟨x, y, w, hXlow, hYlow, hunitw, hXeig, hYeig⟩

/-- Three disjoint regions can be shifted to positive operators with a common
normalized zero-energy test for their sum. AKLV, Section 6.1. -/
theorem exists_three_disjoint_ground_shifts
    {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}
    (S T U : Finset V) (hST : Disjoint S T) (hSU : Disjoint S U) (hTU : Disjoint T U)
    (X N Y : Matrix (Entropy.SiteConfig n) (Entropy.SiteConfig n) ℂ)
    (hsX : Entropy.IsSupportedOn X S) (hsN : Entropy.IsSupportedOn N T)
    (hsY : Entropy.IsSupportedOn Y U)
    (hX : X.IsHermitian) (hN : N.IsHermitian) (hY : Y.IsHermitian)
    (σ₀ : Entropy.SiteConfig n) :
    ∃ (x m y : ℝ) (w : Entropy.SiteConfig n → ℂ),
      (X - (x : ℂ) • 1).PosSemidef ∧ (N - (m : ℂ) • 1).PosSemidef ∧
      (Y - (y : ℂ) • 1).PosSemidef ∧ star w ⬝ᵥ w = 1 ∧
      (X.PosSemidef → 0 ≤ x) ∧ (N.PosSemidef → 0 ≤ m) ∧ (Y.PosSemidef → 0 ≤ y) ∧
      ((X - (x : ℂ) • 1) + (N - (m : ℂ) • 1) + (Y - (y : ℂ) • 1)) *ᵥ w = 0 := by
  classical
  obtain ⟨x, m, u, hXlow, hNlow, huunit, huX, huN⟩ :=
    exists_common_ground_shifts_of_disjoint_support S T hST X N hsX hsN hX hN σ₀
  have hsXN : Entropy.IsSupportedOn (X + N) (S ∪ T) := by
    have hX' := hsX.mono (Finset.subset_union_left : S ⊆ S ∪ T)
    have hN' := hsN.mono (Finset.subset_union_right : T ⊆ S ∪ T)
    constructor
    · intro σ τ h
      simp only [Matrix.add_apply, hX'.1 σ τ h, hN'.1 σ τ h, add_zero]
    · intro σ τ σ' τ' h1 h2 h3 h4
      simp only [Matrix.add_apply, hX'.2 σ τ σ' τ' h1 h2 h3 h4,
        hN'.2 σ τ σ' τ' h1 h2 h3 h4]
  obtain ⟨p, y, w, hXNlow, hYlow, hwunit, hwXN, hwY⟩ :=
    exists_common_ground_shifts_of_disjoint_support (S ∪ T) U
      (Finset.disjoint_union_left.mpr ⟨hSU, hTU⟩) (X + N) Y hsXN hsY (hX.add hN) hY σ₀
  have hsumlow : (X + N - ((x + m : ℝ) : ℂ) • 1).PosSemidef := by
    convert hXlow.add hNlow using 1
    rw [Complex.ofReal_add, add_smul]
    abel
  have hsumu : (X + N) *ᵥ u = ((x + m : ℝ) : ℂ) • u := by
    rw [Matrix.add_mulVec, huX, huN, Complex.ofReal_add, add_smul]
  have hp : p = x + m := Matrix.groundEnergy_eq_of_normalized_eigenvectors
    (X + N) p (x + m) w u hwXN hwunit hsumu huunit hXNlow hsumlow
  refine ⟨x, m, y, w, hXlow, hNlow, hYlow, hwunit,
    (fun h ↦ h.nonneg_of_normalized_eigenvector x u huX huunit),
    (fun h ↦ h.nonneg_of_normalized_eigenvector m u huN huunit),
    (fun h ↦ h.nonneg_of_normalized_eigenvector y w hwY hwunit), ?_⟩
  have hsum : (X - (x : ℂ) • 1) + (N - (m : ℂ) • 1) + (Y - (y : ℂ) • 1) =
      (X + N - (p : ℂ) • 1) + (Y - (y : ℂ) • 1) := by
    rw [hp, Complex.ofReal_add, add_smul]
    abel
  rw [hsum, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    hwXN, sub_self, zero_add, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    hwY, sub_self]

end TNLean.MPS.AreaLaw.AKLV
