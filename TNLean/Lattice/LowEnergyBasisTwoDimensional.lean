/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.LowEnergyBasisConstruction

/-!
# Choosing the ground-space basis in dimension two

Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1678–1694, chooses an original
compression with maximal eigenvalue spread and diagonalizes it. If every spread is zero,
all compressions are scalar and their off-diagonal parts vanish in every orthonormal basis.
The non-scalar case retains the source's explicit spectral denominator.
-/

open scoped InnerProductSpace

namespace TNLean.Lattice

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- The difference of the two eigenvalues of a self-adjoint operator on a two-dimensional
space. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1680–1687. -/
noncomputable def twoDimensionalSpectralSpread (A : E →L[ℂ] E) (hA : IsSelfAdjoint A)
    (hn : Module.finrank ℂ E = 2) : ℝ :=
  |hA.isSymmetric.eigenvalues hn 0 - hA.isSymmetric.eigenvalues hn 1|

/-- A two-dimensional Hermitian compression with zero spectral spread is scalar.
This is the degenerate case of Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 1678–1694. -/
theorem eq_smul_one_of_twoDimensionalSpectralSpread_eq_zero (A : E →L[ℂ] E)
    (hA : IsSelfAdjoint A) (hn : Module.finrank ℂ E = 2)
    (hzero : twoDimensionalSpectralSpread A hA hn = 0) :
    ∃ r : ℝ, A = (r : ℂ) • (1 : E →L[ℂ] E) := by
  let b := hA.isSymmetric.eigenvectorBasis hn
  let r := hA.isSymmetric.eigenvalues hn
  have hr : r 0 = r 1 := sub_eq_zero.mp (abs_eq_zero.mp hzero)
  have hAb (a : Fin 2) : A (b a) = (r 0 : ℂ) • b a := by
    calc A (b a) = (r a : ℂ) • b a := hA.isSymmetric.apply_eigenvectorBasis hn a
      _ = (r 0 : ℂ) • b a := by congr 1; fin_cases a <;> simp_all
  refine ⟨r 0, ?_⟩
  ext x
  calc A x = A (∑ a, ⟪b a, x⟫_ℂ • b a) := congrArg A (b.sum_repr' x).symm
    _ = (r 0 : ℂ) • ∑ a, ⟪b a, x⟫_ℂ • b a := by
      simp only [map_sum, map_smul, hAb, Finset.smul_sum, smul_smul, mul_comm]
    _ = ((r 0 : ℂ) • (1 : E →L[ℂ] E)) x := by rw [b.sum_repr']; rfl

/-- A two-dimensional Hermitian operator differs from a real scalar by an operator whose
norm is its spectral spread. This gives the estimate complementary to division by the
spectral spread in Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1683–1694. -/
theorem exists_norm_sub_smul_one_eq_twoDimensionalSpectralSpread (A : E →L[ℂ] E)
    (hA : IsSelfAdjoint A) (hn : Module.finrank ℂ E = 2) :
    ∃ r : ℝ, ‖A - (r : ℂ) • (1 : E →L[ℂ] E)‖ = twoDimensionalSpectralSpread A hA hn := by
  let b := hA.isSymmetric.eigenvectorBasis hn
  let r := hA.isSymmetric.eigenvalues hn
  have hAb (a : Fin 2) : A (b a) = (r a : ℂ) • b a :=
    hA.isSymmetric.apply_eigenvectorBasis hn a
  have hdecomp : A - (r 0 : ℂ) • (1 : E →L[ℂ] E) =
      ((r 1 - r 0 : ℝ) : ℂ) • InnerProductSpace.rankOne ℂ (b 1) (b 1) := by
    ext x
    have hx : x = ⟪b 0, x⟫_ℂ • b 0 + ⟪b 1, x⟫_ℂ • b 1 := by
      simpa only [Fin.sum_univ_two] using (b.sum_repr' x).symm
    rw [hx]
    simp [InnerProductSpace.rankOne_apply, map_add, map_smul, hAb, b.inner_eq_ite, smul_smul]
    module
  refine ⟨r 0, ?_⟩
  rw [hdecomp, norm_smul, InnerProductSpace.norm_rankOne, b.orthonormal.1 1, mul_one,
    mul_one, Complex.norm_real]
  exact abs_sub_comm _ _

/-- In any orthonormal basis of a two-dimensional space, the off-diagonal part of a
Hermitian operator has norm at most its spectral spread. Together with the commutator
estimate this removes small spectral denominators from the qualitative bound of Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, eq. `oibu`, lines 1683–1694. -/
theorem norm_inner_le_twoDimensionalSpectralSpread (A : E →L[ℂ] E)
    (hA : IsSelfAdjoint A) (hn : Module.finrank ℂ E = 2)
    {v : Fin 2 → E} (hv : Orthonormal ℂ v) {a c : Fin 2} (hac : a ≠ c) :
    ‖⟪v a, A (v c)⟫_ℂ‖ ≤ twoDimensionalSpectralSpread A hA hn := by
  obtain ⟨r, hr⟩ := exists_norm_sub_smul_one_eq_twoDimensionalSpectralSpread A hA hn
  have heq : ⟪v a, (A - (r : ℂ) • (1 : E →L[ℂ] E)) (v c)⟫_ℂ =
      ⟪v a, A (v c)⟫_ℂ := by
    simp only [sub_apply, smul_apply, one_apply_eq_self, inner_sub_right, inner_smul_right,
      hv.inner_eq_zero hac, mul_zero, sub_zero]
  rw [← heq, ← hr]
  refine (norm_inner_le_norm _ _).trans ?_
  simpa only [hv.1 a, hv.1 c, one_mul, mul_one] using
    (A - (r : ℂ) • (1 : E →L[ℂ] E)).le_opNorm (v c)

/-- The off-diagonal operator version of the spectral-spread bound. Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1683–1694. -/
theorem norm_offDiagonalPartFamily_le_twoDimensionalSpectralSpread (A : E →L[ℂ] E)
    (hA : IsSelfAdjoint A) (hn : Module.finrank ℂ E = 2)
    {v : Fin 2 → E} (hv : Orthonormal ℂ v) :
    ‖offDiagonalPartFamily v A‖ ≤ twoDimensionalSpectralSpread A hA hn := by
  have hδ : 0 ≤ twoDimensionalSpectralSpread A hA hn := by
    unfold twoDimensionalSpectralSpread
    exact abs_nonneg _
  simpa only [Nat.reduceSub, Nat.cast_one, one_mul] using
    norm_offDiagonalPartFamily_le hv A hδ fun _ _ hac =>
      norm_inner_le_twoDimensionalSpectralSpread A hA hn hv hac

/-- For a finite Hermitian family on a two-dimensional space, either every member is
scalar, or an original member with maximal positive spectral spread has an orthonormal
eigenbasis controlling every off-diagonal part with the source's denominator.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1678–1694. -/
theorem exists_orthonormalBasis_maximal_twoDimensionalSpectralSpread [Finite ι]
    (B : ι → E →L[ℂ] E) (hB : ∀ i, IsSelfAdjoint (B i)) (hn : Module.finrank ℂ E = 2) :
    (∀ i, ∃ r : ℝ, B i = (r : ℂ) • (1 : E →L[ℂ] E)) ∨
    ∃ (j : ι) (b : OrthonormalBasis (Fin 2) ℂ E),
      0 < twoDimensionalSpectralSpread (B j) (hB j) hn ∧
      (∀ i, twoDimensionalSpectralSpread (B i) (hB i) hn ≤
        twoDimensionalSpectralSpread (B j) (hB j) hn) ∧
      (∀ a, B j (b a) = ((hB j).isSymmetric.eigenvalues hn a : ℂ) • b a) ∧
      ∀ i, ‖offDiagonalPartFamily b (B i)‖ ≤
        ‖B j * B i - B i * B j‖ / twoDimensionalSpectralSpread (B j) (hB j) hn := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let δ := fun i => twoDimensionalSpectralSpread (B i) (hB i) hn
  by_cases hzero : ∀ i, δ i = 0
  · exact Or.inl fun i => eq_smul_one_of_twoDimensionalSpectralSpread_eq_zero
      (B i) (hB i) hn (hzero i)
  · obtain ⟨i, hi⟩ := not_forall.mp hzero
    obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ δ ⟨i, Finset.mem_univ i⟩
    have hδ : 0 < δ j := lt_of_lt_of_le
      (lt_of_le_of_ne (abs_nonneg _) (Ne.symm hi)) (hj i (Finset.mem_univ i))
    let b := (hB j).isSymmetric.eigenvectorBasis hn
    let r := (hB j).isSymmetric.eigenvalues hn
    have hgap : ∀ a c : Fin 2, a ≠ c → δ j ≤ |r a - r c| := by
      intro a c hac
      fin_cases a <;> fin_cases c <;> simp_all [δ, twoDimensionalSpectralSpread, abs_sub_comm, r]
    refine Or.inr ⟨j, b, hδ, fun i => hj i (Finset.mem_univ i),
      fun a => (hB j).isSymmetric.apply_eigenvectorBasis hn a, fun i => ?_⟩
    simpa only [Nat.reduceSub, Nat.cast_one, one_mul] using
      norm_offDiagonalPartFamily_le_norm_commutator_div (hB j) (B i) b.orthonormal
        (fun a => (hB j).isSymmetric.apply_eigenvectorBasis hn a) hδ hgap

set_option backward.isDefEq.respectTransparency false in
/-- Normalizing by the original term bounds and comparing the spectral-spread estimate
with the commutator estimate removes the small denominator. The resulting decay is the
square root of the commutator decay. This gives a uniform version of the qualitative
two-dimensional assertion of Hastings, arXiv:cond-mat/0508554v3, eq. `oibu`, lines 1678–1694. -/
theorem exists_orthonormalBasis_norm_inner_le_sqrt_commutator_decay [Finite ι]
    (B : ι → E →L[ℂ] E) (hB : ∀ i, IsSelfAdjoint (B i)) (hn : Module.finrank ℂ E = 2)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hNorm : ∀ i, ‖B i‖ ≤ w i)
    {C : ℝ} (hC : 0 ≤ C) (f : ι → ι → ℝ) (hf : ∀ i j, 0 ≤ f i j)
    (hcomm : ∀ i j, ‖B j * B i - B i * B j‖ ≤ C * w j * w i * (f j i) ^ 2) :
    ∃ b : OrthonormalBasis (Fin 2) ℂ E,
      (∀ i a c, a ≠ c → ⟪b a, B i (b c)⟫_ℂ = 0) ∨
      ∃ j, ∀ i a c, a ≠ c → ‖⟪b a, B i (b c)⟫_ℂ‖ ≤ Real.sqrt C * w i * f j i := by
  classical
  let D : ι → E →L[ℂ] E := fun i => (w i)⁻¹ • B i
  have hD (i : ι) : IsSelfAdjoint (D i) := (IsSelfAdjoint.all ((w i)⁻¹)).smul (hB i)
  have hrestore (i : ι) : w i • D i = B i := by
    by_cases hi : w i = 0
    · have hBi : B i = 0 := norm_eq_zero.mp
        (((hNorm i).trans_eq hi).antisymm (norm_nonneg _))
      simp [D, hi, hBi]
    · simp only [D, smul_smul, mul_inv_cancel₀ hi, one_smul]
  rcases exists_orthonormalBasis_maximal_twoDimensionalSpectralSpread D hD hn with
    hscalar | ⟨j, b, hδ, hmax, hDb, _⟩
  · let b := (stdOrthonormalBasis ℂ E).reindex (finCongr hn)
    refine ⟨b, Or.inl fun i a c hac => ?_⟩
    obtain ⟨r, hr⟩ := hscalar i
    rw [← hrestore i, hr]
    simp only [smul_apply, one_apply_eq_self, ← Complex.coe_smul, inner_smul_right,
      b.orthonormal.inner_eq_zero hac, mul_zero]
  · let δ := twoDimensionalSpectralSpread (D j) (hD j) hn
    let r := (hD j).isSymmetric.eigenvalues hn
    have hwj : 0 < w j := by
      by_contra hj
      have hj0 : w j = 0 := le_antisymm (not_lt.mp hj) (hw j)
      have hr (a : Fin 2) : r a = 0 := by
        have hz : (r a : ℂ) • b a = 0 := (hDb a).symm.trans (by simp [D, hj0])
        exact Complex.ofReal_eq_zero.mp
          ((smul_eq_zero.mp hz).resolve_right (b.orthonormal.ne_zero a))
      have : δ = 0 := by
        change |r 0 - r 1| = 0
        rw [hr 0, hr 1, sub_self, abs_zero]
      exact (ne_of_gt hδ) this
    have hgap {a c : Fin 2} (hac : a ≠ c) : δ ≤ |r a - r c| := by
      fin_cases a <;> fin_cases c <;> simp_all [δ, twoDimensionalSpectralSpread, abs_sub_comm, r]
    refine ⟨b, Or.inr ⟨j, fun i a c hac => ?_⟩⟩
    let z := ‖⟪b a, B i (b c)⟫_ℂ‖
    have hz : 0 ≤ z := norm_nonneg _
    have hsmall : z ≤ w i * δ := by
      have heq : z = w i * ‖⟪b a, D i (b c)⟫_ℂ‖ := by
        dsimp only [z]
        rw [← hrestore i]
        simp only [smul_apply, ← Complex.coe_smul, inner_smul_right, norm_mul,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i)]
      rw [heq]
      exact mul_le_mul_of_nonneg_left
        ((norm_inner_le_twoDimensionalSpectralSpread (D i) (hD i) hn b.orthonormal hac).trans
          (hmax i)) (hw i)
    have hscaled : ‖D j * B i - B i * D j‖ ≤ C * w i * (f j i) ^ 2 := by
      have heq : D j * B i - B i * D j = (w j)⁻¹ • (B j * B i - B i * B j) := by
        simp only [D, smul_mul_assoc, mul_smul_comm, smul_sub]
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hwj)]
      calc _ ≤ (w j)⁻¹ * (C * w j * w i * (f j i) ^ 2) :=
          mul_le_mul_of_nonneg_left (hcomm i j) (inv_nonneg.mpr hwj.le)
        _ = _ := by field_simp
    have hlarge : δ * z ≤ C * w i * (f j i) ^ 2 := by
      have hne : r a ≠ r c := fun heq => by
        have := hgap hac
        rw [heq, sub_self, abs_zero] at this
        exact (not_le_of_gt hδ) this
      have hh := norm_inner_le_norm_commutator_div (hD j) (B i) (hDb a) (hDb c) hne
      simp only [b.orthonormal.1 a, b.orthonormal.1 c, mul_one] at hh
      have hh' : z ≤ ‖D j * B i - B i * D j‖ / δ :=
        hh.trans (div_le_div_of_nonneg_left (norm_nonneg _) hδ (hgap hac))
      simpa only [mul_comm] using (((le_div_iff₀ hδ).mp hh').trans hscaled)
    have hsquare : z ^ 2 ≤ C * (w i) ^ 2 * (f j i) ^ 2 := by
      calc z ^ 2 = z * z := pow_two z
        _ ≤ (w i * δ) * z := mul_le_mul_of_nonneg_right hsmall hz
        _ = w i * (δ * z) := by ring
        _ ≤ w i * (C * w i * (f j i) ^ 2) := mul_le_mul_of_nonneg_left hlarge (hw i)
        _ = _ := by ring
    have hright : 0 ≤ Real.sqrt C * w i * f j i :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hw i)) (hf j i)
    change z ≤ _
    apply (pow_le_pow_iff_left₀ hz hright two_ne_zero).mp
    simpa only [mul_pow, Real.sq_sqrt hC] using hsquare

end TNLean.Lattice
