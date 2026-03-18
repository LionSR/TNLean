/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Basic
import TNLean.Channel.Peripheral.IrreducibleChannel
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Determinants of quantum channels

This file provides a minimal formal interface for the determinant of a quantum
channel viewed as a linear endomorphism of the $d^2$-dimensional complex vector
space `Matrix (Fin d) (Fin d) ℂ`, following Wolf §6.1.1.

## Main definitions

* `channelMatrix` : the matrix of a channel with respect to the standard matrix basis
* `channelDet` : the determinant of that matrix representation
* `unitaryChannel` : conjugation by a unitary matrix

## Main results

* `channelDet_eq_linearMap_det` : the chosen matrix determinant agrees with `LinearMap.det`
* `channelDet_eq_zero_iff_not_bijective` : determinant zero iff the underlying linear map is
  not invertible
* `channelDet_norm_le_one_of_positive_tracePreserving` : Wolf's determinant bound (statement)
* `channelDet_norm_eq_one_iff_exists_unitaryChannel` : Wolf's unitary characterization for CPTP
  maps (backward direction proved; forward direction is a documented sorry)

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, §6.1.1][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators Kronecker Matrix.Norms.Frobenius
open Matrix

variable {d : ℕ}

/-- The ambient matrix algebra `M_d(ℂ)`. -/
private abbrev MatrixAlg (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

/-- Endomorphisms of `M_d(ℂ)`. -/
private abbrev MatrixEnd (d : ℕ) := MatrixAlg d →ₗ[ℂ] MatrixAlg d

/-- Index type for the standard basis of `M_d(ℂ)`.

We use `Fin d × Fin d × Unit`, which has cardinality $d^2$. -/
private abbrev MatrixBasisIndex (d : ℕ) := Fin d × Fin d × Unit

/-- The standard basis of `M_d(ℂ)` coming from matrix units. -/
private noncomputable def matrixSpaceBasis (d : ℕ) :
    Module.Basis (MatrixBasisIndex d) ℂ (MatrixAlg d) :=
  Module.Basis.matrix (Fin d) (Fin d) (Module.Basis.singleton Unit ℂ)

/-- Column-stacking vectorization as a linear equivalence. -/
private noncomputable def matrixVecLinearEquiv (d : ℕ) :
    MatrixAlg d ≃ₗ[ℂ] (Fin d × Fin d → ℂ) :=
  LinearEquiv.ofBijective
    { toFun := Matrix.vec
      map_add' := Matrix.vec_add
      map_smul' := Matrix.vec_smul }
    Matrix.vec_bijective

section Determinant

/-- The matrix representation of a channel with respect to `matrixSpaceBasis d`. -/
noncomputable def channelMatrix (T : MatrixEnd d) :
    Matrix (MatrixBasisIndex d) (MatrixBasisIndex d) ℂ :=
  (LinearMap.toMatrix (matrixSpaceBasis d) (matrixSpaceBasis d)) T

/-- The determinant of a channel's matrix representation on `M_d(ℂ)`. -/
noncomputable def channelDet (T : MatrixEnd d) : ℂ :=
  Matrix.det (n := MatrixBasisIndex d) (channelMatrix T)

/-- `channelDet` agrees with the basis-independent `LinearMap.det`. -/
theorem channelDet_eq_linearMap_det (T : MatrixEnd d) :
    channelDet T = LinearMap.det T := by
  unfold channelDet channelMatrix
  exact LinearMap.det_toMatrix (matrixSpaceBasis d) T

/-- Nonzero channel determinant iff the map is a unit in `Module.End`. -/
theorem channelDet_ne_zero_iff_isUnit (T : MatrixEnd d) :
    channelDet T ≠ 0 ↔ IsUnit T := by
  simpa [channelDet_eq_linearMap_det] using
    ((isUnit_iff_ne_zero : IsUnit (LinearMap.det T) ↔ LinearMap.det T ≠ 0).symm.trans
      (LinearMap.isUnit_iff_isUnit_det (f := T)).symm)

/-- A channel determinant is nonzero exactly when the underlying linear map is injective. -/
theorem channelDet_ne_zero_iff_injective (T : MatrixEnd d) :
    channelDet T ≠ 0 ↔ Function.Injective T := by
  simpa [LinearMap.ker_eq_bot] using
    (channelDet_ne_zero_iff_isUnit (T := T)).trans (LinearMap.isUnit_iff_ker_eq_bot T)

/-- A channel determinant is nonzero exactly when the underlying linear map is bijective. -/
theorem channelDet_ne_zero_iff_bijective (T : MatrixEnd d) :
    channelDet T ≠ 0 ↔ Function.Bijective T := by
  have hbij : Function.Injective T ↔ Function.Bijective T :=
    ⟨fun hT => ⟨hT, (LinearMap.injective_iff_surjective (f := T)).1 hT⟩, (·.1)⟩
  exact (channelDet_ne_zero_iff_injective (T := T)).trans hbij

/-- Wolf Thm 6.1: `det T = 0` iff `T` is not invertible as a linear map on `M_d(ℂ)`. -/
theorem channelDet_eq_zero_iff_not_bijective (T : MatrixEnd d) :
    channelDet T = 0 ↔ ¬ Function.Bijective T := by
  simpa using not_congr (channelDet_ne_zero_iff_bijective (d := d) T)

/-- The determinant of the identity channel is `1`. -/
@[simp]
theorem channelDet_id :
    channelDet (1 : MatrixEnd d) = 1 := by
  simp only [channelDet_eq_linearMap_det, map_one]

end Determinant

section Unitary

/-- The unitary channel `X ↦ U X U†`. -/
noncomputable def unitaryChannel (U : Matrix.unitaryGroup (Fin d) ℂ) : MatrixEnd d where
  toFun X := (U : MatrixAlg d) * X * (U : MatrixAlg d)ᴴ
  map_add' X Y := by simp only [mul_add, add_mul]
  map_smul' a X := by simp only [mul_smul_comm, smul_mul_assoc, RingHom.id_apply]

/-- Unitary conjugation is positive. -/
theorem unitaryChannel_isPositiveMap (U : Matrix.unitaryGroup (Fin d) ℂ) :
    IsPositiveMap (unitaryChannel U) := by
  intro X hX
  simpa [unitaryChannel, Matrix.mul_assoc] using
    hX.mul_mul_conjTranspose_same (B := (U : MatrixAlg d))

/-- Unitary conjugation is completely positive, with a single Kraus operator. -/
theorem unitaryChannel_isCPMap (U : Matrix.unitaryGroup (Fin d) ℂ) :
    IsCPMap (unitaryChannel U) := by
  refine ⟨1, fun _ => (U : MatrixAlg d), ?_⟩
  intro X
  simp only [unitaryChannel, Fin.sum_univ_one, LinearMap.coe_mk, AddHom.coe_mk]

/-- Unitary conjugation is trace-preserving. -/
theorem unitaryChannel_isTracePreserving (U : Matrix.unitaryGroup (Fin d) ℂ) :
    IsTracePreservingMap (unitaryChannel U) := by
  intro X
  have hU : (U : MatrixAlg d)ᴴ * (U : MatrixAlg d) = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.UnitaryGroup.star_mul_self U
  simpa [unitaryChannel, Matrix.mul_assoc, hU] using
    (Matrix.trace_mul_cycle (U : MatrixAlg d) X ((U : MatrixAlg d)ᴴ))

/-- Unitary conjugation is a quantum channel. -/
theorem unitaryChannel_isChannel (U : Matrix.unitaryGroup (Fin d) ℂ) :
    IsChannel (unitaryChannel U) :=
  ⟨unitaryChannel_isCPMap U, unitaryChannel_isTracePreserving U⟩

end Unitary

section WolfStatements

variable {T : MatrixEnd d}

private theorem trace_zero_hermitian_eq_smul_density_sub_density [NeZero d]
    {X : MatrixAlg d} (hX : X.IsHermitian) (htrX : Matrix.trace X = 0) :
    ∃ c : ℂ, 0 ≤ c ∧ ∃ ρ σ : MatrixAlg d,
      ρ ∈ densityMatrices d ∧ σ ∈ densityMatrices d ∧ X = c • (ρ - σ) := by
  obtain ⟨ρ₀, hρ₀_mem⟩ := densityMatrices_nonempty (D := d) (Nat.pos_of_ne_zero (NeZero.ne d))
  by_cases hX0 : X = 0
  · exact ⟨0, by simp, ρ₀, ρ₀, hρ₀_mem, hρ₀_mem, by simp [hX0]⟩
  · let Q₁ : MatrixAlg d := X⁺
    let Q₂ : MatrixAlg d := X⁻
    have hQ₁_psd : Q₁.PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg X)
    have hQ₂_psd : Q₂.PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg X)
    have hX_decomp : X = Q₁ - Q₂ := by
      simpa [Q₁, Q₂] using (CFC.posPart_sub_negPart X (isSelfAdjoint_iff.mpr hX)).symm
    have htr_eq : Matrix.trace Q₁ = Matrix.trace Q₂ := by
      rw [hX_decomp, Matrix.trace_sub] at htrX
      exact sub_eq_zero.mp htrX
    let c : ℂ := Matrix.trace Q₁
    have hc_nonneg : 0 ≤ c := by
      simpa [c] using hQ₁_psd.trace_nonneg
    have hc_ne : c ≠ 0 := by
      intro hc0
      have hQ₁_zero : Q₁ = 0 := by
        apply (hQ₁_psd.trace_eq_zero_iff).1
        simpa [c] using hc0
      have hQ₂_zero : Q₂ = 0 := by
        apply (hQ₂_psd.trace_eq_zero_iff).1
        rw [← htr_eq]
        simpa [c] using hc0
      apply hX0
      simp [hX_decomp, hQ₁_zero, hQ₂_zero]
    let ρ : MatrixAlg d := c⁻¹ • Q₁
    let σ : MatrixAlg d := c⁻¹ • Q₂
    have hc_inv_nonneg : 0 ≤ c⁻¹ := by
      simpa using (inv_nonneg).2 hc_nonneg
    have hρ_mem : ρ ∈ densityMatrices d := by
      refine ⟨hQ₁_psd.smul hc_inv_nonneg, ?_⟩
      simp [ρ, c, hc_ne]
    have hσ_mem : σ ∈ densityMatrices d := by
      refine ⟨hQ₂_psd.smul hc_inv_nonneg, ?_⟩
      change Matrix.trace (c⁻¹ • Q₂) = 1
      rw [Matrix.trace_smul, ← htr_eq]
      change c⁻¹ * c = 1
      field_simp [hc_ne]
    refine ⟨c, hc_nonneg, ρ, σ, hρ_mem, hσ_mem, ?_⟩
    simp [ρ, σ, c, hX_decomp, hc_ne, smul_sub]

private theorem positiveTracePreserving_bounded_orbit_of_trace_zero_hermitian [NeZero d]
    {T : MatrixEnd d} (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T)
    {X : MatrixAlg d} (hX : X.IsHermitian) (htrX : Matrix.trace X = 0) :
    ∃ C : ℝ, ∀ n : ℕ, ‖(T ^ n) X‖ ≤ C := by
  have hmap_density : ∀ ρ : MatrixAlg d, ρ ∈ densityMatrices d → T ρ ∈ densityMatrices d := by
    intro ρ hρ
    exact ⟨hPos ρ hρ.1, by rw [hTP ρ, hρ.2]⟩
  have hiter_density : ∀ n : ℕ, ∀ ρ : MatrixAlg d, ρ ∈ densityMatrices d →
      (T ^ n) ρ ∈ densityMatrices d := by
    intro n
    induction n with
    | zero =>
        intro ρ hρ
        simpa using hρ
    | succ n ih =>
        intro ρ hρ
        rw [pow_succ']
        exact hmap_density ((T ^ n) ρ) (ih ρ hρ)
  have hbounded_density : ∃ M : ℝ, ∀ ρ : MatrixAlg d, ρ ∈ densityMatrices d → ‖ρ‖ ≤ M := by
    have hbd : Bornology.IsBounded
        {X : MatrixAlg d | X.PosSemidef ∧ ‖Matrix.trace X‖ ≤ 1} :=
      posSemidef_trace_bounded_isBounded (D := d) 1
    rw [isBounded_iff_forall_norm_le] at hbd
    obtain ⟨M, hM⟩ := hbd
    exact ⟨M, fun ρ hρ => hM ρ ⟨hρ.1, by rw [hρ.2]; simp⟩⟩
  obtain ⟨M, hM⟩ := hbounded_density
  obtain ⟨c, hc_nonneg, ρ, σ, hρ_mem, hσ_mem, hX_eq⟩ :=
    trace_zero_hermitian_eq_smul_density_sub_density (d := d) hX htrX
  refine ⟨‖c‖ * (M + M), ?_⟩
  intro n
  have hρ_orbit : ‖(T ^ n) ρ‖ ≤ M := hM ((T ^ n) ρ) (hiter_density n ρ hρ_mem)
  have hσ_orbit : ‖(T ^ n) σ‖ ≤ M := hM ((T ^ n) σ) (hiter_density n σ hσ_mem)
  calc
    ‖(T ^ n) X‖ = ‖(T ^ n) (c • (ρ - σ))‖ := by rw [hX_eq]
    _ = ‖c • ((T ^ n) ρ - (T ^ n) σ)‖ := by simp [map_sub]
    _ = ‖c‖ * ‖(T ^ n) ρ - (T ^ n) σ‖ := by rw [norm_smul]
    _ ≤ ‖c‖ * (‖(T ^ n) ρ‖ + ‖(T ^ n) σ‖) := by
      gcongr
      exact norm_sub_le _ _
    _ ≤ ‖c‖ * (M + M) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hρ_orbit hσ_orbit) (norm_nonneg _)

private theorem positiveTracePreserving_eigenvalue_norm_le_one [NeZero d]
    {T : MatrixEnd d} (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T)
    (μ : ℂ) (hμ : Module.End.HasEigenvalue T μ) :
    ‖μ‖ ≤ 1 := by
  obtain ⟨z, hz⟩ := hμ.exists_hasEigenvector
  have hz_eig : T z = μ • z := Module.End.mem_eigenspace_iff.mp hz.1
  have hz_ne : z ≠ 0 := hz.2
  by_cases htrz : Matrix.trace z = 0
  · let x : MatrixAlg d := (1 / 2 : ℝ) • (z + zᴴ)
    let y : MatrixAlg d := (1 / 2 : ℝ) • (Complex.I • (zᴴ - z))
    have hx_herm : x.IsHermitian := by
      ext i j
      simp [x, add_comm]
    have hy_herm : y.IsHermitian := by
      ext i j
      simp [y, sub_eq_add_neg, add_comm]
    have hx_tr : Matrix.trace x = 0 := by
      simp [x, htrz]
    have hy_tr : Matrix.trace y = 0 := by
      simp [y, htrz]
    have hmulI (w : ℂ) : Complex.I * ((2 : ℂ)⁻¹ * (Complex.I * w)) = -((2 : ℂ)⁻¹ * w) := by
      calc
        Complex.I * ((2 : ℂ)⁻¹ * (Complex.I * w)) =
            (Complex.I * Complex.I) * ((2 : ℂ)⁻¹ * w) := by
          ring
        _ = -((2 : ℂ)⁻¹ * w) := by norm_num [Complex.I_sq]
    have hIy : Complex.I • y = (1 / 2 : ℝ) • (z - zᴴ) := by
      ext i j
      simp [y, sub_eq_add_neg, mul_add, hmulI, add_comm]
    have hz_decomp : z = x + Complex.I • y := by
      rw [hIy]
      ext i j
      simp [x, sub_eq_add_neg]
      ring
    obtain ⟨Cx, hCx⟩ :=
      positiveTracePreserving_bounded_orbit_of_trace_zero_hermitian (d := d) hPos hTP
        hx_herm hx_tr
    obtain ⟨Cy, hCy⟩ :=
      positiveTracePreserving_bounded_orbit_of_trace_zero_hermitian (d := d) hPos hTP
        hy_herm hy_tr
    have hz_pow : ∀ n : ℕ, (T ^ n) z = μ ^ n • z := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [pow_succ']
          change T ((T ^ n) z) = μ ^ (n + 1) • z
          rw [ih, map_smul, hz_eig]
          simp [pow_succ, smul_smul, mul_comm]
    have hz_pow_decomp : ∀ n : ℕ, (T ^ n) z = (T ^ n) x + Complex.I • (T ^ n) y := by
      intro n
      rw [hz_decomp]
      simp
    by_contra hμ_le
    have hμ_gt : 1 < ‖μ‖ := lt_of_not_ge hμ_le
    have hz_norm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz_ne
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((Cx + Cy) / ‖z‖) hμ_gt
    have hpow_gt : Cx + Cy < ‖μ‖ ^ n * ‖z‖ := by
      exact (div_lt_iff₀ hz_norm_pos).mp hn
    have hpow_le : ‖μ‖ ^ n * ‖z‖ ≤ Cx + Cy := by
      calc
        ‖μ‖ ^ n * ‖z‖ = ‖μ ^ n • z‖ := by rw [norm_smul, norm_pow]
        _ = ‖(T ^ n) z‖ := by rw [hz_pow n]
        _ = ‖(T ^ n) x + Complex.I • (T ^ n) y‖ := by rw [hz_pow_decomp n]
        _ ≤ ‖(T ^ n) x‖ + ‖Complex.I • (T ^ n) y‖ := norm_add_le _ _
        _ = ‖(T ^ n) x‖ + ‖(T ^ n) y‖ := by
          rw [norm_smul]
          simp
        _ ≤ Cx + Cy := add_le_add (hCx n) (hCy n)
    exact (not_lt_of_ge hpow_le) hpow_gt
  · have hμ_eq : μ = 1 := by
      apply mul_right_cancel₀ htrz
      calc
        μ * Matrix.trace z = Matrix.trace (μ • z) := by simp [Matrix.trace_smul, smul_eq_mul]
        _ = Matrix.trace (T z) := by rw [hz_eig]
        _ = Matrix.trace z := hTP z
        _ = 1 * Matrix.trace z := by simp
    simp [hμ_eq]

/-- Wolf Thm. 6.1(1): for a positive trace-preserving map on `M_d(ℂ)`, the channel
determinant satisfies `|det T| ≤ 1`.

This theorem is currently recorded as a statement; the analytic proof remains to be formalized.
-/
theorem channelDet_norm_le_one_of_positive_tracePreserving
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T) :
    ‖channelDet T‖ ≤ 1 := by
  classical
  by_cases hd : d = 0
  · subst hd
    rw [channelDet_eq_linearMap_det, LinearMap.det_eq_one_of_subsingleton]
    norm_num
  · haveI : NeZero d := ⟨hd⟩
    let A : Matrix (MatrixBasisIndex d) (MatrixBasisIndex d) ℂ := channelMatrix T
    have hspectrum : spectrum ℂ A = spectrum ℂ T := by
      change spectrum ℂ (channelMatrix T) = spectrum ℂ T
      exact AlgEquiv.spectrum_eq (LinearMap.toMatrixAlgEquiv (matrixSpaceBasis d)) T
    have hroot_le : ∀ μ ∈ A.charpoly.roots, ‖μ‖ ≤ 1 := by
      intro μ hμ
      have hμ_root : Polynomial.IsRoot A.charpoly μ :=
        (Polynomial.mem_roots A.charpoly_monic.ne_zero).1 hμ
      have hμ_specA : μ ∈ spectrum ℂ A :=
        Matrix.mem_spectrum_of_isRoot_charpoly hμ_root
      have hμ_specT : μ ∈ spectrum ℂ T := by simpa [hspectrum] using hμ_specA
      have hμ_eig : Module.End.HasEigenvalue T μ :=
        (Module.End.hasEigenvalue_iff_mem_spectrum).2 hμ_specT
      exact positiveTracePreserving_eigenvalue_norm_le_one (d := d) hPos hTP μ hμ_eig
    have hprod_le_aux :
        ∀ s : Multiset ℂ, (∀ μ ∈ s, ‖μ‖ ≤ 1) → ‖s.prod‖ ≤ 1 := by
      intro s
      refine Multiset.induction_on s ?_ ?_
      · intro _
        simp only [Multiset.prod_zero, norm_one, le_refl]
      · intro a s ih hs
        have ha : ‖a‖ ≤ 1 := hs a (Multiset.mem_cons_self a s)
        have hs' : ∀ μ ∈ s, ‖μ‖ ≤ 1 :=
          fun μ hμ => hs μ (Multiset.mem_cons_of_mem hμ)
        calc ‖(a ::ₘ s).prod‖ = ‖a * s.prod‖ := by simp only [Multiset.prod_cons]
          _ = ‖a‖ * ‖s.prod‖ := by rw [norm_mul]
          _ ≤ 1 * 1 := by gcongr; exact ih hs'
          _ = 1 := by norm_num
    have hprod_le : ‖A.charpoly.roots.prod‖ ≤ 1 :=
      hprod_le_aux A.charpoly.roots hroot_le
    calc ‖channelDet T‖ = ‖A.det‖ := rfl
      _ = ‖A.charpoly.roots.prod‖ := by rw [Matrix.det_eq_prod_roots_charpoly]
      _ ≤ 1 := hprod_le

/-- CPTP specialization of Wolf's determinant bound. -/
theorem channelDet_norm_le_one_of_channel
    (hT : IsChannel T) :
    ‖channelDet T‖ ≤ 1 := by
  classical
  by_cases hd : d = 0
  · subst hd
    rw [channelDet_eq_linearMap_det, LinearMap.det_eq_one_of_subsingleton]
    norm_num
  · haveI : NeZero d := ⟨hd⟩
    let A : Matrix (MatrixBasisIndex d) (MatrixBasisIndex d) ℂ := channelMatrix T
    have hspectrum : spectrum ℂ A = spectrum ℂ T := by
      change spectrum ℂ (channelMatrix T) = spectrum ℂ T
      exact AlgEquiv.spectrum_eq (LinearMap.toMatrixAlgEquiv (matrixSpaceBasis d)) T
    have hroot_le : ∀ μ ∈ A.charpoly.roots, ‖μ‖ ≤ 1 := by
      intro μ hμ
      have hμ_root : Polynomial.IsRoot A.charpoly μ :=
        (Polynomial.mem_roots A.charpoly_monic.ne_zero).1 hμ
      have hμ_specA : μ ∈ spectrum ℂ A :=
        Matrix.mem_spectrum_of_isRoot_charpoly hμ_root
      have hμ_specT : μ ∈ spectrum ℂ T := by simpa [hspectrum] using hμ_specA
      have hμ_eig : Module.End.HasEigenvalue T μ :=
        (Module.End.hasEigenvalue_iff_mem_spectrum).2 hμ_specT
      exact IsChannel.eigenvalue_norm_le_one hT μ hμ_eig
    have hprod_le_aux :
        ∀ s : Multiset ℂ, (∀ μ ∈ s, ‖μ‖ ≤ 1) → ‖s.prod‖ ≤ 1 := by
      intro s
      refine Multiset.induction_on s ?_ ?_
      · intro _
        simp only [Multiset.prod_zero, norm_one, le_refl]
      · intro a s ih hs
        have ha : ‖a‖ ≤ 1 := hs a (Multiset.mem_cons_self a s)
        have hs' : ∀ μ ∈ s, ‖μ‖ ≤ 1 :=
          fun μ hμ => hs μ (Multiset.mem_cons_of_mem hμ)
        calc ‖(a ::ₘ s).prod‖ = ‖a * s.prod‖ := by simp only [Multiset.prod_cons]
          _ = ‖a‖ * ‖s.prod‖ := by rw [norm_mul]
          _ ≤ 1 * 1 := by gcongr; exact ih hs'
          _ = 1 := by norm_num
    have hprod_le : ‖A.charpoly.roots.prod‖ ≤ 1 :=
      hprod_le_aux A.charpoly.roots hroot_le
    calc ‖channelDet T‖ = ‖A.det‖ := rfl
      _ = ‖A.charpoly.roots.prod‖ := by rw [Matrix.det_eq_prod_roots_charpoly]
      _ ≤ 1 := hprod_le

/-- Wolf Thm 6.1(2) restricted to CPTP maps: a quantum channel `T` on `M_d(ℂ)` satisfies
`‖det T‖ = 1` if and only if `T` is a unitary channel `X ↦ U X U†`.

**Why CPTP and not merely positive TP?**
Wolf's full Thm 6.1(2) states that for a *positive* trace-preserving map the condition
`‖det T‖ = 1` characterises *two* branches:
  (1) unitary conjugation `X ↦ U X U†`, and
  (2) maps unitarily equivalent to transposition `X ↦ U Xᵀ U†`.
The transposition map has `‖det T‖ = 1` but is **not** completely positive; it is the
canonical example of a positive-but-not-CP map.  Therefore the transposition branch does not
appear for CPTP maps, and the biconditional `‖det T‖ = 1 ↔ ∃ U, T = unitaryChannel U` is
correct under the `IsChannel` hypothesis.

**Proof status.**
- Backward direction (`←`): proved — `channelDet_norm_eq_one_of_unitaryChannel`.
- Forward direction (`→`): *sorry* — requires formalising the spectral argument from Wolf's
  proof that the only CPTP fixed points of the bound `‖det T‖ ≤ 1` are unitary conjugations.
  In outline: `‖det T‖ = 1` forces every eigenvalue of T (as a map on `M_d²(ℂ)`) to have
  modulus 1; combined with complete positivity and trace-preservation this forces T to be
  unitary conjugation (Wolf §6.1.1). -/
theorem channelDet_norm_eq_one_iff_exists_unitaryChannel
    (hT : IsChannel T) :
    ‖channelDet T‖ = 1 ↔ ∃ U : Matrix.unitaryGroup (Fin d) ℂ, T = unitaryChannel U := by
  constructor
  · -- Forward direction: |det T| = 1 → T is a unitary channel.
    -- This is the hard part of Wolf Thm 6.1(2); it requires the spectral argument that
    -- complete positivity and trace-preservation, combined with all eigenvalues having
    -- modulus 1, force T to be unitary conjugation.
    intro _h
    sorry
  · -- Backward direction: if T is a unitary channel then |det T| = 1.
    rintro ⟨U, rfl⟩
    exact channelDet_norm_eq_one_of_unitaryChannel U

/-- CPTP specialization of the unitary characterization (alias of
`channelDet_norm_eq_one_iff_exists_unitaryChannel`). -/
theorem channelDet_norm_eq_one_iff_exists_unitaryChannel_of_channel
    (hT : IsChannel T) :
    ‖channelDet T‖ = 1 ↔ ∃ U : Matrix.unitaryGroup (Fin d) ℂ, T = unitaryChannel U :=
  channelDet_norm_eq_one_iff_exists_unitaryChannel hT

/-- The determinant of a unitary channel equals `1`. -/
theorem channelDet_unitary_eq_one (U : Matrix.unitaryGroup (Fin d) ℂ) :
    channelDet (unitaryChannel U) = 1 := by
  let e : MatrixAlg d ≃ₗ[ℂ] (Fin d × Fin d → ℂ) := matrixVecLinearEquiv d
  let M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
    ((U : MatrixAlg d).map star) ⊗ₖ (U : MatrixAlg d)
  have hvec : ∀ X : MatrixAlg d,
      e (unitaryChannel U X) = Matrix.toLin' M (e X) := by
    intro X
    change Matrix.vec (((U : MatrixAlg d) * X * (U : MatrixAlg d)ᴴ) : MatrixAlg d) =
      M.mulVec (Matrix.vec X)
    symm
    simpa [M, unitaryChannel, Matrix.conjTranspose] using
      (Matrix.kronecker_mulVec_vec (A := (U : MatrixAlg d)) (X := X)
        (B := (U : MatrixAlg d).map star))
  have hconj :
      ((e : MatrixAlg d →ₗ[ℂ] (Fin d × Fin d → ℂ)) ∘ₗ unitaryChannel U ∘ₗ
          ((e.symm : (Fin d × Fin d → ℂ) ≃ₗ[ℂ] MatrixAlg d) :
            (Fin d × Fin d → ℂ) →ₗ[ℂ] MatrixAlg d)) =
        Matrix.toLin' M := by
    apply LinearMap.ext
    intro w
    ext ij
    simpa [e] using congrFun (hvec (e.symm w)) ij
  have hdet_map_star :
      ((U : MatrixAlg d).map star).det = star (Matrix.det (U : MatrixAlg d)) := by
    simpa using (RingEquiv.map_det (starRingAut : ℂ ≃+* ℂ) (U : MatrixAlg d)).symm
  have hdet_unitary :
      star (Matrix.det (U : MatrixAlg d)) * Matrix.det (U : MatrixAlg d) = 1 := by
    have hU : ((U : MatrixAlg d)ᴴ) * (U : MatrixAlg d) = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using Matrix.UnitaryGroup.star_mul_self U
    have h := congrArg Matrix.det hU
    simpa [Matrix.det_mul, Matrix.det_conjTranspose] using h
  calc
    channelDet (unitaryChannel U) = LinearMap.det (unitaryChannel U) :=
      channelDet_eq_linearMap_det (T := unitaryChannel U)
    _ = LinearMap.det
          (((e : MatrixAlg d →ₗ[ℂ] (Fin d × Fin d → ℂ)) ∘ₗ unitaryChannel U ∘ₗ
            ((e.symm : (Fin d × Fin d → ℂ) ≃ₗ[ℂ] MatrixAlg d) :
              (Fin d × Fin d → ℂ) →ₗ[ℂ] MatrixAlg d))) :=
        (LinearMap.det_conj (f := unitaryChannel U) (e := e)).symm
    _ = LinearMap.det (Matrix.toLin' M) := by rw [hconj]
    _ = Matrix.det M := by rw [LinearMap.det_toLin']
    _ = ((U : MatrixAlg d).map star).det ^ d * Matrix.det (U : MatrixAlg d) ^ d := by
          simpa [M] using
            (Matrix.det_kronecker (A := (U : MatrixAlg d).map star)
              (B := (U : MatrixAlg d)))
    _ = (star (Matrix.det (U : MatrixAlg d)) * Matrix.det (U : MatrixAlg d)) ^ d := by
          rw [hdet_map_star, mul_pow]
    _ = 1 := by rw [hdet_unitary, one_pow]

/-- Every unitary channel has determinant of modulus `1`. -/
theorem channelDet_norm_eq_one_of_unitaryChannel (U : Matrix.unitaryGroup (Fin d) ℂ) :
    ‖channelDet (unitaryChannel U)‖ = 1 := by
  simp [channelDet_unitary_eq_one]

end WolfStatements
