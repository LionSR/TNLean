/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Basic
import TNLean.Channel.Peripheral.IrreducibleChannel
import TNLean.Channel.KrausRepresentation
import TNLean.Channel.Schwarz.MultiplicativeDomainFull
import TNLean.Algebra.SkolemNoether
import Mathlib.Algebra.Central.Matrix
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.MeanInequalities
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
  maps

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
  obtain ⟨ρ₀, hρ₀_mem⟩ :=
    densityMatrices_nonempty (D := d) (Nat.pos_of_ne_zero (NeZero.ne d))
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
  have hmap_density :
      ∀ ρ : MatrixAlg d, ρ ∈ densityMatrices d → T ρ ∈ densityMatrices d := by
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
  have hbounded_density :
      ∃ M : ℝ, ∀ ρ : MatrixAlg d, ρ ∈ densityMatrices d → ‖ρ‖ ≤ M := by
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
    have hmulI (w : ℂ) :
        Complex.I * ((2 : ℂ)⁻¹ * (Complex.I * w)) = -((2 : ℂ)⁻¹ * w) := by
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

/-- If every factor in a finite product has norm at most `1`, then the product also has norm at
most `1`. -/
private lemma norm_prod_le_one_of_forall_mem'
    (s : Multiset ℂ) (hs : ∀ μ ∈ s, ‖μ‖ ≤ 1) :
    ‖s.prod‖ ≤ 1 := by
  induction s using Multiset.induction with
  | empty => simp
  | @cons a s ih =>
      have ha : ‖a‖ ≤ 1 := hs a (Multiset.mem_cons_self a s)
      have hs' : ∀ ν ∈ s, ‖ν‖ ≤ 1 := fun ν hν => hs ν (Multiset.mem_cons_of_mem hν)
      calc
        ‖(a ::ₘ s).prod‖ = ‖a * s.prod‖ := by simp [Multiset.prod_cons]
        _ = ‖a‖ * ‖s.prod‖ := by rw [norm_mul]
        _ ≤ 1 * 1 := by gcongr; exact ih hs'
        _ = 1 := by norm_num

/-- Eigenvalues of a positive trace-preserving map on `M_d(ℂ)` determine roots of the
characteristic polynomial with norm ≤ 1, so the determinant (= product of roots) has norm ≤ 1. -/
private lemma channelDet_norm_le_one_of_eigenvalues_bounded
    (hroot_le : ∀ μ ∈ (channelMatrix T).charpoly.roots, ‖μ‖ ≤ 1) :
    ‖channelDet T‖ ≤ 1 := by
  calc ‖channelDet T‖ = ‖(channelMatrix T).det‖ := rfl
    _ = ‖(channelMatrix T).charpoly.roots.prod‖ := by rw [Matrix.det_eq_prod_roots_charpoly]
    _ ≤ 1 := norm_prod_le_one_of_forall_mem' _ hroot_le

/-- Wolf Thm. 6.1(1): for a positive trace-preserving map on `M_d(ℂ)`, the channel
determinant satisfies `|det T| ≤ 1`. -/
theorem channelDet_norm_le_one_of_positive_tracePreserving
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T) :
    ‖channelDet T‖ ≤ 1 := by
  classical
  by_cases hd : d = 0
  · subst hd
    rw [channelDet_eq_linearMap_det, LinearMap.det_eq_one_of_subsingleton]
    norm_num
  · haveI : NeZero d := ⟨hd⟩
    apply channelDet_norm_le_one_of_eigenvalues_bounded
    intro μ hμ
    exact positiveTracePreserving_eigenvalue_norm_le_one (d := d) hPos hTP μ
      (Module.End.hasEigenvalue_iff_mem_spectrum.2
        ((AlgEquiv.spectrum_eq (LinearMap.toMatrixAlgEquiv (matrixSpaceBasis d)) T) ▸
          Matrix.mem_spectrum_of_isRoot_charpoly
            ((Polynomial.mem_roots (channelMatrix T).charpoly_monic.ne_zero).1 hμ)))

/-- CPTP specialization of Wolf's determinant bound. -/
theorem channelDet_norm_le_one_of_channel
    (hT : IsChannel T) :
    ‖channelDet T‖ ≤ 1 :=
  channelDet_norm_le_one_of_positive_tracePreserving hT.cp.isPositiveMap hT.tp

/-! ### Helper lemmas for the forward direction of Wolf Thm 6.1(2) -/

/-- Product of norms = 1 with each factor ≤ 1 implies each factor = 1. -/
private lemma norm_eq_one_of_prod_norm_eq_one
    (s : Multiset ℂ) (hs : ∀ μ ∈ s, ‖μ‖ ≤ 1) (hprod : ‖s.prod‖ = 1) :
    ∀ μ ∈ s, ‖μ‖ = 1 := by
  induction s using Multiset.induction with
  | empty => intro μ hμ; simp at hμ
  | @cons a s ih =>
    intro μ hμ
    have ha : ‖a‖ ≤ 1 := hs a (Multiset.mem_cons_self a s)
    have hs' : ∀ ν ∈ s, ‖ν‖ ≤ 1 := fun ν hν => hs ν (Multiset.mem_cons_of_mem hν)
    rw [Multiset.prod_cons, norm_mul] at hprod
    have hprod_s_le : ‖s.prod‖ ≤ 1 := norm_prod_le_one_of_forall_mem' s hs'
    have ha_eq : ‖a‖ = 1 := by nlinarith [norm_nonneg a, norm_nonneg s.prod]
    have hs_eq : ‖s.prod‖ = 1 := by nlinarith [norm_nonneg a]
    rcases Multiset.mem_cons.mp hμ with rfl | hμs
    · exact ha_eq
    · exact ih hs' hs_eq μ hμs

/-- For a CPTP map with `‖det T‖ = 1`, every eigenvalue has modulus exactly 1. -/
private theorem channel_all_eigenvalues_norm_one [NeZero d]
    (hT : IsChannel T) (hdet : ‖channelDet T‖ = 1) :
    ∀ μ : ℂ, Module.End.HasEigenvalue T μ → ‖μ‖ = 1 := by
  let A : Matrix (MatrixBasisIndex d) (MatrixBasisIndex d) ℂ := channelMatrix T
  have hspectrum : spectrum ℂ A = spectrum ℂ T :=
    AlgEquiv.spectrum_eq (LinearMap.toMatrixAlgEquiv (matrixSpaceBasis d)) T
  have hroot_le : ∀ μ ∈ A.charpoly.roots, ‖μ‖ ≤ 1 := by
    intro μ hμ
    exact IsChannel.eigenvalue_norm_le_one hT μ
      (Module.End.hasEigenvalue_iff_mem_spectrum.2
        (hspectrum ▸ Matrix.mem_spectrum_of_isRoot_charpoly
          ((Polynomial.mem_roots A.charpoly_monic.ne_zero).1 hμ)))
  have hprod_eq : ‖A.charpoly.roots.prod‖ = 1 := by
    have : ‖channelDet T‖ = ‖A.charpoly.roots.prod‖ := by
      change ‖A.det‖ = ‖A.charpoly.roots.prod‖
      rw [Matrix.det_eq_prod_roots_charpoly]
    rw [← this]; exact hdet
  have hroot_eq := norm_eq_one_of_prod_norm_eq_one _ hroot_le hprod_eq
  intro μ hμ_eig
  have hμ_specT : μ ∈ spectrum ℂ T := Module.End.hasEigenvalue_iff_mem_spectrum.1 hμ_eig
  have hμ_specA : μ ∈ spectrum ℂ A := hspectrum ▸ hμ_specT
  exact hroot_eq μ ((Polynomial.mem_roots A.charpoly_monic.ne_zero).2
    ((Matrix.mem_spectrum_iff_isRoot_charpoly).1 hμ_specA))

private theorem stdBasis_conjTranspose_mul_self (i j : Fin d) :
    (Matrix.stdBasis ℂ (Fin d) (Fin d) (i, j))ᴴ *
        Matrix.stdBasis ℂ (Fin d) (Fin d) (i, j) =
      Matrix.single j j (1 : ℂ) := by
  ext a b
  rw [Matrix.stdBasis_eq_single, Matrix.conjTranspose_single]
  by_cases hja : j = a
  · by_cases hjb : j = b
    · subst hja; subst hjb
      simp [Matrix.mul_apply, Matrix.single]
    · have hab : a ≠ b := by simpa [hja] using hjb
      simp [Matrix.mul_apply, Matrix.single, hja, hab]
  · simp [Matrix.mul_apply, Matrix.single, hja]

private theorem stdBasis_conjTranspose_eq_swap (i j : Fin d) :
    (Matrix.stdBasis ℂ (Fin d) (Fin d) (i, j))ᴴ =
      Matrix.stdBasis ℂ (Fin d) (Fin d) (j, i) := by
  rw [Matrix.stdBasis_eq_single, Matrix.stdBasis_eq_single, Matrix.conjTranspose_single]
  simp

private theorem stdBasis_mul_conjTranspose_self (i j : Fin d) :
    Matrix.stdBasis ℂ (Fin d) (Fin d) (i, j) *
        (Matrix.stdBasis ℂ (Fin d) (Fin d) (i, j))ᴴ =
      Matrix.single i i (1 : ℂ) := by
  simpa [stdBasis_conjTranspose_eq_swap] using
    (stdBasis_conjTranspose_mul_self (d := d) (i := j) (j := i))

private theorem sum_single_diag_one :
    ∑ j : Fin d, Matrix.single j j (1 : ℂ) = (1 : MatrixAlg d) := by
  ext a b
  rw [Finset.sum_apply]
  by_cases hab : a = b
  · subst hab
    simp [Matrix.single]
  · simp [Matrix.single, hab]

private theorem sum_stdBasis_mul_conjTranspose :
    ∑ ij : Fin d × Fin d,
      Matrix.stdBasis ℂ (Fin d) (Fin d) ij * (Matrix.stdBasis ℂ (Fin d) (Fin d) ij)ᴴ =
        (d : ℂ) • (1 : MatrixAlg d) := by
  calc
    ∑ ij : Fin d × Fin d,
        Matrix.stdBasis ℂ (Fin d) (Fin d) ij * (Matrix.stdBasis ℂ (Fin d) (Fin d) ij)ᴴ =
          ∑ ij : Fin d × Fin d, Matrix.single ij.1 ij.1 (1 : ℂ) := by
            refine Finset.sum_congr rfl ?_
            intro ij _
            rcases ij with ⟨i, j⟩
            simpa using stdBasis_mul_conjTranspose_self (d := d) i j
    _ = ∑ i : Fin d, ∑ j : Fin d, Matrix.single i i (1 : ℂ) := by
          simpa using
            (Finset.sum_product' (s := (Finset.univ : Finset (Fin d)))
              (t := (Finset.univ : Finset (Fin d)))
              (f := fun i j => Matrix.single i i (1 : ℂ)))
    _ = ∑ i : Fin d, (d : ℂ) • Matrix.single i i (1 : ℂ) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          simp
    _ = (d : ℂ) • ∑ i : Fin d, Matrix.single i i (1 : ℂ) := by rw [Finset.smul_sum]
    _ = (d : ℂ) • (1 : MatrixAlg d) := by rw [sum_single_diag_one]

private theorem stdBasis_orthonormal_of_inner_eq_trace
    [NormedAddCommGroup (MatrixAlg d)] [InnerProductSpace ℂ (MatrixAlg d)]
    (hinner : ∀ X Y : MatrixAlg d, inner ℂ X Y = Matrix.trace (Y * Xᴴ)) :
    Orthonormal ℂ ⇑(Matrix.stdBasis ℂ (Fin d) (Fin d)) := by
  rw [orthonormal_iff_ite]
  intro a b
  rcases a with ⟨i, j⟩
  rcases b with ⟨k, l⟩
  rw [hinner, Matrix.stdBasis_eq_single, Matrix.stdBasis_eq_single, Matrix.conjTranspose_single]
  rw [Matrix.trace_mul_single]
  simp [Matrix.single, eq_comm]

/-- The Heisenberg dual `T*(X) = ∑ Kᵢ† X Kᵢ` of a CPTP map with `‖det T‖ = 1`
is multiplicative on all of `M_d(ℂ)`.

This is the analytic core of Wolf Thm 6.1(2). The proof uses the Kadison–Schwarz
trace-summing argument: each KS gap is PSD; summed over an ON basis the total gap
trace equals `d² − ‖T*‖²_HS`; AM-GM on the eigenvalues of `T∘T*` (PSD operator
with determinant 1) forces `‖T*‖²_HS ≥ d²`; hence all gaps vanish, every matrix
lies in the multiplicative domain, and `T*` is multiplicative. -/
-- Helper: For a PSD matrix with trace 0, the matrix is 0.
-- (Already available as Matrix.PosSemidef.trace_eq_zero_iff.)

-- Helper: If nonneg reals sum to ≤ 0, each is 0.
private lemma eq_zero_of_nonneg_of_sum_le_zero {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (hsum : ∑ i, f i ≤ 0) :
    ∀ i, f i = 0 := by
  intro i
  have h1 : ∑ i, f i ≥ 0 := Finset.sum_nonneg (fun i _ => hf i)
  have h2 : ∑ i, f i = 0 := le_antisymm hsum h1
  have h3 := Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hf i) |>.mp h2
  exact h3 i (Finset.mem_univ i)

private lemma complex_star_mul_re (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by
  rw [show star z = starRingEnd ℂ z from rfl, Complex.conj_mul',
    ← Complex.ofReal_pow]
  exact Complex.ofReal_re _

private lemma trace_conjTranspose_mul_self_re_eq_sum_sq {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) :
    (Matrix.trace (Aᴴ * A)).re = ∑ j, ∑ i, ‖A i j‖ ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  refine Finset.sum_congr rfl ?_
  intro i _
  simpa using complex_star_mul_re (A i j)

private lemma matrix_det_norm_one_trace_conjTranspose_mul_self_ge [NeZero d]
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hdet : ‖A.det‖ = 1) :
    (d : ℝ) ^ 2 ≤ (Matrix.trace (Aᴴ * A)).re := by
  let B : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ := Aᴴ * A
  have hBherm : B.IsHermitian := by
    simpa [B] using Matrix.isHermitian_conjTranspose_mul_self A
  have hBpsd : B.PosSemidef := by
    simpa [B] using Matrix.posSemidef_conjTranspose_mul_self A
  have hdetB : Matrix.det B = 1 := by
    change Matrix.det (Aᴴ * A) = 1
    rw [Matrix.det_mul, Matrix.det_conjTranspose]
    have hconj : star A.det * A.det = ((‖A.det‖ ^ 2 : ℝ) : ℂ) := by
      simpa [show star A.det = starRingEnd ℂ A.det from rfl, ← Complex.ofReal_pow] using
        (Complex.conj_mul' A.det)
    rw [hconj, hdet]
    norm_num
  have hprod_eq : ∏ i, hBherm.eigenvalues i = 1 := by
    have h : Matrix.det B = ∏ i, (hBherm.eigenvalues i : ℂ) := hBherm.det_eq_prod_eigenvalues
    rw [hdetB] at h
    have h' : ((∏ i, hBherm.eigenvalues i : ℝ) : ℂ) = 1 := by
      simpa using h.symm
    exact_mod_cast h'
  have hd_pos : 0 < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hamgm : 1 ≤ (∑ i, hBherm.eigenvalues i) / ((d : ℝ) * d) := by
    have := Real.geom_mean_le_arith_mean (s := Finset.univ) (w := fun _ => (1 : ℝ))
      (z := fun i => hBherm.eigenvalues i)
      (by intro i hi; positivity)
      (by simp [Fintype.card_prod, Nat.cast_mul, NeZero.ne d])
      (by intro i hi; simpa using hBpsd.eigenvalues_nonneg i)
    simpa [hprod_eq, Fintype.card_prod, Nat.cast_mul, NeZero.ne d] using this
  have hmul_pos : 0 < (d : ℝ) * d := mul_pos hd_pos hd_pos
  have hsum_ge : (d : ℝ) * d ≤ ∑ i, hBherm.eigenvalues i :=
    (one_le_div hmul_pos).mp hamgm
  have htrace_eq : (Matrix.trace B).re = ∑ i, hBherm.eigenvalues i := by
    simpa using congrArg Complex.re hBherm.trace_eq_sum_eigenvalues
  simpa [B, pow_two] using hsum_ge.trans_eq htrace_eq.symm

/-- **AM-GM lower bound on Hilbert-Schmidt norm via determinant.**

For a linear endomorphism `Φ` of the matrix algebra with `‖det Φ‖ = 1`,
the Hilbert-Schmidt norm satisfies `‖Φ‖²_HS ≥ d²`. This follows from AM-GM
on the singular values: their product is `|det Φ| = 1`, so their squared sum
(= the HS norm) is at least `d²`.

This is the analytic ingredient for Wolf Thm 6.1(2). -/
private lemma channelDet_norm_one_hs_norm_ge [NeZero d]
    (Φ : MatrixEnd d) (hdet_Φ : ‖channelDet Φ‖ = 1) :
    (d : ℝ) ^ 2 ≤ ∑ ij : Fin d × Fin d,
      (Matrix.trace ((Φ (Matrix.stdBasis ℂ (Fin d) (Fin d) ij))ᴴ *
        Φ (Matrix.stdBasis ℂ (Fin d) (Fin d) ij))).re := by
  let b : Module.Basis (Fin d × Fin d) ℂ (MatrixAlg d) :=
    Matrix.stdBasis ℂ (Fin d) (Fin d)
  let A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ := LinearMap.toMatrix b b Φ
  have hA_det : ‖A.det‖ = 1 := by
    simpa [A, b, channelDet_eq_linearMap_det] using hdet_Φ
  have hA_hs :
      (Matrix.trace (Aᴴ * A)).re = ∑ ij : Fin d × Fin d,
        (Matrix.trace ((Φ (Matrix.stdBasis ℂ (Fin d) (Fin d) ij))ᴴ *
          Φ (Matrix.stdBasis ℂ (Fin d) (Fin d) ij))).re := by
    calc
      (Matrix.trace (Aᴴ * A)).re =
          ∑ ij : Fin d × Fin d, ∑ kl : Fin d × Fin d,
            ‖(Φ (b ij)) kl.1 kl.2‖ ^ 2 := by
              simp [A, b, trace_conjTranspose_mul_self_re_eq_sum_sq,
                LinearMap.toMatrix_apply, Matrix.stdBasis]
      _ = ∑ ij : Fin d × Fin d,
            (Matrix.trace ((Φ (Matrix.stdBasis ℂ (Fin d) (Fin d) ij))ᴴ *
              Φ (Matrix.stdBasis ℂ (Fin d) (Fin d) ij))).re := by
            refine Finset.sum_congr rfl ?_
            intro ij _
            have hsum_sq :
                ∑ kl : Fin d × Fin d,
                    ‖Φ (Matrix.stdBasis ℂ (Fin d) (Fin d) ij) kl.1 kl.2‖ ^ 2 =
                  ∑ j : Fin d, ∑ i : Fin d,
                    ‖Φ (Matrix.stdBasis ℂ (Fin d) (Fin d) ij) i j‖ ^ 2 := by
              calc
                ∑ kl : Fin d × Fin d,
                    ‖Φ (Matrix.stdBasis ℂ (Fin d) (Fin d) ij) kl.1 kl.2‖ ^ 2
                    = ∑ i : Fin d, ∑ j : Fin d,
                        ‖Φ (Matrix.stdBasis ℂ (Fin d) (Fin d) ij) i j‖ ^ 2 := by
                          simpa [Finset.univ_product_univ] using
                            (Finset.sum_product'
                              (s := (Finset.univ : Finset (Fin d)))
                              (t := (Finset.univ : Finset (Fin d)))
                              (f := fun i j =>
                                ‖Φ (Matrix.stdBasis ℂ (Fin d) (Fin d) ij) i j‖ ^ 2))
                _ = ∑ j : Fin d, ∑ i : Fin d,
                      ‖Φ (Matrix.stdBasis ℂ (Fin d) (Fin d) ij) i j‖ ^ 2 := by
                        rw [Finset.sum_comm]
            exact hsum_sq.trans
              (trace_conjTranspose_mul_self_re_eq_sum_sq
                (A := Φ (Matrix.stdBasis ℂ (Fin d) (Fin d) ij))).symm
  calc
    (d : ℝ) ^ 2 ≤ (Matrix.trace (Aᴴ * A)).re :=
      matrix_det_norm_one_trace_conjTranspose_mul_self_ge (d := d) A hA_det
    _ = ∑ ij : Fin d × Fin d,
          (Matrix.trace ((Φ (Matrix.stdBasis ℂ (Fin d) (Fin d) ij))ᴴ *
            Φ (Matrix.stdBasis ℂ (Fin d) (Fin d) ij))).re := hA_hs

-- KS trace-summing + Kraus commutation + basis extensionality
-- This theorem performs a long Kadison-Schwarz trace-summing argument over matrix bases.
private theorem heisenberg_dual_multiplicative [NeZero d]
    {T : MatrixEnd d} (_hT : IsChannel T) (hdet : ‖channelDet T‖ = 1)
    (_hall : ∀ μ : ℂ, Module.End.HasEigenvalue T μ → ‖μ‖ = 1)
    {r : ℕ} (K : Fin r → MatrixAlg d) (hK : ∀ X, T X = ∑ i, K i * X * (K i)ᴴ)
    (hK_tp : ∑ i : Fin r, (K i)ᴴ * K i = 1)
    (Td : MatrixEnd d) (hTd : ∀ X, Td X = ∑ i : Fin r, (K i)ᴴ * X * K i) :
    ∀ M N : MatrixAlg d, Td (M * N) = Td M * Td N := by
  -- ── Setup: Td is a Kraus map with conjugate-transposed operators ──
  -- Define the Kraus operators for Td
  set L : Fin r → MatrixAlg d := fun i => (K i)ᴴ with hL_def
  -- Td(X) = ∑ L_i X L_i† = krausMap L X
  have hTd_kraus : ∀ X, Td X = KadisonSchwarz.krausMap L X := by
    intro X; simp only [KadisonSchwarz.krausMap, hL_def, hTd, conjTranspose_conjTranspose]
  -- L is unital: ∑ L_i L_i† = ∑ K_i† K_i = I
  have hL_unital : KadisonSchwarz.IsUnitalKraus L := by
    change ∑ i, (K i)ᴴ * ((K i)ᴴ)ᴴ = 1
    simp [conjTranspose_conjTranspose, hK_tp]
  -- ── Step 1: KS equality for every standard basis element ──
  -- For each (i,j), e_{ij} * e_{ij}† = e_{ii}, and the KS gap
  -- G(e_{ij}) = Td(e_{ij}e_{ij}†) - Td(e_{ij})Td(e_{ij})† ≥ 0
  -- We show ∑ G(e_{ij}) = 0 (matrix), hence each G(e_{ij}) = 0.
  -- ‖channelDet Td‖ = 1
  have hdet_Td : ‖channelDet Td‖ = 1 := by
    let b : Module.Basis (Fin d × Fin d) ℂ (MatrixAlg d) :=
      Matrix.stdBasis ℂ (Fin d) (Fin d)
    have hAdj : ∀ ρ X : MatrixAlg d,
        Matrix.trace (ρ * T X) = Matrix.trace (Td ρ * X) := by
      intro ρ X
      simpa [Kraus.map, Kraus.adjointMap, hK, hTd, Matrix.mul_assoc] using
        (Kraus.trace_mul_map_eq_trace_adjointMap_mul (K := K) ρ X)
    have hT_star : ∀ X : MatrixAlg d, T Xᴴ = (T X)ᴴ := by
      intro X
      simp [hK, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    have hmat : LinearMap.toMatrix b b Td = (LinearMap.toMatrix b b T)ᴴ := by
      ext i j
      simp only [Matrix.conjTranspose_apply, LinearMap.toMatrix_apply, b, RCLike.star_def]
      have hcoef : (Td (Matrix.stdBasis ℂ (Fin d) (Fin d) j)) i.1 i.2 =
          star ((T (Matrix.stdBasis ℂ (Fin d) (Fin d) i)) j.1 j.2) := by
        calc
          (Td (Matrix.stdBasis ℂ (Fin d) (Fin d) j)) i.1 i.2
              = Matrix.trace (Td (Matrix.stdBasis ℂ (Fin d) (Fin d) j) *
                  (Matrix.stdBasis ℂ (Fin d) (Fin d) i)ᴴ) := by
                    rcases i with ⟨a, b⟩
                    simp [Matrix.stdBasis_eq_single, Matrix.conjTranspose_single,
                      Matrix.trace_mul_single]
          _ = Matrix.trace (Matrix.stdBasis ℂ (Fin d) (Fin d) j *
                T ((Matrix.stdBasis ℂ (Fin d) (Fin d) i)ᴴ)) := by
                simpa using (hAdj (Matrix.stdBasis ℂ (Fin d) (Fin d) j)
                  ((Matrix.stdBasis ℂ (Fin d) (Fin d) i)ᴴ)).symm
          _ = Matrix.trace (Matrix.stdBasis ℂ (Fin d) (Fin d) j *
                (T (Matrix.stdBasis ℂ (Fin d) (Fin d) i))ᴴ) := by rw [hT_star]
          _ = star (Matrix.trace (T (Matrix.stdBasis ℂ (Fin d) (Fin d) i) *
                (Matrix.stdBasis ℂ (Fin d) (Fin d) j)ᴴ)) := by
                rw [← Matrix.trace_conjTranspose]
                simp
          _ = star ((T (Matrix.stdBasis ℂ (Fin d) (Fin d) i)) j.1 j.2) := by
                rcases j with ⟨c, d⟩
                simp [Matrix.stdBasis_eq_single, Matrix.conjTranspose_single,
                  Matrix.trace_mul_single]
      simpa [b, Matrix.stdBasis] using hcoef
    calc
      ‖channelDet Td‖ = ‖LinearMap.det Td‖ := by rw [channelDet_eq_linearMap_det]
      _ = ‖Matrix.det (LinearMap.toMatrix b b Td)‖ := by
            rw [← LinearMap.det_toMatrix (b := b) (f := Td)]
      _ = ‖Matrix.det ((LinearMap.toMatrix b b T)ᴴ)‖ := by rw [hmat]
      _ = ‖star (Matrix.det (LinearMap.toMatrix b b T))‖ := by
            rw [Matrix.det_conjTranspose]
      _ = ‖Matrix.det (LinearMap.toMatrix b b T)‖ := by simp
      _ = ‖LinearMap.det T‖ := by rw [LinearMap.det_toMatrix (b := b) (f := T)]
      _ = ‖channelDet T‖ := by rw [← channelDet_eq_linearMap_det]
      _ = 1 := hdet
  -- Each KS gap G(e_{ij}) = Td(e_{ij}·e_{ij}†) - Td(e_{ij})·Td(e_{ij})† is PSD
  have hgap_psd : ∀ ij : Fin d × Fin d,
      (KadisonSchwarz.krausMap L
        (Matrix.stdBasis ℂ (Fin d) (Fin d) ij *
         (Matrix.stdBasis ℂ (Fin d) (Fin d) ij)ᴴ) -
      KadisonSchwarz.krausMap L (Matrix.stdBasis ℂ (Fin d) (Fin d) ij) *
        (KadisonSchwarz.krausMap L (Matrix.stdBasis ℂ (Fin d) (Fin d) ij))ᴴ).PosSemidef := by
    intro ij
    -- Apply KS to X = e_{ij}†; this gives the "right" gap ≥ 0
    have h := KadisonSchwarz.kadison_schwarz L hL_unital
                (Matrix.stdBasis ℂ (Fin d) (Fin d) ij)ᴴ
    simp only [conjTranspose_conjTranspose,
      KadisonSchwarz.krausMap_conjTranspose] at h
    exact h
  -- Each gap has nonneg trace (since PSD)
  have hgap_trace_nonneg : ∀ ij : Fin d × Fin d,
      0 ≤ (Matrix.trace (KadisonSchwarz.krausMap L
        (Matrix.stdBasis ℂ (Fin d) (Fin d) ij *
         (Matrix.stdBasis ℂ (Fin d) (Fin d) ij)ᴴ) -
      KadisonSchwarz.krausMap L (Matrix.stdBasis ℂ (Fin d) (Fin d) ij) *
        (KadisonSchwarz.krausMap L (Matrix.stdBasis ℂ (Fin d) (Fin d) ij))ᴴ)).re := by
    intro ij
    exact (Complex.le_def.mp (hgap_psd ij).trace_nonneg).1
  -- Sum of gap traces = d² - ‖Td‖²_HS
  -- First, sum of traces of Td(e_{ij}e_{ij}†) = d²
  -- Second, sum of traces of Td(e_{ij})Td(e_{ij})† = ‖Td‖²_HS
  -- Combined with AM-GM lower bound ‖Td‖²_HS ≥ d², the sum of gap traces ≤ 0
  have hgap_trace_sum_le : ∑ ij : Fin d × Fin d,
      (Matrix.trace (KadisonSchwarz.krausMap L
        (Matrix.stdBasis ℂ (Fin d) (Fin d) ij *
         (Matrix.stdBasis ℂ (Fin d) (Fin d) ij)ᴴ) -
      KadisonSchwarz.krausMap L (Matrix.stdBasis ℂ (Fin d) (Fin d) ij) *
        (KadisonSchwarz.krausMap L (Matrix.stdBasis ℂ (Fin d) (Fin d) ij))ᴴ)).re ≤ 0 := by
    let e : Fin d × Fin d → MatrixAlg d := Matrix.stdBasis ℂ (Fin d) (Fin d)
    have hTd_one : Td 1 = 1 := by
      rw [hTd]
      simpa using hK_tp
    have hfirstC : ∑ ij : Fin d × Fin d,
        Matrix.trace (KadisonSchwarz.krausMap L (e ij * (e ij)ᴴ)) = (d : ℂ) * d := by
      calc
        ∑ ij : Fin d × Fin d, Matrix.trace (KadisonSchwarz.krausMap L (e ij * (e ij)ᴴ))
            = ∑ ij : Fin d × Fin d, Matrix.trace (Td (e ij * (e ij)ᴴ)) := by
                refine Finset.sum_congr rfl ?_
                intro ij _
                rw [hTd_kraus]
        _ = Matrix.trace (Td (∑ ij : Fin d × Fin d, e ij * (e ij)ᴴ)) := by
              rw [← Matrix.trace_sum, ← map_sum]
        _ = Matrix.trace (Td ((d : ℂ) • (1 : MatrixAlg d))) := by
              rw [show (∑ ij : Fin d × Fin d, e ij * (e ij)ᴴ) =
                  (d : ℂ) • (1 : MatrixAlg d) by
                simpa [e] using sum_stdBasis_mul_conjTranspose (d := d)]
        _ = Matrix.trace ((d : ℂ) • Td (1 : MatrixAlg d)) := by simp
        _ = Matrix.trace ((d : ℂ) • (1 : MatrixAlg d)) := by rw [hTd_one]
        _ = (d : ℂ) * d := by simp
    have hfirst : ∑ ij : Fin d × Fin d,
        (Matrix.trace (KadisonSchwarz.krausMap L (e ij * (e ij)ᴴ))).re = (d : ℝ) ^ 2 := by
      rw [← Complex.re_sum, hfirstC]
      simp [pow_two]
    have hsecond_eq : ∑ ij : Fin d × Fin d,
        (Matrix.trace (KadisonSchwarz.krausMap L (e ij) *
          (KadisonSchwarz.krausMap L (e ij))ᴴ)).re =
          ∑ ij : Fin d × Fin d, (Matrix.trace ((Td (e ij))ᴴ * Td (e ij))).re := by
      refine Finset.sum_congr rfl ?_
      intro ij _
      rw [hTd_kraus]
      have hcyc (X : MatrixAlg d) : Matrix.trace (X * Xᴴ) = Matrix.trace (Xᴴ * X) := by
        simpa using (Matrix.trace_mul_cycle X (1 : MatrixAlg d) Xᴴ)
      rw [hcyc]
    have hsecond_ge : (d : ℝ) ^ 2 ≤ ∑ ij : Fin d × Fin d,
        (Matrix.trace (KadisonSchwarz.krausMap L (e ij) *
          (KadisonSchwarz.krausMap L (e ij))ᴴ)).re := by
      rw [hsecond_eq]
      simpa [e] using channelDet_norm_one_hs_norm_ge (d := d) Td hdet_Td
    have hsum_eq : ∑ ij : Fin d × Fin d,
        (Matrix.trace (KadisonSchwarz.krausMap L (e ij * (e ij)ᴴ) -
          KadisonSchwarz.krausMap L (e ij) * (KadisonSchwarz.krausMap L (e ij))ᴴ)).re =
          (∑ ij : Fin d × Fin d,
            (Matrix.trace (KadisonSchwarz.krausMap L (e ij * (e ij)ᴴ))).re) -
          (∑ ij : Fin d × Fin d,
            (Matrix.trace (KadisonSchwarz.krausMap L (e ij) *
              (KadisonSchwarz.krausMap L (e ij))ᴴ)).re) := by
      simp [Matrix.trace_sub, Complex.sub_re, Finset.sum_sub_distrib]
    rw [show (∑ ij : Fin d × Fin d,
        (Matrix.trace (KadisonSchwarz.krausMap L
          (Matrix.stdBasis ℂ (Fin d) (Fin d) ij *
           (Matrix.stdBasis ℂ (Fin d) (Fin d) ij)ᴴ) -
        KadisonSchwarz.krausMap L (Matrix.stdBasis ℂ (Fin d) (Fin d) ij) *
          (KadisonSchwarz.krausMap L (Matrix.stdBasis ℂ (Fin d) (Fin d) ij))ᴴ)).re) =
        ∑ ij : Fin d × Fin d,
          (Matrix.trace (KadisonSchwarz.krausMap L (e ij * (e ij)ᴴ) -
            KadisonSchwarz.krausMap L (e ij) * (KadisonSchwarz.krausMap L (e ij))ᴴ)).re by
        simp [e]]
    rw [hsum_eq]
    nlinarith [hfirst, hsecond_ge]
  -- Each gap trace = 0 (nonneg terms summing to ≤ 0)
  have hgap_trace_zero : ∀ ij : Fin d × Fin d,
      (Matrix.trace (KadisonSchwarz.krausMap L
        (Matrix.stdBasis ℂ (Fin d) (Fin d) ij *
         (Matrix.stdBasis ℂ (Fin d) (Fin d) ij)ᴴ) -
      KadisonSchwarz.krausMap L (Matrix.stdBasis ℂ (Fin d) (Fin d) ij) *
        (KadisonSchwarz.krausMap L (Matrix.stdBasis ℂ (Fin d) (Fin d) ij))ᴴ)).re = 0 :=
    eq_zero_of_nonneg_of_sum_le_zero _ hgap_trace_nonneg hgap_trace_sum_le
  -- Each gap = 0 (PSD with real-part-of-trace 0 → trace 0 → matrix 0)
  have hks_all_basis : ∀ ij : Fin d × Fin d,
      KadisonSchwarz.krausMap L
        (Matrix.stdBasis ℂ (Fin d) (Fin d) ij *
         (Matrix.stdBasis ℂ (Fin d) (Fin d) ij)ᴴ) =
      KadisonSchwarz.krausMap L (Matrix.stdBasis ℂ (Fin d) (Fin d) ij) *
        (KadisonSchwarz.krausMap L (Matrix.stdBasis ℂ (Fin d) (Fin d) ij))ᴴ := by
    intro ij
    have hpsd := hgap_psd ij
    have htr_re := hgap_trace_zero ij
    have htr_im := (Complex.le_def.mp hpsd.trace_nonneg).2.symm
    have htr : Matrix.trace (KadisonSchwarz.krausMap L
        (Matrix.stdBasis ℂ (Fin d) (Fin d) ij *
         (Matrix.stdBasis ℂ (Fin d) (Fin d) ij)ᴴ) -
      KadisonSchwarz.krausMap L (Matrix.stdBasis ℂ (Fin d) (Fin d) ij) *
        (KadisonSchwarz.krausMap L (Matrix.stdBasis ℂ (Fin d) (Fin d) ij))ᴴ) = 0 :=
      Complex.ext htr_re htr_im
    exact sub_eq_zero.mp (hpsd.trace_eq_zero_iff.mp htr)
  -- ── Step 2: Kraus commutation for basis elements ──
  have hbasis_commute : ∀ (ij : Fin d × Fin d) (a : Fin r),
      Matrix.stdBasis ℂ (Fin d) (Fin d) ij * K a =
        K a * Td (Matrix.stdBasis ℂ (Fin d) (Fin d) ij) := by
    intro ij
    let e : MatrixAlg d := Matrix.stdBasis ℂ (Fin d) (Fin d) ij
    let es : MatrixAlg d := Matrix.stdBasis ℂ (Fin d) (Fin d) (ij.2, ij.1)
    have hes : es = eᴴ := by
      exact (stdBasis_conjTranspose_eq_swap (d := d) ij.1 ij.2).symm
    have hes_star : esᴴ = e := by
      rw [hes, conjTranspose_conjTranspose]
    have hTd_es : KadisonSchwarz.krausMap L es = (KadisonSchwarz.krausMap L e)ᴴ := by
      rw [hes, KadisonSchwarz.krausMap_conjTranspose]
    have hks_basis :
        KadisonSchwarz.krausMap L (eᴴ * e) =
          (KadisonSchwarz.krausMap L e)ᴴ * KadisonSchwarz.krausMap L e := by
      calc
        KadisonSchwarz.krausMap L (eᴴ * e)
            = KadisonSchwarz.krausMap L (es * esᴴ) := by
                rw [hes]
                simp
        _ = KadisonSchwarz.krausMap L es * (KadisonSchwarz.krausMap L es)ᴴ :=
              hks_all_basis (ij.2, ij.1)
        _ = (KadisonSchwarz.krausMap L e)ᴴ * KadisonSchwarz.krausMap L e := by
              rw [hTd_es]
              simp
    have h := KadisonSchwarz.kraus_commute_of_ks_equality
      (K := L) hL_unital (X := e) hks_basis
    intro a; have ha := h a
    simp only [hL_def, conjTranspose_conjTranspose] at ha
    rwa [← hTd_kraus] at ha
  -- ── Step 3: Kraus commutation for ALL matrices (by linearity) ──
  have hcommute : ∀ (X : MatrixAlg d) (a : Fin r), X * K a = K a * Td X := by
    intro X a
    -- The map F : X ↦ X * K a - K a * Td X is linear and vanishes on
    -- every standard basis element. Use basis extensionality to conclude F = 0.
    set F : MatrixEnd d :=
      LinearMap.mulRight ℂ (K a) - (LinearMap.mulLeft ℂ (K a)).comp Td
    have hF_apply : ∀ Y, F Y = Y * K a - K a * Td Y := fun Y => by
      simp [F, LinearMap.mulRight_apply, LinearMap.mulLeft_apply]
    have hF_zero : F = 0 := by
      apply Module.Basis.ext (matrixSpaceBasis d)
      intro ⟨i, j, u⟩
      simp only [LinearMap.zero_apply]
      rw [hF_apply]
      obtain rfl : u = () := Subsingleton.elim u ()
      -- matrixSpaceBasis d (i, j, ()) relates to stdBasis ℂ (Fin d) (Fin d) (i, j)
      have hbasis_eq : matrixSpaceBasis d (i, j, ()) =
          Matrix.stdBasis ℂ (Fin d) (Fin d) (i, j) := by
        simp only [matrixSpaceBasis, Module.Basis.matrix_apply,
          Module.Basis.singleton_apply, Matrix.stdBasis_eq_single]
      rw [hbasis_eq]
      exact sub_eq_zero.mpr (hbasis_commute (i, j) a)
    have hFX : X * K a - K a * Td X = 0 := by
      simpa [hF_apply X] using congrArg (fun G : MatrixEnd d => G X) hF_zero
    exact sub_eq_zero.mp hFX
  -- ── Step 4: Conclude multiplicativity from Kraus commutation ──
  intro M N
  simp only [hTd]
  -- Rewrite RHS: (∑ K_i† M K_i) * (∑ K_j† N K_j) = ∑ (K_i† M K_i) * (∑ K_j† N K_j)
  rw [Finset.sum_mul]
  -- Suffices to show term-by-term equality
  refine Finset.sum_congr rfl ?_
  intro a _
  have hNKa := hcommute N a
  calc (K a)ᴴ * (M * N) * K a
      = (K a)ᴴ * M * (N * K a) := by simp [Matrix.mul_assoc]
    _ = (K a)ᴴ * M * (K a * Td N) := by rw [hNKa]
    _ = (K a)ᴴ * M * K a * Td N := by simp [Matrix.mul_assoc]
    _ = (K a)ᴴ * M * K a * ∑ b : Fin r, (K b)ᴴ * N * K b := by
        rw [show Td N = ∑ b : Fin r, (K b)ᴴ * N * K b from hTd N]

/-- Extract a unitary from the Skolem–Noether inner form plus star-preservation.

Given `T(A) = P⁻¹AP` where `P ∈ GL_d(ℂ)`, and `T` preserves `*` (i.e. `Tᴴ = T†`),
`P†P` commutes with all matrices and is therefore scalar. Since `P†P` is PSD
and invertible, the scalar is positive real, and `V = (√c)⁻¹ · P†` is unitary
with `T = unitaryChannel V`. -/
private theorem extract_unitary_from_inner_form [NeZero d]
    {T : MatrixEnd d} (_hT : IsChannel T)
    (P : GL (Fin d) ℂ)
    (hT_inner : ∀ A : MatrixAlg d,
        T A = (↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d) * A * (↑P : MatrixAlg d))
    (hP_star_comm : ∀ Y : MatrixAlg d,
        (↑P : MatrixAlg d)ᴴ * (↑P : MatrixAlg d) * Y =
          Y * ((↑P : MatrixAlg d)ᴴ * (↑P : MatrixAlg d))) :
    ∃ U : Matrix.unitaryGroup (Fin d) ℂ, T = unitaryChannel U := by
  -- GL identities
  have hPinvP : (↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d) * (↑P : MatrixAlg d) = 1 := by
    exact congrArg Units.val (inv_mul_cancel P)
  have hPPinv : (↑P : MatrixAlg d) * (↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d) = 1 := by
    exact congrArg Units.val (mul_inv_cancel P)
  -- Step 1: P†P is in the center → is a scalar matrix
  have hPHP_center :
      (↑P : MatrixAlg d)ᴴ * (↑P : MatrixAlg d) ∈
        Set.range (Matrix.scalar (Fin d) : ℂ →+* MatrixAlg d) := by
    rw [← Matrix.center_eq_range, Semigroup.mem_center_iff]
    exact fun Y => (hP_star_comm Y).symm
  obtain ⟨c, hc_eq⟩ := hPHP_center
  rw [Matrix.scalar_apply] at hc_eq
  have hPHP_smul :
      (↑P : MatrixAlg d)ᴴ * (↑P : MatrixAlg d) = c • (1 : MatrixAlg d) := by
    rw [← hc_eq, ← Matrix.smul_one_eq_diagonal]
  -- Step 2: c ≥ 0 (from PSD)
  have hPHP_psd : ((↑P : MatrixAlg d)ᴴ * (↑P : MatrixAlg d)).PosSemidef :=
    Matrix.posSemidef_conjTranspose_mul_self _
  have hc_nonneg : 0 ≤ c := by
    have := hPHP_psd.diag_nonneg (i := (0 : Fin d))
    rwa [hPHP_smul, Pi.smul_apply, Pi.smul_apply, one_apply_eq,
      smul_eq_mul, mul_one] at this
  -- Step 3: c ≠ 0 (from invertibility of P)
  have hc_ne : c ≠ 0 := by
    intro hc0
    have h0 : (↑P : MatrixAlg d)ᴴ * (↑P : MatrixAlg d) = 0 := by
      rw [hPHP_smul, hc0, zero_smul]
    have hPH_zero : (↑P : MatrixAlg d)ᴴ = 0 := by
      have := congr_arg (· * (↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d)) h0
      simp only [zero_mul, Matrix.mul_assoc] at this
      rwa [hPPinv, mul_one] at this
    have hP_zero : (↑P : MatrixAlg d) = 0 := by
      rw [← conjTranspose_conjTranspose (↑P : MatrixAlg d),
        hPH_zero, conjTranspose_zero]
    exact one_ne_zero (show (1 : MatrixAlg d) = 0 by
      rw [← hPPinv, hP_zero, zero_mul])
  -- Step 4: c is a positive real number
  have hc_re_nonneg : 0 ≤ c.re := (Complex.nonneg_iff.mp hc_nonneg).1
  have hc_im_zero : c.im = 0 := (Complex.nonneg_iff.mp hc_nonneg).2.symm
  have hc_re_pos : 0 < c.re := by
    rcases lt_or_eq_of_le hc_re_nonneg with h | h
    · exact h
    · exact absurd (Complex.ext h.symm (by simp [hc_im_zero])) hc_ne
  -- Step 5: Define V = (√c)⁻¹ • P and prove V†V = 1
  set r := Real.sqrt c.re with hr_def
  have hr_pos : 0 < r := Real.sqrt_pos.mpr hc_re_pos
  have hr_ne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr_pos.ne'
  have hr_sq : (↑r : ℂ) * (↑r : ℂ) = c := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc_re_nonneg]
    exact Complex.ext (Complex.ofReal_re _) (by simp [hc_im_zero])
  set V : MatrixAlg d := (↑r : ℂ)⁻¹ • (↑P : MatrixAlg d) with hV_def
  have hstar_r_inv : star ((↑r : ℂ)⁻¹) = (↑r : ℂ)⁻¹ := by
    rw [star_inv₀, show star (↑r : ℂ) = ↑r from RCLike.conj_ofReal r]
  have hVHV : Vᴴ * V = 1 := by
    simp only [hV_def, conjTranspose_smul, smul_mul_assoc, mul_smul_comm, hPHP_smul,
      hstar_r_inv, smul_smul]
    rw [show (↑r : ℂ)⁻¹ * ((↑r : ℂ)⁻¹ * c) = 1 from by
      field_simp; rw [sq]; exact hr_sq.symm]
    exact one_smul _ _
  -- Step 6: U = V† is unitary
  have hU_mem : Vᴴ ∈ Matrix.unitaryGroup (Fin d) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    have : star Vᴴ = V := by
      rw [Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose]
    rw [this]
    exact hVHV
  set U : Matrix.unitaryGroup (Fin d) ℂ := ⟨Vᴴ, hU_mem⟩
  -- Step 7: T = unitaryChannel U
  -- Key: Pm = ↑r • V and Pinvm = (↑r)⁻¹ • V†
  have hPm_eq : (↑P : MatrixAlg d) = (↑r : ℂ) • V := by
    simp [hV_def, smul_smul, mul_inv_cancel₀ hr_ne]
  have hPinvm_eq :
      (↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d) = (↑r : ℂ)⁻¹ • Vᴴ := by
    have hVPinv : V * (↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d) =
        (↑r : ℂ)⁻¹ • (1 : MatrixAlg d) := by
      have h : (↑r : ℂ) • (V * (↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d)) = 1 := by
        rw [← smul_mul_assoc, ← hPm_eq]; exact hPPinv
      rw [show V * (↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d) =
          (↑r : ℂ)⁻¹ • (1 : MatrixAlg d) from by
        have := congr_arg ((↑r : ℂ)⁻¹ • ·) h
        simp only [smul_smul, inv_mul_cancel₀ hr_ne, one_smul] at this
        exact this]
    calc (↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d)
        = 1 * (↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d) := (one_mul _).symm
      _ = (Vᴴ * V) * (↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d) := by rw [hVHV]
      _ = Vᴴ * (V * (↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d)) := by
          rw [Matrix.mul_assoc]
      _ = Vᴴ * ((↑r : ℂ)⁻¹ • (1 : MatrixAlg d)) := by rw [hVPinv]
      _ = (↑r : ℂ)⁻¹ • Vᴴ := by rw [mul_smul_comm, mul_one]
  refine ⟨U, LinearMap.ext fun A => ?_⟩
  simp only [unitaryChannel, LinearMap.coe_mk, AddHom.coe_mk]
  change T A = Vᴴ * A * (Vᴴ)ᴴ
  rw [conjTranspose_conjTranspose, hT_inner A, hPinvm_eq, hPm_eq,
    smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul,
    inv_mul_cancel₀ hr_ne, one_smul]

/-- **Wolf Thm 6.1(2), forward direction.** -/
private theorem forward_det_one_implies_unitaryChannel [NeZero d]
    (hT : IsChannel T) (hdet : ‖channelDet T‖ = 1) :
    ∃ U : Matrix.unitaryGroup (Fin d) ℂ, T = unitaryChannel U := by
  classical
  have hall := channel_all_eigenvalues_norm_one (d := d) hT hdet
  obtain ⟨r, K, hK⟩ := hT.cp
  have hK_tp : ∑ i : Fin r, (K i)ᴴ * K i = 1 :=
    kraus_sum_conjTranspose_mul_of_tp K T hK hT.tp
  -- Build the Heisenberg dual
  let Td : MatrixEnd d :=
    { toFun := fun X => ∑ i : Fin r, (K i)ᴴ * X * K i
      map_add' := fun X Y => by simp [mul_add, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c X => by simp [Finset.smul_sum] }
  have hTd_def : ∀ X, Td X = ∑ i : Fin r, (K i)ᴴ * X * K i := fun _ => rfl
  have hTd_one : Td 1 = 1 := by
    change ∑ i : Fin r, (K i)ᴴ * 1 * K i = 1
    simp [hK_tp]
  have hTd_star : ∀ X : MatrixAlg d, Td Xᴴ = (Td X)ᴴ := by
    intro X
    change ∑ i, (K i)ᴴ * Xᴴ * K i = (∑ i, (K i)ᴴ * X * K i)ᴴ
    simp [conjTranspose_sum, conjTranspose_mul, Matrix.mul_assoc]
  -- Td is multiplicative
  have hMul := heisenberg_dual_multiplicative hT hdet hall K hK hK_tp Td hTd_def
  have hTd_ne : Td ≠ 0 := by
    intro h; have := congr_fun (congr_arg DFunLike.coe h) 1; simp [hTd_one] at this
  -- Td is bijective (nonzero multiplicative map on simple algebra)
  have hTd_bij := MPSTensor.linear_mul_endomorphism_bijective Td hMul hTd_ne
  -- Skolem–Noether: Td(X) = PXP⁻¹
  let Td_alg := MPSTensor.linearMapToAlgHom Td hMul hTd_bij.2
  let Td_equiv : MatrixAlg d ≃ₐ[ℂ] MatrixAlg d := AlgEquiv.ofBijective Td_alg hTd_bij
  obtain ⟨P, hP⟩ := MPSTensor.skolemNoether_matrix Td_equiv
  -- Key identities for P
  have hPinvP : (↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d) * (↑P : MatrixAlg d) = 1 := by
    have : (P⁻¹ * P : GL (Fin d) ℂ) = 1 := inv_mul_cancel _
    exact congrArg Units.val this
  have hPPinv : (↑P : MatrixAlg d) * (↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d) = 1 := by
    have : (P * P⁻¹ : GL (Fin d) ℂ) = 1 := mul_inv_cancel _
    exact congrArg Units.val this
  -- Trace adjointness: tr(T(A)*B) = tr(A*Td(B))
  have hAdj : ∀ A B : MatrixAlg d, trace (T A * B) = trace (A * Td B) := by
    intro A B
    simp only [hK, hTd_def]
    rw [Finset.sum_mul, trace_sum]
    conv_rhs => rw [Matrix.mul_sum, trace_sum]
    apply Finset.sum_congr rfl
    intro i _
    simpa [Matrix.mul_assoc] using
      (Matrix.trace_mul_cycle A ((K i)ᴴ * B) (K i)).symm
  -- Derive T(A) = P⁻¹AP from trace adjointness
  have hT_inner : ∀ A : MatrixAlg d,
      T A = (↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d) * A * (↑P : MatrixAlg d) := by
    intro A
    suffices h : ∀ B, trace ((T A -
        (↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d) * A * (↑P : MatrixAlg d)) * B) = 0 by
      exact sub_eq_zero.mp ((Matrix.trace_mul_right_eq_zero_iff _).mp h)
    intro B
    rw [sub_mul, trace_sub, hAdj A B]
    change trace (A * Td B) -
      trace ((↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d) * A *
        (↑P : MatrixAlg d) * B) = 0
    rw [show Td B = Td_equiv B from rfl, hP B, sub_eq_zero]
    simpa [Matrix.mul_assoc] using
      (Matrix.trace_mul_cycle (A * (↑P : MatrixAlg d)) B
        ((↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d)))
  -- `Pᴴ * P` commutes with all matrices, from star-preservation of `Td`.
  have hP_star_comm : ∀ Y : MatrixAlg d,
      (↑P : MatrixAlg d)ᴴ * (↑P : MatrixAlg d) * Y =
        Y * ((↑P : MatrixAlg d)ᴴ * (↑P : MatrixAlg d)) := by
    intro Y
    have hstar_inner : ∀ X : MatrixAlg d,
        (↑P : MatrixAlg d) * Xᴴ * (↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d) =
          (↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d)ᴴ * Xᴴ * (↑P : MatrixAlg d)ᴴ := by
      intro X
      have h := hTd_star X
      rw [show Td Xᴴ = Td_equiv Xᴴ from rfl, hP Xᴴ] at h
      rw [show Td X = Td_equiv X from rfl, hP X] at h
      simpa [Matrix.mul_assoc, conjTranspose_mul, conjTranspose_conjTranspose] using h
    have hPstarPinvstar :
        (↑P : MatrixAlg d)ᴴ * (↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d)ᴴ = 1 := by
      rw [← conjTranspose_mul, hPinvP, conjTranspose_one]
    specialize hstar_inner Yᴴ
    simp only [conjTranspose_conjTranspose] at hstar_inner
    calc
      (↑P : MatrixAlg d)ᴴ * (↑P : MatrixAlg d) * Y
          = (↑P : MatrixAlg d)ᴴ *
              ((↑P : MatrixAlg d) * Y * (↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d)) *
              (↑P : MatrixAlg d) := by
            simp [Matrix.mul_assoc]
      _ = (↑P : MatrixAlg d)ᴴ *
            ((↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d)ᴴ * Y * (↑P : MatrixAlg d)ᴴ) *
            (↑P : MatrixAlg d) := by rw [hstar_inner]
      _ = ((↑P : MatrixAlg d)ᴴ * (↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d)ᴴ) * Y *
            ((↑P : MatrixAlg d)ᴴ * (↑P : MatrixAlg d)) := by
            simp [Matrix.mul_assoc]
      _ = Y * ((↑P : MatrixAlg d)ᴴ * (↑P : MatrixAlg d)) := by
            rw [Matrix.mul_assoc, hPstarPinvstar, Matrix.one_mul]
  -- Extract unitary from inner form + P†P commuting with everything
  exact extract_unitary_from_inner_form hT P hT_inner hP_star_comm

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

/-- Wolf Thm 6.1(2) restricted to CPTP maps: `‖det T‖ = 1 ↔ ∃ U, T = unitaryChannel U`.

The transposition branch from Wolf's general Thm 6.1(2) for positive TP maps does not
appear for CPTP maps since the transpose map is not completely positive. -/
theorem channelDet_norm_eq_one_iff_exists_unitaryChannel
    (hT : IsChannel T) :
    ‖channelDet T‖ = 1 ↔ ∃ U : Matrix.unitaryGroup (Fin d) ℂ, T = unitaryChannel U := by
  constructor
  · intro h
    by_cases hd : d = 0
    · subst hd; exact ⟨1, Subsingleton.elim _ _⟩
    · haveI : NeZero d := ⟨hd⟩
      exact forward_det_one_implies_unitaryChannel hT h
  · rintro ⟨U, rfl⟩
    exact channelDet_norm_eq_one_of_unitaryChannel U

/-- CPTP specialization of the unitary characterization (alias of
`channelDet_norm_eq_one_iff_exists_unitaryChannel`). -/
theorem channelDet_norm_eq_one_iff_exists_unitaryChannel_of_channel
    (hT : IsChannel T) :
    ‖channelDet T‖ = 1 ↔ ∃ U : Matrix.unitaryGroup (Fin d) ℂ, T = unitaryChannel U :=
  channelDet_norm_eq_one_iff_exists_unitaryChannel hT

end WolfStatements
