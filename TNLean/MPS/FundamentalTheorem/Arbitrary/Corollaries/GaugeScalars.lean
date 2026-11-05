/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.Arbitrary.Corollaries.ClassForm
import TNLean.MPS.Periodic.PhaseClasses

/-!
# The gauge scalars of admissible, normal and periodic blocks

For an admissible tensor `R` (irreducible, with a nonzero letter), every gauge scalar `c`
(`c • R` gauge related to `R`) is a root of unity; for a normal tensor of positive bond dimension
the only gauge scalar is `1`. For an irreducible block
whose transfer map has spectral radius one and peripheral spectrum the `m`-th roots of unity,
every gauge scalar satisfies `c ^ m = 1`, as do the scalars in the `ℤ_m`-gauge clause of the
periodic equal case.

The period is the one of `MPSTensor.IsSpectrallyPeriodic`, which records exactly the
three conditions: irreducible transfer map, spectral radius one, peripheral
spectrum the `m`-th roots of unity. The left-canonical version `MPSTensor.IsPeriodic` follows.

## Main results

* `MPSTensor.exists_pos_pow_eq_one_of_mem_gaugeScalars`.
* `MPSTensor.gaugeScalars_eq_singleton_one_of_isNormal`.
* `MPSTensor.IsSpectrallyPeriodic.pow_eq_one_of_mem_gaugeScalars`.
* `MPSTensor.IsPeriodic.pow_eq_one_of_mem_gaugeScalars`: the version for left-canonical blocks.
* `MPSTensor.gaugeScalarsSubgroup`, `MPSTensor.gaugeScalars_eq_image_gaugeScalarsSubgroup`,
  `MPSTensor.finite_gaugeScalars`, `MPSTensor.finite_gaugeScalarsSubgroup`: the gauge scalars of
  an admissible tensor form a finite subgroup of `ℂˣ`.

## References

* De las Cuevas, Cirac, Schuch, Pérez-García, arXiv:1708.00029, lines 248–261 (periodic blocks).
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ} {R : MPSTensor d D} {c : ℂ}

/-- A gauge scalar `c` of `R` fixes every word trace up to the factor `c ^ |w|`:
`c ^ |w| tr R^w = tr R^w`. -/
theorem pow_length_mul_trace_evalWord_eq_of_mem_gaugeScalars (hc : c ∈ gaugeScalars R)
    (w : List (Fin d)) :
    c ^ w.length * Matrix.trace (Kraus.evalWord R w) = Matrix.trace (Kraus.evalWord R w) := by
  have hc' : IsGaugeRelated (c • R) R := hc
  have h := hc'.trace_evalWord_eq w
  rwa [show c • R = fun i => c • R i from rfl, Kraus.evalWord_smul, Matrix.trace_smul,
    smul_eq_mul] at h

/-- If a word with nonzero trace has length `n`, every gauge scalar satisfies `c ^ n = 1`. -/
private theorem pow_length_eq_one_of_mem_gaugeScalars (hc : c ∈ gaugeScalars R)
    {w : List (Fin d)} (hw : Matrix.trace (Kraus.evalWord R w) ≠ 0) : c ^ w.length = 1 :=
  mul_right_cancel₀ hw ((pow_length_mul_trace_evalWord_eq_of_mem_gaugeScalars hc w).trans
    (one_mul _).symm)

/-- **Gauge scalars are roots of unity.** Every gauge scalar of an admissible tensor is a root of
unity. -/
theorem exists_pos_pow_eq_one_of_mem_gaugeScalars (hirr : Matrix.IsIrreducibleAction R)
    (hlet : ∃ i, R i ≠ 0) (hc : c ∈ gaugeScalars R) : ∃ n : ℕ, 0 < n ∧ c ^ n = 1 := by
  obtain ⟨w, hw, htr⟩ := exists_ne_nil_and_trace_evalWord_ne_zero hirr hlet
  exact ⟨w.length, List.length_pos_of_ne_nil hw, pow_length_eq_one_of_mem_gaugeScalars hc htr⟩

/-- **Normal tensors have trivial gauge scalars.** A normal tensor of positive bond dimension has
`1` as its only gauge scalar. -/
theorem gaugeScalars_eq_singleton_one_of_isNormal (hR : Kraus.IsNormal R) (hD : 0 < D) :
    gaugeScalars R = {1} := by
  have : NeZero D := ⟨hD.ne'⟩
  ext c
  rw [Set.mem_singleton_iff]
  constructor
  · intro hc
    obtain ⟨i, hi⟩ := exists_ne_zero_of_isNormal hR
    obtain ⟨L, -, hspan⟩ := hR
    have hspan' := hspan.span_eq_top
    -- a word of length `L` with nonzero trace, since the identity is in the span
    have h1 : ∃ σ : Fin L → Fin d, Matrix.trace (Kraus.evalWord R (List.ofFn σ)) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have hle : Submodule.span ℂ
          (Set.range fun σ : Fin L → Fin d => Kraus.evalWord R (List.ofFn σ)) ≤
            LinearMap.ker (Matrix.traceLinearMap (Fin D) ℂ ℂ) :=
        Submodule.span_le.2 (Set.range_subset_iff.2 fun σ => by simpa using hcon σ)
      rw [hspan'] at hle
      have h1 := hle (Submodule.mem_top (x := (1 : Matrix (Fin D) (Fin D) ℂ)))
      simp only [LinearMap.mem_ker, Matrix.traceLinearMap_apply, Matrix.trace_one,
        Fintype.card_fin, Nat.cast_eq_zero] at h1
      omega
    -- a word of length `L + 1` with nonzero trace, since `(R i)ᴴ` is in the span
    have h2 : ∃ σ : Fin L → Fin d,
        Matrix.trace (Kraus.evalWord R (i :: List.ofFn σ)) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have hle : Submodule.span ℂ
          (Set.range fun σ : Fin L → Fin d => Kraus.evalWord R (List.ofFn σ)) ≤
            LinearMap.ker ((Matrix.traceLinearMap (Fin D) ℂ ℂ).comp
              (LinearMap.mulLeft ℂ (R i))) :=
        Submodule.span_le.2 (Set.range_subset_iff.2 fun σ => by
          simpa [Kraus.evalWord] using hcon σ)
      rw [hspan'] at hle
      have h2 := hle (Submodule.mem_top (x := (R i)ᴴ))
      simp only [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.mulLeft_apply,
        Matrix.traceLinearMap_apply] at h2
      open scoped ComplexOrder in
      exact hi (Matrix.trace_mul_conjTranspose_self_eq_zero_iff.1 h2)
    obtain ⟨σ, hσ⟩ := h1
    obtain ⟨τ, hτ⟩ := h2
    have p1 := pow_length_eq_one_of_mem_gaugeScalars hc hσ
    have p2 := pow_length_eq_one_of_mem_gaugeScalars hc hτ
    rw [List.length_ofFn] at p1
    rw [List.length_cons, List.length_ofFn, pow_succ, p1, one_mul] at p2
    exact p2
  · rintro rfl
    change IsGaugeRelated ((1 : ℂ) • R) R
    rw [one_smul]
    exact IsGaugeRelated.refl R

open scoped Matrix.Norms.Operator in
/-- An eigenvalue of an endomorphism of square matrices is bounded in modulus by its spectral
radius; here the spectral radius is one. -/
private theorem norm_le_one_of_hasEigenvalue
    {E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hE : spectralRadius ℂ ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) E) = 1)
    {μ : ℂ} (hμ : Module.End.HasEigenvalue E μ) : ‖μ‖ ≤ 1 := by
  have hmem : μ ∈ spectrum ℂ ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) E) :=
    by rw [AlgEquiv.spectrum_eq]; exact Module.End.hasEigenvalue_iff_mem_spectrum.mp hμ
  have h := le_iSup₂ (f := fun k (_ : k ∈ spectrum ℂ
    ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) E)) =>
      ((‖k‖₊ : NNReal) : ENNReal)) μ hmem
  rw [← spectralRadius_eq_of_unital, hE] at h
  have h' : ‖μ‖₊ ≤ 1 := by exact_mod_cast h
  exact_mod_cast h'

/-- **Gauge scalars of a periodic block.** For a block with irreducible transfer map of spectral
radius one and peripheral spectrum the `m`-th roots of unity, every gauge scalar is an `m`-th root
of unity. -/
theorem IsSpectrallyPeriodic.pow_eq_one_of_mem_gaugeScalars {m : ℕ}
    (hR : IsSpectrallyPeriodic m R) (hc : c ∈ gaugeScalars R) : c ^ m = 1 := by
  -- `1` is a peripheral eigenvalue; let `v` be an eigenvector
  have h1 : (1 : ℂ) ∈ peripheralEigenvalues (Kraus.transferMap (d := d) (D := D) R) := by
    rw [hR.peripheral_eq]
    exact one_pow m
  obtain ⟨v, hv⟩ := h1.1.exists_hasEigenvector
  have hEv : Kraus.transferMap (d := d) (D := D) R v = v := by
    rw [Module.End.mem_eigenspace_iff.mp hv.1, one_smul]
  have hv0 : v ≠ 0 := hv.2
  have hc' : IsGaugeRelated (c • R) R := hc
  obtain ⟨X, Y, hXY, hYX, hint⟩ := hc'
  have hint' : ∀ i, c • (R i * X) = X * R i := fun i => by
    rw [← hint i, Pi.smul_apply, Matrix.smul_mul]
  have hY : ∀ i, R i * Y = c • (Y * R i) := fun i => by
    calc R i * Y = Y * (X * R i) * Y := by
          rw [← Matrix.mul_assoc, hYX, Matrix.one_mul]
      _ = Y * (c • (R i * X)) * Y := by rw [hint']
      _ = c • (Y * R i * (X * Y)) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = c • (Y * R i) := by rw [hXY, Matrix.mul_one]
  -- `c` is an eigenvalue, with eigenvector `Y v`
  have hEY : Kraus.transferMap (d := d) (D := D) R (Y * v) = c • (Y * v) := by
    rw [Kraus.transferMap_apply]
    calc ∑ i, R i * (Y * v) * (R i)ᴴ = ∑ i, c • (Y * (R i * v * (R i)ᴴ)) :=
          Finset.sum_congr rfl fun i _ => by
            rw [← Matrix.mul_assoc, hY i]
            simp only [Matrix.smul_mul, Matrix.mul_assoc]
      _ = c • (Y * ∑ i, R i * v * (R i)ᴴ) := by rw [Matrix.mul_sum, Finset.smul_sum]
      _ = c • (Y * v) := by rw [← Kraus.transferMap_apply, hEv]
  -- `c • E (X v) = X v`
  have hEX : c • Kraus.transferMap (d := d) (D := D) R (X * v) = X * v := by
    rw [Kraus.transferMap_apply]
    calc c • ∑ i, R i * (X * v) * (R i)ᴴ = ∑ i, X * (R i * v * (R i)ᴴ) := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Matrix.mul_assoc, ← Matrix.smul_mul, ← Matrix.smul_mul, hint']
          simp only [Matrix.mul_assoc]
      _ = X * ∑ i, R i * v * (R i)ᴴ := by rw [Matrix.mul_sum]
      _ = X * v := by rw [← Kraus.transferMap_apply, hEv]
  have hYv : Y * v ≠ 0 := fun h0 => hv0 (by
    rw [← Matrix.one_mul v, ← hXY, Matrix.mul_assoc, h0, Matrix.mul_zero])
  have hXv : X * v ≠ 0 := fun h0 => hv0 (by
    rw [← Matrix.one_mul v, ← hYX, Matrix.mul_assoc, h0, Matrix.mul_zero])
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hEX
    exact hXv hEX.symm
  have hle : ‖c‖ ≤ 1 := norm_le_one_of_hasEigenvalue hR.spectral_radius_one
    (hasEigenvalue_of_eigenvector_eq _ c _ hEY hYv)
  have hEX' : Kraus.transferMap (d := d) (D := D) R (X * v) = c⁻¹ • (X * v) := by
    calc Kraus.transferMap (d := d) (D := D) R (X * v)
        = c⁻¹ • (c • Kraus.transferMap (d := d) (D := D) R (X * v)) := by
          rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      _ = c⁻¹ • (X * v) := by rw [hEX]
  have hle' : ‖c⁻¹‖ ≤ 1 := norm_le_one_of_hasEigenvalue hR.spectral_radius_one
    (hasEigenvalue_of_eigenvector_eq _ c⁻¹ _ hEX' hXv)
  have hnorm : ‖c‖ = 1 := by
    rw [norm_inv] at hle'
    have hpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
    have : 1 ≤ ‖c‖ := by
      rwa [inv_le_one₀ hpos] at hle'
    linarith
  have hmem : c ∈ peripheralEigenvalues (Kraus.transferMap (d := d) (D := D) R) :=
    ⟨hasEigenvalue_of_eigenvector_eq _ c _ hEY hYv, hnorm⟩
  rw [hR.peripheral_eq] at hmem
  exact hmem

/-- **Gauge scalars of a left-canonical periodic block.** Every gauge scalar of a block of period
`m` is an `m`-th root of unity. -/
theorem IsPeriodic.pow_eq_one_of_mem_gaugeScalars {m : ℕ} (hR : IsPeriodic m R)
    (hc : c ∈ gaugeScalars R) : c ^ m = 1 :=
  hR.isSpectrallyPeriodic.pow_eq_one_of_mem_gaugeScalars hc

/-! ### The group of gauge scalars -/

/-- The units among the gauge scalars of `R`, a subgroup of `ℂˣ`: if
`c R ≃ R` and `c' R ≃ R`, then `c c' R ≃ c R ≃ R`, and `c⁻¹ R ≃ c⁻¹ c R = R`. -/
def gaugeScalarsSubgroup {D : ℕ} (R : MPSTensor d D) : Subgroup ℂˣ where
  carrier := {u | (u : ℂ) ∈ gaugeScalars R}
  mul_mem' {u v} hu hv := by
    have hu' : IsGaugeRelated ((u : ℂ) • R) R := hu
    have hv' : IsGaugeRelated ((v : ℂ) • R) R := hv
    change IsGaugeRelated (((u * v : ℂˣ) : ℂ) • R) R
    rw [Units.val_mul, ← smul_smul]
    exact (hv'.smul (u : ℂ)).trans hu'
  one_mem' := by
    change IsGaugeRelated (((1 : ℂˣ) : ℂ) • R) R
    rw [Units.val_one, one_smul]
    exact IsGaugeRelated.refl R
  inv_mem' {u} hu := by
    have hu' : IsGaugeRelated ((u : ℂ) • R) R := hu
    change IsGaugeRelated (((u⁻¹ : ℂˣ) : ℂ) • R) R
    have h := (hu'.smul ((u⁻¹ : ℂˣ) : ℂ)).symm
    rwa [smul_smul, Units.inv_mul, one_smul] at h

/-- `0` is not a gauge scalar of a tensor with a nonzero letter. -/
theorem zero_notMem_gaugeScalars (hlet : ∃ i, R i ≠ 0) : (0 : ℂ) ∉ gaugeScalars R := by
  intro h0
  have h : IsGaugeRelated ((0 : ℂ) • R) R := h0
  obtain ⟨i, hi⟩ := hlet
  exact hi ((h.forall_eq_zero_iff.1 fun j => by rw [Pi.smul_apply, zero_smul]) i)

/-- **Gauge scalars form a group.** For a tensor with a nonzero letter,
the gauge scalars are exactly the image of the subgroup `gaugeScalarsSubgroup R` of `ℂˣ`. -/
theorem gaugeScalars_eq_image_gaugeScalarsSubgroup (hlet : ∃ i, R i ≠ 0) :
    gaugeScalars R = ((↑) : ℂˣ → ℂ) '' (gaugeScalarsSubgroup R : Set ℂˣ) := by
  ext c
  constructor
  · intro hc
    have hc0 : c ≠ 0 := fun h => zero_notMem_gaugeScalars hlet (h ▸ hc)
    exact ⟨Units.mk0 c hc0, hc, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact hu

/-- **Gauge scalars are finite.** An admissible tensor has finitely
many gauge scalars: all of them are `|w|`-th roots of unity for one nonempty word `w` with
`tr R^w ≠ 0`. -/
theorem finite_gaugeScalars (hirr : Matrix.IsIrreducibleAction R) (hlet : ∃ i, R i ≠ 0) :
    (gaugeScalars R).Finite := by
  obtain ⟨w, hw, htr⟩ := exists_ne_nil_and_trace_evalWord_ne_zero hirr hlet
  have hn : 0 < w.length := List.length_pos_of_ne_nil hw
  refine (Polynomial.nthRoots w.length (1 : ℂ)).toFinset.finite_toSet.subset fun c hc => ?_
  rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots hn]
  exact pow_length_eq_one_of_mem_gaugeScalars hc htr

/-- **The group of gauge scalars is finite.** For an admissible
tensor, the subgroup `gaugeScalarsSubgroup R` of `ℂˣ` is finite. -/
theorem finite_gaugeScalarsSubgroup (hirr : Matrix.IsIrreducibleAction R)
    (hlet : ∃ i, R i ≠ 0) : Finite (gaugeScalarsSubgroup R) :=
  ((finite_gaugeScalars hirr hlet).preimage Units.val_injective.injOn).to_subtype

end MPSTensor
