/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.Primitive
import TNLean.MPS.RFP.ZeroCorrelationLength

/-!
# Ingredients of the decaying-correlation estimate

The lower bound on the preparation depth of a normal matrix product state
(arXiv:2307.01696, Theorem 1) rests on a correlation estimate, Lemma 2 of the
Supplemental Material ("Proof of Theorem 1"): suitable local observables have
a connected correlation of size at least `c e^{-(s-1)/ξ}` at separation `s`.
This file proves the ingredients of that estimate which are specific to matrix
product states and do not depend on the finite-size trace formula or on the
peripheral spectral expansion.

* `exists_physicalObservableTransfer_eq`: when the words of length `L` span
  the matrix algebra, every linear map on virtual matrices is the inserted
  transfer map `E_O` of an observable `O` on `L` sites. This is the source's
  step "we can always choose `O` (and `O'`), such that the corresponding
  transfer matrix `E_O = |A⟩⟨B|` for arbitrary `A, B` (up to a normalization
  constant)".
* `exists_limitCorrelator_eq_pow`: for an eigenvector `R` of the transfer map
  with eigenvalue `λ ≠ 1`, suitable observables make the length-independent
  part of the correlator equal to `λ^t`.

The two general estimates used alongside these, the Vandermonde window bound
`Complex.exists_window_le_norm_sum_mul_pow` and the expectation-overlap bound
`LinearMap.IsSymmetric.norm_inner_mul_norm_sub_le`, live in
`TNLean/Algebra/ExponentialSumWindow.lean` and
`TNLean/Algebra/ExpectationOverlap.lean`.

The chapter entries are `lem:ldp_observable_transfer_surjective` and
`lem:ldp_limit_correlator_eigenvalue`.
-/

open scoped Matrix BigOperators InnerProductSpace

namespace MPSTensor

variable {d D : ℕ}

/-! ### Inserted transfer maps of observables -/

/-- Observables on `L` sites realize every linear map on virtual matrices as an
inserted transfer map, provided the products of `L` matrices of `A` span the
full matrix algebra.

This is the step "Since the tensor `A` is injective, we can always choose `O`
(and `O'`), such that the corresponding transfer matrix `E_O = |A⟩⟨B|` for
arbitrary `A, B` (up to a normalization constant)" in arXiv:2307.01696,
Supplemental Material, proof of Lemma 2, stated for every linear map and for
the blocked length `L` at which a normal tensor becomes injective. -/
theorem exists_physicalObservableTransfer_eq {A : MPSTensor d D} {L : ℕ}
    (hL : Kraus.IsNBlkInjective A L)
    (Φ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) :
    ∃ O : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ,
      physicalObservableTransfer A L O = Φ := by
  classical
  have hcoeff : ∀ a b : Fin D, ∃ c : (Fin L → Fin d) → ℂ,
      ∑ σ, c σ • Kraus.evalWord A (List.ofFn σ) = Matrix.single a b 1 := by
    intro a b
    have hmem : Matrix.single a b (1 : ℂ) ∈ Submodule.span ℂ
        (Set.range fun σ : Fin L → Fin d ↦ Kraus.evalWord A (List.ofFn σ)) := by
      rw [hL.span_eq_top]
      exact Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hmem
    exact ⟨c, hc⟩
  choose C hC using hcoeff
  let Ounit : Fin D → Fin D → Fin D → Fin D →
      Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ :=
    fun a b c e τ σ ↦ C a b σ * starRingEnd ℂ (C c e τ)
  have hunit : ∀ a b c e (X : Matrix (Fin D) (Fin D) ℂ),
      physicalObservableTransfer A L (Ounit a b c e) X =
        Matrix.single a b 1 * X * (Matrix.single c e 1)ᴴ := by
    intro a b c e X
    rw [physicalObservableTransfer_coeff_mul, hC, hC]
  refine ⟨∑ a, ∑ b, ∑ c, ∑ e, (Φ (Matrix.single b e 1)) a c • Ounit a b c e, ?_⟩
  apply LinearMap.ext
  intro X
  have hlin := physicalObservableTransferₗ_apply A L
    (∑ a, ∑ b, ∑ c, ∑ e, (Φ (Matrix.single b e 1)) a c • Ounit a b c e)
  rw [← hlin]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    physicalObservableTransferₗ_apply, hunit]
  conv_rhs => rw [Matrix.matrix_eq_sum_single X]
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, map_sum, Matrix.conjTranspose_single,
    star_one, Matrix.single_mul_mul_single, smul_eq_mul]
  rw [Finset.sum_eq_single i (fun x _ hx ↦ by simp [hx]) (by simp),
    Finset.sum_comm,
    Finset.sum_eq_single j (fun x _ hx ↦ by simp [hx]) (by simp)]
  refine Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun e _ ↦ ?_
  rw [show Matrix.single b e (X b e) = X b e • Matrix.single b e (1 : ℂ) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul]
  simp [mul_comm]

/-! ### The length-independent part of the correlator -/

/-- The length-independent part of the connected correlator of observables
`X` and `Y` on blocks of `L` sites, at `t` unobserved sites between the blocks:
`Tr E_X((E_A - P)^t (E_Y ρ))`, with `P = fixedPointProj ρ`, `P(Z) = (Tr Z / Tr ρ) ρ`.
In the gauge `E_A = |ρ⟩⟨1| + R` of arXiv:2307.01696, eq. (5), with `Tr ρ = 1`,
`P` is the leading term `|R_1⟩⟨L_1|` of the transfer matrix in the Supplemental
Material, proof of Lemma 2.

This is the term that remains of the connected correlator `Δ` of
arXiv:2307.01696, Supplemental Material, proof of Lemma 2, once the long arc
`E_1^{N-s-1}` is replaced by its leading term `|R_1⟩⟨L_1|`; the source writes
it as `∑_{i ≥ 2} λ_i^{s-1} ⟨L_1|E_O|R_i⟩⟨L_i|E_{O'}|R_1⟩`. -/
noncomputable def limitCorrelator (A : MPSTensor d D)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : Matrix.trace ρ ≠ 0) (L : ℕ)
    (X Y : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) (t : ℕ) : ℂ :=
  Matrix.trace (physicalObservableTransfer A L X
    (((Kraus.transferMap A - fixedPointProj ρ hρ) ^ t)
      (physicalObservableTransfer A L Y ρ)))

/-- For an eigenvector `R` of the transfer map with eigenvalue `λ ≠ 1`, there
are observables on `L` sites whose length-independent correlator is exactly
`λ^t`, provided the products of `L` matrices of `A` span the matrix algebra.

This is the choice of `O, O'` in arXiv:2307.01696, Supplemental Material, proof
of Lemma 2, which imposes `⟨L_1|E_O|R_i⟩ = ⟨L_i|E_{O'}|R_1⟩ = 0` for `i > 2`
and `⟨L_1|E_O|R_2⟩⟨L_2|E_{O'}|R_1⟩ = 1`, here with `E_{O'} = |R⟩⟨1|` and
`E_O` a rank-one map with trace functional dual to `R`. The source's condition
`⟨L_i|E_O|R_i⟩ = 0`, which makes the one-point functions vanish, is not part of
this statement. The observables need not be Hermitian. -/
theorem exists_limitCorrelator_eq_pow {A : MPSTensor d D} {L : ℕ}
    (hL : Kraus.IsNBlkInjective A L) (hA : ∑ i, (A i)ᴴ * A i = 1)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : Matrix.trace ρ = 1)
    {R : Matrix (Fin D) (Fin D) ℂ} {lam : ℂ} (hR : R ≠ 0)
    (hRlam : Kraus.transferMap A R = lam • R) (hlam : lam ≠ 1) :
    ∃ X Y : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ,
      ∀ t : ℕ, limitCorrelator A ρ (by rw [hρ]; exact one_ne_zero) L X Y t = lam ^ t := by
  classical
  have htr : Matrix.trace ρ ≠ 0 := by rw [hρ]; exact one_ne_zero
  have hP : ∀ Z, fixedPointProj ρ htr Z = Matrix.trace Z • ρ := fun Z ↦ by
    simp [fixedPointProj, hρ]
  have htrR : Matrix.trace R = 0 := by
    have h : Matrix.trace (Kraus.transferMap A R) = Matrix.trace R :=
      Kraus.isTracePreservingMap_mapLM_of_isTP A hA R
    rw [hRlam, Matrix.trace_smul, smul_eq_mul] at h
    have : (lam - 1) * Matrix.trace R = 0 := by rw [sub_mul, h, one_mul, sub_self]
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hlam)
  have hpow : ∀ t : ℕ, ((Kraus.transferMap A - fixedPointProj ρ htr) ^ t) R = lam ^ t • R := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply, hRlam,
        hP, htrR, zero_smul, sub_zero, smul_smul, pow_succ', mul_comm lam]
  obtain ⟨i, j, hij⟩ : ∃ i j, R i j ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hR (Matrix.ext h)
  let φ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun Z ↦ Z i j / R i j
      map_add' := fun Z W ↦ by simp [add_div]
      map_smul' := fun c Z ↦ by simp [mul_div_assoc] }
  obtain ⟨X, hX⟩ := exists_physicalObservableTransfer_eq hL (LinearMap.smulRight φ ρ)
  obtain ⟨Y, hY⟩ := exists_physicalObservableTransfer_eq hL
    (LinearMap.smulRight (Matrix.traceLinearMap (Fin D) ℂ ℂ) R)
  refine ⟨X, Y, fun t ↦ ?_⟩
  simp only [limitCorrelator, hX, hY, Matrix.traceLinearMap_apply, hρ, one_smul, hpow,
    LinearMap.smulRight_apply, map_smul, Matrix.trace_smul, smul_eq_mul]
  simp [φ, hij]

end MPSTensor
