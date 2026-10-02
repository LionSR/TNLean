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
lemma exists_physicalObservableTransfer_eq {A : MPSTensor d D} {L : ℕ}
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

/-- The connected fixed-point contraction of physical observables on independent
finite blocks, with `n` unobserved sites between them. The inner insertion is
centered so that the formula includes adjacent blocks (`n = 0`).

Reference: arXiv:2011.12127, Section II.B.3, lines 433–441. In a trace-preserving
gauge with normalized fixed state, this equals the two-point expectation minus
the product of the one-point expectations. -/
noncomputable def physicalConnectedCorrelator (A : MPSTensor d D)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : Matrix.trace ρ ≠ 0) (L₁ L₂ : ℕ)
    (X : Matrix (Cfg d L₁) (Cfg d L₁) ℂ)
    (Y : Matrix (Cfg d L₂) (Cfg d L₂) ℂ) (n : ℕ) : ℂ :=
  Matrix.trace (physicalObservableTransfer A L₁ X
    (((Kraus.transferMap A - fixedPointProj ρ hρ) ^ n)
      (physicalObservableTransfer A L₂ Y ρ -
        fixedPointProj ρ hρ (physicalObservableTransfer A L₂ Y ρ))))

/-- The length-independent connected correlator of two observables supported on
blocks of the same length, including adjacent blocks.

This specializes the connected fixed-point contraction to the equal-support
observables of arXiv:2307.01696, Supplemental Material, proof of Lemma 2. -/
noncomputable def limitCorrelator (A : MPSTensor d D)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : Matrix.trace ρ ≠ 0) (L : ℕ)
    (X Y : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) (t : ℕ) : ℂ :=
  physicalConnectedCorrelator A ρ hρ L L X Y t

/-- Centering the input removes the fixed-point component of every power,
including the zeroth power. This is the transfer-map reduction in
arXiv:2011.12127, Section II.B.3, lines 433–441. -/
private theorem compl_pow_apply_centered
    (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (htr : Matrix.trace ρ ≠ 0)
    (hTP : IsTracePreservingMap E) (hFix : E ρ = ρ)
    (Z : Matrix (Fin D) (Fin D) ℂ) (n : ℕ) :
    ((E - fixedPointProj ρ htr) ^ n) (Z - fixedPointProj ρ htr Z) =
      (E ^ n) Z - fixedPointProj ρ htr Z := by
  have hEP : E (fixedPointProj ρ htr Z) = fixedPointProj ρ htr Z := by
    simp [fixedPointProj, hFix]
  have hPE : ∀ k : ℕ, fixedPointProj ρ htr ((E ^ k) Z) = fixedPointProj ρ htr Z := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      simpa [pow_succ', Module.End.mul_apply, fixedPointProj, hTP ((E ^ k) Z)] using ih
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    simp only [LinearMap.sub_apply, map_sub, hEP, hPE n, fixedPointProj_idempotent,
      sub_self, sub_zero, pow_succ', Module.End.mul_apply]

/-- The centered physical contraction equals the two-point expectation minus
the product of the one-point expectations, for every separation.
Reference: arXiv:2011.12127, Section II.B.3, lines 433–441. -/
theorem physicalConnectedCorrelator_eq_twoPoint_sub
    (A : MPSTensor d D) (ρ : Matrix (Fin D) (Fin D) ℂ)
    (htr : Matrix.trace ρ ≠ 0) (hTr : Matrix.trace ρ = 1)
    (hTP : ∑ i, (A i)ᴴ * A i = 1) (hFix : Kraus.transferMap A ρ = ρ)
    (L₁ L₂ : ℕ) (X : Matrix (Cfg d L₁) (Cfg d L₁) ℂ)
    (Y : Matrix (Cfg d L₂) (Cfg d L₂) ℂ) (n : ℕ) :
    physicalConnectedCorrelator A ρ htr L₁ L₂ X Y n =
      Matrix.trace (physicalObservableTransfer A L₁ X
        (((Kraus.transferMap A) ^ n) (physicalObservableTransfer A L₂ Y ρ))) -
      Matrix.trace (physicalObservableTransfer A L₁ X ρ) *
        Matrix.trace (physicalObservableTransfer A L₂ Y ρ) := by
  rw [physicalConnectedCorrelator, compl_pow_apply_centered _ _ htr
    (Kraus.isTracePreservingMap_mapLM_of_isTP A hTP) hFix]
  simp [map_sub, fixedPointProj, hTr, map_smul, Matrix.trace_smul, mul_comm]

/-- At positive separation the complementary transfer power already removes
the disconnected contribution, as in arXiv:2307.01696, Supplemental Material,
proof of Lemma 2. -/
theorem physicalConnectedCorrelator_eq_compl_pow_of_pos
    (A : MPSTensor d D) (ρ : Matrix (Fin D) (Fin D) ℂ)
    (htr : Matrix.trace ρ ≠ 0) (hTP : ∑ i, (A i)ᴴ * A i = 1)
    (hFix : Kraus.transferMap A ρ = ρ)
    (L₁ L₂ : ℕ) (X : Matrix (Cfg d L₁) (Cfg d L₁) ℂ)
    (Y : Matrix (Cfg d L₂) (Cfg d L₂) ℂ) {n : ℕ} (hn : 1 ≤ n) :
    physicalConnectedCorrelator A ρ htr L₁ L₂ X Y n =
      Matrix.trace (physicalObservableTransfer A L₁ X
        (((Kraus.transferMap A - fixedPointProj ρ htr) ^ n)
          (physicalObservableTransfer A L₂ Y ρ))) := by
  rw [physicalConnectedCorrelator, compl_pow_apply_centered _ _ htr
    (Kraus.isTracePreservingMap_mapLM_of_isTP A hTP) hFix,
    pow_eq_fixedPointProj_add_compl_pow _ htr
      (Kraus.isTracePreservingMap_mapLM_of_isTP A hTP) hFix hn]
  simp only [LinearMap.add_apply, add_sub_cancel_left]

/-- The equal-support limit correlator has the uncentered complementary-power
formula at positive separation, as in arXiv:2307.01696, Supplemental Material,
proof of Lemma 2. -/
theorem limitCorrelator_eq_compl_pow_of_pos
    (A : MPSTensor d D) (ρ : Matrix (Fin D) (Fin D) ℂ)
    (htr : Matrix.trace ρ ≠ 0) (hTP : ∑ i, (A i)ᴴ * A i = 1)
    (hFix : Kraus.transferMap A ρ = ρ) (L : ℕ)
    (X Y : Matrix (Cfg d L) (Cfg d L) ℂ) {n : ℕ} (hn : 1 ≤ n) :
    limitCorrelator A ρ htr L X Y n =
      Matrix.trace (physicalObservableTransfer A L X
        (((Kraus.transferMap A - fixedPointProj ρ htr) ^ n)
          (physicalObservableTransfer A L Y ρ))) :=
  physicalConnectedCorrelator_eq_compl_pow_of_pos A ρ htr hTP hFix L L X Y hn

/-- For an eigenvector `R` of the transfer map with eigenvalue `λ ≠ 1`, there
are observables on `L` sites whose length-independent correlator is exactly
`λ^t`, provided the products of `L` matrices of `A` span the matrix algebra.

This is the choice of `O, O'` in arXiv:2307.01696, Supplemental Material, proof
of Lemma 2, which imposes `⟨L_1|E_O|R_i⟩ = ⟨L_i|E_{O'}|R_1⟩ = 0` for `i > 2`
and `⟨L_1|E_O|R_2⟩⟨L_2|E_{O'}|R_1⟩ = 1`, here with `E_{O'} = |R⟩⟨1|` and
`E_O` a rank-one map with trace functional dual to `R`. The source's condition
`⟨L_i|E_O|R_i⟩ = 0`, which makes the one-point functions vanish, is not part of
this statement. The observables need not be Hermitian. -/
lemma exists_limitCorrelator_eq_pow {A : MPSTensor d D} {L : ℕ}
    (hL : Kraus.IsNBlkInjective A L) (hA : ∑ i, (A i)ᴴ * A i = 1)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : Matrix.trace ρ = 1)
    {R : Matrix (Fin D) (Fin D) ℂ} {lam : ℂ} (hR : R ≠ 0)
    (hRlam : Kraus.transferMap A R = lam • R) (hlam : lam ≠ 1) :
    ∃ X Y : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ,
      ∀ (htr : Matrix.trace ρ ≠ 0) (t : ℕ), limitCorrelator A ρ htr L X Y t = lam ^ t := by
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
  refine ⟨X, Y, fun _ t ↦ ?_⟩
  simp only [limitCorrelator, physicalConnectedCorrelator, hX, hY,
    Matrix.traceLinearMap_apply, hρ, one_smul, LinearMap.smulRight_apply, hP, htrR,
    zero_smul, sub_zero, hpow, map_smul, Matrix.trace_smul, smul_eq_mul]
  simp [φ, hij]

end MPSTensor
