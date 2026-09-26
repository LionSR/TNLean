/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Vandermonde
import TNLean.MPS.RFP.ZeroCorrelationLength

/-!
# Ingredients of the decaying-correlation estimate

The lower bound on the preparation depth of a normal matrix product state
(arXiv:2307.01696, Theorem 1) rests on a correlation estimate, Lemma 2 of the
Supplemental Material ("Proof of Theorem 1"): suitable local observables have
a connected correlation of size at least `c e^{-(s-1)/ξ}` at separation `s`.
This file proves the ingredients of that estimate which do not depend on the
finite-size trace formula or on the peripheral spectral expansion.

* `exists_physicalObservableTransfer_eq`: when the words of length `L` span
  the matrix algebra, every linear map on virtual matrices is the inserted
  transfer map `E_O` of an observable `O` on `L` sites. This is the source's
  step "we can always choose `O` such that `E_O = |A⟩⟨B|`".
* `exists_limitCorrelator_eq_pow`: for an eigenvector `R` of the transfer map
  with eigenvalue `λ ≠ 1`, suitable observables make the length-independent
  part of the correlator equal to `λ^t`.
* `exists_window_le_norm_sum_mul_pow`: a nonzero exponential sum with distinct
  unimodular frequencies is bounded below, uniformly in `t`, at one of any `K`
  consecutive integers.
* `norm_inner_mul_norm_sub_le`: two unit vectors with overlap bounded below
  give close expectations to an observable with small variances in both.

The chapter entries are `lem:ldp_observable_transfer_surjective`,
`lem:ldp_limit_correlator_eigenvalue`, `lem:ldp_vandermonde_window`, and
`lem:ldp_expectation_overlap`.
-/

open scoped Matrix BigOperators InnerProductSpace

namespace MPSTensor

variable {d D : ℕ}

/-! ### Inserted transfer maps of observables -/

/-- The inserted transfer map `O ↦ E_O` as a linear map in the observable.

This is the map `E_Q = ∑_{i,j} ⟨i|Q|j⟩ (A^i)^* ⊗ A^j` of arXiv:2307.01696,
Supplemental Material, proof of Lemma 2, written for observables on `L` sites
and acting on virtual matrices. -/
noncomputable def physicalObservableTransferₗ (A : MPSTensor d D) (L : ℕ) :
    Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ →ₗ[ℂ]
      (Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) where
  toFun O := physicalObservableTransfer A L O
  map_add' O₁ O₂ := by
    simp only [physicalObservableTransfer, Matrix.add_apply, add_smul,
      Finset.sum_add_distrib]
  map_smul' c O := by
    simp only [physicalObservableTransfer, Matrix.smul_apply, smul_eq_mul, mul_smul,
      Finset.smul_sum, RingHom.id_apply]

@[simp] theorem physicalObservableTransferₗ_apply (A : MPSTensor d D) (L : ℕ)
    (O : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    physicalObservableTransferₗ A L O = physicalObservableTransfer A L O := rfl

/-- The inserted transfer map of the product observable built from two
coefficient families is a two-sided multiplication. -/
theorem physicalObservableTransfer_coeff_mul (A : MPSTensor d D) (L : ℕ)
    (c e : (Fin L → Fin d) → ℂ) (X : Matrix (Fin D) (Fin D) ℂ) :
    physicalObservableTransfer A L (fun τ σ ↦ c σ * starRingEnd ℂ (e τ)) X =
      (∑ σ : Fin L → Fin d, c σ • Kraus.evalWord A (List.ofFn σ)) * X *
        (∑ τ : Fin L → Fin d, e τ • Kraus.evalWord A (List.ofFn τ))ᴴ := by
  simp only [physicalObservableTransfer, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
  simp only [mul_assoc, Matrix.sum_mul, Algebra.smul_mul_assoc,
    Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, RCLike.star_def,
    Matrix.mul_sum, Algebra.mul_smul_comm, Finset.smul_sum, smul_smul, mul_comm]
  rw [Finset.sum_comm]

/-- Observables on `L` sites realize every linear map on virtual matrices as an
inserted transfer map, provided the products of `L` matrices of `A` span the
full matrix algebra.

This is the step "since the tensor `A` is injective, we can always choose `O`
such that the corresponding transfer matrix `E_O = |A⟩⟨B|` for arbitrary
`A, B`" in arXiv:2307.01696, Supplemental Material, proof of Lemma 2, stated
for every linear map and for the blocked length `L` at which a normal tensor
becomes injective. -/
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

/-- The rank-one map `P(Z) = Tr(Z) ρ` onto the right fixed point.

In the gauge `E_A = |ρ⟩⟨1| + R` of arXiv:2307.01696, eq. (5), this is the
leading term `|R_1⟩⟨L_1|` of the transfer matrix in the Supplemental Material,
proof of Lemma 2. -/
noncomputable def traceProjection (ρ : Matrix (Fin D) (Fin D) ℂ) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
  LinearMap.smulRight (Matrix.traceLinearMap (Fin D) ℂ ℂ) ρ

@[simp] theorem traceProjection_apply (ρ Z : Matrix (Fin D) (Fin D) ℂ) :
    traceProjection ρ Z = Matrix.trace Z • ρ := rfl

/-- The length-independent part of the connected correlator of observables
`X` and `Y` on blocks of `L` sites, at `t` unobserved sites between the blocks:
`Tr E_X((E_A - P)^t (E_Y ρ))`.

This is the term that remains of the connected correlator `Δ` of
arXiv:2307.01696, Supplemental Material, proof of Lemma 2, once the long arc
`E_1^{N-s-1}` is replaced by its leading term `|R_1⟩⟨L_1|`; the source writes
it as `∑_{i ≥ 2} λ_i^{s-1} ⟨L_1|E_O|R_i⟩⟨L_i|E_{O'}|R_1⟩`. -/
noncomputable def limitCorrelator (A : MPSTensor d D)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (L : ℕ)
    (X Y : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) (t : ℕ) : ℂ :=
  Matrix.trace (physicalObservableTransfer A L X
    (((Kraus.transferMap A - traceProjection ρ) ^ t)
      (physicalObservableTransfer A L Y ρ)))

/-- A transfer map of a tensor with `∑ᵢ (A^i)† A^i = 1` preserves the trace.

This is the left fixed point `⟨L_1| = ⟨1|` of arXiv:2307.01696, eq. (5). -/
theorem trace_transferMap_of_sum_conjTranspose_mul_self {A : MPSTensor d D}
    (hA : ∑ i, (A i)ᴴ * A i = 1) (Z : Matrix (Fin D) (Fin D) ℂ) :
    Matrix.trace (Kraus.transferMap A Z) = Matrix.trace Z := by
  rw [Kraus.transferMap_apply, Matrix.trace_sum]
  calc ∑ i, Matrix.trace (A i * Z * (A i)ᴴ)
      = ∑ i, Matrix.trace ((A i)ᴴ * A i * Z) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
    _ = Matrix.trace ((∑ i, (A i)ᴴ * A i) * Z) := by
        rw [Finset.sum_mul, Matrix.trace_sum]
    _ = Matrix.trace Z := by rw [hA, Matrix.one_mul]

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
      ∀ t : ℕ, limitCorrelator A ρ L X Y t = lam ^ t := by
  classical
  have htrR : Matrix.trace R = 0 := by
    have h := trace_transferMap_of_sum_conjTranspose_mul_self hA R
    rw [hRlam, Matrix.trace_smul, smul_eq_mul] at h
    have : (lam - 1) * Matrix.trace R = 0 := by rw [sub_mul, h, one_mul, sub_self]
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hlam)
  have hpow : ∀ t : ℕ, ((Kraus.transferMap A - traceProjection ρ) ^ t) R = lam ^ t • R := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply, hRlam,
        traceProjection_apply, htrR, zero_smul, sub_zero, smul_smul, pow_succ', mul_comm lam]
  obtain ⟨i, j, hij⟩ : ∃ i j, R i j ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hR (Matrix.ext h)
  let φ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun Z ↦ Z i j / R i j
      map_add' := fun Z W ↦ by simp [add_div]
      map_smul' := fun c Z ↦ by simp [mul_div_assoc] }
  obtain ⟨X, hX⟩ := exists_physicalObservableTransfer_eq hL (LinearMap.smulRight φ ρ)
  obtain ⟨Y, hY⟩ := exists_physicalObservableTransfer_eq hL (traceProjection R)
  refine ⟨X, Y, fun t ↦ ?_⟩
  simp only [limitCorrelator, hX, hY, traceProjection_apply, hρ, one_smul, hpow,
    LinearMap.smulRight_apply, map_smul, Matrix.trace_smul, smul_eq_mul]
  simp [φ, hij]

/-! ### Exponential sums on windows of consecutive integers -/

/-- A nonzero exponential sum `∑ⱼ aⱼ μⱼ^t` with distinct unimodular frequencies
is bounded below, uniformly in `t`, at one of any `K` consecutive integers.

This is the Vandermonde estimate that replaces, for complex subleading
eigenvalues, the final step "the second and third [conditions] ensure
(auxform2) for sufficiently large `N`" of arXiv:2307.01696, Supplemental
Material, proof of Lemma 2: the leading part of the correlator is a sum over
the eigenvalues of modulus `|λ₂|`, which can vanish at individual separations. -/
theorem exists_window_le_norm_sum_mul_pow {K : ℕ} {μ : Fin K → ℂ}
    (hμ : Function.Injective μ) (hnorm : ∀ j, ‖μ j‖ = 1)
    {a : Fin K → ℂ} (ha : a ≠ 0) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ t : ℕ, ∃ u : Fin K,
      c₀ ≤ ‖∑ j, a j * μ j ^ (t + (u : ℕ))‖ := by
  classical
  let W : (Fin K → ℂ) →ₗ[ℂ] (Fin K → ℂ) :=
    { toFun := fun v u ↦ ∑ j, v j * μ j ^ (u : ℕ)
      map_add' := fun v w ↦ by
        funext u
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c v ↦ by
        funext u
        simp [Finset.mul_sum, mul_assoc] }
  have hW : Function.Injective W := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hμ
      (fun i ↦ congrFun hv i)
  obtain ⟨C, hCpos, hC⟩ := W.injective_iff_antilipschitz.mp hW
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  refine ⟨‖a‖ / ((C : ℝ) + 1), div_pos hapos (by positivity), ?_⟩
  intro t
  let b : Fin K → ℂ := fun j ↦ a j * μ j ^ t
  have hb : ‖a‖ ≤ ‖b‖ := by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg b)).mpr fun j ↦ ?_
    have : ‖a j‖ = ‖b j‖ := by simp [b, norm_pow, hnorm]
    rw [this]
    exact norm_le_pi_norm b j
  have hWb : ‖b‖ ≤ C * ‖W b‖ := by
    have := hC.le_mul_dist b 0
    simpa [dist_eq_norm] using this
  have hWb' : ‖a‖ / ((C : ℝ) + 1) ≤ ‖W b‖ := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg (W b), NNReal.coe_nonneg C]
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  have hlt : ‖W b‖ < ‖a‖ / ((C : ℝ) + 1) := by
    refine (pi_norm_lt_iff (div_pos hapos (by positivity))).mpr fun u ↦ ?_
    have hu := hcon u
    have : W b u = ∑ j, a j * μ j ^ (t + (u : ℕ)) := by
      simp [W, b, pow_add, mul_assoc]
    rw [this]
    exact hu
  exact absurd hWb' (not_le.mpr hlt)

/-! ### Expectations in two overlapping states -/

/-- For a Hermitian operator `T` and unit vectors `φ, ψ`,
`|⟨φ|ψ⟩| |⟨T⟩_φ - ⟨T⟩_ψ| ≤ ‖(T - ⟨T⟩_φ)φ‖ + ‖(T - ⟨T⟩_ψ)ψ‖`.

This is the estimate used to transfer expectations from a matrix product state
to a state of overlap at least `1/2` in the proof of arXiv:2307.01696,
Theorem 1 (Supplemental Material, "Proof of Theorem 1"); the source bounds
the same difference through the trace distance, eq. (auxdp) and
eq. (eq:tilde_distance). -/
theorem norm_inner_mul_norm_sub_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) {φ ψ : E}
    (hφ : ‖φ‖ = 1) (hψ : ‖ψ‖ = 1) :
    ‖⟪φ, ψ⟫_ℂ‖ * ‖⟪φ, T φ⟫_ℂ - ⟪ψ, T ψ⟫_ℂ‖ ≤
      ‖T φ - ⟪φ, T φ⟫_ℂ • φ‖ + ‖T ψ - ⟪ψ, T ψ⟫_ℂ • ψ‖ := by
  set a := ⟪φ, T φ⟫_ℂ
  set b := ⟪ψ, T ψ⟫_ℂ
  have ha : starRingEnd ℂ a = a := by
    simp only [a, ← hT φ φ]
    exact hT.conj_inner_sym φ φ
  have hid : (a - b) * ⟪φ, ψ⟫_ℂ =
      ⟪φ, T ψ - b • ψ⟫_ℂ - ⟪T φ - a • φ, ψ⟫_ℂ := by
    rw [inner_sub_right, inner_sub_left, inner_smul_right, inner_smul_left, ha,
      hT φ ψ]
    ring
  calc ‖⟪φ, ψ⟫_ℂ‖ * ‖a - b‖ = ‖(a - b) * ⟪φ, ψ⟫_ℂ‖ := by
        rw [norm_mul, mul_comm]
    _ = ‖⟪φ, T ψ - b • ψ⟫_ℂ - ⟪T φ - a • φ, ψ⟫_ℂ‖ := by rw [hid]
    _ ≤ ‖⟪φ, T ψ - b • ψ⟫_ℂ‖ + ‖⟪T φ - a • φ, ψ⟫_ℂ‖ := norm_sub_le _ _
    _ ≤ ‖φ‖ * ‖T ψ - b • ψ‖ + ‖T φ - a • φ‖ * ‖ψ‖ :=
        add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ = ‖T φ - a • φ‖ + ‖T ψ - b • ψ‖ := by rw [hφ, hψ]; ring

end MPSTensor
