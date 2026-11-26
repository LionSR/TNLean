/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.Arbitrary.Proportional
import QICLean.Algebra.Word.OrderedProduct
import TNLean.MPS.FundamentalTheorem.Periodic.RepeatedBlocks
import TNLean.MPS.CanonicalForm.Periodic.SectorNormalization

/-!
# Weighted states and dependent states

For a tensor `A` and a square matrix `M`, the tensor `A ⊗ M` has letters `A^i ⊗ M`, so that
`tr (A ⊗ M)^w = tr A^w · tr M^|w|`. This reduces relations between the states of two tensors to the
fundamental theorem for equal states:

* `tr V^N V_N(A) = tr U^N V_N(B)` for all large `N` exactly when `A ⊗ V` and `B ⊗ U` have the same
  states, exactly when the factors of `A` weighted by the nonzero eigenvalues of `V` correspond to
  the factors of `B` weighted by those of `U`;
* with `V = 𝔼_{B,B}` and `U = 𝔼_{B,A}`, the transfer matrices, this identity at length `N` says
  that `V_N(A)` and `V_N(B)` are linearly dependent.

`U = V = 1` is the fundamental theorem itself, and `U = (λ)`, `V = 1` the case of constants `λ ^ N`.

## Main results

* `MPSTensor.tfae_weightedStates`: equivalent forms of the weighted identity.
* `MPSTensor.forall_trace_pow_mul_mpv_eq_iff_exists_equiv_isGaugeRelated`.
* `MPSTensor.eventually_mpv_eq_pow_mul_iff_exists_equiv_isGaugeRelated_smul`.
* `MPSTensor.tfae_statesDependent`: equivalent forms of linear dependence of the states.
* `MPSTensor.exists_mpv_eq_mul_iff`, `MPSTensor.eq_trace_mixedTransfer_div`: the constant.
* `MPSTensor.forall_exists_isGaugeRelated_smul_of_eventually_statesDependentAt`.
* `MPSTensor.fundamentalTheorem_irreducibleForm_of_statesDependent`: the classical proportional
  theorems from dependent states.
-/

open Filter

section WeightedStates

open scoped Matrix Kronecker

namespace MPSTensor

variable {d : ℕ}

/-! ### The tensor `A ⊗ M` -/

/-- The tensor `A ⊗ M`, with letters `A^i ⊗ M`. -/
noncomputable def weightTensor {D m : ℕ} (A : MPSTensor d D) (M : Matrix (Fin m) (Fin m) ℂ) :
    MPSTensor d (D * m) :=
  fun i => Matrix.reindex finProdFinEquiv finProdFinEquiv (A i ⊗ₖ M)

/-- The mixed transfer matrix `𝔼_{X,Y} = ∑_i conj(X^i) ⊗ Y^i`. -/
noncomputable def mixedTransfer {D₁ D₂ : ℕ} (X : MPSTensor d D₁) (Y : MPSTensor d D₂) :
    Matrix (Fin (D₁ * D₂)) (Fin (D₁ * D₂)) ℂ :=
  ∑ i, Matrix.reindex finProdFinEquiv finProdFinEquiv ((X i).map star ⊗ₖ Y i)

/-- The nonzero eigenvalues of `M`, with algebraic multiplicity. -/
noncomputable def nonzeroSpectrum {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) : Multiset ℂ :=
  M.charpoly.roots.filter (· ≠ 0)

/-- The states of `A` and `B` are linearly dependent at length `N`. -/
def StatesDependentAt {D₁ D₂ : ℕ} (A : MPSTensor d D₁) (B : MPSTensor d D₂) (N : ℕ) : Prop :=
  ∃ a b : ℂ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ σ : Fin N → Fin d, a * mpv A σ = b * mpv B σ

private theorem trace_reindex {n k : ℕ} (e : Fin n × Fin k ≃ Fin (n * k))
    (M : Matrix (Fin n × Fin k) (Fin n × Fin k) ℂ) :
    Matrix.trace (Matrix.reindex e e M) = Matrix.trace M := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp e.symm fun x => M x x

/-- Word evaluation in `A ⊗ M`. -/
theorem evalWord_weightTensor {D m : ℕ} (A : MPSTensor d D) (M : Matrix (Fin m) (Fin m) ℂ)
    (w : List (Fin d)) :
    Kraus.evalWord (weightTensor A M) w =
      Matrix.reindex finProdFinEquiv finProdFinEquiv (Kraus.evalWord A w ⊗ₖ (M ^ w.length)) := by
  induction w with
  | nil => simp [Kraus.evalWord]
  | cons i w ih =>
      simp only [Kraus.evalWord_cons, List.length_cons, weightTensor]
      rw [ih, ← Matrix.coe_reindexRingEquiv ℂ finProdFinEquiv, ← map_mul,
        ← Matrix.mul_kronecker_mul, pow_succ']

/-- The word traces of `A ⊗ M`: `tr (A ⊗ M)^w = tr A^w · tr M^|w|`. -/
theorem trace_evalWord_weightTensor {m D : ℕ} (A : MPSTensor d D)
    (M : Matrix (Fin m) (Fin m) ℂ) (w : List (Fin d)) :
    Matrix.trace (Kraus.evalWord (weightTensor A M) w) =
      Matrix.trace (Kraus.evalWord A w) * Matrix.trace (M ^ w.length) := by
  rw [evalWord_weightTensor, trace_reindex, Matrix.trace_kronecker]

/-- The states of `A ⊗ M`: `V_N(A ⊗ M) = tr M^N · V_N(A)`. -/
theorem mpv_weightTensor {m D : ℕ} (A : MPSTensor d D) (M : Matrix (Fin m) (Fin m) ℂ) {N : ℕ}
    (σ : Fin N → Fin d) :
    mpv (weightTensor A M) σ = Matrix.trace (M ^ N) * mpv A σ := by
  simp only [mpv_eq, coeff_eq]
  rw [trace_evalWord_weightTensor, List.length_ofFn, mul_comm]

/-- The trace powers of `M` at positive exponents are the power sums of its nonzero eigenvalues. -/
theorem trace_pow_eq_sum_nonzeroSpectrum {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) {k : ℕ}
    (hk : 0 < k) :
    Matrix.trace (M ^ k) = ((nonzeroSpectrum M).map (· ^ k)).sum := by
  rw [trace_pow_eq_sum_roots_charpoly, nonzeroSpectrum]
  conv_lhs => rw [← Multiset.filter_add_not (· ≠ 0) M.charpoly.roots]
  rw [Multiset.map_add, Multiset.sum_add]
  have h0 : ((M.charpoly.roots.filter fun a => ¬ a ≠ 0).map (· ^ k)).sum = 0 := by
    refine Multiset.sum_eq_zero fun x hx => ?_
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hx
    have : a = 0 := by simpa using (Multiset.mem_filter.mp ha).2
    simp [this, hk.ne']
  rw [h0, add_zero]

private theorem evalWord_sum_pow {n : ℕ} (T : Fin d → Matrix (Fin n) (Fin n) ℂ) (N : ℕ) :
    (∑ i, T i) ^ N = ∑ σ : Fin N → Fin d, Kraus.evalWord T (List.ofFn σ) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [pow_succ', ih, Finset.sum_mul_sum, Finset.sum_comm]
      rw [← Fintype.sum_fin_succ_pi
        (fun i (τ : Fin N → Fin d) => T i * Kraus.evalWord T (List.ofFn τ))]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [List.ofFn_succ, Kraus.evalWord_cons]

private theorem evalWord_mixed {D₁ D₂ : ℕ} (X : MPSTensor d D₁) (Y : MPSTensor d D₂)
    (w : List (Fin d)) :
    Kraus.evalWord (fun i => Matrix.reindex finProdFinEquiv finProdFinEquiv
        ((X i).map star ⊗ₖ Y i)) w =
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        ((Kraus.evalWord X w).map star ⊗ₖ Kraus.evalWord Y w) := by
  induction w with
  | nil => simp [Kraus.evalWord]
  | cons i w ih =>
      have hs : ∀ P Q : Matrix (Fin D₁) (Fin D₁) ℂ, (P * Q).map star = P.map star * Q.map star :=
        fun P Q => by
          ext a b
          simp [Matrix.mul_apply, Matrix.map_apply]
      simp only [Kraus.evalWord_cons]
      rw [ih, ← Matrix.coe_reindexRingEquiv ℂ finProdFinEquiv, ← map_mul,
        ← Matrix.mul_kronecker_mul, hs]

/-- `tr 𝔼_{X,Y}^N = ⟨V_N(X), V_N(Y)⟩`. -/
theorem trace_mixedTransfer_pow {D₁ D₂ : ℕ} (X : MPSTensor d D₁) (Y : MPSTensor d D₂) (N : ℕ) :
    Matrix.trace (mixedTransfer X Y ^ N) = ∑ σ : Fin N → Fin d, star (mpv X σ) * mpv Y σ := by
  rw [mixedTransfer, evalWord_sum_pow, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [evalWord_mixed, trace_reindex, Matrix.trace_kronecker]
  simp only [mpv_eq, coeff_eq, Matrix.trace, Matrix.diag_apply, Matrix.map_apply, star_sum]

/-! ### Weighted states -/

section

variable {DA DB m n : ℕ}

/-- Equal states of `A ⊗ V` and `B ⊗ U` are the identity `tr V^N V_N(A) = tr U^N V_N(B)`. -/
theorem sameMPV₂Pos_weightTensor_iff {A : MPSTensor d DA} {B : MPSTensor d DB}
    {V : Matrix (Fin m) (Fin m) ℂ} {U : Matrix (Fin n) (Fin n) ℂ} :
    SameMPV₂Pos (weightTensor A V) (weightTensor B U) ↔
      ∀ N, 0 < N → ∀ σ : Fin N → Fin d,
        Matrix.trace (V ^ N) * mpv A σ = Matrix.trace (U ^ N) * mpv B σ := by
  simp only [SameMPV₂Pos, mpv_weightTensor]

/-- **Weighted states, equivalent forms.** The identity `tr V^N V_N(A) = tr U^N V_N(B)` for large
`N`, the same for every `N ≥ 1`, equal states of `A ⊗ V` and `B ⊗ U`, and reductions of these two
tensors onto one family of nonzero irreducible tensors, are equivalent. -/
theorem tfae_weightedStates (A : MPSTensor d DA) (B : MPSTensor d DB)
    (V : Matrix (Fin m) (Fin m) ℂ) (U : Matrix (Fin n) (Fin n) ℂ) :
    List.TFAE
      [∀ᶠ N in atTop, ∀ σ : Fin N → Fin d,
          Matrix.trace (V ^ N) * mpv A σ = Matrix.trace (U ^ N) * mpv B σ,
        ∀ N, 0 < N → ∀ σ : Fin N → Fin d,
          Matrix.trace (V ^ N) * mpv A σ = Matrix.trace (U ^ N) * mpv B σ,
        SameMPV₂Pos (weightTensor A V) (weightTensor B U),
        ∃ (r : ℕ) (D : Fin r → ℕ) (C : ∀ k, MPSTensor d (D k)),
          (∀ k, Matrix.IsIrreducibleAction (C k)) ∧ (∀ k, ∃ i, C k i ≠ 0) ∧
            Nonempty (MultiBlockCompression (weightTensor A V) Finset.univ C) ∧
            Nonempty (MultiBlockCompression (weightTensor B U) Finset.univ C)] := by
  tfae_have 1 → 3 := fun h => by
    obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp h
    refine sameMPV₂Pos_of_forall_le_length_trace_evalWord_eq N₁ fun w hw => ?_
    rw [trace_evalWord_weightTensor, trace_evalWord_weightTensor]
    have h1 := hN₁ w.length hw w.get
    simp only [mpv_eq, coeff_eq, List.ofFn_get] at h1
    linear_combination h1
  tfae_have 3 → 2 := sameMPV₂Pos_weightTensor_iff.1
  tfae_have 2 → 1 := fun h => eventually_atTop.2 ⟨1, fun N hN => h N hN⟩
  tfae_have 3 ↔ 4 := sameMPV₂Pos_iff_exists_multiBlockCompression
  tfae_finish

/-- The enumeration `μ` of the nonzero spectrum of `V` has nonzero entries. -/
private theorem ne_zero_of_map_eq_nonzeroSpectrum {K : Type*} [Fintype K] {μ : K → ℂ}
    {V : Matrix (Fin m) (Fin m) ℂ} (hμ : Finset.univ.val.map μ = nonzeroSpectrum V) (k : K) :
    μ k ≠ 0 := by
  have : μ k ∈ nonzeroSpectrum V := by
    rw [← hμ]
    exact Multiset.mem_map_of_mem μ (Finset.mem_univ k)
  exact (Multiset.mem_filter.mp this).2

/-- `tr V^N V_N(A)` as a weighted sum over the factors of `A` and the nonzero eigenvalues of `V`. -/
private theorem trace_pow_mul_mpv_eq_sum {ι K : Type*} [DecidableEq ι] [Fintype K] {D : ι → ℕ}
    {S : Finset ι} {C : ∀ s, MPSTensor d (D s)} {A : MPSTensor d DA}
    (P : MultiBlockCompression A S C) {V : Matrix (Fin m) (Fin m) ℂ} {μ : K → ℂ}
    (hμ : Finset.univ.val.map μ = nonzeroSpectrum V) {N : ℕ} (hN : 0 < N)
    (σ : Fin N → Fin d) :
    Matrix.trace (V ^ N) * mpv A σ =
      ∑ x : {s // s ∈ S} × K, μ x.2 ^ N * mpv (C x.1.1) σ := by
  rw [trace_pow_eq_sum_nonzeroSpectrum V hN, ← hμ, Multiset.map_map,
    mpv_eq_sum_coe_sort_of_multiBlockCompression P hN σ]
  change (∑ k, μ k ^ N) * _ = _
  rw [Finset.sum_mul_sum, Fintype.sum_prod_type, Finset.sum_comm]

/-- **Weighted states, by factors.** The identity holds exactly when the factors of `A` weighted by
the nonzero eigenvalues of `V` correspond to the factors of `B` weighted by those of `U`, up to
gauge. -/
theorem forall_trace_pow_mul_mpv_eq_iff_exists_equiv_isGaugeRelated
    {A : MPSTensor d DA} {B : MPSTensor d DB}
    {V : Matrix (Fin m) (Fin m) ℂ} {U : Matrix (Fin n) (Fin n) ℂ}
    {ι κ K L : Type*} [DecidableEq ι] [DecidableEq κ] [Fintype K] [Fintype L]
    {D : ι → ℕ} {D' : κ → ℕ} {S : Finset ι} {T : Finset κ}
    {C : ∀ s, MPSTensor d (D s)} {C' : ∀ t, MPSTensor d (D' t)}
    (hP : Nonempty (MultiBlockCompression A S C)) (hQ : Nonempty (MultiBlockCompression B T C'))
    (hirr : ∀ s ∈ S, Matrix.IsIrreducibleAction (C s)) (hlet : ∀ s ∈ S, ∃ i, C s i ≠ 0)
    (hirr' : ∀ t ∈ T, Matrix.IsIrreducibleAction (C' t)) (hlet' : ∀ t ∈ T, ∃ i, C' t i ≠ 0)
    {μ : K → ℂ} {ν : L → ℂ} (hμ : Finset.univ.val.map μ = nonzeroSpectrum V)
    (hν : Finset.univ.val.map ν = nonzeroSpectrum U) :
    (∀ N, 0 < N → ∀ σ : Fin N → Fin d,
        Matrix.trace (V ^ N) * mpv A σ = Matrix.trace (U ^ N) * mpv B σ) ↔
      ∃ τ : {s // s ∈ S} × K ≃ {t // t ∈ T} × L, ∀ x,
        IsGaugeRelated (μ x.2 • C x.1.1) (ν (τ x).2 • C' (τ x).1.1) := by
  obtain ⟨P⟩ := hP
  obtain ⟨Q⟩ := hQ
  rw [← forall_sum_pow_mul_mpv_eq_iff_exists_equiv_isGaugeRelated
    (C := fun x : {s // s ∈ S} × K => C x.1.1) (C' := fun y : {t // t ∈ T} × L => C' y.1.1)
    (μ := fun x => μ x.2) (ν := fun y => ν y.2)
    (fun x => hirr _ x.1.2) (fun x => hlet _ x.1.2) (fun y => hirr' _ y.1.2)
    (fun y => hlet' _ y.1.2) (fun x => ne_zero_of_map_eq_nonzeroSpectrum hμ x.2)
    (fun y => ne_zero_of_map_eq_nonzeroSpectrum hν y.2)]
  refine forall₂_congr fun N hN => forall_congr' fun σ => ?_
  rw [trace_pow_mul_mpv_eq_sum P hμ hN σ, trace_pow_mul_mpv_eq_sum Q hν hN σ]

end

/-! ### Dependent states -/

section

variable {DA DB : ℕ}

private theorem star_mul_self_sum_eq_zero_iff {N : ℕ} (f : (Fin N → Fin d) → ℂ) :
    ∑ σ, star (f σ) * f σ = 0 ↔ ∀ σ, f σ = 0 := by
  have hc : ∀ z : ℂ, star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
    rw [Complex.star_def, Complex.conj_mul']
    push_cast
    rfl
  simp only [hc, ← Complex.ofReal_sum, Complex.ofReal_eq_zero]
  rw [Finset.sum_eq_zero_iff_of_nonneg fun σ _ => by positivity]
  simp

/-- Linear dependence at length `N` is the identity
`‖V_N(B)‖² V_N(A) = ⟨V_N(B), V_N(A)⟩ V_N(B)`. -/
theorem statesDependentAt_iff_trace_mixedTransfer (A : MPSTensor d DA) (B : MPSTensor d DB)
    (N : ℕ) :
    StatesDependentAt A B N ↔ ∀ σ : Fin N → Fin d,
      Matrix.trace (mixedTransfer B B ^ N) * mpv A σ =
        Matrix.trace (mixedTransfer B A ^ N) * mpv B σ := by
  simp only [trace_mixedTransfer_pow]
  set nB : ℂ := ∑ σ : Fin N → Fin d, star (mpv B σ) * mpv B σ with hnB
  set ip : ℂ := ∑ σ : Fin N → Fin d, star (mpv B σ) * mpv A σ with hip
  constructor
  · rintro ⟨a, b, hab, h⟩ σ
    by_cases ha : a = 0
    · have hb : b ≠ 0 := by simpa [ha] using hab
      have hB0 : ∀ τ : Fin N → Fin d, mpv B τ = 0 := fun τ => by
        have := h τ
        simpa [ha, hb] using this.symm
      have h1 : nB = 0 := by
        rw [hnB]
        exact Finset.sum_eq_zero fun τ _ => by rw [hB0 τ, mul_zero]
      have h2 : ip = 0 := by
        rw [hip]
        exact Finset.sum_eq_zero fun τ _ => by rw [hB0 τ, star_zero, zero_mul]
      rw [h1, h2, zero_mul, zero_mul]
    · have hsum : a * ip = b * nB := by
        rw [hip, hnB, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun τ _ => ?_
        linear_combination star (mpv B τ) * h τ
      have hσ := h σ
      apply mul_left_cancel₀ ha
      linear_combination nB * hσ - mpv B σ * hsum
  · intro h
    by_cases hn : nB = 0
    · have hB0 := (star_mul_self_sum_eq_zero_iff (fun τ => mpv B τ)).1 hn
      exact ⟨0, 1, Or.inr one_ne_zero, fun σ => by rw [zero_mul, one_mul, hB0 σ]⟩
    · exact ⟨nB, ip, Or.inl hn, h⟩

/-- **Dependent states, equivalent forms.** Linear dependence of the states at all large lengths, at
all positive lengths, and equal states of `A ⊗ 𝔼_{B,B}` and `B ⊗ 𝔼_{B,A}`, are equivalent. -/
theorem tfae_statesDependent (A : MPSTensor d DA) (B : MPSTensor d DB) :
    List.TFAE
      [∀ᶠ N in atTop, StatesDependentAt A B N,
        ∀ N, 0 < N → StatesDependentAt A B N,
        SameMPV₂Pos (weightTensor A (mixedTransfer B B)) (weightTensor B (mixedTransfer B A))] := by
  have h := tfae_weightedStates A B (mixedTransfer B B) (mixedTransfer B A)
  have h13 := h.out 1 3
  have h23 := h.out 2 3
  simp only [← statesDependentAt_iff_trace_mixedTransfer] at h13 h23
  tfae_have 1 ↔ 3 := h13
  tfae_have 2 ↔ 3 := h23
  tfae_finish

/-- **Dependent states, the constant.** There is `c` with `V_N(A) = c V_N(B)` exactly when the two
vectors are dependent and `V_N(B) = 0` forces `V_N(A) = 0`. -/
theorem exists_mpv_eq_mul_iff (A : MPSTensor d DA) (B : MPSTensor d DB) (N : ℕ) :
    (∃ c : ℂ, ∀ σ : Fin N → Fin d, mpv A σ = c * mpv B σ) ↔
      StatesDependentAt A B N ∧
        ((∀ σ : Fin N → Fin d, mpv B σ = 0) → ∀ σ : Fin N → Fin d, mpv A σ = 0) := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨⟨1, c, Or.inl one_ne_zero, fun σ => by rw [one_mul, hc]⟩,
      fun hB σ => by rw [hc, hB, mul_zero]⟩
  · rintro ⟨⟨a, b, hab, h⟩, hz⟩
    by_cases ha : a = 0
    · have hb : b ≠ 0 := by simpa [ha] using hab
      have hB0 : ∀ τ : Fin N → Fin d, mpv B τ = 0 := fun τ => by
        have := h τ
        simpa [ha, hb] using this.symm
      exact ⟨0, fun σ => by rw [hz hB0 σ, zero_mul]⟩
    · refine ⟨b / a, fun σ => ?_⟩
      field_simp
      linear_combination h σ

/-- Where `V_N(B) ≠ 0`, the constant is `tr 𝔼_{B,A}^N / tr 𝔼_{B,B}^N`. -/
theorem eq_trace_mixedTransfer_div {A : MPSTensor d DA} {B : MPSTensor d DB} {N : ℕ} {c : ℂ}
    (h : ∀ σ : Fin N → Fin d, mpv A σ = c * mpv B σ) (hB : ∃ σ : Fin N → Fin d, mpv B σ ≠ 0) :
    c = Matrix.trace (mixedTransfer B A ^ N) / Matrix.trace (mixedTransfer B B ^ N) := by
  have hn : Matrix.trace (mixedTransfer B B ^ N) ≠ 0 := by
    rw [trace_mixedTransfer_pow]
    intro h0
    obtain ⟨σ, hσ⟩ := hB
    exact hσ ((star_mul_self_sum_eq_zero_iff (fun τ => mpv B τ)).1 h0 σ)
  rw [eq_div_iff hn, trace_mixedTransfer_pow, trace_mixedTransfer_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [h σ]
  ring

/-! ### Constants `λ ^ N` and dependent states -/

/-- **Constants of the form `λ ^ N`.** `V_N(A) = λ ^ N V_N(B)` for all large `N`, with `λ ≠ 0`,
exactly when the factors of `A` correspond to those of `B` along a bijection, each gauge related to
`λ` times its partner. -/
theorem eventually_mpv_eq_pow_mul_iff_exists_equiv_isGaugeRelated_smul
    {A : MPSTensor d DA} {B : MPSTensor d DB}
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {D : ι → ℕ} {D' : κ → ℕ} {S : Finset ι}
    {T : Finset κ} {C : ∀ s, MPSTensor d (D s)} {C' : ∀ t, MPSTensor d (D' t)}
    (hP : Nonempty (MultiBlockCompression A S C)) (hQ : Nonempty (MultiBlockCompression B T C'))
    (hirr : ∀ s ∈ S, Matrix.IsIrreducibleAction (C s)) (hlet : ∀ s ∈ S, ∃ i, C s i ≠ 0)
    (hirr' : ∀ t ∈ T, Matrix.IsIrreducibleAction (C' t)) (hlet' : ∀ t ∈ T, ∃ i, C' t i ≠ 0)
    {lam : ℂ} (hlam : lam ≠ 0) :
    (∀ᶠ N in atTop, ∀ σ : Fin N → Fin d, mpv A σ = lam ^ N * mpv B σ) ↔
      ∃ τ : {s // s ∈ S} ≃ {t // t ∈ T}, ∀ s, IsGaugeRelated (C s.1) (lam • C' (τ s).1) := by
  refine ⟨exists_equiv_isGaugeRelated_smul_of_eventually_mpv_eq_pow_mul hP hQ hirr hlet hirr'
    hlet' hlam, ?_⟩
  rintro ⟨τ, hτ⟩
  obtain ⟨P⟩ := hP
  obtain ⟨Q⟩ := hQ
  refine eventually_atTop.2 ⟨1, fun N hN σ => ?_⟩
  have hN' : 0 < N := hN
  rw [mpv_eq_sum_coe_sort_of_multiBlockCompression P hN' σ,
    mpv_eq_sum_coe_sort_of_multiBlockCompression Q hN' σ, Finset.mul_sum,
    ← Equiv.sum_comp τ (fun t => lam ^ N * mpv (C' t.1) σ)]
  refine Finset.sum_congr rfl fun s _ => ?_
  have h1 := (hτ s).trace_evalWord_eq (List.ofFn σ)
  rw [trace_evalWord_smul, List.length_ofFn] at h1
  simpa only [mpv_eq, coeff_eq] using h1

/-- A list of factors that is nonempty gives a nonzero state. -/
private theorem exists_mpv_ne_zero_of_multiBlockCompression {κ : Type*} [DecidableEq κ]
    {D' : κ → ℕ} {T : Finset κ} {C' : ∀ t, MPSTensor d (D' t)} {B : MPSTensor d DB}
    (Q : MultiBlockCompression B T C')
    (hirr' : ∀ t ∈ T, Matrix.IsIrreducibleAction (C' t)) (hlet' : ∀ t ∈ T, ∃ i, C' t i ≠ 0)
    (hT : T.Nonempty) : ∃ (N : ℕ) (σ : Fin N → Fin d), 0 < N ∧ mpv B σ ≠ 0 := by
  by_contra hno
  push Not at hno
  have hE : (∀ N, 0 < N → ∀ σ : Fin N → Fin d,
      ∑ t : {t // t ∈ T}, (1 : ℂ) ^ N * mpv (C' t.1) σ =
        ∑ e : Empty, (1 : ℂ) ^ N * mpv (e.elim : MPSTensor d 0) σ) := by
    intro N hN σ
    simp only [one_pow, one_mul, Finset.univ_eq_empty, Finset.sum_empty]
    rw [← mpv_eq_sum_coe_sort_of_multiBlockCompression Q hN σ]
    exact hno N σ hN
  obtain ⟨τ, -⟩ := (forall_sum_pow_mul_mpv_eq_iff_exists_equiv_isGaugeRelated
    (C := fun t : {t // t ∈ T} => C' t.1) (C' := fun e : Empty => e.elim) (μ := fun _ => 1)
    (ν := fun _ => 1) (fun t => hirr' _ t.2) (fun t => hlet' _ t.2) (fun e => e.elim)
    (fun e => e.elim) (fun _ => one_ne_zero) (fun e => e.elim)).1 hE
  obtain ⟨t, ht⟩ := hT
  exact (τ ⟨t, ht⟩).elim

/-- Given an eigenvalue-enumeration of a matrix with nonzero trace power, the index type is
nonempty. -/
private theorem nonempty_of_trace_pow_ne_zero {m N : ℕ} {V : Matrix (Fin m) (Fin m) ℂ}
    {K : Type*} [Fintype K] {μ : K → ℂ} (hμ : Finset.univ.val.map μ = nonzeroSpectrum V)
    (hN : 0 < N) (h : Matrix.trace (V ^ N) ≠ 0) : Nonempty K := by
  by_contra hK
  rw [not_nonempty_iff] at hK
  apply h
  rw [trace_pow_eq_sum_nonzeroSpectrum V hN, ← hμ]
  simp

/-- Every multiset of complex numbers is enumerated by a finite type. -/
private theorem exists_enumeration (s : Multiset ℂ) :
    ∃ (K : Type) (_ : Fintype K) (μ : K → ℂ), Finset.univ.val.map μ = s := by
  refine ⟨Fin s.toList.length, inferInstance, s.toList.get, ?_⟩
  rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]

/-- **Dependent states, classes of factors.** If the states of `A` and `B` are linearly dependent at
all large lengths and both tensors have nonzero factors, then every factor of either tensor is gauge
related to a nonzero multiple of a factor of the other. -/
theorem forall_exists_isGaugeRelated_smul_of_eventually_statesDependentAt
    {A : MPSTensor d DA} {B : MPSTensor d DB}
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {D : ι → ℕ} {D' : κ → ℕ} {S : Finset ι}
    {T : Finset κ} {C : ∀ s, MPSTensor d (D s)} {C' : ∀ t, MPSTensor d (D' t)}
    (hP : Nonempty (MultiBlockCompression A S C)) (hQ : Nonempty (MultiBlockCompression B T C'))
    (hirr : ∀ s ∈ S, Matrix.IsIrreducibleAction (C s)) (hlet : ∀ s ∈ S, ∃ i, C s i ≠ 0)
    (hirr' : ∀ t ∈ T, Matrix.IsIrreducibleAction (C' t)) (hlet' : ∀ t ∈ T, ∃ i, C' t i ≠ 0)
    (hS : S.Nonempty) (hT : T.Nonempty)
    (h : ∀ᶠ N in atTop, StatesDependentAt A B N) :
    (∀ s ∈ S, ∃ t ∈ T, ∃ c : ℂ, c ≠ 0 ∧ IsGaugeRelated (C s) (c • C' t)) ∧
      ∀ t ∈ T, ∃ s ∈ S, ∃ c : ℂ, c ≠ 0 ∧ IsGaugeRelated (C' t) (c • C s) := by
  classical
  obtain ⟨Q'⟩ := id hQ
  obtain ⟨K, _, μ, hμ⟩ := exists_enumeration (nonzeroSpectrum (mixedTransfer B B))
  obtain ⟨L, _, ν, hν⟩ := exists_enumeration (nonzeroSpectrum (mixedTransfer B A))
  have hdep : ∀ N, 0 < N → StatesDependentAt A B N := ((tfae_statesDependent A B).out 1 2).1 h
  have hall : ∀ N, 0 < N → ∀ σ : Fin N → Fin d,
      Matrix.trace (mixedTransfer B B ^ N) * mpv A σ =
        Matrix.trace (mixedTransfer B A ^ N) * mpv B σ := fun N hN =>
    (statesDependentAt_iff_trace_mixedTransfer A B N).1 (hdep N hN)
  obtain ⟨τ, hτ⟩ := (forall_trace_pow_mul_mpv_eq_iff_exists_equiv_isGaugeRelated hP hQ hirr hlet
    hirr' hlet' hμ hν).1 hall
  obtain ⟨N, σ, hN, hσ⟩ := exists_mpv_ne_zero_of_multiBlockCompression Q' hirr' hlet' hT
  have hK : Nonempty K := nonempty_of_trace_pow_ne_zero hμ hN (by
    rw [trace_mixedTransfer_pow]
    intro h0
    exact hσ ((star_mul_self_sum_eq_zero_iff (fun τ => mpv B τ)).1 h0 σ))
  obtain ⟨k₀⟩ := hK
  obtain ⟨s₀, hs₀⟩ := hS
  obtain ⟨t₀, l₀⟩ := τ (⟨s₀, hs₀⟩, k₀)
  have hμ0 := ne_zero_of_map_eq_nonzeroSpectrum hμ
  have hν0 := ne_zero_of_map_eq_nonzeroSpectrum hν
  constructor
  · intro s hs
    rcases hτx : τ (⟨s, hs⟩, k₀) with ⟨t, l⟩
    have hg := hτ (⟨s, hs⟩, k₀)
    rw [hτx] at hg
    refine ⟨t.1, t.2, (μ k₀)⁻¹ * ν l, mul_ne_zero (inv_ne_zero (hμ0 k₀)) (hν0 l), ?_⟩
    have := hg.smul (μ k₀)⁻¹
    simpa [smul_smul, inv_mul_cancel₀ (hμ0 k₀)] using this
  · intro t ht
    rcases hτx : τ.symm (⟨t, ht⟩, l₀) with ⟨s, k⟩
    have hg := hτ (s, k)
    have he : τ (s, k) = (⟨t, ht⟩, l₀) := by rw [← hτx, Equiv.apply_symm_apply]
    rw [he] at hg
    refine ⟨s.1, s.2, (ν l₀)⁻¹ * μ k, mul_ne_zero (inv_ne_zero (hν0 l₀)) (hμ0 _), ?_⟩
    have := hg.symm.smul (ν l₀)⁻¹
    simpa [smul_smul, inv_mul_cancel₀ (hν0 l₀)] using this

end

end MPSTensor

end WeightedStates

section ClassicalDependent

/-!
## The classical proportional theorems from dependent states

The fundamental theorems of Cirac, Pérez-García, Schuch and Verstraete (arXiv:1606.00608,
Theorem 2.10) and of De las Cuevas, Cirac, Schuch and Pérez-García (arXiv:1708.00029, theorem
`thm:bd`) match the bases of two tensors whose states are proportional for all `N`. The theorem of
this file contains both: normal tensors are the irreducible tensors of period one. It follows
from the statement on classes of factors for dependent states, which
needs only linear dependence of the states at all large lengths: constants `γ_N = 0` are allowed.
Thus `C ⊕ (-C)` and `C`, whose states are related by `γ_N = 1 + (-1) ^ N`, are covered.

### Main results

* `MPSTensor.fundamentalTheorem_irreducibleForm_of_statesDependent`

### References

* Cirac, Pérez-García, Schuch, Verstraete, arXiv:1606.00608, Theorem 2.10.
* De las Cuevas, Cirac, Schuch, Pérez-García, arXiv:1708.00029, theorem `thm:bd`, lines 613--623.
-/

open scoped Matrix.Norms.Operator

namespace MPSTensor

variable {d : ℕ}

/-- A block whose transfer map has spectral radius one has a nonzero letter. -/
private theorem exists_ne_zero_of_spectralRadius_eq_one {n : ℕ} {C : MPSTensor d n}
    (hC : spectralRadius ℂ ((Module.End.toContinuousLinearMap (Matrix (Fin n) (Fin n) ℂ))
      (Kraus.transferMap (ι := Fin d) (n := Fin n) C)) = 1) : ∃ i, C i ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have h0 : Kraus.transferMap (ι := Fin d) (n := Fin n) C = 0 := by
    refine LinearMap.ext fun Z => ?_
    rw [Kraus.transferMap_apply]
    simp [hcon]
  rw [h0, map_zero, spectrum.spectralRadius_zero] at hC
  exact zero_ne_one hC

/-- A sector decomposition with nonzero irreducible basis blocks reduces onto its weighted
blocks. -/
private theorem nonempty_multiBlockCompression_toTensor (P : SectorDecomposition d)
    (hirr : ∀ j, Matrix.IsIrreducibleAction (P.basis j)) (hlet : ∀ j, ∃ i, P.basis j i ≠ 0) :
    Nonempty (MultiBlockCompression (D := fun x : (Σ j, Fin (P.copies j)) => P.basisDim x.1)
      P.toTensor Finset.univ (fun x => P.weight x.1 x.2 • P.basis x.1)) := by
  classical
  obtain ⟨Q, -⟩ := exists_multiBlockCompression_z_eq_of_isIrreducibleAction Finset.univ
    (D := fun x : (Σ j, Fin (P.copies j)) => P.basisDim x.1)
    (fun x => P.weight x.1 x.2 • P.basis x.1)
    (fun x _ => isIrreducibleAction_smul (hirr x.1) (P.weight_ne_zero _ _))
    (fun x _ => exists_smul_apply_ne_zero (hlet x.1) (P.weight_ne_zero _ _)) P.toTensor
    (fun w _ => by
      have h := P.mpv_toTensor_eq_sum_sectors w.get
      simp only [mpv_eq, coeff_eq, List.ofFn_get] at h
      rw [h, Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun q _ => ?_
      rw [trace_evalWord_smul])
  exact ⟨Q⟩

/-- A gauge relation with a phase is a repeated-block relation. -/
private theorem hetRepeatedBlocks_of_isGaugeRelated_smul {D₁ D₂ : ℕ} {A : MPSTensor d D₁}
    {B : MPSTensor d D₂} {c : ℂ} (hc : ‖c‖ = 1) (h : IsGaugeRelated A (c • B)) :
    HetRepeatedBlocks A B := by
  have hdim : D₁ = D₂ := h.dim_eq
  subst hdim
  obtain ⟨G, hG⟩ := isGaugeRelated_iff_gaugeEquiv.1 h
  refine ⟨rfl, c, G⁻¹, hc, fun i => ?_⟩
  simp only [cast_eq, inv_inv]
  have hgi : ((G⁻¹ : GL (Fin D₁) ℂ) : Matrix (Fin D₁) (Fin D₁) ℂ) *
      (G : Matrix (Fin D₁) (Fin D₁) ℂ) = 1 := Units.inv_mul G
  have hi : (c • B) i = (G : Matrix (Fin D₁) (Fin D₁) ℂ) * A i *
      ((G⁻¹ : GL (Fin D₁) ℂ) : Matrix (Fin D₁) (Fin D₁) ℂ) := hG i
  calc A i = (((G⁻¹ : GL (Fin D₁) ℂ) : Matrix (Fin D₁) (Fin D₁) ℂ) *
        (G : Matrix (Fin D₁) (Fin D₁) ℂ)) * A i *
        (((G⁻¹ : GL (Fin D₁) ℂ) : Matrix (Fin D₁) (Fin D₁) ℂ) *
          (G : Matrix (Fin D₁) (Fin D₁) ℂ)) := by
        rw [hgi, Matrix.one_mul, Matrix.mul_one]
    _ = ((G⁻¹ : GL (Fin D₁) ℂ) : Matrix (Fin D₁) (Fin D₁) ℂ) * ((c • B) i) *
        (G : Matrix (Fin D₁) (Fin D₁) ℂ) := by
        rw [hi]
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul]

/-- Under dependent states, every basis block of one decomposition is a repeated block of a basis
block of the other, when all gauge scalars between basis blocks have modulus one. -/
private theorem forall_exists_hetRepeatedBlocks_of_statesDependent (P Q : SectorDecomposition d)
    (hirrP : ∀ j, Matrix.IsIrreducibleAction (P.basis j)) (hletP : ∀ j, ∃ i, P.basis j i ≠ 0)
    (hirrQ : ∀ k, Matrix.IsIrreducibleAction (Q.basis k)) (hletQ : ∀ k, ∃ i, Q.basis k i ≠ 0)
    (hP0 : 0 < P.basisCount) (hQ0 : 0 < Q.basisCount)
    (hnorm : ∀ j k (c : ℂ), IsGaugeRelated (P.basis j) (c • Q.basis k) → ‖c‖ = 1)
    (hdep : ∀ᶠ N in atTop, StatesDependentAt P.toTensor Q.toTensor N) :
    (∀ j, ∃ k, HetRepeatedBlocks (P.basis j) (Q.basis k)) ∧
      ∀ k, ∃ j, HetRepeatedBlocks (P.basis j) (Q.basis k) := by
  classical
  have hS : (Finset.univ : Finset (Σ j, Fin (P.copies j))).Nonempty :=
    ⟨⟨⟨0, hP0⟩, ⟨0, P.copies_pos _⟩⟩, Finset.mem_univ _⟩
  have hT : (Finset.univ : Finset (Σ k, Fin (Q.copies k))).Nonempty :=
    ⟨⟨⟨0, hQ0⟩, ⟨0, Q.copies_pos _⟩⟩, Finset.mem_univ _⟩
  obtain ⟨h1, h2⟩ := forall_exists_isGaugeRelated_smul_of_eventually_statesDependentAt
    (nonempty_multiBlockCompression_toTensor P hirrP hletP)
    (nonempty_multiBlockCompression_toTensor Q hirrQ hletQ)
    (fun x _ => isIrreducibleAction_smul (hirrP x.1) (P.weight_ne_zero _ _))
    (fun x _ => exists_smul_apply_ne_zero (hletP x.1) (P.weight_ne_zero _ _))
    (fun x _ => isIrreducibleAction_smul (hirrQ x.1) (Q.weight_ne_zero _ _))
    (fun x _ => exists_smul_apply_ne_zero (hletQ x.1) (Q.weight_ne_zero _ _)) hS hT hdep
  constructor
  · intro j
    obtain ⟨t, -, c, -, hg⟩ := h1 ⟨j, ⟨0, P.copies_pos j⟩⟩ (Finset.mem_univ _)
    set μ := P.weight j ⟨0, P.copies_pos j⟩ with hμ
    have hμ0 : μ ≠ 0 := P.weight_ne_zero _ _
    have hg' : IsGaugeRelated (P.basis j) ((μ⁻¹ * (c * Q.weight t.1 t.2)) • Q.basis t.1) := by
      have := hg.smul μ⁻¹
      simpa [smul_smul, inv_mul_cancel₀ hμ0] using this
    exact ⟨t.1, hetRepeatedBlocks_of_isGaugeRelated_smul (hnorm _ _ _ hg') hg'⟩
  · intro k
    obtain ⟨s, -, c, hc, hg⟩ := h2 ⟨k, ⟨0, Q.copies_pos k⟩⟩ (Finset.mem_univ _)
    set ν := Q.weight k ⟨0, Q.copies_pos k⟩ with hν
    have hμ0 : c * P.weight s.1 s.2 ≠ 0 := mul_ne_zero hc (P.weight_ne_zero _ _)
    have hg' : IsGaugeRelated (P.basis s.1)
        (((c * P.weight s.1 s.2)⁻¹ * ν) • Q.basis k) := by
      have := hg.symm.smul (c * P.weight s.1 s.2)⁻¹
      rw [smul_smul c (P.weight s.1 s.2) (P.basis s.1), smul_smul (c * P.weight s.1 s.2)⁻¹,
        inv_mul_cancel₀ hμ0, one_smul, smul_smul] at this
      exact this
    exact ⟨s.1, hetRepeatedBlocks_of_isGaugeRelated_smul (hnorm _ _ _ hg') hg'⟩

/-- **De las Cuevas et al., proportional case, with dependent states.** Two tensors in irreducible
form with bases of periodic tensors, both nonempty, whose states are linearly dependent at all
large lengths have bases matched up to a phase and a gauge, with equal periods.

Source: arXiv:1708.00029, theorem `thm:bd`, lines 613--623; the source assumes proportional states
for all `N`. The hypotheses `0 < P.basisCount`, `0 < Q.basisCount` exclude the empty form, whose
state vanishes and is dependent on every state. -/
theorem fundamentalTheorem_irreducibleForm_of_statesDependent
    (P Q : SectorDecomposition d)
    (hIrrP : ∀ j, Kraus.IsIrreducibleFamily (P.basis j))
    (hRadP : ∀ j,
      spectralRadius ℂ
        ((Module.End.toContinuousLinearMap
            (Matrix (Fin (P.basisDim j)) (Fin (P.basisDim j)) ℂ))
          (Kraus.transferMap (ι := Fin d) (n := Fin (P.basisDim j)) (P.basis j))) = 1)
    (hIrrQ : ∀ k, Kraus.IsIrreducibleFamily (Q.basis k))
    (hRadQ : ∀ k,
      spectralRadius ℂ
        ((Module.End.toContinuousLinearMap
            (Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ))
          (Kraus.transferMap (ι := Fin d) (n := Fin (Q.basisDim k)) (Q.basis k))) = 1)
    (hNonRepP : ∀ i j, i ≠ j → ¬ HetRepeatedBlocks (P.basis i) (P.basis j))
    (hNonRepQ : ∀ i j, i ≠ j → ¬ HetRepeatedBlocks (Q.basis i) (Q.basis j))
    (hP0 : 0 < P.basisCount) (hQ0 : 0 < Q.basisCount)
    (hdep : ∀ᶠ N in atTop, StatesDependentAt P.toTensor Q.toTensor N) :
    ∃ (periodP : Fin P.basisCount → ℕ) (periodQ : Fin Q.basisCount → ℕ),
      (∀ j, IsSpectrallyPeriodic (periodP j) (P.basis j)) ∧
      (∀ k, IsSpectrallyPeriodic (periodQ k) (Q.basis k)) ∧
      PeriodicBasisMatchingWitness P.basis Q.basis periodP periodQ := by
  classical
  choose periodP hPerP using fun j =>
    exists_isSpectrallyPeriodic_of_irreducible_of_spectralRadius_one (hIrrP j) (hRadP j)
  choose periodQ hPerQ using fun k =>
    exists_isSpectrallyPeriodic_of_irreducible_of_spectralRadius_one (hIrrQ k) (hRadQ k)
  obtain ⟨hf, hg⟩ := forall_exists_hetRepeatedBlocks_of_statesDependent P Q
    (fun j => Kraus.isIrreducibleAction_of_isIrreducibleFamily _ (hIrrP j))
    (fun j => exists_ne_zero_of_spectralRadius_eq_one (hRadP j))
    (fun k => Kraus.isIrreducibleAction_of_isIrreducibleFamily _ (hIrrQ k))
    (fun k => exists_ne_zero_of_spectralRadius_eq_one (hRadQ k)) hP0 hQ0
    (fun j k _ h => norm_eq_one_of_isGaugeRelated_smul (hRadP j) (hRadQ k) h) hdep
  choose f hf using hf
  choose g hg using hg
  have hfinj : Function.Injective f := fun j₁ j₂ hj => by
    by_contra hne
    have h₂ : HetRepeatedBlocks (Q.basis (f j₁)) (P.basis j₂) := hj ▸ (hf j₂).symm
    exact hNonRepP j₁ j₂ hne ((hf j₁).trans h₂)
  have hginj : Function.Injective g := fun k₁ k₂ hk => by
    by_contra hne
    have h₂ : HetRepeatedBlocks (P.basis (g k₁)) (Q.basis k₂) := hk ▸ hg k₂
    exact hNonRepQ k₁ k₂ hne ((hg k₁).symm.trans h₂)
  have hcard : P.basisCount = Q.basisCount := by
    have h1 := Fintype.card_le_of_injective f hfinj
    have h2 := Fintype.card_le_of_injective g hginj
    simp only [Fintype.card_fin] at h1 h2
    omega
  have hfbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hfinj, by simp [hcard]⟩
  refine ⟨periodP, periodQ, hPerP, hPerQ, hcard, Equiv.ofBijective f hfbij, fun j => ?_⟩
  exact ⟨IsSpectrallyPeriodic.period_eq_of_hetRepeatedBlocks (hPerP j) (hPerQ _) (hf j), hf j⟩

end MPSTensor

end ClassicalDependent
