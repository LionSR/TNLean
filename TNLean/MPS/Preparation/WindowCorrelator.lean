/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixTracePairing
import QICLean.Kraus.MapIterate
import TNLean.MPS.MPDO.CommutingForm
import TNLean.MPS.Overlap.Basic
import TNLean.MPS.RFP.ZeroCorrelationLength

/-!
# Correlators of block observables in a translation-invariant matrix product state

For operators `X, Y` on `L` consecutive sites, the connected correlator
`G_N(X,Y;s) = ⟨X_1 Y_s⟩ - ⟨X_1⟩⟨Y_s⟩` in the normalized vector
`|φ_N⟩ = ∑ Tr(A^{i_1} ⋯ A^{i_N}) |i_1 ⋯ i_N⟩` is the quantity bounded below in
arXiv:2307.01696, Supplemental Material, Lemma 2. This file expresses it through
inserted transfer maps: for `N = L + m + L + n`,
`⟨φ_N|X_1 Y_{L+m+1}|φ_N⟩ = tr(E_X E_A^m E_Y E_A^n)` as a trace of a linear map
on virtual matrices.

## Main declarations

* `chainWindowOperator N a X`: the operator `X` on the sites `a+1, …, a+L`
  of a chain of `N` sites, identity elsewhere.
* `mpvExpectation A N O`: the expectation of `O` in the normalized vector `φ_N`.
* `mpvConnectedCorrelator`: the connected correlator of two window operators.
* `inner_mpvState_toEuclideanLin`: `⟨φ_N|O|φ_N⟩ = tr E_O`.
* `physicalObservableTransfer_appendObservable`: the inserted transfer map of a
  tensor product of block observables is the composition of the two maps.
* `inner_mpvState_chainWindowOperator_mul`: the two-window trace formula.
-/

open scoped Matrix BigOperators InnerProductSpace Kronecker

namespace MPSTensor

variable {d D : ℕ}

/-! ### Tensor products of block observables -/

/-- The inserted transfer map in coordinates,
`E_O(Z) = ∑_{σ,τ} O_{τσ} A^σ Z (A^τ)†` (arXiv:1606.00608, lines 490--496). -/
theorem physicalObservableTransfer_apply' (A : MPSTensor d D) (L : ℕ)
    (O : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) (Z : Matrix (Fin D) (Fin D) ℂ) :
    physicalObservableTransfer A L O Z = ∑ σ : Fin L → Fin d, ∑ τ : Fin L → Fin d,
      O τ σ • (Kraus.evalWord A (List.ofFn σ) * Z * (Kraus.evalWord A (List.ofFn τ))ᴴ) := by
  simp [physicalObservableTransfer, Matrix.mul_assoc]

/-- The tensor product of an operator on `L₁` consecutive sites and an operator on
the next `L₂` sites, as an operator on `L₁ + L₂` sites. This is the product of
block observables in the correlators of arXiv:2307.01696, Supplemental Material,
proof of Lemma 2. -/
noncomputable def appendObservable {L₁ L₂ : ℕ}
    (O₁ : Matrix (Fin L₁ → Fin d) (Fin L₁ → Fin d) ℂ)
    (O₂ : Matrix (Fin L₂ → Fin d) (Fin L₂ → Fin d) ℂ) :
    Matrix (Fin (L₁ + L₂) → Fin d) (Fin (L₁ + L₂) → Fin d) ℂ :=
  Matrix.reindex (Fin.appendEquiv L₁ L₂) (Fin.appendEquiv L₁ L₂) (O₁ ⊗ₖ O₂)

/-- Matrix entries of a tensor product of block observables (arXiv:2307.01696,
Supplemental Material, proof of Lemma 2). -/
theorem appendObservable_apply {L₁ L₂ : ℕ}
    (O₁ : Matrix (Fin L₁ → Fin d) (Fin L₁ → Fin d) ℂ)
    (O₂ : Matrix (Fin L₂ → Fin d) (Fin L₂ → Fin d) ℂ)
    (τ σ : Fin (L₁ + L₂) → Fin d) :
    appendObservable O₁ O₂ τ σ =
      O₁ (fun i ↦ τ (Fin.castAdd L₂ i)) (fun i ↦ σ (Fin.castAdd L₂ i)) *
        O₂ (fun i ↦ τ (Fin.natAdd L₁ i)) (fun i ↦ σ (Fin.natAdd L₁ i)) := by
  simp [appendObservable, Matrix.kroneckerMap_apply]

/-- Matrix entries of a tensor product of block observables at concatenated
configurations (arXiv:2307.01696, Supplemental Material, proof of Lemma 2). -/
theorem appendObservable_append {L₁ L₂ : ℕ}
    (O₁ : Matrix (Fin L₁ → Fin d) (Fin L₁ → Fin d) ℂ)
    (O₂ : Matrix (Fin L₂ → Fin d) (Fin L₂ → Fin d) ℂ)
    (τ₁ σ₁ : Fin L₁ → Fin d) (τ₂ σ₂ : Fin L₂ → Fin d) :
    appendObservable O₁ O₂ (Fin.append τ₁ τ₂) (Fin.append σ₁ σ₂) =
      O₁ τ₁ σ₁ * O₂ τ₂ σ₂ := by
  simp [appendObservable_apply]

/-- Tensor products of block observables multiply factorwise. This is used for the
correlators of arXiv:2307.01696, Supplemental Material, proof of Lemma 2. -/
theorem appendObservable_mul {L₁ L₂ : ℕ}
    (O₁ P₁ : Matrix (Fin L₁ → Fin d) (Fin L₁ → Fin d) ℂ)
    (O₂ P₂ : Matrix (Fin L₂ → Fin d) (Fin L₂ → Fin d) ℂ) :
    appendObservable O₁ O₂ * appendObservable P₁ P₂ =
      appendObservable (O₁ * P₁) (O₂ * P₂) := by
  simp only [appendObservable, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
    ← Matrix.mul_kronecker_mul]

/-- The tensor product of identities is the identity (arXiv:2307.01696,
Supplemental Material, proof of Lemma 2, `E_𝟙 = E_A^L`). -/
@[simp] theorem appendObservable_one_one {L₁ L₂ : ℕ} :
    appendObservable (1 : Matrix (Fin L₁ → Fin d) (Fin L₁ → Fin d) ℂ)
      (1 : Matrix (Fin L₂ → Fin d) (Fin L₂ → Fin d) ℂ) = 1 := by
  simp [appendObservable]

/-- The inserted transfer map of a tensor product of block observables is the
composition of the inserted transfer maps, `E_{O₁ ⊗ O₂} = E_{O₁} E_{O₂}`: the
words of length `L₁ + L₂` are the concatenations of words of lengths `L₁` and
`L₂`. This is the factorization of the transfer-matrix expression of
correlators in arXiv:2307.01696, Supplemental Material, proof of Lemma 2, and in
arXiv:1606.00608, lines 490--496. -/
theorem physicalObservableTransfer_appendObservable (A : MPSTensor d D) {L₁ L₂ : ℕ}
    (O₁ : Matrix (Fin L₁ → Fin d) (Fin L₁ → Fin d) ℂ)
    (O₂ : Matrix (Fin L₂ → Fin d) (Fin L₂ → Fin d) ℂ) :
    physicalObservableTransfer A (L₁ + L₂) (appendObservable O₁ O₂) =
      physicalObservableTransfer A L₁ O₁ * physicalObservableTransfer A L₂ O₂ := by
  classical
  have hsum : ∀ f : (Fin (L₁ + L₂) → Fin d) → Matrix (Fin D) (Fin D) ℂ,
      ∑ σ, f σ = ∑ σ₁ : Fin L₁ → Fin d, ∑ σ₂ : Fin L₂ → Fin d, f (Fin.append σ₁ σ₂) := by
    intro f
    rw [← (Fin.appendEquiv L₁ L₂).sum_comp, Fintype.sum_prod_type]
    rfl
  apply LinearMap.ext
  intro Z
  rw [Module.End.mul_apply, physicalObservableTransfer_apply', hsum]
  simp_rw [hsum, physicalObservableTransfer_apply', appendObservable_append, List.ofFn_fin_append,
    Kraus.evalWord_append, Matrix.conjTranspose_mul, Finset.mul_sum, Finset.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum, smul_smul, Matrix.mul_assoc]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm

/-- The identity observable on `L` sites inserts the `L`-th power of the transfer
map, `E_{𝟙} = E_A^L`. -/
theorem physicalObservableTransfer_one (A : MPSTensor d D) (L : ℕ) :
    physicalObservableTransfer A L (1 : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) =
      Kraus.transferMap A ^ L := by
  classical
  apply LinearMap.ext
  intro Z
  rw [Kraus.transferMap, Kraus.mapLM_pow_apply, physicalObservableTransfer_apply']
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [Finset.sum_eq_single σ (fun τ _ hτ ↦ by rw [Matrix.one_apply_ne hτ, zero_smul])
    (by simp), Matrix.one_apply_eq, one_smul]

/-! ### Expectations as traces of inserted transfer maps -/

/-- The expectation of an operator `O` on the chain in the vector `φ_N` is the
trace of its inserted transfer map, `⟨φ_N|O|φ_N⟩ = tr E_O`. This is the trace
formula for expectations in arXiv:2307.01696, Supplemental Material, proof of
Lemma 2, and arXiv:1606.00608, lines 490--496, for an operator on all `N`
sites. -/
theorem inner_mpvState_toEuclideanLin (A : MPSTensor d D) (N : ℕ)
    (O : Matrix (Cfg d N) (Cfg d N) ℂ) :
    ⟪mpvState A N, Matrix.toEuclideanLin O (mpvState A N)⟫_ℂ =
      LinearMap.trace ℂ (Matrix (Fin D) (Fin D) ℂ) (physicalObservableTransfer A N O) := by
  classical
  have htr : ∀ M K : Matrix (Fin D) (Fin D) ℂ,
      LinearMap.trace ℂ (Matrix (Fin D) (Fin D) ℂ)
        ((LinearMap.mulLeft ℂ M).comp (LinearMap.mulRight ℂ K)) =
        Matrix.trace M * Matrix.trace K := by
    intro M K
    rw [Matrix.linearMap_trace_eq_sum_apply_single]
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
      ← Matrix.mul_assoc, Matrix.entry_mul_single_mul, Matrix.trace, Finset.sum_mul_sum,
      Matrix.diag_apply]
  simp only [physicalObservableTransfer, map_sum, map_smul, htr, smul_eq_mul,
    Matrix.trace_conjTranspose, RCLike.star_def]
  simp only [PiLp.inner_apply, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    mpvState_apply, mpv_eq, coeff_eq, RCLike.inner_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ ↦ Finset.sum_congr rfl fun σ _ ↦ ?_
  ring

/-! ### Operators on windows of consecutive sites -/

/-- The operator `X` on the `L` consecutive sites `a+1, …, a+L` of a periodic chain
of `N` sites, acting as the identity elsewhere; it is `0` when the window start
`a` is not a site or `L > N`. This is the operator `O_s` of arXiv:2307.01696,
Supplemental Material, Lemma 2, on the block of sites starting at `s = a + 1`. -/
noncomputable def chainWindowOperator {L : ℕ} (N a : ℕ)
    (X : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    Matrix (Cfg d N) (Cfg d N) ℂ :=
  if h : L ≤ N ∧ a < N then MPOTensor.embedLocalOperator L N h.1 ⟨a, h.2⟩ X else 0

/-- On a window that does not wrap around the ring, the operator acts as `X` on the
window and as the identity elsewhere. This is used for the correlators of
arXiv:2307.01696, Supplemental Material, proof of Lemma 2. -/
theorem chainWindowOperator_apply {L N a : ℕ} (ha : a < N) (haL : a + L ≤ N)
    (X : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) (τ σ : Cfg d N) :
    chainWindowOperator N a X τ σ =
      if ∀ k : Fin N, ¬ (a ≤ k.val ∧ k.val < a + L) → τ k = σ k then
        X (fun j ↦ τ ⟨a + j.val, by omega⟩) (fun j ↦ σ ⟨a + j.val, by omega⟩)
      else 0 := by
  have hLN : L ≤ N := by omega
  rw [chainWindowOperator, dite_eq_left ⟨hLN, ha⟩, MPOTensor.embedLocalOperator_apply]
  have hoff : ∀ k : Fin N, (k.val + N - a) % N < L ↔ a ≤ k.val ∧ k.val < a + L := by
    intro k
    by_cases hk : a ≤ k.val
    · have h1 : k.val + N - a = (k.val - a) + N := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [Nat.mod_eq_of_lt (by omega)]
      omega
  have hcond : MPOTensor.AgreesOutsideWindow (d := d) L hLN ⟨a, ha⟩ τ σ ↔
      ∀ k : Fin N, ¬ (a ≤ k.val ∧ k.val < a + L) → τ k = σ k := by
    rw [MPOTensor.agreesOutsideWindow_iff]
    refine forall_congr' fun k ↦ ?_
    rw [hoff k, eq_comm]
  have hext : ∀ ν : Cfg d N, MPSTensor.extractWindow L ⟨a, ha⟩ ν =
      fun j ↦ ν ⟨a + j.val, by omega⟩ := by
    intro ν
    funext j
    simp only [MPSTensor.extractWindow]
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt (by omega))
  simp only [hcond, hext]

/-- A window in the first `p` sites of a chain of `p + q` sites. This is used for the
correlators of arXiv:2307.01696, Supplemental Material, proof of Lemma 2. -/
theorem chainWindowOperator_add_left {L p q a : ℕ} (ha : a < p) (haL : a + L ≤ p)
    (X : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    chainWindowOperator (p + q) a X =
      appendObservable (chainWindowOperator p a X) 1 := by
  classical
  ext τ σ
  rw [chainWindowOperator_apply (by omega) (by omega), appendObservable_apply,
    chainWindowOperator_apply ha haL, Matrix.one_apply]
  have hiff : (∀ k : Fin (p + q), ¬ (a ≤ k.val ∧ k.val < a + L) → τ k = σ k) ↔
      (∀ k : Fin p, ¬ (a ≤ k.val ∧ k.val < a + L) →
        τ (Fin.castAdd q k) = σ (Fin.castAdd q k)) ∧
      ((fun i ↦ τ (Fin.natAdd p i)) = fun i ↦ σ (Fin.natAdd p i)) := by
    constructor
    · intro h
      refine ⟨fun k hk ↦ h _ hk, funext fun i ↦ h _ ?_⟩
      simp only [Fin.natAdd]
      omega
    · rintro ⟨h₁, h₂⟩ k hk
      refine Fin.addCases (fun k hk ↦ h₁ k hk) (fun i _ ↦ congrFun h₂ i) k hk
  by_cases h₁ : ∀ k : Fin p, ¬ (a ≤ k.val ∧ k.val < a + L) →
      τ (Fin.castAdd q k) = σ (Fin.castAdd q k)
  · by_cases h₂ : (fun i ↦ τ (Fin.natAdd p i)) = fun i ↦ σ (Fin.natAdd p i)
    · rw [ite_eq_left (hiff.2 ⟨h₁, h₂⟩), ite_eq_left h₁, ite_eq_left h₂, mul_one]
      rfl
    · rw [ite_eq_right fun h ↦ h₂ (hiff.1 h).2, ite_eq_right h₂, mul_zero]
  · rw [ite_eq_right fun h ↦ h₁ (hiff.1 h).1, ite_eq_right h₁, zero_mul]

/-- A window in the last `q` sites of a chain of `p + q` sites. This is used for the
correlators of arXiv:2307.01696, Supplemental Material, proof of Lemma 2. -/
theorem chainWindowOperator_add_right {L p q a : ℕ} (hpa : p ≤ a) (ha : a < p + q)
    (haL : a + L ≤ p + q) (X : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    chainWindowOperator (p + q) a X =
      appendObservable 1 (chainWindowOperator q (a - p) X) := by
  classical
  ext τ σ
  rw [chainWindowOperator_apply ha haL, appendObservable_apply,
    chainWindowOperator_apply (by omega) (by omega), Matrix.one_apply]
  have hiff : (∀ k : Fin (p + q), ¬ (a ≤ k.val ∧ k.val < a + L) → τ k = σ k) ↔
      ((fun i ↦ τ (Fin.castAdd q i)) = fun i ↦ σ (Fin.castAdd q i)) ∧
      (∀ k : Fin q, ¬ (a - p ≤ k.val ∧ k.val < a - p + L) →
        τ (Fin.natAdd p k) = σ (Fin.natAdd p k)) := by
    constructor
    · intro h
      refine ⟨funext fun i ↦ h _ ?_, fun k hk ↦ h _ ?_⟩
      · simp only [Fin.castAdd, Fin.castLE]
        omega
      · simp only [Fin.natAdd]
        omega
    · rintro ⟨h₁, h₂⟩ k hk
      refine Fin.addCases (fun i _ ↦ congrFun h₁ i) (fun k hk ↦ h₂ k ?_) k hk
      simp only [Fin.natAdd] at hk
      omega
  have hX : ∀ ν : Fin (p + q) → Fin d,
      (fun j : Fin L ↦ ν ⟨a + j.val, by omega⟩) =
        fun j : Fin L ↦ (fun i ↦ ν (Fin.natAdd p i)) ⟨a - p + j.val, by omega⟩ := by
    intro ν
    funext j
    exact congrArg ν (Fin.ext (by simp only [Fin.natAdd]; omega))
  by_cases h₁ : (fun i ↦ τ (Fin.castAdd q i)) = fun i ↦ σ (Fin.castAdd q i)
  · by_cases h₂ : ∀ k : Fin q, ¬ (a - p ≤ k.val ∧ k.val < a - p + L) →
        τ (Fin.natAdd p k) = σ (Fin.natAdd p k)
    · rw [ite_eq_left (hiff.2 ⟨h₁, h₂⟩), ite_eq_left h₁, ite_eq_left h₂, one_mul, hX τ, hX σ]
    · rw [ite_eq_right fun h ↦ h₂ (hiff.1 h).2, ite_eq_right h₂, mul_zero]
  · rw [ite_eq_right fun h ↦ h₁ (hiff.1 h).1, ite_eq_right h₁, zero_mul]

/-- A window covering the whole chain. This is used for the correlators of
arXiv:2307.01696, Supplemental Material, proof of Lemma 2. -/
theorem chainWindowOperator_self {L : ℕ} (hL : 0 < L)
    (X : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    chainWindowOperator L 0 X = X := by
  classical
  ext τ σ
  rw [chainWindowOperator_apply hL (by omega)]
  rw [ite_eq_left fun k hk ↦ absurd ⟨Nat.zero_le _, by simp⟩ hk]
  congr 1 <;> funext j <;> exact congrArg _ (Fin.ext (by simp))

/-- The window at the first `L` sites of a chain of `L + m + L + n` sites, written as a
tensor product over the four blocks. This is used for the correlators of
arXiv:2307.01696, Supplemental Material, proof of Lemma 2. -/
theorem chainWindowOperator_zero_eq_appendObservable {L : ℕ} (hL : 0 < L) (m n : ℕ)
    (X : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    chainWindowOperator (L + m + L + n) 0 X =
      appendObservable (appendObservable (appendObservable X 1) 1) 1 := by
  rw [chainWindowOperator_add_left (by omega) (by omega),
    chainWindowOperator_add_left (by omega) (by omega),
    chainWindowOperator_add_left (by omega) (by omega), chainWindowOperator_self hL]

/-- The window at the sites `L + m + 1, …, 2L + m` of a chain of `L + m + L + n` sites,
written as a tensor product over the four blocks. This is used for the correlators of
arXiv:2307.01696, Supplemental Material, proof of Lemma 2. -/
theorem chainWindowOperator_add_eq_appendObservable {L : ℕ} (hL : 0 < L) (m n : ℕ)
    (Y : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    chainWindowOperator (L + m + L + n) (L + m) Y =
      appendObservable (appendObservable (appendObservable 1 1) Y) 1 := by
  rw [chainWindowOperator_add_left (by omega) (by omega),
    chainWindowOperator_add_right le_rfl (by omega) (by omega), Nat.sub_self,
    chainWindowOperator_self hL, appendObservable_one_one]

/-- The two-window trace formula: on a chain of `N = L + m + L + n` sites, with `X`
on the sites `1, …, L` and `Y` on the sites `L + m + 1, …, 2L + m`,
`⟨φ_N|X_1 Y_{L+m+1}|φ_N⟩ = tr(E_X E_A^m E_Y E_A^n)`.

This is the expansion "Expanding the traces in (eq:TI-MPS2)" of the connected
correlator in arXiv:2307.01696, Supplemental Material, proof of Lemma 2, where
the source writes `⟨O_1 O'_s⟩ ∝ tr(E_O E_1^{s-2} E_{O'} E_1^{N-s})` for one-site
observables. -/
theorem inner_mpvState_chainWindowOperator_mul (A : MPSTensor d D) {L : ℕ} (hL : 0 < L)
    (m n : ℕ) (X Y : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    ⟪mpvState A (L + m + L + n), Matrix.toEuclideanLin
        (chainWindowOperator (L + m + L + n) 0 X *
          chainWindowOperator (L + m + L + n) (L + m) Y)
        (mpvState A (L + m + L + n))⟫_ℂ =
      LinearMap.trace ℂ (Matrix (Fin D) (Fin D) ℂ)
        (physicalObservableTransfer A L X * Kraus.transferMap A ^ m *
          physicalObservableTransfer A L Y * Kraus.transferMap A ^ n) := by
  rw [chainWindowOperator_zero_eq_appendObservable hL,
    chainWindowOperator_add_eq_appendObservable hL, appendObservable_mul, appendObservable_mul,
    appendObservable_mul, mul_one, mul_one, one_mul, mul_one, inner_mpvState_toEuclideanLin,
    physicalObservableTransfer_appendObservable,
    physicalObservableTransfer_appendObservable, physicalObservableTransfer_appendObservable,
    physicalObservableTransfer_one, physicalObservableTransfer_one]

/-- The window operator of the identity is the identity. This is used for the
correlators of arXiv:2307.01696, Supplemental Material, proof of Lemma 2. -/
theorem chainWindowOperator_one {L N a : ℕ} (ha : a < N) (haL : a + L ≤ N) :
    chainWindowOperator N a (1 : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) = 1 := by
  classical
  ext τ σ
  rw [chainWindowOperator_apply ha haL, Matrix.one_apply, Matrix.one_apply]
  by_cases h : ∀ k : Fin N, ¬ (a ≤ k.val ∧ k.val < a + L) → τ k = σ k
  · rw [ite_eq_left h]
    by_cases hτσ : τ = σ
    · subst hτσ
      simp
    · rw [ite_eq_right hτσ, ite_eq_right]
      intro hw
      refine hτσ (funext fun k ↦ ?_)
      by_cases hk : a ≤ k.val ∧ k.val < a + L
      · have := congrFun hw ⟨k.val - a, by omega⟩
        simpa [show a + (k.val - a) = k.val by omega] using this
      · exact h k hk
  · rw [ite_eq_right h, ite_eq_right]
    rintro rfl
    exact h fun _ _ ↦ rfl

/-! ### Normalized expectations and the connected correlator -/

/-- The expectation `⟨φ_N|O|φ_N⟩` of an operator on the chain in the normalized
vector `φ_N/‖φ_N‖` of arXiv:2307.01696, Supplemental Material, eq. (TI-MPS2)
(chapter display `eq:ldp_ti_mps`). It is `0` when `φ_N = 0`. -/
noncomputable def mpvExpectation (A : MPSTensor d D) (N : ℕ)
    (O : Matrix (Cfg d N) (Cfg d N) ℂ) : ℂ :=
  ⟪((‖mpvState A N‖ : ℂ)⁻¹) • mpvState A N,
    Matrix.toEuclideanLin O (((‖mpvState A N‖ : ℂ)⁻¹) • mpvState A N)⟫_ℂ

/-- The normalized expectation is the ratio `⟨φ_N|O|φ_N⟩ / ⟨φ_N|φ_N⟩`. This is used for
the correlators of arXiv:2307.01696, Supplemental Material, proof of Lemma 2. -/
theorem mpvExpectation_eq_div (A : MPSTensor d D) (N : ℕ)
    (O : Matrix (Cfg d N) (Cfg d N) ℂ) :
    mpvExpectation A N O =
      ⟪mpvState A N, Matrix.toEuclideanLin O (mpvState A N)⟫_ℂ /
        ⟪mpvState A N, mpvState A N⟫_ℂ := by
  rw [mpvExpectation, map_smul, inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K]
  simp only [map_inv₀, Complex.conj_ofReal]
  field_simp
  rfl

/-- The connected correlator
`G_N(X,Y) = ⟨X_{a+1} Y_{b+1}⟩ - ⟨X_{a+1}⟩⟨Y_{b+1}⟩` in the normalized vector `φ_N`, with
`X` on the sites `a+1, …, a+L` and `Y` on the sites `b+1, …, b+L`. With `a = 0`
and `b = s - 1` this is `G_N(X,Y;s)` of the chapter display
`eq:ldp_connected_correlator`, the quantity bounded in arXiv:2307.01696,
Supplemental Material, Lemma 2, eq. (auxform2). -/
noncomputable def mpvConnectedCorrelator (A : MPSTensor d D) (N : ℕ) {L : ℕ} (a b : ℕ)
    (X Y : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) : ℂ :=
  mpvExpectation A N (chainWindowOperator N a X * chainWindowOperator N b Y) -
    mpvExpectation A N (chainWindowOperator N a X) *
      mpvExpectation A N (chainWindowOperator N b Y)

end MPSTensor
