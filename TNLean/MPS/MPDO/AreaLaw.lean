/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.Defs
import TNLean.Analysis.Entropy
import Mathlib.Data.List.Rotate
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Saturation of the area law for MPDO and MPS tensors

This file formalizes the **saturation of the area law** (SAL) predicate for
matrix product density operators and the pure matrix product state analogue,
following arXiv:1606.00608 (Cirac–Pérez-García–Schuch–Verstraete), Section 4.4
("Mutual information. Saturation of the area law", line 789) and Section 3
("Saturation of the area law", line 593).

For a chain of `N` spins in a normalized state `σ^{(N)}(M)`, the mutual
information between a block of `L` neighboring spins and the rest is

  `I_L = S_L + S_{N-L} - S_N`

(arXiv:1606.00608, eq. line 797), where `S_L` is the von Neumann entropy of the
reduced state of `L` neighboring spins. A tensor `M` generating MPDO **verifies
SAL** when `I_1 = I_2 = ⋯` (Definition 4.6, line 811). Equivalently
(line 815), `I_L = I_{L+1}` whenever `1 ≤ L < ⌊N/2⌋`. The pure analogue
(Definition 3.13, line 600) asks the block von Neumann entropies
`S_1^{(N)} = S_2^{(N)} = ⋯` of the pure state to coincide.

## Main definitions

* `blockReducedState`: the reduced state of the first `L` of `L + K` contiguous
  spins, using the general right partial trace `Matrix.partialTraceRight`.
* `MPOTensor.normalizedMPO`: the normalized density operator
  `σ^{(N)}(M) = ρ^{(N)}(M) / tr[ρ^{(N)}(M)]`.
* `MPOTensor.reducedBlockState`: the reduced state of the first `L` spins of
  `σ^{(N)}(M)`.
* `MPOTensor.blockEntropy`: the block entropy `S_L`.
* `MPOTensor.mutualInfoChain`: the mutual information `I_L = S_L + S_{N-L} - S_N`.
* `MPOTensor.IsSAL`: the saturation-of-the-area-law predicate for MPDO.
* `MPSTensor.normalizedPureState`, `MPSTensor.pureBlockEntropy`,
  `MPSTensor.IsSAL`: the pure-state analogues.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608, Definition 4.6
  (line 811), Definition 3.13 (line 600), eq. line 797.
-/

open scoped Matrix ComplexOrder BigOperators
open Matrix Finset

/-! ## Translation invariance of the periodic MPDO

The periodic MPO density operator $\rho^{(N)}(M)$ closes the MPO word with a bond
trace, hence is invariant under the simultaneous cyclic shift of bra and ket
configurations. This is the translation invariance required for the
mutual-information monotonicity. -/

/-- `List.ofFn` precomposed with `finRotate` is the one-step list rotation. A
general fact about `List.ofFn`, `finRotate`, and `List.rotate`. -/
theorem ofFn_comp_finRotate {α : Type*} {n : ℕ} (σ : Fin (n + 1) → α) :
    List.ofFn (σ ∘ finRotate (n + 1)) = (List.ofFn σ).rotate 1 := by
  apply List.ext_getElem
  · simp
  · intro i h1 _
    simp only [List.getElem_ofFn, Function.comp_apply, List.getElem_rotate,
      List.length_ofFn]
    congr 1
    have : finRotate (n + 1) ⟨i, by simpa using h1⟩
        = ⟨(i + 1) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩ := by
      rw [finRotate_apply]; ext; simp [Fin.add_def]
    rw [this]

namespace MPOTensor

variable {d D : ℕ}

/-- List-level cyclicity: rotating both equal-length words by one position
leaves the closed-word trace unchanged. -/
theorem trace_evalWord_rotate_one (M : MPOTensor d D) :
    ∀ (w w' : List (Fin d)), w.length = w'.length →
      Matrix.trace (evalWord M (w.rotate 1) (w'.rotate 1))
        = Matrix.trace (evalWord M w w') := by
  intro w w' h
  cases w with
  | nil =>
      rw [List.length_nil, eq_comm, List.length_eq_zero_iff] at h
      subst h; rfl
  | cons a l =>
      cases w' with
      | nil => simp at h
      | cons b k =>
          rw [List.rotate_cons_succ, List.rotate_zero, List.rotate_cons_succ,
            List.rotate_zero, ← trace_evalWord_cons_eq_append M a b l k (by simpa using h)]

/-- Cyclically shifting both configurations leaves the closed-word MPO entry
unchanged. -/
theorem mpoMatrixEntry_comp_finRotate (M : MPOTensor d D) {N : ℕ}
    (σ τ : Fin N → Fin d) :
    mpoMatrixEntry M (σ ∘ finRotate N) (τ ∘ finRotate N) = mpoMatrixEntry M σ τ := by
  cases N with
  | zero => rfl
  | succ n =>
      rw [mpoMatrixEntry, ofFn_comp_finRotate, ofFn_comp_finRotate, mpoMatrixEntry,
        trace_evalWord_rotate_one M _ _ (by simp)]

/-- The cyclic-shift reindexing of configurations on `N` sites:
`rotateConfig N d σ = σ ∘ finRotate N`. -/
def rotateConfig (N d : ℕ) : (Fin N → Fin d) ≃ (Fin N → Fin d) :=
  Equiv.arrowCongr (finRotate N).symm (Equiv.refl (Fin d))

@[simp] lemma rotateConfig_apply (N d : ℕ) (σ : Fin N → Fin d) :
    rotateConfig N d σ = σ ∘ finRotate N := rfl

/-- **Translation invariance of the periodic MPDO.** `mpo M N` is invariant under
the simultaneous cyclic shift of bra and ket configurations. -/
theorem mpo_submatrix_rotateConfig (M : MPOTensor d D) (N : ℕ) :
    (mpo M N).submatrix (rotateConfig N d) (rotateConfig N d) = mpo M N := by
  ext σ τ
  simp only [Matrix.submatrix_apply, mpo_apply, rotateConfig_apply]
  exact mpoMatrixEntry_comp_finRotate M σ τ

/-- The closed-word MPO entry is invariant under a `p`-fold cyclic shift of both
configurations (iterating the single-shift invariance). -/
theorem mpoMatrixEntry_comp_finRotate_pow (M : MPOTensor d D) {N : ℕ}
    (p : ℕ) (σ τ : Fin N → Fin d) :
    mpoMatrixEntry M (σ ∘ (finRotate N : Fin N → Fin N)^[p])
        (τ ∘ (finRotate N : Fin N → Fin N)^[p])
      = mpoMatrixEntry M σ τ := by
  induction p with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ, ← Function.comp_assoc, ← Function.comp_assoc,
        mpoMatrixEntry_comp_finRotate, ih]

/-- **Translation invariance under a `p`-fold shift.** `mpo M N` is invariant
under the simultaneous `p`-fold cyclic shift of bra and ket configurations. -/
theorem mpo_submatrix_finRotate_pow (M : MPOTensor d D) (N p : ℕ) :
    (mpo M N).submatrix (fun σ => σ ∘ (finRotate N : Fin N → Fin N)^[p])
        (fun σ => σ ∘ (finRotate N : Fin N → Fin N)^[p]) = mpo M N := by
  ext σ τ
  simp only [Matrix.submatrix_apply, mpo_apply]
  exact mpoMatrixEntry_comp_finRotate_pow M p σ τ

end MPOTensor

/-! ## Cyclic shift on configurations -/

/-- `finRotate` advances the value by one modulo `N`. -/
theorem coe_finRotate_mod {N : ℕ} (i : Fin N) :
    ((finRotate N) i : ℕ) = (i.val + 1) % N := by
  match N with
  | 0 => exact i.elim0
  | n + 1 =>
    rw [coe_finRotate]
    rcases eq_or_ne i (Fin.last n) with h | h
    · subst h; simp [Fin.val_last, Nat.mod_self]
    · rw [if_neg h]
      have : (i : ℕ) < n := Fin.val_lt_last h
      rw [Nat.mod_eq_of_lt (by omega)]

/-- The value of the `p`-fold cyclic shift is `(i + p) mod N`. -/
theorem coe_finRotate_pow {N : ℕ} (p : ℕ) (i : Fin N) :
    (((finRotate N : Fin N → Fin N)^[p]) i : ℕ) = (i.val + p) % N := by
  induction p with
  | zero => simp [Nat.mod_eq_of_lt i.isLt]
  | succ k ih =>
    rw [Function.iterate_succ_apply', coe_finRotate_mod, ih, Nat.mod_add_mod, Nat.add_assoc]

/-- **Cyclic shift by `p` swaps the first `p` coordinates to the back.**
For `x : Fin p → α` and `y : Fin q → α`, shifting `append x y` by `p` yields
`append y x` (after the `Fin (p + q) ≃ Fin (q + p)` length cast). This is the
configuration-level form of the periodic MPDO's translation invariance. -/
theorem append_comp_finRotate_pow {α : Type*} {p q : ℕ}
    (x : Fin p → α) (y : Fin q → α) :
    (Fin.append x y) ∘ ((finRotate (p + q) : Fin (p + q) → Fin (p + q))^[p])
      = (Fin.append y x) ∘ Fin.cast (Nat.add_comm p q) := by
  funext i
  simp only [Function.comp_apply]
  rcases lt_or_ge i.val q with hiq | hiq
  · have hm : (finRotate (p + q) : Fin (p + q) → Fin (p + q))^[p] i
        = Fin.natAdd p ⟨i.val, hiq⟩ := by
      apply Fin.ext
      rw [coe_finRotate_pow, Nat.mod_eq_of_lt (by omega)]
      simp only [Fin.natAdd_mk]; omega
    have hc : Fin.cast (Nat.add_comm p q) i = Fin.castAdd p ⟨i.val, hiq⟩ := by
      apply Fin.ext; simp
    rw [hm, hc, Fin.append_right, Fin.append_left]
  · have hm : (finRotate (p + q) : Fin (p + q) → Fin (p + q))^[p] i
        = Fin.castAdd q ⟨i.val - q, by omega⟩ := by
      apply Fin.ext
      rw [coe_finRotate_pow, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      simp only [Fin.castAdd_mk]; omega
    have hc : Fin.cast (Nat.add_comm p q) i = Fin.natAdd q ⟨i.val - q, by omega⟩ := by
      apply Fin.ext; simp only [Fin.val_cast, Fin.natAdd_mk]; omega
    rw [hm, hc, Fin.append_left, Fin.append_right]

/-- The length cast commutes with the `p`-fold cyclic shift. -/
theorem cast_comp_finRotate_pow {N M : ℕ} (h : N = M) (p : ℕ) :
    (Fin.cast h) ∘ ((finRotate N : Fin N → Fin N)^[p])
      = ((finRotate M : Fin M → Fin M)^[p]) ∘ (Fin.cast h) := by
  funext i
  apply Fin.ext
  simp only [Function.comp_apply, Fin.val_cast]
  rw [coe_finRotate_pow, coe_finRotate_pow]
  subst h; rfl

/-- **Window-to-prefix configuration identity.** Placing the `m`-block `u` at the
front (with `z, x` after) equals placing it in the middle (with `x` before and
`z` after) composed with the `p`-fold cyclic shift, where `p = |x|`. This is the
configuration form of translation invariance: a block in the middle of the chain
is the same as a block at the front after a cyclic shift. -/
theorem window_eq_prefix_rotate {d N p m s : ℕ}
    (x : Fin p → Fin d) (u : Fin m → Fin d) (z : Fin s → Fin d)
    (hA : N = m + (s + p)) (hB : N = p + m + s) :
    (Fin.append u (Fin.append z x)) ∘ Fin.cast hA
      = ((Fin.append (Fin.append x u) z) ∘ Fin.cast hB)
        ∘ ((finRotate N : Fin N → Fin N)^[p]) := by
  funext j
  simp only [Function.comp_apply]
  rcases lt_or_ge j.val m with h1 | h1
  · have hL : Fin.cast hA j = Fin.castAdd (s + p) ⟨j.val, h1⟩ := by
      apply Fin.ext; simp
    have hR : Fin.cast hB ((finRotate N : Fin N → Fin N)^[p] j)
        = Fin.castAdd s (Fin.natAdd p ⟨j.val, h1⟩) := by
      apply Fin.ext
      rw [Fin.val_cast, coe_finRotate_pow, Nat.mod_eq_of_lt (by omega)]
      simp; omega
    rw [hL, hR, Fin.append_left, Fin.append_left, Fin.append_right]
  · rcases lt_or_ge j.val (m + s) with h2 | h2
    · have hL : Fin.cast hA j = Fin.natAdd m (Fin.castAdd p ⟨j.val - m, by omega⟩) := by
        apply Fin.ext; simp; omega
      have hR : Fin.cast hB ((finRotate N : Fin N → Fin N)^[p] j)
          = Fin.natAdd (p + m) ⟨j.val - m, by omega⟩ := by
        apply Fin.ext
        rw [Fin.val_cast, coe_finRotate_pow, Nat.mod_eq_of_lt (by omega)]
        simp; omega
      rw [hL, hR, Fin.append_right, Fin.append_left, Fin.append_right]
    · have hL : Fin.cast hA j = Fin.natAdd m (Fin.natAdd s ⟨j.val - m - s, by omega⟩) := by
        apply Fin.ext; simp; omega
      have hR : Fin.cast hB ((finRotate N : Fin N → Fin N)^[p] j)
          = Fin.castAdd s (Fin.castAdd m ⟨j.val - m - s, by omega⟩) := by
        apply Fin.ext
        rw [Fin.val_cast, coe_finRotate_pow, Nat.mod_eq_sub_mod (by omega),
          Nat.mod_eq_of_lt (by omega)]
        simp; omega
      rw [hL, hR, Fin.append_right, Fin.append_right, Fin.append_left, Fin.append_left]

/-! ## Trace normalization -/

namespace Matrix

/-- Normalizing a positive semidefinite matrix by the inverse of its
(nonnegative real) trace preserves positive semidefiniteness. -/
theorem PosSemidef.smul_inv_trace {n : Type*} [Fintype n]
    {P : Matrix n n ℂ} (hP : P.PosSemidef) : (P.trace⁻¹ • P).PosSemidef := by
  have htr_nonneg : (0 : ℂ) ≤ P.trace := hP.trace_nonneg
  have hre : 0 ≤ P.trace.re := (RCLike.nonneg_iff.mp htr_nonneg).1
  have him : P.trace.im = 0 := (RCLike.nonneg_iff.mp htr_nonneg).2
  set r : ℝ := P.trace.re with hr
  have htr_eq : P.trace = (r : ℂ) := Complex.ext rfl (by simp [him, hr])
  have hinv_eq : (P.trace)⁻¹ = ((r⁻¹ : ℝ) : ℂ) := by rw [htr_eq, Complex.ofReal_inv]
  rw [hinv_eq]
  exact hP.smul (a := ((r⁻¹ : ℝ) : ℂ)) (by exact_mod_cast inv_nonneg.mpr hre)

end Matrix

/-! ## Contiguous-block reduced state -/

/-- The identification splitting a configuration on `L + K` contiguous spins into
its first `L` and last `K` parts:
`(Fin (L + K) → Fin d) ≃ (Fin L → Fin d) × (Fin K → Fin d)`. -/
def blockSplitEquiv (d L K : ℕ) :
    (Fin (L + K) → Fin d) ≃ (Fin L → Fin d) × (Fin K → Fin d) :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl (Fin d))).trans
    (Equiv.sumArrowEquivProdArrow (Fin L) (Fin K) (Fin d))

/-- The reduced state of the first `L` of `L + K` contiguous spins, obtained by
tracing out the last `K` spins after splitting the index via `blockSplitEquiv`. -/
noncomputable def blockReducedState (d L K : ℕ)
    (ρ : Matrix (Fin (L + K) → Fin d) (Fin (L + K) → Fin d) ℂ) :
    Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ :=
  Matrix.partialTraceRight
    (ρ.submatrix (blockSplitEquiv d L K).symm (blockSplitEquiv d L K).symm)

/-- The block reduced state preserves Hermiticity. -/
theorem blockReducedState_isHermitian {d L K : ℕ}
    {ρ : Matrix (Fin (L + K) → Fin d) (Fin (L + K) → Fin d) ℂ}
    (hρ : ρ.IsHermitian) : (blockReducedState d L K ρ).IsHermitian :=
  Matrix.partialTraceRight_isHermitian (hρ.submatrix _)

/-- The block reduced state preserves positive semidefiniteness. -/
theorem blockReducedState_posSemidef {d L K : ℕ}
    {ρ : Matrix (Fin (L + K) → Fin d) (Fin (L + K) → Fin d) ℂ}
    (hρ : ρ.PosSemidef) : (blockReducedState d L K ρ).PosSemidef :=
  (hρ.submatrix _).partialTraceRight

/-- The block reduced state preserves the trace. -/
theorem blockReducedState_trace {d L K : ℕ}
    (ρ : Matrix (Fin (L + K) → Fin d) (Fin (L + K) → Fin d) ℂ) :
    (blockReducedState d L K ρ).trace = ρ.trace := by
  rw [blockReducedState, Matrix.trace_partialTraceRight]
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact (blockSplitEquiv d L K).symm.sum_comp (fun p => ρ p p)

/-- The inverse block split is concatenation of the two parts via `Fin.append`. -/
theorem blockSplitEquiv_symm_apply {d L K : ℕ} (a : Fin L → Fin d) (b : Fin K → Fin d) :
    (blockSplitEquiv d L K).symm (a, b) = Fin.append a b := by
  funext i
  simp only [blockSplitEquiv, Equiv.symm_trans_apply, Equiv.sumArrowEquivProdArrow,
    Equiv.coe_fn_symm_mk, Equiv.arrowCongr_symm, Equiv.refl_symm, Equiv.arrowCongr_apply,
    Equiv.coe_refl, Function.comp, id_eq]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [Equiv.symm_symm, finSumFinEquiv_symm_apply_castAdd]
  · simp [Equiv.symm_symm, finSumFinEquiv_symm_apply_natAdd]

/-- Concatenating the two parts of a block split recovers the original
configuration. -/
theorem append_blockSplitEquiv {d K₁ K₂ : ℕ} (k : Fin (K₁ + K₂) → Fin d) :
    Fin.append (blockSplitEquiv d K₁ K₂ k).1 (blockSplitEquiv d K₁ K₂ k).2 = k := by
  rw [← blockSplitEquiv_symm_apply, Prod.mk.eta, Equiv.symm_apply_apply]

/-- **Composition of contiguous-block reductions.** Tracing out the last `K₁`
spins of the reduced state on the first `L + K₁` of `L + K₁ + K₂` spins equals
tracing out the last `K₁ + K₂` spins directly (after reassociating the index).
This is the prefix-consistency step: reducing a prefix and then a shorter prefix
agrees with reducing to the shorter prefix in one step. -/
theorem blockReducedState_comp {d L K₁ K₂ : ℕ}
    (X : Matrix (Fin (L + K₁ + K₂) → Fin d) (Fin (L + K₁ + K₂) → Fin d) ℂ) :
    blockReducedState d L K₁ (blockReducedState d (L + K₁) K₂ X)
      = blockReducedState d L (K₁ + K₂)
          (X.submatrix
            (Equiv.arrowCongr (finCongr (Nat.add_assoc L K₁ K₂)) (Equiv.refl (Fin d))).symm
            (Equiv.arrowCongr (finCongr (Nat.add_assoc L K₁ K₂)) (Equiv.refl (Fin d))).symm) := by
  rw [blockReducedState, blockReducedState, Matrix.partialTraceRight_submatrix_left,
    Matrix.submatrix_submatrix, Matrix.partialTraceRight_partialTraceRight,
    Matrix.partialTraceRight_submatrix_right (blockSplitEquiv d K₁ K₂),
    blockReducedState, Matrix.submatrix_submatrix, Matrix.submatrix_submatrix]
  ext p i
  simp only [partialTraceRight_apply, Matrix.submatrix_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1 <;>
  · simp only [Function.comp, Prod.map, blockSplitEquiv_symm_apply, id_eq, Fin.append_assoc,
      append_blockSplitEquiv]
    funext x
    simp only [Equiv.arrowCongr_symm, Equiv.refl_symm, Equiv.arrowCongr_apply, Equiv.coe_refl,
      id_eq, finCongr_symm, finCongr_apply, Function.comp_apply]

/-- Reindexing the input of a block reduction by a prefix-preserving `finCongr`
on the suffix length leaves the reduced state unchanged: it only relabels the
traced-out spins. The suffix-length equality is `subst`ed away, after which the
reindex collapses to the identity. -/
theorem blockReducedState_submatrix_finCongr {d L K K' : ℕ} (h : L + K = L + K')
    (ρ : Matrix (Fin (L + K) → Fin d) (Fin (L + K) → Fin d) ℂ) :
    blockReducedState d L K'
        (ρ.submatrix (Equiv.arrowCongr (finCongr h) (Equiv.refl (Fin d))).symm
          (Equiv.arrowCongr (finCongr h) (Equiv.refl (Fin d))).symm)
      = blockReducedState d L K ρ := by
  have hKK' : K = K' := by omega
  subst hKK'
  simp

/-! ## Normalized MPO and block entropies -/

namespace MPOTensor

variable {d D : ℕ}

/-- The **normalized density operator** of the MPO for system size `N`:

  `σ^{(N)}(M) = ρ^{(N)}(M) / tr[ρ^{(N)}(M)]`.

This is the convention of arXiv:1606.00608, line 792: entropic quantities are
always taken on the normalized state. -/
noncomputable def normalizedMPO (M : MPOTensor d D) (N : ℕ) :
    Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ :=
  (Matrix.trace (mpo M N))⁻¹ • mpo M N

/-- The normalized MPO is positive semidefinite when `M` generates an MPDO: the
normalizing scalar `(tr ρ)⁻¹` is a nonnegative real, so it preserves positive
semidefiniteness. -/
theorem normalizedMPO_posSemidef (M : MPOTensor d D) (N : ℕ)
    (hM : (mpo M N).PosSemidef) : (normalizedMPO M N).PosSemidef := by
  rw [normalizedMPO]; exact hM.smul_inv_trace

/-- The normalized MPO is Hermitian when `M` generates an MPDO. -/
theorem normalizedMPO_isHermitian (M : MPOTensor d D) (N : ℕ)
    (hM : (mpo M N).PosSemidef) : (normalizedMPO M N).IsHermitian :=
  (normalizedMPO_posSemidef M N hM).isHermitian

/-- The normalized MPO has unit trace when the unnormalized trace is nonzero. -/
theorem normalizedMPO_trace (M : MPOTensor d D) (N : ℕ)
    (hN : (mpo M N).trace ≠ 0) : (normalizedMPO M N).trace = 1 := by
  rw [normalizedMPO, Matrix.trace_smul, smul_eq_mul, inv_mul_cancel₀ hN]

/-- The reindexing equiv that views a configuration on `N = L + (N - L)` spins as
one on `L + (N - L)` spins, used to feed `normalizedMPO M N` into the
contiguous-block reduced state. -/
def blockReindexEquiv (d N L : ℕ) (hL : L ≤ N) :
    (Fin N → Fin d) ≃ (Fin (L + (N - L)) → Fin d) :=
  Equiv.arrowCongr (finCongr (Nat.add_sub_cancel' hL).symm) (Equiv.refl (Fin d))

/-- The **reduced state of the first `L` spins** of the normalized state
`σ^{(N)}(M)`, for `L ≤ N`. -/
noncomputable def reducedBlockState (M : MPOTensor d D) (N L : ℕ) (hL : L ≤ N) :
    Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ :=
  blockReducedState d L (N - L)
    ((normalizedMPO M N).submatrix (blockReindexEquiv d N L hL).symm
      (blockReindexEquiv d N L hL).symm)

/-- The reduced block state is Hermitian when `M` generates an MPDO. -/
theorem reducedBlockState_isHermitian (M : MPOTensor d D) (N L : ℕ) (hL : L ≤ N)
    (hM : (mpo M N).PosSemidef) : (reducedBlockState M N L hL).IsHermitian :=
  blockReducedState_isHermitian ((normalizedMPO_isHermitian M N hM).submatrix _)

/-- The reduced block state is positive semidefinite when `M` generates an MPDO. -/
theorem reducedBlockState_posSemidef (M : MPOTensor d D) (N L : ℕ) (hL : L ≤ N)
    (hM : (mpo M N).PosSemidef) : (reducedBlockState M N L hL).PosSemidef :=
  blockReducedState_posSemidef ((normalizedMPO_posSemidef M N hM).submatrix _)

/-- The **block entropy** `S_L`: the von Neumann entropy of the reduced state of
the first `L` spins of the normalized state `σ^{(N)}(M)`.

Source: arXiv:1606.00608, line 797 (`S_L` is the von Neumann entropy of the
reduced state of `L` neighboring spins). -/
noncomputable def blockEntropy (M : MPOTensor d D) (N L : ℕ) (hL : L ≤ N)
    (hM : (mpo M N).PosSemidef) : ℝ :=
  vonNeumannEntropy (reducedBlockState M N L hL)
    (reducedBlockState_isHermitian M N L hL hM)

/-- The **mutual information** `I_L = S_L + S_{N-L} - S_N` between a block of `L`
spins and the rest of the chain, for the normalized state `σ^{(N)}(M)`.

The complement term `S_{N-L}` is taken as the entropy of the *first* `N-L` spins
(`blockEntropy M N (N - L)`). This is the entropy of the complement of the
`L`-block because `mpo M N` is a trace of a product of the `M` tensors, hence
cyclically (translationally) invariant, so the reduced state of the first `N-L`
spins and that of the last `N-L` spins have equal entropy.

Source: arXiv:1606.00608, eq. line 797. -/
noncomputable def mutualInfoChain (M : MPOTensor d D) (N L : ℕ) (hL : L ≤ N)
    (hM : (mpo M N).PosSemidef) : ℝ :=
  blockEntropy M N L hL hM
    + blockEntropy M N (N - L) (Nat.sub_le N L) hM
    - blockEntropy M N N (le_refl N) hM

/-- The mutual information equals `S_L + S_{N-L} - S_N`, the source formula
(arXiv:1606.00608, eq. line 797). This holds by definition. -/
theorem mutualInfoChain_eq (M : MPOTensor d D) (N L : ℕ) (hL : L ≤ N)
    (hM : (mpo M N).PosSemidef) :
    mutualInfoChain M N L hL hM
      = blockEntropy M N L hL hM
        + blockEntropy M N (N - L) (Nat.sub_le N L) hM
        - blockEntropy M N N (le_refl N) hM :=
  rfl

/-- A tensor `M` **verifies saturation of the area law** (SAL) if it generates
MPDO, every system-size density operator has nonzero trace (so the normalized
state is well defined), and the mutual information is constant in the block size:
`I_L = I_{L+1}` for all `L` with `1 ≤ L < ⌊N/2⌋`, for all `N` (i.e. the chain
`I_1 = I_2 = ⋯ = I_{⌊N/2⌋}`).

Source: arXiv:1606.00608, Definition 4.6 (line 811), with the equivalent
form `I_L = I_{L+1}` for `L < ⌊N/2⌋` (line 815); the chain starts at `I_1`. -/
def IsSAL (M : MPOTensor d D) : Prop :=
  ∃ hMpdo : IsMPDO M, (∀ N, (mpo M N).trace ≠ 0) ∧
    ∀ N L : ℕ, 1 ≤ L → (hL : L < N / 2) →
      mutualInfoChain M N L (Nat.le_of_lt (hL.trans_le (Nat.div_le_self N 2))) (hMpdo N)
        = mutualInfoChain M N (L + 1) (hL.trans_le (Nat.div_le_self N 2)) (hMpdo N)

/-- **Saturation telescopes.** If `M` verifies saturation of the area law then all
mutual informations in the range `1 ≤ L ≤ ⌊N/2⌋` coincide: the consecutive
equalities `I_L = I_{L+1}` of the definition chain into `I_L = I_{L'}` for any two
block sizes `L, L'` in the range.

Source: arXiv:1606.00608, Definition 4.6 (line 811): the saturation condition is
written as the equality chain `I_1 = I_2 = ⋯ = I_{⌊N/2⌋}`. -/
theorem mutualInfoChain_eq_of_isSAL (M : MPOTensor d D) (hSAL : IsSAL M)
    {N L L' : ℕ} (hL1 : 1 ≤ L) (hLN : L ≤ N / 2) (hL'1 : 1 ≤ L')
    (hL'N : L' ≤ N / 2) :
    let hM : (mpo M N).PosSemidef := (Classical.choose hSAL) N
    mutualInfoChain M N L (hLN.trans (Nat.div_le_self N 2)) hM
      = mutualInfoChain M N L' (hL'N.trans (Nat.div_le_self N 2)) hM := by
  classical
  dsimp only
  let hMpdo : IsMPDO M := Classical.choose hSAL
  rcases Classical.choose_spec hSAL with ⟨_, hstep⟩
  -- Climbing `k` steps from a block size `m` stays an equality while `m + k ≤ ⌊N/2⌋`.
  have climb : ∀ k m : ℕ, 1 ≤ m → ∀ h : m + k ≤ N / 2,
      mutualInfoChain M N m
          ((Nat.le_add_right m k).trans (h.trans (Nat.div_le_self N 2))) (hMpdo N)
        = mutualInfoChain M N (m + k) (h.trans (Nat.div_le_self N 2)) (hMpdo N) := by
    intro k
    induction k with
    | zero => intro m _ _; rfl
    | succ k ih =>
      intro m hm1 h
      have hmk : m + k < N / 2 := by omega
      exact (ih m hm1 (le_of_lt hmk)).trans (hstep N (m + k) (by omega) hmk)
  rcases le_total L L' with hle | hle
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
    exact climb k L hL1 hL'N
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
    exact (climb k L' hL'1 hLN).symm

end MPOTensor

/-! ## Pure-state analogue -/

namespace MPSTensor

variable {d D : ℕ}

/-- The (unnormalized) pure-state density operator `|V^{(N)}(A)⟩⟨V^{(N)}(A)|` for
system size `N`, with matrix elements
`(σ, τ) ↦ mpv A σ * conj (mpv A τ)`.

Source: arXiv:1606.00608, Section 3 (the state `|V^{(N)}(A)⟩`), line 595. -/
noncomputable def pureState (A : MPSTensor d D) (N : ℕ) :
    Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ :=
  Matrix.vecMulVec (fun σ => mpv A σ) (star fun σ => mpv A σ)

/-- The pure-state density operator is positive semidefinite (it is a rank-one
projector up to normalization). -/
theorem pureState_posSemidef (A : MPSTensor d D) (N : ℕ) :
    (pureState A N).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star _

/-- The pure-state density operator is Hermitian. -/
theorem pureState_isHermitian (A : MPSTensor d D) (N : ℕ) :
    (pureState A N).IsHermitian :=
  (pureState_posSemidef A N).isHermitian

/-- The **normalized pure state** `σ^{(N)}(A) = |V⟩⟨V| / tr[|V⟩⟨V|]`. -/
noncomputable def normalizedPureState (A : MPSTensor d D) (N : ℕ) :
    Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ :=
  (Matrix.trace (pureState A N))⁻¹ • pureState A N

/-- The normalized pure state is positive semidefinite. -/
theorem normalizedPureState_posSemidef (A : MPSTensor d D) (N : ℕ) :
    (normalizedPureState A N).PosSemidef := by
  rw [normalizedPureState]; exact (pureState_posSemidef A N).smul_inv_trace

/-- The normalized pure state is Hermitian. -/
theorem normalizedPureState_isHermitian (A : MPSTensor d D) (N : ℕ) :
    (normalizedPureState A N).IsHermitian :=
  (normalizedPureState_posSemidef A N).isHermitian

/-- The reduced state of the first `L` spins of the normalized pure state
`σ^{(N)}(A)`, for `L ≤ N`. -/
noncomputable def reducedPureBlockState (A : MPSTensor d D) (N L : ℕ) (hL : L ≤ N) :
    Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ :=
  blockReducedState d L (N - L)
    ((normalizedPureState A N).submatrix
      (MPOTensor.blockReindexEquiv d N L hL).symm
      (MPOTensor.blockReindexEquiv d N L hL).symm)

/-- The reduced pure block state is Hermitian. -/
theorem reducedPureBlockState_isHermitian (A : MPSTensor d D) (N L : ℕ) (hL : L ≤ N) :
    (reducedPureBlockState A N L hL).IsHermitian :=
  blockReducedState_isHermitian ((normalizedPureState_isHermitian A N).submatrix _)

/-- The reduced pure block state is positive semidefinite. -/
theorem reducedPureBlockState_posSemidef (A : MPSTensor d D) (N L : ℕ) (hL : L ≤ N) :
    (reducedPureBlockState A N L hL).PosSemidef :=
  blockReducedState_posSemidef ((normalizedPureState_posSemidef A N).submatrix _)

/-- The reduced pure block state has unit trace when the pure state is normalizable. -/
theorem reducedPureBlockState_trace (A : MPSTensor d D) (N L : ℕ) (hL : L ≤ N)
    (htr : Matrix.trace (pureState A N) ≠ 0) :
    (reducedPureBlockState A N L hL).trace = 1 := by
  rw [reducedPureBlockState, blockReducedState_trace, Matrix.trace_submatrix_equiv,
    normalizedPureState, Matrix.trace_smul, smul_eq_mul, inv_mul_cancel₀ htr]

/-- The **pure block entropy** `S_L^{(N)}(A)`: the von Neumann entropy of the
reduced state of the first `L` spins of the normalized pure state `σ^{(N)}(A)`.

Source: arXiv:1606.00608, eq. line 597. -/
noncomputable def pureBlockEntropy (A : MPSTensor d D) (N L : ℕ) (hL : L ≤ N) : ℝ :=
  vonNeumannEntropy (reducedPureBlockState A N L hL)
    (reducedPureBlockState_isHermitian A N L hL)

/-- A tensor `A` **saturates the area law** (SAL) if the block entropies of the
generated pure state are constant in the block size:
`S_L^{(N)}(A) = S_{L+1}^{(N)}(A)` for all `L` with `1 ≤ L < ⌊N/2⌋`, for all `N`.

Source: arXiv:1606.00608, Definition 3.13 (line 600):
`S_1^{(N)}(A) = S_2^{(N)}(A) = ⋯ = S_{N/2}^{(N)}(A)` (the chain starts at `S_1`). -/
def IsSAL (A : MPSTensor d D) : Prop :=
  ∀ N L : ℕ, 1 ≤ L → (hL : L < N / 2) →
    pureBlockEntropy A N L (Nat.le_of_lt (hL.trans_le (Nat.div_le_self N 2)))
      = pureBlockEntropy A N (L + 1) (hL.trans_le (Nat.div_le_self N 2))

end MPSTensor

open Polynomial in
/-- **The normalized global pure state has zero von Neumann entropy** (`S_N = 0`,
arXiv:1606.00608, Section 3, line 599). The state `|V⟩⟨V| / ‖V‖²` is a rank-one
projector, so its characteristic polynomial is `X^{n-1}(X - 1)` and the entropy
sum over the eigenvalues of -λ log λ vanishes. -/
theorem vonNeumannEntropy_normalizedPureState {d D : ℕ} (A : MPSTensor d D) (N : ℕ)
    (htr : Matrix.trace (MPSTensor.pureState A N) ≠ 0) :
    vonNeumannEntropy (MPSTensor.normalizedPureState A N)
        (MPSTensor.normalizedPureState_isHermitian A N) = 0 := by
  set n := Fintype.card (Fin N → Fin d) with hn
  have hcard : 1 ≤ n := by
    rw [hn, Nat.one_le_iff_ne_zero]; intro h0
    haveI : IsEmpty (Fin N → Fin d) := Fintype.card_eq_zero_iff.mp h0
    exact htr (by simp [Matrix.trace, Matrix.diag, Finset.univ_eq_empty])
  have hdotEq : (fun σ : Fin N → Fin d => MPSTensor.mpv A σ) ⬝ᵥ
      (star (fun σ : Fin N → Fin d => MPSTensor.mpv A σ)) =
      Matrix.trace (MPSTensor.pureState A N) := by
    rw [Matrix.trace]
    simp only [Matrix.diag, MPSTensor.pureState, Matrix.vecMulVec_apply, dotProduct,
      Pi.star_apply]
  have hnp : MPSTensor.normalizedPureState A N
      = Matrix.vecMulVec ((Matrix.trace (MPSTensor.pureState A N))⁻¹ •
          (fun σ : Fin N → Fin d => MPSTensor.mpv A σ))
          (star (fun σ : Fin N → Fin d => MPSTensor.mpv A σ)) := by
    rw [Matrix.smul_vecMulVec]; rfl
  have hdot : ((Matrix.trace (MPSTensor.pureState A N))⁻¹ •
        (fun σ : Fin N → Fin d => MPSTensor.mpv A σ)) ⬝ᵥ
        (star (fun σ : Fin N → Fin d => MPSTensor.mpv A σ)) = 1 := by
    rw [smul_dotProduct, hdotEq, smul_eq_mul, inv_mul_cancel₀ htr]
  rw [vonNeumannEntropy_eq_charpoly_roots, hnp, Matrix.charpoly_vecMulVec, hdot, one_smul, ← hn]
  have hX1 : (X - 1 : ℂ[X]) ≠ 0 := by
    rw [show (1 : ℂ[X]) = C 1 by simp]; exact X_sub_C_ne_zero 1
  have hfact : (X ^ n - X ^ (n - 1) : ℂ[X]) = X ^ (n - 1) * (X - 1) := by
    rw [mul_sub, mul_one, ← pow_succ, Nat.sub_add_cancel hcard]
  rw [hfact, Polynomial.roots_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) hX1),
    Polynomial.roots_pow, Polynomial.roots_X,
    show (X - 1 : ℂ[X]) = X - C 1 by simp, Polynomial.roots_X_sub_C]
  simp [Multiset.map_nsmul, Multiset.sum_nsmul, Real.negMulLog_zero, Real.negMulLog_one]
