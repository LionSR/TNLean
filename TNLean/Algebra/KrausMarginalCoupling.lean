/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.SparsePositiveCoupling
import Mathlib.Basic.Complex.BigOperators
import QICLean.Algebra.MatrixSpectralDecomp
import QICLean.Analysis.MatrixSqrt

/-!
# Sparse Kraus families with prescribed positive marginals

Positive matrices of the same nonzero trace admit a rectangular Kraus
family with the two prescribed Gram sums. Its cardinality is at most the
sum of their ranks minus one. This is the marginal-coupling ingredient in
the cyclic root-selection argument associated with arXiv:1708.00029,
Theorem 4.1; see `docs/paper-gaps/dccsp17_root_kraus_rank_thm41.tex`.
-/

open scoped Matrix ComplexOrder BigOperators

namespace Matrix

private theorem unit_spectral_decomposition {n : Type*} [Fintype n]
    {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    ∃ (w : Fin A.rank → ℝ) (u : Fin A.rank → n → ℂ),
      (∀ i, 0 < w i) ∧ (∀ i, star (u i) ⬝ᵥ u i = 1) ∧
      A = ∑ i, (w i : ℂ) • vecMulVec (u i) (star (u i)) := by
  classical
  let I := {j : n // hA.isHermitian.eigenvalues j ≠ 0}
  let U := hA.isHermitian.eigenvectorUnitary
  let term : n → Matrix n n ℂ := fun j =>
    (hA.isHermitian.eigenvalues j : ℂ) •
      vecMulVec (fun p => U p j) (fun p => star (U p j))
  have hAll : A = ∑ j : n, term j := hA.eq_sum_eigenvalue_smul_eigenprojector
  have hSplit := Fintype.sum_subtype_add_sum_subtype
    (p := fun j : n => hA.isHermitian.eigenvalues j ≠ 0) term
  have hZero : ∑ j : {j : n // ¬ hA.isHermitian.eigenvalues j ≠ 0}, term j = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have hj : hA.isHermitian.eigenvalues j = 0 := by simpa using j.property
    simp [term, hj]
  have hTrim : A = ∑ j : I, term j := by
    exact hAll.trans (by simpa only [hZero, add_zero] using hSplit.symm)
  have hCard : Fintype.card I = A.rank := hA.isHermitian.rank_eq_card_non_zero_eigs.symm
  let e : Fin A.rank ≃ I := Fintype.equivOfCardEq (by simpa using hCard.symm)
  refine ⟨fun i => hA.isHermitian.eigenvalues (e i),
    fun i p => U p (e i), ?_, ?_, ?_⟩
  · intro i
    exact (hA.eigenvalues_nonneg (e i)).lt_of_ne (e i).property.symm
  · intro i
    have h := congrArg (fun M : Matrix n n ℂ => M (e i) (e i))
      (Unitary.coe_star_mul_self U)
    simpa [Matrix.star_eq_conjTranspose, Matrix.mul_apply,
      Matrix.conjTranspose_apply, dotProduct] using h
  · calc
      A = ∑ j : I, term j := hTrim
      _ = ∑ i : Fin A.rank, term (e i) :=
        (Fintype.sum_equiv e _ _ (fun i => rfl)).symm

private theorem trace_re_eq_sum_weights {n ι : Type*} [Fintype n]
    [Fintype ι] {A : Matrix n n ℂ} (w : ι → ℝ) (u : ι → n → ℂ)
    (hu : ∀ i, star (u i) ⬝ᵥ u i = 1)
    (hA : A = ∑ i, (w i : ℂ) • vecMulVec (u i) (star (u i))) :
    A.trace.re = ∑ i, w i := by
  have hUnit (i : ι) : (vecMulVec (u i) (star (u i))).trace = 1 := by
    simpa [Matrix.trace_vecMulVec, dotProduct, mul_comm] using hu i
  have hTrace : A.trace = ∑ i, (w i : ℂ) := by
    rw [hA, Matrix.trace_sum]
    simp only [Matrix.trace_smul, hUnit, smul_eq_mul, mul_one]
  simpa only [Complex.re_sum, Complex.ofReal_re] using congrArg Complex.re hTrace

private theorem rankOne_gram_sums {m n : Type*} [Fintype m] [Fintype n]
    (u : n → ℂ) (v : m → ℂ) (hu : star u ⬝ᵥ u = 1) (hv : star v ⬝ᵥ v = 1)
    {w : ℝ} (hw : 0 ≤ w) :
    let K := (Real.sqrt w : ℂ) • vecMulVec u (star v)
    K * Kᴴ = (w : ℂ) • vecMulVec u (star u) ∧
      Kᴴ * K = (w : ℂ) • vecMulVec v (star v) := by
  have hSquare : Real.sqrt w * Real.sqrt w = w := by
    simpa only [pow_two] using Real.sq_sqrt hw
  constructor <;>
    simp [Matrix.conjTranspose_smul, Matrix.conjTranspose_vecMulVec,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.vecMulVec_mul_vecMulVec,
      hu, hv, smul_smul, hSquare]

private theorem collect_weights {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] {n : Type*} (row : ι → κ) (w : ι → ℝ) (a : κ → ℝ)
    (P : κ → Matrix n n ℂ)
    (hRow : ∀ i, (∑ k, if row k = i then w k else 0) = a i) :
    ∑ k, (w k : ℂ) • P (row k) = ∑ i, (a i : ℂ) • P i := by
  have hCast (i : κ) : (∑ k, if row k = i then (w k : ℂ) else 0) = (a i : ℂ) := by
    have h := congrArg Complex.ofReal (hRow i)
    simpa only [Complex.ofReal_sum, apply_ite, Complex.ofReal_zero] using h
  calc
    _ = ∑ i, ∑ k, (if row k = i then (w k : ℂ) else 0) • P i := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      simp
    _ = ∑ i, (a i : ℂ) • P i := by simp only [← Finset.sum_smul, hCast]

/-- Positive matrices of the same positive trace are the two Gram sums
of a rectangular Kraus family with at most the sum of their ranks minus
one operators. This is the sparse positive-marginal construction used
in the cyclic selection argument for arXiv:1708.00029, Theorem 4.1;
it does not assert a channel-root selector by itself. -/
theorem exists_kraus_coupling_of_trace_eq {m n : Type*}
    [Fintype m] [Fintype n]
    {A : Matrix n n ℂ} {B : Matrix m m ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hTrace : A.trace = B.trace) (hPos : 0 < A.trace.re) :
    ∃ (r : ℕ) (K : Fin r → Matrix n m ℂ),
      r + 1 ≤ A.rank + B.rank ∧
      (∑ i, K i * (K i)ᴴ) = A ∧ (∑ i, (K i)ᴴ * K i) = B := by
  classical
  obtain ⟨a, u, ha, hu, hDecompA⟩ := unit_spectral_decomposition hA
  obtain ⟨b, v, hb, hv, hDecompB⟩ := unit_spectral_decomposition hB
  have hSumA := trace_re_eq_sum_weights a u hu hDecompA
  have hSumB := trace_re_eq_sum_weights b v hv hDecompB
  have hNEA : Nonempty (Fin A.rank) := by
    by_contra h
    have : IsEmpty (Fin A.rank) := not_nonempty_iff.mp h
    have hZero : ∑ i, a i = 0 := by simp
    linarith
  have hNEB : Nonempty (Fin B.rank) := by
    by_contra h
    have : IsEmpty (Fin B.rank) := not_nonempty_iff.mp h
    have hZero : ∑ i, b i = 0 := by simp
    have h := congrArg Complex.re hTrace
    linarith
  let _ : Nonempty (Fin A.rank) := hNEA
  let _ : Nonempty (Fin B.rank) := hNEB
  have hMass : ∑ i, a i = ∑ j, b j := by rw [← hSumA, ← hSumB, hTrace]
  have hTotal : 0 < ∑ i, a i := by rwa [← hSumA]
  obtain ⟨r, row, col, w, hCard, hw, hRow, hCol⟩ :=
    SparseCoupling.exists_positive_mass_coupling a b (fun i => (ha i).le)
      (fun j => (hb j).le) hMass hTotal
  let K : Fin r → Matrix n m ℂ := fun k =>
    (Real.sqrt (w k) : ℂ) • vecMulVec (u (row k)) (star (v (col k)))
  have hLeft (k : Fin r) : K k * (K k)ᴴ =
      (w k : ℂ) • vecMulVec (u (row k)) (star (u (row k))) :=
    (rankOne_gram_sums _ _ (hu (row k)) (hv (col k)) (hw k)).1
  have hRight (k : Fin r) : (K k)ᴴ * K k =
      (w k : ℂ) • vecMulVec (v (col k)) (star (v (col k))) :=
    (rankOne_gram_sums _ _ (hu (row k)) (hv (col k)) (hw k)).2
  refine ⟨r, K, by simpa only [Fintype.card_fin] using hCard, ?_, ?_⟩
  · simp_rw [hLeft]
    exact (collect_weights row w a (fun i => vecMulVec (u i) (star (u i))) hRow).trans
      hDecompA.symm
  · simp_rw [hRight]
    exact (collect_weights col w b (fun j => vecMulVec (v j) (star (v j))) hCol).trans
      hDecompB.symm

/-- A faithful input state, a positive output, and a positive trace effect
with compatible total mass admit a Kraus family of cardinality at most the
sum of the output and effect ranks minus one. This constructs the residual
map replacement in the cyclic square-root argument for arXiv:1708.00029,
Theorem 4.1. The cyclic channel selector itself is a separate obligation. -/
theorem exists_kraus_state_effect_coupling {m n : Type*}
    [Fintype m] [Fintype n]
    {ρ B : Matrix m m ℂ} {A : Matrix n n ℂ}
    (hρ : ρ.PosDef) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hTrace : A.trace = (B * ρ).trace) (hPos : 0 < A.trace.re) :
    ∃ (r : ℕ) (K : Fin r → Matrix n m ℂ),
      r + 1 ≤ A.rank + B.rank ∧
      (∑ i, K i * ρ * (K i)ᴴ) = A ∧ (∑ i, (K i)ᴴ * K i) = B := by
  classical
  let S := hρ.posSemidef.isHermitian.cfc Real.sqrt
  let T := hρ.posSemidef.supportInvSqrt
  have hS : S.IsHermitian := hρ.posSemidef.cfc_sqrt_isHermitian
  have hT : T.IsHermitian := hρ.posSemidef.supportInvSqrt_isHermitian
  have hSS : S * S = ρ := hρ.posSemidef.cfc_sqrt_mul_self
  have hST : S * T = 1 := by
    simpa only [hρ.supportProj_eq_one] using hρ.posSemidef.cfc_sqrt_mul_supportInvSqrt
  have hTS : T * S = 1 := by
    simpa only [hρ.supportProj_eq_one] using hρ.posSemidef.supportInvSqrt_mul_cfc_sqrt
  have hTρT : T * ρ * T = 1 := by
    exact hρ.posSemidef.supportInvSqrt_mul_self_mul_supportInvSqrt.trans
      hρ.supportProj_eq_one
  let D := S * B * S
  have hD : D.PosSemidef := by
    simpa only [hS.eq] using hB.conjTranspose_mul_mul_same S
  have hTraceD : D.trace = (B * ρ).trace := by
    change (S * B * S).trace = _
    rw [Matrix.trace_mul_cycle, hSS, Matrix.trace_mul_comm]
  have hTDT : T * D * T = B := by
    calc
      T * D * T = (T * S) * B * (S * T) := by simp only [D, Matrix.mul_assoc]
      _ = B := by rw [hTS, hST, Matrix.one_mul, Matrix.mul_one]
  have hRank : D.rank = B.rank := by
    apply le_antisymm
    · exact (Matrix.rank_mul_le_left (S * B) S).trans (Matrix.rank_mul_le_right S B)
    · rw [← hTDT]
      exact (Matrix.rank_mul_le_left (T * D) T).trans (Matrix.rank_mul_le_right T D)
  obtain ⟨r, L, hCard, hLeft, hRight⟩ :=
    exists_kraus_coupling_of_trace_eq hA hD (hTrace.trans hTraceD.symm) hPos
  let K : Fin r → Matrix n m ℂ := fun i => L i * T
  have hPrepared (i : Fin r) : K i * ρ * (K i)ᴴ = L i * (L i)ᴴ := by
    dsimp only [K]
    rw [Matrix.conjTranspose_mul, hT.eq]
    calc
      L i * T * ρ * (T * (L i)ᴴ) = L i * (T * ρ * T) * (L i)ᴴ := by
        simp only [Matrix.mul_assoc]
      _ = L i * (L i)ᴴ := by rw [hTρT, Matrix.mul_one]
  refine ⟨r, K, by simpa only [hRank] using hCard, ?_, ?_⟩
  · simpa only [hPrepared] using hLeft
  · calc
      ∑ i, (K i)ᴴ * K i = T * (∑ i, (L i)ᴴ * L i) * T := by
        simp only [K, Matrix.conjTranspose_mul, hT.eq, Matrix.mul_sum, Matrix.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        simp only [Matrix.mul_assoc]
      _ = B := by rw [hRight, hTDT]

end Matrix
