/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.GHZSectors
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.RepeatedBlock
import TNLean.MPS.Examples.GHZ
import TNLean.MPS.Overlap.Basic

/-!
# GHZ and product states from upper-triangular tensors

For positive chain length, `ghzB` generates the unnormalized GHZ state
$|0\cdots0\rangle+|1\cdots1\rangle$, represented by the standard `ghzTensor`.
The tensor `repB` generates $2(|0\rangle+2|1\rangle)^{\otimes N}$ at every length.
These identifications use the proved word-trace identities of the two examples.

The state conventions are those of arXiv:2011.12127, Appendix A, product states
and the GHZ state: a bond-one tensor multiplies local amplitudes, and the GHZ
matrices have entries $A^i_{\alpha\beta}=\delta_{i=\alpha=\beta}$.
The upper-triangular source tensors are the explicit examples of
`Notes/OpenProblemsTN/strategies/p5_asymmetric_compression_theorem.tex`,
not additional models from the review.

At length zero, `ghzB` has amplitude four, whereas `ghzTensor` has amplitude two.
Thus their equality is restricted to positive length. The factor two for `repB`
already agrees with its empty-word trace.
-/

open scoped Matrix BigOperators

namespace MPSTensor

private theorem scalar_mpv_product (A : MPSTensor 2 1) {N : ℕ}
    (σ : Fin N → Fin 2) : mpv A σ = ∏ n, A (σ n) 0 0 := by
  have h : ∀ {N : ℕ} (σ : Fin N → Fin 2),
      Kraus.evalWord A (List.ofFn σ) 0 0 = ∏ n, A (σ n) 0 0 := by
    intro N σ
    induction N with
    | zero => simp
    | succ N ih =>
      simp [List.ofFn_succ, Kraus.evalWord_cons, Matrix.mul_apply,
        Fin.prod_univ_succ, ih]
  simpa [mpv, coeff, Matrix.trace] using h σ

/-- Each scalar GHZ block is the corresponding standard GHZ sector. -/
theorem ghzC_eq_ghzSectorTensor (x : Fin 2) : ghzC x = ghzSectorTensor x := by
  funext i
  ext a b
  fin_cases x <;> fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [ghzC, ghzSectorTensor]

/-- A GHZ sector has amplitude one exactly on its constant configuration. -/
theorem ghzC_mpv {N : ℕ} (x : Fin 2) (σ : Fin N → Fin 2) :
    mpv (ghzC x) σ = if ∀ n, σ n = x then 1 else 0 := by
  classical
  rw [scalar_mpv_product, ghzC_eq_ghzSectorTensor]
  simp only [ghzSectorTensor, Matrix.ite_apply, Matrix.one_apply_eq, Matrix.zero_apply]
  rw [Fintype.prod_boole]
  split_ifs <;> rfl

/-- The standard GHZ tensor has the sum of the two constant-configuration amplitudes. -/
theorem ghzTensor_mpv {N : ℕ} (σ : Fin N → Fin 2) :
    mpv ghzTensor σ = (if ∀ n, σ n = 0 then 1 else 0) +
      (if ∀ n, σ n = 1 then 1 else 0) := by
  classical
  have h : ∀ {N : ℕ} (σ : Fin N → Fin 2),
      Kraus.evalWord ghzTensor (List.ofFn σ) =
        Matrix.diagonal (fun x => ∏ n, if σ n = x then (1 : ℂ) else 0) := by
    intro N σ
    induction N with
    | zero => simp [Matrix.diagonal_one]
    | succ N ih =>
      rw [List.ofFn_succ, Kraus.evalWord_cons, ghzTensor_apply, ih,
        Matrix.diagonal_mul_diagonal]
      congr 1
      funext x
      simp [Fin.prod_univ_succ, Pi.single_apply, eq_comm]
  rw [mpv, coeff, h, Matrix.trace_diagonal]
  simp only [Fin.sum_univ_two, Fintype.prod_boole]
  split_ifs <;> rfl

/-- For $N>0$, the source amplitude is $\delta_{\sigma=0}+\delta_{\sigma=1}$. -/
theorem ghzB_mpv {N : ℕ} (hN : 0 < N) (σ : Fin N → Fin 2) :
    mpv ghzB σ = (if ∀ n, σ n = 0 then 1 else 0) +
      (if ∀ n, σ n = 1 then 1 else 0) := by
  have h := ghzSectors_compression.mpv_eq_sum N hN σ
  simp only [Fin.sum_univ_two] at h
  rw [h, ghzC_mpv, ghzC_mpv]

/-- The source and the standard GHZ tensor generate the same positive-length states. -/
theorem ghzB_sameMPV₂Pos_ghzTensor : SameMPV₂Pos ghzB ghzTensor := by
  intro N hN σ
  rw [ghzB_mpv hN, ghzTensor_mpv]

/-- The positive-length GHZ identification is an equality of Hilbert-space vectors. -/
theorem ghzB_mpvState_eq {N : ℕ} (hN : 0 < N) :
    mpvState ghzB N = mpvState ghzTensor N := by
  ext σ
  exact ghzB_sameMPV₂Pos_ghzTensor N hN σ

/-- The GHZ source and target differ at the empty word, with traces four and two. -/
theorem ghzB_not_sameMPV₂_ghzTensor : ¬ SameMPV₂ ghzB ghzTensor := by
  intro h
  have h0 := h 0 Fin.elim0
  norm_num at h0

/-- The scalar tensor `repA` generates $(|0\rangle+2|1\rangle)^{\otimes N}$. -/
theorem repA_mpv {N : ℕ} (σ : Fin N → Fin 2) :
    mpv repA σ = ∏ n, (![1, 2] : Fin 2 → ℂ) (σ n) := by
  rw [scalar_mpv_product]
  apply Finset.prod_congr rfl
  intro n _
  have hi : σ n = 0 ∨ σ n = 1 := by omega
  rcases hi with hi | hi <;> simp [hi, repA]

/-- The repeated source has twice the scalar target amplitude, including at length zero. -/
theorem repB_mpv_eq_two_mul {N : ℕ} (σ : Fin N → Fin 2) :
    mpv repB σ = 2 * mpv repA σ := by
  by_cases hN : N = 0
  · subst N
    simp
  · have hw : List.ofFn σ ≠ [] := by
      intro h
      have := congrArg List.length h
      simp only [List.length_ofFn, List.length_nil] at this
      exact hN this
    exact repB_trace_evalWord_eq_two_mul (List.ofFn σ) hw

/-- The amplitude of `repB` is twice the product of the local amplitudes $(1,2)$. -/
theorem repB_mpv {N : ℕ} (σ : Fin N → Fin 2) :
    mpv repB σ = 2 * ∏ n, (![1, 2] : Fin 2 → ℂ) (σ n) := by
  rw [repB_mpv_eq_two_mul, repA_mpv]

/-- The repeated source state is twice the bond-one product state at every length. -/
theorem repB_mpvState_eq (N : ℕ) : mpvState repB N = (2 : ℂ) • mpvState repA N := by
  ext σ
  simpa using repB_mpv_eq_two_mul σ

/-- The unnormalized GHZ source state has squared norm two at every positive length. -/
theorem ghzB_mpvState_norm_sq {N : ℕ} (hN : 0 < N) :
    ‖mpvState ghzB N‖ ^ 2 = 2 := by
  classical
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  rw [EuclideanSpace.norm_sq_eq]
  have hterm (σ : Fin N → Fin 2) :
      ‖mpvState ghzB N σ‖ ^ 2 =
        (if σ = fun _ => 0 then (1 : ℝ) else 0) +
        (if σ = fun _ => 1 then (1 : ℝ) else 0) := by
    rw [mpvState_apply, ghzB_mpv hN]
    by_cases h0 : ∀ n, σ n = 0
    · simp [funext_iff, h0]
    · by_cases h1 : ∀ n, σ n = 1 <;> simp [funext_iff, h0, h1]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  norm_num

/-- The bond-one state with local amplitudes $(1,2)$ has squared norm $5^N$. -/
theorem repA_mpvState_norm_sq (N : ℕ) : ‖mpvState repA N‖ ^ 2 = 5 ^ N := by
  classical
  rw [EuclideanSpace.norm_sq_eq]
  simp_rw [mpvState_apply, repA_mpv, norm_prod, ← Finset.prod_pow]
  rw [← Fintype.prod_sum (fun (_ : Fin N) (i : Fin 2) =>
    ‖(![1, 2] : Fin 2 → ℂ) i‖ ^ 2)]
  norm_num [Fin.sum_univ_two]

/-- The repeated source state has squared norm $4\,5^N$, also at length zero. -/
theorem repB_mpvState_norm_sq (N : ℕ) : ‖mpvState repB N‖ ^ 2 = 4 * 5 ^ N := by
  rw [repB_mpvState_eq, norm_smul, mul_pow, repA_mpvState_norm_sq]
  norm_num

end MPSTensor
