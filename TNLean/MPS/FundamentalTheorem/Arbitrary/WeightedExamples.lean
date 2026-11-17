/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.Arbitrary.Corollaries.ClassWeights
import TNLean.MPS.FundamentalTheorem.Arbitrary.Examples

/-!
# Sharpness of the theorems on dependent states

Two examples.

**The clause on zero states.** For `A = C ⊕ C` and `B = C ⊕ (-C)` the states
`V_N(A) = 2 V_N(C)` and `V_N(B) = (1 + (-1) ^ N) V_N(C)` are dependent at every length, but
`V_N(A) = γ_N V_N(B)` fails at every odd `N`. So dependent states need not be proportional, and
dependence does not determine the factors.

**No common factor.** For `A = C ⊕ 2C ⊕ D ⊕ 8D` and `B = C ⊕ 2C ⊕ 4C ⊕ D ⊕ 4D ⊕ 16D`, with `C`, `D`
irreducible and in different classes, `(1 + 2 ^ N + 4 ^ N) V_N(A) = (1 + 2 ^ N) V_N(B)` at every
length, yet the weights do not factor through a common family: there are no multisets `U`, `U'`,
`G₁`, `G₂` with `U G₁ = {1, 2}`, `U G₂ = {1, 8}`, `U' G₁ = {1, 2, 4}`, `U' G₂ = {1, 4, 16}`.
-/

open Filter

namespace MPSTensor

namespace ArbitraryExamples

/-! ### The clause on zero states -/

/-- `A = C ⊕ C`. -/
noncomputable def depA : MPSTensor 2 (∑ _k : Fin 2, 2) :=
  toTensorFromBlocks (d := 2) (dim := fun _ => 2) ![1, 1] fun _ => propC

/-- `B = C ⊕ (-C)`. -/
noncomputable def depB : MPSTensor 2 (∑ _k : Fin 2, 2) :=
  toTensorFromBlocks (d := 2) (dim := fun _ => 2) ![1, -1] fun _ => propC

private theorem mpv_depA {N : ℕ} (σ : Fin N → Fin 2) : mpv depA σ = 2 * mpv propC σ := by
  rw [depA, mpv_toTensorFromBlocks_eq_sum, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_pow, smul_eq_mul]
  ring

private theorem mpv_depB {N : ℕ} (σ : Fin N → Fin 2) :
    mpv depB σ = (1 + (-1) ^ N) * mpv propC σ := by
  rw [depB, mpv_toTensorFromBlocks_eq_sum, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_pow, smul_eq_mul]
  ring

private theorem evalWord_propC_replicate (N : ℕ) :
    Kraus.evalWord propC (List.replicate N 0) = !![1, 2 ^ N - 1; 0, 2 ^ N] := by
  induction N with
  | zero =>
      ext i j
      fin_cases i <;> fin_cases j <;> simp
  | succ N ih =>
      rw [List.replicate_succ, Kraus.evalWord_cons, ih]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [propC, Matrix.mul_apply, Fin.sum_univ_two, pow_succ]
      all_goals ring

private theorem mpv_propC_const (N : ℕ) :
    mpv propC (fun _ : Fin N => (0 : Fin 2)) = 1 + 2 ^ N := by
  simp only [mpv_eq, coeff_eq, List.ofFn_const]
  rw [evalWord_propC_replicate]
  simp [Matrix.trace_fin_two]

/-- **Example, the clause on zero states.** `V_N(A)` and `V_N(B)` are dependent at every length, but
`V_N(A) = γ_N V_N(B)` fails at every odd `N`. -/
theorem statesDependentAt_depA_depB_and_not_exists_of_odd :
    (∀ N, StatesDependentAt depA depB N) ∧
      ∀ N, Odd N → ¬ ∃ c : ℂ, ∀ σ : Fin N → Fin 2, mpv depA σ = c * mpv depB σ := by
  constructor
  · intro N
    refine ⟨1 + (-1) ^ N, 2, Or.inr two_ne_zero, fun σ => ?_⟩
    rw [mpv_depA, mpv_depB]
    ring
  · rintro N hodd ⟨c, hc⟩
    have h1 := hc fun _ => 0
    rw [mpv_depA, mpv_depB, mpv_propC_const] at h1
    rw [hodd.neg_one_pow] at h1
    have h2 : (1 + 2 ^ N : ℂ) = ((1 + 2 ^ N : ℕ) : ℂ) := by push_cast; rfl
    have h3 : (1 + 2 ^ N : ℂ) ≠ 0 := by
      rw [h2]
      exact Nat.cast_ne_zero.2 (by positivity)
    have h4 : (2 : ℂ) * (1 + 2 ^ N) = 0 := by
      rw [h1]
      ring
    exact (mul_ne_zero two_ne_zero h3) h4

/-! ### No common factor -/

/-- The second tensor `D = ([[1, 0], [1, 1]], [[0, 1], [3, 0]])`. -/
noncomputable def propD : MPSTensor 2 2 := ![!![1, 0; 1, 1], !![0, 1; 3, 0]]

/-- `A = C ⊕ 2C ⊕ D ⊕ 8D`. -/
noncomputable def commonA : MPSTensor 2 (∑ _k : Fin 4, 2) :=
  toTensorFromBlocks (d := 2) (dim := fun _ => 2) ![1, 2, 1, 8] ![propC, propC, propD, propD]

/-- `B = C ⊕ 2C ⊕ 4C ⊕ D ⊕ 4D ⊕ 16D`. -/
noncomputable def commonB : MPSTensor 2 (∑ _k : Fin 6, 2) :=
  toTensorFromBlocks (d := 2) (dim := fun _ => 2) ![1, 2, 4, 1, 4, 16]
    ![propC, propC, propC, propD, propD, propD]

/-- A tensor on `ℂ²` is irreducible if the letters give a map `(x, y) ↦ (0, x)` and a map sending
the second basis vector to a vector with nonzero first coordinate. -/
private theorem isIrreducibleAction_of_shift {T : MPSTensor 2 2}
    (hshift : ∀ (v : Fin 2 → ℂ) (W : Submodule ℂ (Fin 2 → ℂ)),
      Matrix.IsInvariantSubmodule T W → v ∈ W → ![0, v 0] ∈ W)
    {i : Fin 2} {a b : ℂ} (ha : a ≠ 0) (hmul : (T i).mulVec ![0, 1] = ![a, b]) :
    Matrix.IsIrreducibleAction T := by
  intro W hW
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff W).1 hbot
  have he₂ : (![0, 1] : Fin 2 → ℂ) ∈ W := by
    by_cases hx : v 0 = 0
    · have hy : v 1 ≠ 0 := fun hy => hv0 (by
        ext j
        fin_cases j
        · exact hx
        · exact hy)
      have hvv : v = (v 1) • ![0, 1] := by
        ext j
        fin_cases j <;> simp [hx]
      have := W.smul_mem (v 1)⁻¹ hv
      rw [hvv, smul_smul] at this
      simpa [inv_mul_cancel₀ hy] using this
    · have h1 := hshift v W hW hv
      have hvv : ![0, v 0] = (v 0) • (![0, 1] : Fin 2 → ℂ) := by
        ext j
        fin_cases j <;> simp
      rw [hvv] at h1
      have := W.smul_mem (v 0)⁻¹ h1
      simpa [smul_smul, inv_mul_cancel₀ hx] using this
  have h2 : (![a, b] : Fin 2 → ℂ) ∈ W := hmul ▸ hW i _ he₂
  have he₁ : (![1, 0] : Fin 2 → ℂ) ∈ W := by
    have h3 := W.sub_mem h2 (W.smul_mem b he₂)
    have h4 := W.smul_mem a⁻¹ h3
    have h5 : a⁻¹ • ((![a, b] : Fin 2 → ℂ) - b • ![0, 1]) = ![1, 0] := by
      ext j
      fin_cases j <;> simp [inv_mul_cancel₀ ha]
    rwa [h5] at h4
  refine eq_top_iff.2 fun u _ => ?_
  have hu : u = u 0 • (![1, 0] : Fin 2 → ℂ) + u 1 • ![0, 1] := by
    ext j
    fin_cases j <;> simp
  rw [hu]
  exact W.add_mem (W.smul_mem _ he₁) (W.smul_mem _ he₂)

private theorem isIrreducibleAction_propC : Matrix.IsIrreducibleAction propC := by
  refine isIrreducibleAction_of_shift (i := 0) (a := 1) (b := 2) (fun v W hW hv => ?_) one_ne_zero
    (by
      ext j
      fin_cases j <;> simp [propC, Matrix.mulVec, dotProduct, Fin.sum_univ_two])
  have h := hW 1 v hv
  have he : (propC 1).mulVec v = ![0, v 0] := by
    ext j
    fin_cases j <;> simp [propC, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rwa [he] at h

private theorem isIrreducibleAction_propD : Matrix.IsIrreducibleAction propD := by
  refine isIrreducibleAction_of_shift (i := 1) (a := 1) (b := 0) (fun v W hW hv => ?_) one_ne_zero
    (by
      ext j
      fin_cases j <;> simp [propD, Matrix.mulVec, dotProduct, Fin.sum_univ_two])
  have h := W.sub_mem (hW 0 v hv) hv
  have he : (propD 0).mulVec v - v = ![0, v 0] := by
    ext j
    fin_cases j <;> simp [propD, dotProduct, Fin.sum_univ_two]
  rwa [he] at h

private theorem not_isGaugeRelated_propC_smul_propD (c : ℂ) :
    ¬ IsGaugeRelated propC (c • propD) := by
  intro h
  have h00 := h.trace_evalWord_eq [0, 0]
  have h11 := h.trace_evalWord_eq [1, 1]
  rw [trace_evalWord_smul] at h00 h11
  simp only [Kraus.evalWord_cons, Kraus.evalWord_nil, mul_one, List.length_cons, List.length_nil]
    at h00 h11
  have h11' : c = 0 := by simpa [propC, propD, Matrix.trace_fin_two] using h11
  have h00' : (1 + 2 * 2 : ℂ) = c ^ 2 * (1 + 1) := by
    simpa [propC, propD, Matrix.trace_fin_two] using h00
  rw [h11'] at h00'
  norm_num at h00'

private theorem mpv_commonA {N : ℕ} (σ : Fin N → Fin 2) :
    mpv commonA σ = (1 + 2 ^ N) * mpv propC σ + (1 + 8 ^ N) * mpv propD σ := by
  rw [commonA, mpv_toTensorFromBlocks_eq_sum, Fin.sum_univ_four]
  simp [smul_eq_mul]
  ring

private theorem mpv_commonB {N : ℕ} (σ : Fin N → Fin 2) :
    mpv commonB σ = (1 + 2 ^ N + 4 ^ N) * mpv propC σ + (1 + 4 ^ N + 16 ^ N) * mpv propD σ := by
  rw [commonB, mpv_toTensorFromBlocks_eq_sum, Fin.sum_univ_six]
  simp [smul_eq_mul]
  ring

/-- **Example, no common factor, part one.** `C`, `D` are irreducible and in different classes,
and `(1 + 2 ^ N + 4 ^ N) V_N(A) = (1 + 2 ^ N) V_N(B)`. -/
theorem commonA_commonB_proportional :
    Matrix.IsIrreducibleAction propC ∧ Matrix.IsIrreducibleAction propD ∧
      (∀ c : ℂ, ¬ IsGaugeRelated propC (c • propD)) ∧
      ∀ (N : ℕ) (σ : Fin N → Fin 2),
        (1 + 2 ^ N + 4 ^ N : ℂ) * mpv commonA σ = (1 + 2 ^ N) * mpv commonB σ := by
  refine ⟨isIrreducibleAction_propC, isIrreducibleAction_propD,
    not_isGaugeRelated_propC_smul_propD, fun N σ => ?_⟩
  rw [mpv_commonA, mpv_commonB]
  have h4 : (4 : ℂ) ^ N = (2 ^ N) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h8 : (8 : ℂ) ^ N = (2 ^ N) ^ 3 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h16 : (16 : ℂ) ^ N = (2 ^ N) ^ 4 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h4, h8, h16]
  ring

/-- **Example, no common factor, part two.** The weights of `A` and `B` do not factor through a
common family. -/
theorem not_exists_common_factor {U U' G₁ G₂ : Multiset ℂ}
    (h₁ : weightProduct U G₁ = {1, 2}) (h₂ : weightProduct U G₂ = {1, 8})
    (h₃ : weightProduct U' G₁ = {1, 2, 4}) (h₄ : weightProduct U' G₂ = {1, 4, 16}) : False := by
  have card : ∀ s t : Multiset ℂ, Multiset.card (weightProduct s t) =
      Multiset.card s * Multiset.card t := fun s t => by
    simp [weightProduct]
  have c₁ : Multiset.card U * Multiset.card G₁ = 2 := by rw [← card, h₁]; rfl
  have c₂ : Multiset.card U * Multiset.card G₂ = 2 := by rw [← card, h₂]; rfl
  have c₃ : Multiset.card U' * Multiset.card G₁ = 3 := by rw [← card, h₃]; rfl
  have c₄ : Multiset.card U' * Multiset.card G₂ = 3 := by rw [← card, h₄]; rfl
  -- `|G₁|` divides `2` and `3`, so `|G₁| = 1`; likewise `|G₂| = 1`; so `|U| = 2`.
  have hG₁ : Multiset.card G₁ = 1 := by
    have h := Nat.dvd_gcd (Dvd.intro_left _ c₁) (Dvd.intro_left _ c₃)
    exact Nat.dvd_one.1 (by simpa using h)
  have hG₂ : Multiset.card G₂ = 1 := by
    have h := Nat.dvd_gcd (Dvd.intro_left _ c₂) (Dvd.intro_left _ c₄)
    exact Nat.dvd_one.1 (by simpa using h)
  have hU : Multiset.card U = 2 := by rwa [hG₁, mul_one] at c₁
  obtain ⟨g₁, rfl⟩ := Multiset.card_eq_one.1 hG₁
  obtain ⟨g₂, rfl⟩ := Multiset.card_eq_one.1 hG₂
  obtain ⟨u, v, rfl⟩ := Multiset.card_eq_two.1 hU
  have swap : ∀ (x : ℂ) (s : Multiset ℂ), weightProduct s {x} = s.map (x * ·) := fun x s => by
    induction s using Multiset.induction_on with
    | empty => simp [weightProduct]
    | cons a s ih =>
        simp only [weightProduct] at ih ⊢
        rw [Multiset.cons_product, Multiset.map_add, ih]
        simp [mul_comm]
  rw [swap] at h₁ h₂
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton] at h₁ h₂
  -- Compare sums and products of the two pairs of weights.
  have s₁ := congrArg Multiset.sum h₁
  have s₂ := congrArg Multiset.sum h₂
  have p₁ := congrArg Multiset.prod h₁
  have p₂ := congrArg Multiset.prod h₂
  simp only [Multiset.sum_cons, Multiset.sum_singleton, Multiset.prod_cons,
    Multiset.prod_singleton] at s₁ s₂ p₁ p₂
  have key : (g₂ * u * (g₂ * v)) * (g₁ * u + g₁ * v) ^ 2 =
      (g₁ * u * (g₁ * v)) * (g₂ * u + g₂ * v) ^ 2 := by ring
  rw [s₁, s₂, p₁, p₂] at key
  norm_num at key

end ArbitraryExamples

end MPSTensor
