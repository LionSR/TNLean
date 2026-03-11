/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TNLean.Wielandt.PrimitivePaper
import TNLean.Wielandt.PrimitivityNormal

/-!
# Proposition 3, direction (a) → (c): Primitivity implies strong irreducibility

This file develops helper lemmas toward the (a)→(c) direction of Proposition 3
from arXiv:0909.5347: **IsPrimitivePaper A → IsStronglyIrreduciblePaper A**.

## Proof strategy (following Wolf Ch6 / arXiv:0909.5347)

1. **Sandwich identity** (`sandwich_vecMulVec`): `M * |φ⟩⟨φ| * M† = |Mφ⟩⟨Mφ|`.
2. **Transfer map on rank-one** (`transferMap_pow_rankOne_eq_sum`): Expands
   `E^q(|φ⟩⟨φ|)` as `Σ_σ |ψ_σ⟩⟨ψ_σ|`.
3. **Spanning implies PosDef** (`posDef_sum_vecMulVec_of_span_eq_top`):
   If vectors `{v_i}` span `ℂ^D`, then `Σ |v_i⟩⟨v_i|` is positive definite.
4. **E^q on rank-one is PosDef** (`transferMap_pow_rankOne_posDef`):
   Combines the above to show `E^q(|φ⟩⟨φ|)` is PosDef under primitivity.

## References

- [Sanz, Pérez-García, Wolf, Cirac, arXiv:0909.5347], Proposition 3
- Wolf, *Quantum Channels & Operations: Guided Tour*, §6.4
-/

open scoped Matrix ComplexOrder BigOperators
open Matrix MPSTensor Module

namespace MPSTensor

variable {d D : ℕ}

/-! ## Part 1: Sandwich identity for rank-one matrices -/

/-- **Sandwich identity for rank-one matrices.**
`M * vecMulVec φ (star φ) * M† = vecMulVec (M *ᵥ φ) (star (M *ᵥ φ))` -/
theorem sandwich_vecMulVec
    (M : Matrix (Fin D) (Fin D) ℂ) (φ : Fin D → ℂ) :
    M * vecMulVec φ (star φ) * Mᴴ =
      vecMulVec (M *ᵥ φ) (star (M *ᵥ φ)) := by
  rw [Matrix.mul_assoc, vecMulVec_mul, ← star_mulVec M φ, mul_vecMulVec]

/-! ## Part 2: Transfer map on rank-one matrices -/

/-- **Transfer map power on rank-one matrices.**
`E^q(|φ⟩⟨φ|) = Σ_σ |ψ_σ⟩⟨ψ_σ|` where `ψ_σ = evalWord A (List.ofFn σ) *ᵥ φ`. -/
theorem transferMap_pow_rankOne_eq_sum
    (A : MPSTensor d D) (q : ℕ) (φ : Fin D → ℂ) :
    ((transferMap (d := d) (D := D) A) ^ q) (vecMulVec φ (star φ)) =
      ∑ σ : Fin q → Fin d,
        vecMulVec (evalWord A (List.ofFn σ) *ᵥ φ)
          (star (evalWord A (List.ofFn σ) *ᵥ φ)) := by
  rw [transferMap_pow_apply_eq_sum]
  congr 1; ext σ : 1
  exact sandwich_vecMulVec (evalWord A (List.ofFn σ)) φ

/-! ## Part 3: Spanning vectors give PosDef sum of outer products -/

/-- **Sum of outer products from a spanning set is positive definite.**

If the vectors `{v i}` span all of `Fin D → ℂ`, then `Σ |v i⟩⟨v i|` is PosDef.
The proof uses: `⟨x, (Σ |vᵢ⟩⟨vᵢ|)x⟩ = Σ |⟨vᵢ, x⟩|²`, which is positive
when x ≠ 0 since {vᵢ} spans. -/
theorem posDef_sum_vecMulVec_of_span_eq_top {ι : Type*} [Fintype ι]
    (v : ι → (Fin D → ℂ))
    (hspan : Submodule.span ℂ (Set.range v) = ⊤) :
    (∑ i : ι, vecMulVec (v i) (star (v i))).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · -- Hermitian: (vv†)† = vv†
    change (∑ i : ι, vecMulVec (v i) (star (v i))).IsHermitian
    change (∑ i : ι, vecMulVec (v i) (star (v i)))ᴴ = _
    simp only [conjTranspose_sum, conjTranspose_vecMulVec, star_star]
  · -- Positive definite: ⟨x, Mx⟩ > 0 for x ≠ 0
    intro x hx
    -- Expand: star x ⬝ᵥ (Σ vv† *ᵥ x) = Σ (star x ⬝ᵥ (vv† *ᵥ x))
    simp only [Matrix.sum_mulVec, dotProduct_sum, vecMulVec_mulVec]
    -- Each term: star x ⬝ᵥ (op(star v ⬝ᵥ x) • v) = (star v ⬝ᵥ x) * (star x ⬝ᵥ v)
    -- We'll show each is = ↑(‖star x ⬝ᵥ v i‖²) and the sum is positive
    -- Step 1: Show the sum is a real number ≥ 0, cast to ℂ
    suffices h : (0 : ℝ) < ∑ i : ι, ‖star x ⬝ᵥ v i‖ ^ 2 by
      have heq : ∑ i : ι, star x ⬝ᵥ (MulOpposite.op (star (v i) ⬝ᵥ x) • v i) =
          ↑(∑ i : ι, ‖star x ⬝ᵥ v i‖ ^ 2) := by
        push_cast
        congr 1; ext i
        -- Goal: star x ⬝ᵥ (op(star v ⬝ᵥ x) • v) = ↑‖star x ⬝ᵥ v‖²
        -- Simplify MulOpposite scalar action to multiplication
        change star x ⬝ᵥ (MulOpposite.op (star (v i) ⬝ᵥ x) • v i) = _
        rw [show MulOpposite.op (star (v i) ⬝ᵥ x) • v i =
            (star (v i) ⬝ᵥ x) • v i from by
          ext j; simp [MulOpposite.smul_eq_mul_unop, mul_comm]]
        rw [dotProduct_smul, smul_eq_mul]
        have hconj : star (v i) ⬝ᵥ x = starRingEnd ℂ (star x ⬝ᵥ v i) := by
          simp [dotProduct, map_sum, mul_comm]
        rw [hconj, mul_comm, Complex.mul_conj, ← Complex.sq_norm]
        push_cast; rfl
      rw [heq]
      exact_mod_cast h
    -- Step 2: Show the real sum is positive
    apply Finset.sum_pos'
    · intro i _; positivity
    · -- There exists i with ⟨v i, x⟩ ≠ 0
      by_contra hall
      push_neg at hall
      have horth : ∀ i, star x ⬝ᵥ v i = 0 := by
        intro i
        have h1 := hall i (Finset.mem_univ i)
        have h2 : (0 : ℝ) ≤ ‖star x ⬝ᵥ v i‖ ^ 2 := sq_nonneg _
        have h3 : ‖star x ⬝ᵥ v i‖ ^ 2 = 0 := le_antisymm h1 h2
        rwa [sq_eq_zero_iff, norm_eq_zero] at h3
      -- x is orthogonal to span of {v i}
      have horth_span : ∀ w ∈ Submodule.span ℂ (Set.range v), star x ⬝ᵥ w = 0 := by
        intro w hw
        induction hw using Submodule.span_induction with
        | mem w hw =>
          obtain ⟨i, rfl⟩ := hw; exact horth i
        | zero => simp
        | add w₁ w₂ _ _ h₁ h₂ => rw [dotProduct_add, h₁, h₂, add_zero]
        | smul c w₁ _ hw₁ => rw [dotProduct_smul, hw₁, smul_zero]
      -- star x ⬝ᵥ x = 0
      have hxx : star x ⬝ᵥ x = 0 := horth_span x (hspan ▸ Submodule.mem_top)
      -- But star x ⬝ᵥ x = Σ |x_j|² > 0 for x ≠ 0
      have hxx_real : star x ⬝ᵥ x = ↑(∑ j : Fin D, Complex.normSq (x j)) := by
        simp only [dotProduct, Pi.star_apply]
        push_cast
        congr 1; ext j
        rw [show star (x j) * x j = x j * starRingEnd ℂ (x j) from by
          simp [mul_comm]]
        rw [Complex.mul_conj]
      rw [hxx_real] at hxx
      have hne : ∃ j, x j ≠ 0 := by
        by_contra h; push_neg at h; exact hx (funext h)
      obtain ⟨j, hj⟩ := hne
      have hpos : (0 : ℝ) < ∑ k : Fin D, Complex.normSq (x k) :=
        Finset.sum_pos' (fun k _ => Complex.normSq_nonneg _)
          ⟨j, Finset.mem_univ _, Complex.normSq_pos.mpr hj⟩
      exact absurd (Complex.ofReal_eq_zero.mp hxx) (ne_of_gt hpos)

/-! ## Part 4: Transfer map on rank-one is PosDef under primitivity -/

/-- **Under paper-primitivity, `E^q(|φ⟩⟨φ|)` is positive definite.**

Paper: This is the "positivity improving" property — the key step in
Proposition 3's proof of (a)⟹(c). -/
theorem transferMap_pow_rankOne_posDef
    (A : MPSTensor d D) {q : ℕ}
    (hq : ∀ φ : Fin D → ℂ, φ ≠ 0 → vectorSpreadSpan A φ q = ⊤)
    (φ : Fin D → ℂ) (hφ : φ ≠ 0) :
    (((transferMap (d := d) (D := D) A) ^ q) (vecMulVec φ (star φ))).PosDef := by
  rw [transferMap_pow_rankOne_eq_sum]
  apply posDef_sum_vecMulVec_of_span_eq_top
  have h := hq φ hφ
  rwa [vectorSpreadSpan] at h

end MPSTensor
