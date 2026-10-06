/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.Fibonacci.FibonacciNIMRepDecomposition

/-!+# Unrestricted Fibonacci actions on families of normal states

The multiplicities of a finite normal family invariant under a Fibonacci MPO algebra
are a direct sum of regular two-label actions, provided the unit fixes the family.
The number of state blocks is unrestricted and may be zero. The representatives of the
regular summands are exactly the labels with zero diagonal coefficient in the tau action.

The physical unit condition is required only at the positive length where the periodic
state vectors are linearly independent. Coefficient uniqueness derives the identity action
of the unit; it is not inferred from the fusion relation or from invariance alone.

Source: Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, lines 458--460,
564--568, and 1991--1993. The missing indecomposability hypothesis in the printed
two-block claim is corrected in `docs/paper-gaps/glm23_fibonacci_module_rank_scope.tex`.
This result concerns action multiplicities. It does not classify the L-symbols or prove
their gauge equivalence to the Fibonacci F-symbols.

**Scope restriction (periodic boundary):** the input is the periodic symmetry condition
of lines 567--568, as documented in `docs/paper-gaps/glm23_mpo_symmetric_mps_scope.tex`.
-/

open scoped Matrix

open MPSTensor MPOTensor

namespace FibonacciCompression

variable {κ : Type*} [Fintype κ] [DecidableEq κ]
  {d : ℕ} {χ : Fin 2 → ℕ} {D : κ → ℕ}

/-- Every finite unital Fibonacci-symmetric normal family is a direct sum of regular
two-label families. The physical unit condition at one independent length derives the
unit coefficient matrix, and the resulting number of blocks is even.

Source: GLM23, lines 564--568 and 1991--1993, with the direct-sum correction of
`docs/paper-gaps/glm23_fibonacci_module_rank_scope.tex`. No rank bound, nonemptiness,
symmetry of the coefficients, or indecomposability is assumed. -/
theorem exists_equiv_prod_of_isMPOSymmetricFamily_fibNim
    {O : ∀ a, MPOTensor d (χ a)} (hfus : IsMPOFusionAlgebra O fibNim)
    {A : ∀ x, MPSTensor d (D x)} {M : Fin 2 → κ → κ → ℂ}
    (hsym : IsMPOSymmetricFamily O A M)
    (hA : ∀ x, Kraus.IsNormal (A x)) (hD : ∀ x, 0 < D x)
    {L₀ : ℕ} (hL₀ : 0 < L₀)
    (hli : LinearIndependent ℂ fun x ↦ fun σ : Fin L₀ → Fin d ↦ mpv (A x) σ)
    (hunit : ∀ x, mpo (O 0) L₀ *ᵥ (fun σ : Fin L₀ → Fin d ↦ mpv (A x) σ) =
      fun σ : Fin L₀ → Fin d ↦ mpv (A x) σ) :
    Even (Fintype.card κ) ∧
      ∃ σ : κ ≃ {x // M 1 x x = 0} × Fin 2, ∀ a x y,
        M a x y = if (σ x).1 = (σ y).1 then
          (fibNim a (σ x).2 (σ y).2 : ℂ) else 0 := by
  classical
  obtain ⟨M', hMM', hM'⟩ :=
    exists_isNIMRep_of_isMPOSymmetricFamily hfus hsym hA hD hL₀ hli
  have hunit' : ∀ x y, M' 0 x y = if x = y then 1 else 0 := by
    intro x y
    have hcoeff := Fintype.linearIndependent_iffₛ.1 hli (M 0 x)
      (fun z ↦ if z = x then (1 : ℂ) else 0)
      (by rw [← hsym.mulVec_eq_sum 0 x hL₀]; simpa using hunit x) y
    rw [hMM'] at hcoeff
    by_cases hxy : x = y
    · simpa [hxy] using hcoeff
    · simpa [hxy, Ne.symm hxy] using hcoeff
  obtain ⟨σ, hσ⟩ := exists_equiv_prod_of_isNIMRep_fibNim hM' hunit'
  let e : {x // M' 1 x x = 0} ≃ {x // M 1 x x = 0} :=
    Equiv.subtypeEquivRight fun x ↦ by rw [hMM']; simp
  let σ' := σ.trans (e.prodCongr (Equiv.refl (Fin 2)))
  have hcard : Fintype.card κ =
      Fintype.card {x // M 1 x x = 0} + Fintype.card {x // M 1 x x = 0} := by
    simpa [Fintype.card_prod, Fintype.card_fin, mul_two] using Fintype.card_congr σ'
  refine ⟨⟨_, hcard⟩, σ', ?_⟩
  intro a x y
  change M a x y = if e (σ x).1 = e (σ y).1 then
    (fibNim a (σ x).2 (σ y).2 : ℂ) else 0
  rw [e.injective.eq_iff, hMM', hσ]
  split_ifs <;> simp

end FibonacciCompression
