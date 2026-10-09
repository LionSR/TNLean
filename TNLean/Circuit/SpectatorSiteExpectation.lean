/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.SiteExpectation

/-!
# Site expectations with an untouched spectator

The normalized site expectation acts on the physical matrix indices of each
spectator block. Its Weyl averaging formula tensors every physical Weyl
operator with the spectator identity. Consequently it is contractive in the
matrix `L²` operator norm, and its localization error is bounded by the sum of
physical on-site commutator bounds, independently of the spectator dimension.
No Hermiticity assumption is imposed on the operator being averaged.

The set `K` consists of the retained physical sites. Averaging over a set `Q`
of physical sites therefore means taking `K = Qᶜ`.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`09-amplification.tex`, lines 101–139, especially the averaging argument before
`eq:amplification-shell-oscillation`, at revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Independently
formalized from the manuscript; no upstream Lean proof text is reused.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open Matrix
open scoped BigOperators Kronecker Matrix.Norms.L2Operator

namespace QuantumCircuit

variable {q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Aux : Type*} [Fintype Aux] [DecidableEq Aux]

/-- Apply the native site expectation to each spectator matrix block, leaving
both spectator indices untouched. Source: area law, `09-amplification.tex`,
lines 111–121, including the sentence about operators acting on spectators. -/
noncomputable def spectatorSiteExpectation (q : ℕ) (K : Finset ι)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ :=
  Matrix.of fun x y => siteExpectation q K
    (Matrix.of fun σ τ => B (σ, x.2) (τ, y.2)) x.1 y.1

omit [Fintype Aux] [DecidableEq Aux] in
/-- On a simple tensor, only the physical factor is averaged. In particular,
this formula preserves arbitrary, possibly non-Hermitian spectator operators.
Source: area law, `09-amplification.tex`, lines 111–121. -/
theorem spectatorSiteExpectation_kronecker [NeZero q] (K : Finset ι)
    (A : Matrix (ι → Fin q) (ι → Fin q) ℂ) (S : Matrix Aux Aux ℂ) :
    spectatorSiteExpectation q K (A ⊗ₖ S) = siteExpectation q K A ⊗ₖ S := by
  ext ⟨σ, a⟩ ⟨τ, b⟩
  have hblock : (Matrix.of fun σ' τ' => (A ⊗ₖ S) (σ', a) (τ', b)) = S a b • A := by
    ext σ' τ'
    simp [Matrix.kroneckerMap_apply, mul_comm]
  change siteExpectation q K (Matrix.of fun σ' τ' => (A ⊗ₖ S) (σ', a) (τ', b)) σ τ = _
  rw [hblock, ← siteExpectationLM_apply, map_smul, siteExpectationLM_apply]
  simp [Matrix.kroneckerMap_apply, mul_comm]

omit [Fintype Aux] [DecidableEq Aux] in
/-- An operator acting only on the spectator is fixed by every physical site
expectation. Source: area law, `09-amplification.tex`, lines 111–121. -/
@[simp] theorem spectatorSiteExpectation_one_kronecker [NeZero q] (K : Finset ι)
    (S : Matrix Aux Aux ℂ) :
    spectatorSiteExpectation q K ((1 : Matrix (ι → Fin q) (ι → Fin q) ℂ) ⊗ₖ S) =
      (1 : Matrix (ι → Fin q) (ι → Fin q) ℂ) ⊗ₖ S := by
  rw [spectatorSiteExpectation_kronecker, siteExpectation_one]

private theorem kronecker_one_conjugation_apply
    (U : Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ)
    (σ τ : ι → Fin q) (a b : Aux) :
    ((U ⊗ₖ (1 : Matrix Aux Aux ℂ)) * B * (U ⊗ₖ (1 : Matrix Aux Aux ℂ))ᴴ)
        (σ, a) (τ, b) =
      (U * (Matrix.of fun σ' τ' => B (σ', a) (τ', b)) * Uᴴ) σ τ := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
    Matrix.conjTranspose_apply, Matrix.one_apply, ite_mul, apply_ite]

/-- The spectator expectation is the native outside-Weyl average amplified by
the spectator identity. Source: area law, `09-amplification.tex`, lines 113–121. -/
theorem spectatorSiteExpectation_eq_average [NeZero q] (K : Finset ι)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    spectatorSiteExpectation q K B =
      ((q : ℂ) ^ (2 * Fintype.card ι))⁻¹ •
        ∑ p : ι → ZMod q × ZMod q,
          (outsideWeyl q K p ⊗ₖ (1 : Matrix Aux Aux ℂ)) * B *
            (outsideWeyl q K p ⊗ₖ (1 : Matrix Aux Aux ℂ))ᴴ := by
  ext ⟨σ, a⟩ ⟨τ, b⟩
  simp only [spectatorSiteExpectation, Matrix.of_apply, siteExpectation_eq_average,
    Matrix.smul_apply, Matrix.sum_apply, kronecker_one_conjugation_apply]

/-- The averaged operator commutes with every physical operator supported
outside `K`, with the spectator left untouched. Source: area law,
`09-amplification.tex`, lines 113–121 (the result commutes with the algebra on
the averaged set). -/
theorem spectatorSiteExpectation_commute (K : Finset ι)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ)
    {U : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hU : U ∈ supportedOperators q ((K : Set ι)ᶜ)) :
    Commute (spectatorSiteExpectation q K B) (U ⊗ₖ (1 : Matrix Aux Aux ℂ)) := by
  change spectatorSiteExpectation q K B * (U ⊗ₖ (1 : Matrix Aux Aux ℂ)) =
    (U ⊗ₖ (1 : Matrix Aux Aux ℂ)) * spectatorSiteExpectation q K B
  ext ⟨σ, a⟩ ⟨τ, b⟩
  have h := congrArg (fun M : Matrix (ι → Fin q) (ι → Fin q) ℂ => M σ τ)
    (commute_of_mem_supportedOperators disjoint_compl_right
      (siteExpectation_mem_supportedOperators K
        (Matrix.of fun σ' τ' => B (σ', a) (τ', b))) hU).eq
  simpa [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
    Matrix.one_apply, mul_ite, ite_mul, spectatorSiteExpectation] using h

omit [Fintype Aux] [DecidableEq Aux] in
/-- Retaining every physical site gives the identity map, even in the presence
of a spectator. Source: area law, `09-amplification.tex`, lines 101 and 111–121. -/
@[simp] theorem spectatorSiteExpectation_univ [NeZero q]
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    spectatorSiteExpectation q Finset.univ B = B := by
  ext ⟨σ, a⟩ ⟨τ, b⟩
  change siteExpectation q Finset.univ (Matrix.of fun σ' τ' => B (σ', a) (τ', b)) σ τ = _
  rw [siteExpectation_of_mem_supportedOperators _ (by
    simpa using mem_supportedOperators_univ (Matrix.of fun σ' τ' => B (σ', a) (τ', b)))]
  rfl

private theorem norm_weyl_average_le [NeZero q]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : (ι → ZMod q × ZMod q) → E) (r : ℝ) (hf : ∀ p, ‖f p‖ ≤ r) :
    ‖((q : ℂ) ^ (2 * Fintype.card ι))⁻¹ • ∑ p, f p‖ ≤ r := by
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hN : ((q : ℂ) ^ (2 * Fintype.card ι))⁻¹ *
      (Fintype.card (ι → ZMod q × ZMod q) : ℂ) = 1 := by
    rw [card_weylLabels, inv_mul_cancel₀ (pow_ne_zero _ hq)]
  have hNr := congrArg norm hN
  rw [norm_mul, norm_one, Complex.norm_natCast] at hNr
  rw [norm_smul]
  calc
    _ ≤ ‖((q : ℂ) ^ (2 * Fintype.card ι))⁻¹‖ * ∑ _p : ι → ZMod q × ZMod q, r :=
      mul_le_mul_of_nonneg_left
        ((norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => hf p)) (norm_nonneg _)
    _ = r := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, hNr, one_mul]

/-- The site expectation is a contraction after tensoring with the identity on
any finite spectator. Source: area law, `09-amplification.tex`, lines 111–121.
The norm is the matrix `L²` operator norm. -/
theorem norm_spectatorSiteExpectation_le [NeZero q] (K : Finset ι)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    ‖spectatorSiteExpectation q K B‖ ≤ ‖B‖ := by
  rw [spectatorSiteExpectation_eq_average]
  refine norm_weyl_average_le _ _ fun p => le_of_eq ?_
  have hU := Matrix.kronecker_mem_unitary (outsideWeyl_mem_unitary K p)
    (show (1 : Matrix Aux Aux ℂ) ∈ unitary (Matrix Aux Aux ℂ) from one_mem _)
  rw [← star_eq_conjTranspose, CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hU),
    CStarRing.norm_mem_unitary_mul _ hU]

private theorem norm_commutator_partialWeyl_kronecker_one_le [NeZero q]
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ)
    (ε : ι → ℝ) (p : ι → ZMod q × ZMod q) (S : Finset ι)
    (hε : ∀ y ∈ S, ∀ U ∈ supportedOperators q ({y} : Set ι),
      U ∈ unitary (Matrix (ι → Fin q) (ι → Fin q) ℂ) →
        ‖B * (U ⊗ₖ (1 : Matrix Aux Aux ℂ)) - (U ⊗ₖ (1 : Matrix Aux Aux ℂ)) * B‖ ≤ ε y) :
    ‖B * (partialWeyl S p ⊗ₖ (1 : Matrix Aux Aux ℂ)) -
        (partialWeyl S p ⊗ₖ (1 : Matrix Aux Aux ℂ)) * B‖ ≤ ∑ y ∈ S, ε y := by
  induction S using Finset.induction_on with
  | empty => simp [partialWeyl]
  | insert y S hy ih =>
    have hprod : partialWeyl (insert y S) p ⊗ₖ (1 : Matrix Aux Aux ℂ) =
        (partialWeyl {y} p ⊗ₖ (1 : Matrix Aux Aux ℂ)) *
          (partialWeyl S p ⊗ₖ (1 : Matrix Aux Aux ℂ)) := by
      rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, partialWeyl_insert hy]
    rw [hprod, Finset.sum_insert hy]
    refine (norm_commutator_mul_le B _ _
      (Matrix.kronecker_mem_unitary (partialWeyl_mem_unitary _ p) (one_mem _))
      (Matrix.kronecker_mem_unitary (partialWeyl_mem_unitary _ p) (one_mem _))).trans
        (add_le_add ?_ ?_)
    · exact hε y (Finset.mem_insert_self y S) _ (partialWeyl_singleton_mem y p)
        (partialWeyl_mem_unitary _ p)
    · exact ih fun z hz => hε z (Finset.mem_insert_of_mem hz)

/-- Averaging outside `K` changes an arbitrary operator by at most the sum of
its physical on-site commutator bounds. Every test unitary acts as the identity
on the spectator, and the estimate has no spectator dimension factor. Source:
area law, `09-amplification.tex`, lines 111–121, the averaging argument before
`eq:amplification-shell-oscillation`. -/
theorem norm_sub_spectatorSiteExpectation_le [NeZero q] (K : Finset ι)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) (ε : ι → ℝ)
    (hε : ∀ y ∉ K, ∀ U ∈ supportedOperators q ({y} : Set ι),
      U ∈ unitary (Matrix (ι → Fin q) (ι → Fin q) ℂ) →
        ‖B * (U ⊗ₖ (1 : Matrix Aux Aux ℂ)) - (U ⊗ₖ (1 : Matrix Aux Aux ℂ)) * B‖ ≤ ε y) :
    ‖B - spectatorSiteExpectation q K B‖ ≤ ∑ y ∈ Kᶜ, ε y := by
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  set c : ℂ := ((q : ℂ) ^ (2 * Fintype.card ι))⁻¹ with hc
  have hN : c * (Fintype.card (ι → ZMod q × ZMod q) : ℂ) = 1 := by
    rw [card_weylLabels, hc, inv_mul_cancel₀ (pow_ne_zero _ hq)]
  have hB : B = c • ∑ _p : ι → ZMod q × ZMod q, B := by
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, hN,
      one_smul]
  have hdiff : B - spectatorSiteExpectation q K B =
      c • ∑ p : ι → ZMod q × ZMod q,
        (B - (outsideWeyl q K p ⊗ₖ (1 : Matrix Aux Aux ℂ)) * B *
          (outsideWeyl q K p ⊗ₖ (1 : Matrix Aux Aux ℂ))ᴴ) := by
    rw [Finset.sum_sub_distrib, smul_sub, ← hB, spectatorSiteExpectation_eq_average]
  rw [hdiff]
  refine norm_weyl_average_le _ _ fun p => ?_
  let U := outsideWeyl q K p ⊗ₖ (1 : Matrix Aux Aux ℂ)
  have hU : U ∈ unitary (Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :=
    Matrix.kronecker_mem_unitary (outsideWeyl_mem_unitary K p) (one_mem _)
  have heq : B - U * B * Uᴴ = (B * U - U * B) * Uᴴ := by
    rw [sub_mul, ← star_eq_conjTranspose, mul_assoc B,
      Unitary.mul_star_self_of_mem hU, mul_one]
  change ‖B - U * B * Uᴴ‖ ≤ _
  rw [heq, ← star_eq_conjTranspose, CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hU)]
  dsimp only [U]
  rw [outsideWeyl_eq_partialWeyl]
  exact norm_commutator_partialWeyl_kronecker_one_le B ε p Kᶜ fun y hy =>
    hε y (Finset.mem_compl.mp hy)

end QuantumCircuit
