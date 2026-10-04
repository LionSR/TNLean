/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FiniteGroupCommutant
import TNLean.PEPS.GInjectiveMPS
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Order

/-!
# G-injective tensors spanning a matrix C*-algebra

A family of matrices spanning a unital complex matrix star-subalgebra admits
a finite unitary symmetry group for which its MPS site map is G-injective.
The group and its representation are constructed from the algebra. Invariance
follows from the commutant description. Injectivity follows from the
nondegenerate trace pairing on a star-closed matrix space.

Source: SCP10, arXiv:1001.3807, Theorem 4.1 and Definition 4.2,
`Papers/1001.3807/paper_v3.tex`, lines 852–910. This concerns the site tensor;
no parent-Hamiltonian or ground-space conclusion is asserted.

**Local fix (unital subalgebras):** The printed Theorem 4.1 uses a definition
of C*-algebra not requiring the identity, although every commutant contains
it. The algebra here is unital, as in the corrected commutant theorem.
See `docs/paper-gaps/scp10_finite_group_commutant_unital.tex`.
-/

noncomputable section
open scoped Matrix ComplexOrder

namespace TNLean.PEPS
open Representation

private theorem isGInjective_of_span_and_commutant {n ι G : Type*}
    [Fintype n] [DecidableEq n] [Group G]
    (S : StarSubalgebra ℂ (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (hspan : Submodule.span ℂ (Set.range A) = S.toSubmodule)
    (U : G →* Matrix n n ℂ)
    (hS : ∀ X, X ∈ S ↔ ∀ g, Commute X (U g)) :
    IsGInjective (linHom (Matrix.toLinAlgEquiv'.toMonoidHom.comp U)
      (Matrix.toLinAlgEquiv'.toMonoidHom.comp U))
      (mpsSiteMap (fun i => Matrix.toLin' (A i))) := by
  let E : Matrix n n ℂ ≃ₐ[ℂ] Module.End ℂ (n → ℂ) := Matrix.toLinAlgEquiv'
  let ρ := E.toMonoidHom.comp U
  have hAi (i) : A i ∈ S := by
    change A i ∈ S.toSubmodule
    rw [← hspan]
    exact Submodule.subset_span ⟨i, rfl⟩
  refine ⟨?_, ?_⟩
  · apply (mpsSiteMap_comp_linHom_eq_iff ρ _).mpr
    intro g i
    change E (U g) * E (A i) * E (U g⁻¹) = E (A i)
    rw [← map_mul, ← map_mul]
    apply congrArg E
    rw [((hS (A i)).mp (hAi i) g).eq.symm, mul_assoc, ← map_mul,
      mul_inv_cancel, map_one, mul_one]
  · intro X hX hzero
    let Y := E.symm X
    have hY : Y ∈ S := by
      apply (hS Y).mpr
      intro g
      apply (commute_map_iff E.injective).mp
      dsimp only [Y]
      rw [E.apply_symm_apply]
      change Commute X (ρ g)
      exact ((mem_invariants_linHom_iff ρ X).mp hX g).symm
    let F : Matrix n n ℂ →ₗ[ℂ] ℂ :=
      (Matrix.traceLinearMap n ℂ ℂ).comp (LinearMap.mulRight ℂ Y)
    have hker : S.toSubmodule ≤ LinearMap.ker F := by
      rw [← hspan]
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change (A i * Y).trace = 0
      have hi := congr_fun hzero i
      change LinearMap.trace ℂ (n → ℂ) (E (A i) * X) = 0 at hi
      have hEY : E Y = X := E.apply_symm_apply X
      rw [← hEY, ← map_mul] at hi
      change LinearMap.trace ℂ (n → ℂ) (Matrix.toLin' (A i * Y)) = 0 at hi
      simpa only [Matrix.trace_toLin'_eq] using hi
    have htrace : (Y.conjTranspose * Y).trace = 0 :=
      hker (S.star_mem' hY)
    have hYzero : Y = 0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp htrace
    have hEY : E Y = X := E.apply_symm_apply X
    simpa only [hEY, map_zero] using congrArg E hYzero

/-- A tensor spanning a unital matrix star-subalgebra admits a finite unitary
symmetry group for which its site map is G-injective. Source: SCP10,
Theorem 4.1 and Definition 4.2, arXiv:1001.3807, lines 852–910. -/
theorem _root_.StarSubalgebra.exists_isGInjective_mpsSiteMap_of_span
    {n ι : Type*} [Fintype n] [DecidableEq n]
    (S : StarSubalgebra ℂ (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (hspan : Submodule.span ℂ (Set.range A) = S.toSubmodule) :
    ∃ (G : Type) (_ : Group G) (_ : Finite G) (U : G →* Matrix n n ℂ),
      (∀ g, U g ∈ Matrix.unitaryGroup n ℂ) ∧
      (∀ X : Matrix n n ℂ, X ∈ S ↔ ∀ g, Commute X (U g)) ∧
      IsGInjective (linHom (Matrix.toLinAlgEquiv'.toMonoidHom.comp U)
        (Matrix.toLinAlgEquiv'.toMonoidHom.comp U))
        (mpsSiteMap (fun i => Matrix.toLin' (A i))) := by
  obtain ⟨G, hG, hfinite, U, hU, hS⟩ := S.exists_finite_unitary_group_commutant
  exact ⟨G, hG, hfinite, U, hU, hS, isGInjective_of_span_and_commutant S A hspan U hS⟩

end TNLean.PEPS
