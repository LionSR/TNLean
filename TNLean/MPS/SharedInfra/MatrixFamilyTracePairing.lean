/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixTracePairing
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Trace duality for finite families of virtual matrices

Every linear functional on a finite product of complex matrix algebras has the form
\(M\mapsto\sum_j\operatorname{tr}(\Delta_jM_j)\).
Consequently, a subspace is the full product algebra if the only family whose trace pairing
vanishes on that subspace is the zero family. These facts apply to simultaneous word spans
and to the diagonal virtual boundaries of a direct sum of tensor blocks.
-/

open scoped Matrix BigOperators

namespace Matrix

/-- Every linear functional on a finite matrix algebra is the trace pairing against a matrix:
\(f(M)=\operatorname{tr}(\Delta M)\). -/
theorem exists_trace_representation {n : Type*} [Fintype n]
    (f : Matrix n n ℂ →ₗ[ℂ] ℂ) :
    ∃ Δ : Matrix n n ℂ, ∀ M : Matrix n n ℂ, f M = Matrix.trace (Δ * M) := by
  refine ⟨((Matrix.traceBilinForm n).toDual Matrix.traceBilinForm_nondegenerate).symm f,
    fun M ↦ ?_⟩
  rw [← Matrix.traceBilinForm_apply, LinearMap.BilinForm.apply_toDual_symm_apply]

variable {r : ℕ} {dim : Fin r → ℕ}

/-- A linear functional on a finite family of virtual matrix algebras is a sum of trace pairings:
\(f(M)=\sum_j\operatorname{tr}(\Delta_jM_j)\). -/
theorem exists_family_trace_representation
    (f : ((k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ) →ₗ[ℂ] ℂ) :
    ∃ Δ : (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ,
      ∀ M : (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ,
        f M = ∑ k : Fin r, Matrix.trace (Δ k * M k) := by
  classical
  choose Δ hΔ using fun k : Fin r ↦ exists_trace_representation
    (f.comp (LinearMap.single ℂ
      (fun j : Fin r ↦ Matrix (Fin (dim j)) (Fin (dim j)) ℂ) k))
  refine ⟨Δ, fun M ↦ ?_⟩
  conv_lhs => rw [← Finset.univ_sum_single M]
  rw [map_sum]
  exact Finset.sum_congr rfl fun k _ ↦ by simpa using hΔ k (M k)

/-- A subspace of a finite product of matrix algebras is everything if its annihilator under
\(\sum_j\operatorname{tr}(\Delta_jM_j)\) is zero. -/
theorem family_submodule_eq_top_of_trace_separating
    (W : Submodule ℂ
      ((k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ))
    (hSep : ∀ Δ : (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ,
      (∀ M ∈ W, (∑ k : Fin r, Matrix.trace (Δ k * M k)) = 0) →
        ∀ k, Δ k = 0) :
    W = ⊤ := by
  classical
  by_contra hnot
  have hlt : W < ⊤ := lt_of_le_of_ne le_top hnot
  obtain ⟨f, hfne, hfker⟩ := Submodule.exists_le_ker_of_lt_top W hlt
  obtain ⟨Δ, hf_repr⟩ := exists_family_trace_representation f
  have hΔ : ∀ k, Δ k = 0 := by
    refine hSep Δ ?_
    intro M hM
    have hf0 : f M = 0 := hfker hM
    simpa [hf_repr] using hf0
  have hfzero : f = 0 := by
    apply LinearMap.ext
    intro M
    have hM := hf_repr M
    have hΔzero : Δ = 0 := funext hΔ
    rw [hΔzero] at hM
    simpa using hM
  exact hfne hfzero

end Matrix
