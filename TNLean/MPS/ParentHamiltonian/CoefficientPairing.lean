/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.GroundSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# The \(\ell^2\) pairing of coefficient vectors

A vector of the \(N\)-site space is a function on configurations. Transported to the
\(\ell^2\) space of the same functions, the inner product of two vectors is the sum
over configurations of \(\overline{f(\sigma)}\,g(\sigma)\). Precomposing
configurations with a transposition of two sites permutes the configurations, so it
leaves such sums unchanged and moves from one argument of the pairing to the other.

An operator on the coefficient vectors whose transport to the \(\ell^2\) space is
positive has only nonnegative eigenvalues.

## Main results
* `MPSTensor.sum_cfg_comp_swap`
* `MPSTensor.inner_withLpLinearEquiv_symm`
* `MPSTensor.sum_conj_mul_comp_swap`
* `LinearMap.IsPositive.nonneg_of_apply_eq_smul`
* `MPSTensor.nonneg_of_hasEigenvalue_of_isPositive_conj`
-/

open scoped InnerProductSpace ComplexConjugate ComplexOrder

namespace LinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The eigenvalue of a positive operator for a nonzero eigenvector is nonnegative. -/
theorem IsPositive.nonneg_of_apply_eq_smul {T : E →ₗ[ℂ] E} (hT : T.IsPositive) {v : E}
    (hv : v ≠ 0) {μ : ℂ} (h : T v = μ • v) : 0 ≤ μ := by
  have hnn := hT.inner_nonneg_right v
  rw [h, inner_smul_right, inner_self_eq_norm_sq_to_K] at hnn
  have hr : (0 : ℂ) < ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    exact_mod_cast (show (0 : ℝ) < ‖v‖ ^ 2 by positivity)
  have hμ : μ = μ * ((‖v‖ ^ 2 : ℝ) : ℂ) * ((‖v‖ ^ 2 : ℝ) : ℂ)⁻¹ := by
    rw [mul_assoc, mul_inv_cancel₀ hr.ne', mul_one]
  rw [hμ]
  exact mul_nonneg (by exact_mod_cast hnn) (inv_nonneg.2 hr.le)

end LinearMap

namespace MPSTensor

variable {d L : ℕ}

/-- Precomposing configurations with a transposition of two sites permutes the
configurations, so it leaves sums over all configurations unchanged. -/
theorem sum_cfg_comp_swap {M : Type*} [AddCommMonoid M] (f : Cfg d L → M) (a b : Fin L) :
    ∑ σ : Cfg d L, f (σ ∘ Equiv.swap a b) = ∑ σ, f σ :=
  Fintype.sum_equiv ((Equiv.swap a b).arrowCongr (Equiv.refl _)) _ _ fun _ => rfl

/-- The inner product of two coefficient vectors transported to the \(\ell^2\) space
is the sum over configurations of \(\overline{f(\sigma)}\,g(\sigma)\). -/
theorem inner_withLpLinearEquiv_symm (f g : NSiteSpace d L) :
    ⟪(WithLp.linearEquiv 2 ℂ (NSiteSpace d L)).symm f,
        (WithLp.linearEquiv 2 ℂ (NSiteSpace d L)).symm g⟫_ℂ =
      ∑ σ, conj (f σ) * g σ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- Moving one transposition of sites from the right to the left argument of the
\(\ell^2\) pairing of coefficient vectors. -/
theorem sum_conj_mul_comp_swap (f g : NSiteSpace d L) (a b : Fin L) :
    ∑ σ, conj (f σ) * g (σ ∘ Equiv.swap a b) =
      ∑ σ, conj (f (σ ∘ Equiv.swap a b)) * g σ := by
  rw [← sum_cfg_comp_swap (fun σ => conj (f σ) * g (σ ∘ Equiv.swap a b)) a b]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp [Function.comp_def, Equiv.swap_apply_self]

/-- An operator on coefficient vectors whose transport to the \(\ell^2\) space is
positive has only nonnegative eigenvalues. -/
theorem nonneg_of_hasEigenvalue_of_isPositive_conj {T : NSiteSpace d L →ₗ[ℂ] NSiteSpace d L}
    (hT : ((WithLp.linearEquiv 2 ℂ (NSiteSpace d L)).symm.toLinearMap ∘ₗ T ∘ₗ
      (WithLp.linearEquiv 2 ℂ (NSiteSpace d L)).toLinearMap).IsPositive)
    {μ : ℂ} (hμ : Module.End.HasEigenvalue T μ) : 0 ≤ μ := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  set e := WithLp.linearEquiv 2 ℂ (NSiteSpace d L)
  refine hT.nonneg_of_apply_eq_smul (v := e.symm v) (by simpa using hv.2) ?_
  simp [Module.End.mem_eigenspace_iff.1 hv.1]

end MPSTensor
