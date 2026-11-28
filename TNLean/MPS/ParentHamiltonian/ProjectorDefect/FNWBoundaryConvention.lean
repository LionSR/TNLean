/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.Word
import TNLean.MPS.Tensor.GroundSpace.GroundSpace

/-!
# FNW boundary-map convention

Fannes, Nachtergaele, and Werner use the length-\(N\) boundary map
\[
  F_N(B)(\mu_1,\ldots,\mu_N)
    = \operatorname{Tr}\!\left(Bv(\mu_N)^*\cdots v(\mu_1)^*\right)
\]
in equation (5.5) of Comm. Math. Phys. 144, 443--490 (1992),
DOI 10.1007/BF02099178.  TNLean's ground-space map evaluates matrix words from
the first physical site to the last.  The two maps therefore agree after
reversing the physical sites and setting \(A_\mu=v(\mu)^*\).  Trace cyclicity
moves the boundary matrix across the word; conjugate transposition and reversal
of the finite index list reverse the word.
-/

open scoped Matrix

namespace MPSTensor

variable {α : Type*} [Fintype α] [DecidableEq α] {D : ℕ}

/-- Reversal of the physical sites of a finite-chain configuration. -/
def physicalSiteReverseConfigEquiv (N : ℕ) : (Fin N → α) ≃ (Fin N → α) :=
  Equiv.arrowCongr Fin.revPerm (Equiv.refl α)

/-- The raw linear equivalence that reverses the physical sites of a coefficient
function.  This definition does not use a Hilbert-space structure. -/
def physicalSiteReverse (N : ℕ) : NSiteSpace α N ≃ₗ[ℂ] NSiteSpace α N :=
  LinearEquiv.piCongrLeft' ℂ (fun _ : (Fin N → α) => ℂ)
    (physicalSiteReverseConfigEquiv N)

/-- Physical-site reversal evaluates a coefficient function on the reversed
configuration. -/
@[simp] theorem physicalSiteReverse_apply {N : ℕ} (ψ : NSiteSpace α N) (σ : (Fin N → α)) :
    physicalSiteReverse N ψ σ = ψ (σ ∘ Fin.rev) := by
  rfl

/-- The FNW boundary map of equation (5.5).  The matrix family \(v\) follows the
source convention, before the identification \(A_\mu=v(\mu)^*\). -/
noncomputable def fnwBoundaryMap (v : MPTensor α (Fin D)) (N : ℕ) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] NSiteSpace α N :=
  LinearMap.pi fun σ : (Fin N → α) =>
    (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp
      (LinearMap.mulRight ℂ (Kraus.evalWord v (List.ofFn σ))ᴴ)

/-- Pointwise form of FNW 1992 equation (5.5). -/
@[simp] theorem fnwBoundaryMap_apply (v : MPTensor α (Fin D)) (N : ℕ)
    (B : Matrix (Fin D) (Fin D) ℂ) (σ : (Fin N → α)) :
    fnwBoundaryMap v N B σ =
      Matrix.trace (B * (Kraus.evalWord v (List.ofFn σ))ᴴ) := by
  simp [fnwBoundaryMap, Matrix.traceLinearMap_apply]

/-- Expanding the adjoint in equation (5.5) gives the reversed word of the
pointwise adjoint family. -/
theorem fnwBoundaryMap_apply_eq_trace_reverse (v : MPTensor α (Fin D)) (N : ℕ)
    (B : Matrix (Fin D) (Fin D) ℂ) (σ : (Fin N → α)) :
    fnwBoundaryMap v N B σ =
      Matrix.trace
        (B * Kraus.evalWord (fun μ => (v μ)ᴴ) (List.ofFn σ).reverse) := by
  rw [fnwBoundaryMap_apply, Kraus.evalWord_conjTranspose]

/-- With \(A_\mu=v(\mu)^*\), the FNW boundary map is TNLean's ground-space
map followed by physical-site reversal. -/
theorem fnwBoundaryMap_eq_physicalSiteReverse_comp_groundSpaceMap
    (v : MPTensor α (Fin D)) (N : ℕ) :
    fnwBoundaryMap v N =
      (physicalSiteReverse N).toLinearMap.comp
        (groundSpaceMap (fun μ => (v μ)ᴴ) N) := by
  apply LinearMap.ext
  intro B
  funext σ
  rw [fnwBoundaryMap_apply_eq_trace_reverse]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    physicalSiteReverse_apply, groundSpaceMap_apply]
  rw [← List.ofFn_reverse]
  exact Matrix.trace_mul_comm _ _

end MPSTensor
