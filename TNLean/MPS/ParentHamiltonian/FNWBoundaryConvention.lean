/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.WordAdjoint
import TNLean.MPS.ParentHamiltonian.GroundSpace

/-!
# FNW boundary-map convention

Fannes, Nachtergaele, and Werner use the length-\(N\) boundary map
\[
  F_N(B)(\mu_1,\ldots,\mu_N)
    = \operatorname{Tr}\!\left(Bv(\mu_N)^*\cdots v(\mu_1)^*\right)
\]
in equation (5.5) of Comm. Math. Phys. 144, 443--490 (1992).  TNLean's
`groundSpaceMap` evaluates matrix words from the first physical site to the
last.  The two maps therefore agree after reversing the physical sites and
setting \(A_\mu=v(\mu)^*\).  Trace cyclicity moves the boundary matrix across
the word; the word reversal comes instead from conjugate transposition and
`List.ofFn_reverse`.
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- Reversal of the physical sites of a finite-chain configuration. -/
def physicalSiteReverseConfigEquiv (d N : ℕ) : Cfg d N ≃ Cfg d N :=
  Equiv.arrowCongr Fin.revPerm (Equiv.refl (Fin d))

/-- The raw linear equivalence that reverses the physical sites of a coefficient
function.  This definition does not use a Hilbert-space structure. -/
def physicalSiteReverse (d N : ℕ) : NSiteSpace d N ≃ₗ[ℂ] NSiteSpace d N :=
  LinearEquiv.piCongrLeft' ℂ (fun _ : Cfg d N => ℂ)
    (physicalSiteReverseConfigEquiv d N)

/-- Physical-site reversal evaluates a coefficient function on the reversed
configuration. -/
@[simp] theorem physicalSiteReverse_apply (ψ : NSiteSpace d N) (σ : Cfg d N) :
    physicalSiteReverse d N ψ σ = ψ (σ ∘ Fin.rev) := by
  rfl

/-- The FNW boundary map of equation (5.5).  The matrix family `v` follows the
source convention, before the identification \(A_\mu=v(\mu)^*\). -/
noncomputable def fnwBoundaryMap (v : MPSTensor d D) (N : ℕ) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] NSiteSpace d N :=
  LinearMap.pi fun σ : Cfg d N =>
    (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp
      (LinearMap.mulRight ℂ (Kraus.evalWord v (List.ofFn σ))ᴴ)

/-- Pointwise form of FNW 1992 equation (5.5). -/
@[simp] theorem fnwBoundaryMap_apply (v : MPSTensor d D) (N : ℕ)
    (B : Matrix (Fin D) (Fin D) ℂ) (σ : Cfg d N) :
    fnwBoundaryMap v N B σ =
      Matrix.trace (B * (Kraus.evalWord v (List.ofFn σ))ᴴ) := by
  simp [fnwBoundaryMap, Matrix.traceLinearMap_apply]

/-- Expanding the adjoint in equation (5.5) gives the reversed word of the
pointwise adjoint family. -/
theorem fnwBoundaryMap_apply_eq_trace_reverse (v : MPSTensor d D) (N : ℕ)
    (B : Matrix (Fin D) (Fin D) ℂ) (σ : Cfg d N) :
    fnwBoundaryMap v N B σ =
      Matrix.trace
        (B * Kraus.evalWord (fun μ => (v μ)ᴴ) (List.ofFn σ).reverse) := by
  rw [fnwBoundaryMap_apply, Kraus.evalWord_conjTranspose]

/-- With \(A_\mu=v(\mu)^*\), the FNW boundary map is TNLean's ground-space
map followed by physical-site reversal. -/
theorem fnwBoundaryMap_eq_physicalSiteReverse_comp_groundSpaceMap
    (v : MPSTensor d D) (N : ℕ) :
    fnwBoundaryMap v N =
      (physicalSiteReverse d N).toLinearMap.comp
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
