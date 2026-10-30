/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.CycleParentGroundSpace
import TNLean.MPS.ParentHamiltonian.PhysicalDeformation

/-!
# Periodic-chain physical deformation from the graph theorem

On a cycle with `n≥3` and proper nonempty interaction arcs `0<L<n`,
the graph parent-space transport theorem gives the actual periodic-chain
ground-space correspondence. The constant graph product map is the chain's
on-site tensor power, and physical deformation of the cycle tensor is the
cycle tensor of the physically rotated MPS family. The resulting identity
agrees with `MPSTensor.chainGroundSpace_rotatePhysical`, which the chain
argument proves for all `L` and `n`; here it is derived from the graph
theorem, so the two parent constructions are compared directly.

Source: arXiv:2011.12127, Section IV.C, the parent construction at lines
1987–2011 and physical deformation at lines 2032–2038. No injectivity or
positive physical or bond dimension is assumed.

**Scope restriction (cycle comparison):** The specialization uses `n≥3`
and `0<L<n`; full-ring and smaller-cycle comparisons require their own
boundary and graph conventions. See
`docs/paper-gaps/cpgsv21_physical_deformation_general_graph.tex`.
-/

noncomputable section

open scoped Matrix BigOperators

namespace TNLean.PEPS

variable {n d e D L : ℕ} [NeZero n]

/-- Physical deformation of the actual cycle tensor is physical rotation of
its matrix family. Source: arXiv:2011.12127, Section IV.C, lines 2032–2038. -/
theorem physicalDeform_cycleTensorOfMPS (hn : 3 ≤ n) (A : MPSTensor d D)
    (Λ : Matrix (Fin e) (Fin d) ℂ) :
    physicalDeform (cycleTensorOfMPS hn A) (fun _ ↦ Λ) =
      cycleTensorOfMPS hn (MPSTensor.rotatePhysical Λ A) := by
  unfold physicalDeform cycleTensorOfMPS
  apply congrArg (Tensor.mk (fun _ ↦ D))
  funext v η t
  simp only [MPSTensor.rotatePhysical, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

omit [NeZero n] in
/-- A constant graph physical product map is exactly the chain tensor power.
Source: arXiv:2011.12127, Section IV.C, lines 2035–2037. -/
theorem globalPhysicalMap_const_eq_onSiteTensorPow (Λ : Matrix (Fin d) (Fin d) ℂ) :
    globalPhysicalMap (fun _ : Fin n ↦ Λ) =
      Matrix.toLin' (MPSTensor.onSiteTensorPow n Λ) := by
  apply LinearMap.ext
  intro ψ
  funext σ
  rw [globalPhysicalMap_apply]
  rfl

/-- The graph-generic parent-space transport specializes to the actual chain
spaces on proper arcs. Source: arXiv:2011.12127, Section IV.C, lines
1987–2011 and 2032–2038. This proof uses the graph transport theorem and the
proved equality of the full parent spaces. -/
theorem map_chainGroundSpace_physicalEquiv_of_cycle (hn : 3 ≤ n) (hL : 0 < L)
    (hLn : L < n) (A : MPSTensor d D) (F : (Fin d → ℂ) ≃ₗ[ℂ] (Fin d → ℂ)) :
    (MPSTensor.chainGroundSpace A L n).map
        (Matrix.toLin' (MPSTensor.onSiteTensorPow n (LinearMap.toMatrix' F.toLinearMap))) =
      MPSTensor.chainGroundSpace
        (MPSTensor.rotatePhysical (LinearMap.toMatrix' F.toLinearMap) A) L n := by
  have h := map_regionParentGroundSpace_physicalDeform (cycleTensorOfMPS hn A)
    (fun s ↦ cycleArcFrom s L) (fun _ : Fin n ↦ F)
  rw [physicalDeform_cycleTensorOfMPS,
    regionParentGroundSpace_cycleTensorOfMPS hn hL hLn A,
    regionParentGroundSpace_cycleTensorOfMPS hn hL hLn
      (MPSTensor.rotatePhysical (LinearMap.toMatrix' F.toLinearMap) A)] at h
  change (MPSTensor.chainGroundSpace A L n).map
    (globalPhysicalMap (fun _ : Fin n ↦ LinearMap.toMatrix' F.toLinearMap)) = _ at h
  rwa [globalPhysicalMap_const_eq_onSiteTensorPow] at h

end TNLean.PEPS
