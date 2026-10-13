/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.AugmentedReplicaMetricCoordinates
import QICLean.Representation.ReplicaPrevector
import QICLean.Representation.RegionalAuxiliaryLabels
import QICLean.Analysis.RegionalLowDefectProjection

/-!
# Symmetry and supplied labels of the augmented initial vector

The original replica prevector, expressed in the augmented site coordinates,
is fixed by simultaneous permutation of the copies. Each auxiliary singleton
has the same supplied representation label. Both assertions concern the same
vector and the same coordinate equivalence, without normalization or positive
dimension assumptions.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`07-comparators.tex`, lines 130–153, `comparator:prevector`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open Matrix TensorPower PermutationRepresentation
open scoped Matrix Kronecker

namespace TNLean.PEPS.AreaLaw.Scan

variable {V : Type} [Fintype V] [DecidableEq V]

open Classical in
/-- The literal augmented initial vector is fixed by full copy symmetry.
Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 130–153,
`comparator:prevector`, revision adc7f124. -/
theorem symProj_mulVec_augmentedReplicaPrevector
    (q d k : ℕ) (Ω : (V → Fin q) → ℂ)
    (ell : IrrepLabel (Equiv.Perm (Fin k))) :
    let n := augmentedDimensions (V := V) q (fun _ ↦ d)
    let pre : Config k (fun v ↦ Fin (n v)) → ℂ :=
      replicaPrevector Ω d k ell ∘ augmentedSumReplicaCopiesEquiv q d k
    symProj (copyPerm ((v : V ⊕ Bool) → Fin (n v)) k) *ᵥ pre = pre := by
  classical
  intro n pre
  have hproduct :
      symProj (replicaJointCopyPerm (V → Fin q) (Fin d) (Fin d) k) *ᵥ
        replicaPrevector Ω d k ell = replicaPrevector Ω d k ell :=
    symProj_mulVec_of_mem _ (fun σ ↦ by
      rw [permOp_replicaJointCopyPerm]
      exact replicaPrevector_copyPerm_fixed Ω d k ell σ)
  have hcov := symProj_of_intertwine (augmentedSumReplicaCopiesEquiv (V := V) q d k)
    (φ := copyPerm ((v : V ⊕ Bool) → Fin (n v)) k)
    (ψ := replicaJointCopyPerm (V → Fin q) (Fin d) (Fin d) k)
    (fun σ x ↦ rfl)
  simpa only [hcov, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv,
    Equiv.symm_symm, Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id, pre] using
    congrArg (fun v ↦ v ∘ augmentedSumReplicaCopiesEquiv (V := V) q d k) hproduct

open Classical in
/-- Each original auxiliary site of the literal augmented initial vector
has the same supplied label. C is false and R is true.
Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 130–153,
`comparator:prevector`, revision adc7f124. -/
theorem labelProj_auxiliary_mulVec_augmentedReplicaPrevector
    (q d k : ℕ) (Ω : (V → Fin q) → ℂ)
    (ell : IrrepLabel (Equiv.Perm (Fin k))) (b : Bool) :
    let n := augmentedDimensions (V := V) q (fun _ ↦ d)
    let pre : Config k (fun v ↦ Fin (n v)) → ℂ :=
      replicaPrevector Ω d k ell ∘ augmentedSumReplicaCopiesEquiv q d k
    labelProj (subsystemPerm k (fun v ↦ Fin (n v)) {Sum.inr b}) ell *ᵥ pre = pre := by
  classical
  intro n pre
  have hcov (Q : Finset (Option (Option V))) :=
    labelProj_of_intertwine (augmentedReplicaConfigurationEquiv (V := V) q d k)
      (fun σ x ↦ (augmentedReplicaConfigurationEquiv_subsystemPerm q d k Q σ x).symm) ell
  have haux := labelProj_globalReplicaCopiesEquiv_auxiliary
    (fun _ : V ↦ Fin q) (Fin d) (Fin d) k ell ell
  have hfixed := replicaPrevector_auxiliary_label_fixed Ω d k ell
  cases b
  · have hC :
        labelProj (subsystemPerm k (fun v ↦ Fin (n v)) {Sum.inr false}) ell =
          (1 ⊗ₖ (labelProj (copyPerm (Fin d) k) ell ⊗ₖ 1)).submatrix
            (augmentedSumReplicaCopiesEquiv q d k)
            (augmentedSumReplicaCopiesEquiv q d k) := by
      simpa only [Finset.image_singleton, Matrix.reindex_apply, ← haux.1,
        Matrix.submatrix_submatrix, n,
        show augmentedSiteEquiv (some none : Option (Option V)) = Sum.inr false from rfl,
        augmentedSumReplicaCopiesEquiv, Equiv.coe_trans] using hcov {some none}
    simpa only [hC, pre, Matrix.submatrix_mulVec_equiv, Function.comp_assoc,
      Equiv.self_comp_symm, Function.comp_id] using
      congrArg (fun v ↦ v ∘ augmentedSumReplicaCopiesEquiv (V := V) q d k) hfixed.1
  · have hR :
        labelProj (subsystemPerm k (fun v ↦ Fin (n v)) {Sum.inr true}) ell =
          (1 ⊗ₖ (1 ⊗ₖ labelProj (copyPerm (Fin d) k) ell)).submatrix
            (augmentedSumReplicaCopiesEquiv q d k)
            (augmentedSumReplicaCopiesEquiv q d k) := by
      simpa only [Finset.image_singleton, Matrix.reindex_apply, ← haux.2,
        Matrix.submatrix_submatrix, n,
        show augmentedSiteEquiv (none : Option (Option V)) = Sum.inr true from rfl,
        augmentedSumReplicaCopiesEquiv, Equiv.coe_trans] using hcov {none}
    simpa only [hR, pre, Matrix.submatrix_mulVec_equiv, Function.comp_assoc,
      Equiv.self_comp_symm, Function.comp_id] using
      congrArg (fun v ↦ v ∘ augmentedSumReplicaCopiesEquiv (V := V) q d k) hfixed.2

end TNLean.PEPS.AreaLaw.Scan
