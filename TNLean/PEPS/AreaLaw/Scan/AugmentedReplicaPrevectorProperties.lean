/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.AugmentedReplicaMetricCoordinates
import TNLean.PEPS.AreaLaw.Scan.GlobalReplicaEnergyCoordinates
import QICLean.Representation.ReplicaPrevector
import QICLean.Representation.RegionalAuxiliaryLabels
import QICLean.Analysis.RegionalLowDefectProjection

/-!
# Symmetry and supplied labels of the augmented initial vector

The original replica prevector, expressed in the augmented site coordinates,
is fixed by simultaneous permutation of the copies. Each auxiliary singleton
has the same supplied representation label. Both assertions concern the same
vector and the same coordinate equivalence, without normalization or positive
dimension assumptions. Nonvanishing and the mean-energy eigen-equation are also
preserved under this coordinate identification.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`07-comparators.tex`, lines 130–153, `comparator:prevector`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open Matrix TensorPower TensorPower.ReplicaTransport PermutationRepresentation
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

/-- Reindexing the physical and auxiliary sites preserves the Euclidean norm
of the replica prevector.
Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 130–153,
`comparator:prevector`, revision adc7f124. -/
theorem norm_augmentedReplicaPrevector_eq_global
    {V : Type} [Fintype V] [DecidableEq V] (q d k : ℕ)
    (Ω : (V → Fin q) → ℂ) (ell : IrrepLabel (Equiv.Perm (Fin k))) :
    ‖WithLp.toLp 2
      (replicaPrevector Ω d k ell ∘ augmentedSumReplicaCopiesEquiv q d k)‖ =
      ‖WithLp.toLp 2 (replicaPrevector Ω d k ell ∘
        globalReplicaCopiesEquiv (fun _ : V ↦ Fin q) (Fin d) (Fin d) k)‖ := by
  exact (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (augmentedReplicaConfigurationEquiv (V := V) q d k)).norm_map
      (WithLp.toLp 2 (replicaPrevector Ω d k ell ∘
        globalReplicaCopiesEquiv (fun _ : V ↦ Fin q) (Fin d) (Fin d) k))

/-- The replica prevector is nonzero in the augmented site coordinates exactly
when it is nonzero in the original physical and auxiliary coordinates.
Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 130–153,
`comparator:prevector`, revision adc7f124. -/
theorem augmentedReplicaPrevector_ne_zero_iff_global
    {V : Type} [Fintype V] [DecidableEq V] (q d k : ℕ)
    (Ω : (V → Fin q) → ℂ) (ell : IrrepLabel (Equiv.Perm (Fin k))) :
    replicaPrevector Ω d k ell ∘ augmentedSumReplicaCopiesEquiv q d k ≠ 0 ↔
      WithLp.toLp 2 (replicaPrevector Ω d k ell ∘
        globalReplicaCopiesEquiv (fun _ : V ↦ Fin q) (Fin d) (Fin d) k) ≠ 0 := by
  simpa only [ne_eq, norm_eq_zero, WithLp.toLp_eq_zero] using
    (iff_of_eq (congrArg (fun r : ℝ ↦ r ≠ 0)
      (norm_augmentedReplicaPrevector_eq_global q d k Ω ell)))


/-- Nonvanishing, copy symmetry and the mean-energy eigen-equation are preserved
in the augmented scanner coordinates.
Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 130–153 and
421–438; `08-scanner.tex`, lines 457–490, revision adc7f124. -/
theorem augmented_prevector_properties_of_global
    {V : Type} [Fintype V] [DecidableEq V] (q d k : ℕ)
    (Ω : (V → Fin q) → ℂ) (ell : IrrepLabel (Equiv.Perm (Fin k)))
    (H : Matrix (V → Fin q) (V → Fin q) ℂ) (e : ℝ)
    (hne : WithLp.toLp 2 (replicaPrevector Ω d k ell ∘
      globalReplicaCopiesEquiv (fun _ : V ↦ Fin q) (Fin d) (Fin d) k) ≠ 0)
    (heigen : Matrix.globalReplicaMeanHamiltonian (fun _ : V ↦ Fin q) (Fin d) (Fin d) H k *ᵥ
        (replicaPrevector Ω d k ell ∘
          globalReplicaCopiesEquiv (fun _ : V ↦ Fin q) (Fin d) (Fin d) k) =
      (e : ℂ) • (replicaPrevector Ω d k ell ∘
        globalReplicaCopiesEquiv (fun _ : V ↦ Fin q) (Fin d) (Fin d) k)) :
    let dims := augmentedDimensions (V := V) q (fun _ ↦ d)
    let pre := replicaPrevector Ω d k ell ∘ augmentedSumReplicaCopiesEquiv q d k
    pre ≠ 0 ∧ pre ∈ symmetricSubspace k (fun v ↦ Fin (dims v)) ∧
      copyMean dims k (augmentOperator q (fun _ ↦ d) H) *ᵥ pre = (e : ℂ) • pre := by
  classical
  intro dims pre
  let ecoord := augmentedReplicaConfigurationEquiv (V := V) q d k
  have hpreEq : pre ∘ ecoord = replicaPrevector Ω d k ell ∘
      globalReplicaCopiesEquiv (fun _ : V ↦ Fin q) (Fin d) (Fin d) k := by
    simp only [pre, augmentedSumReplicaCopiesEquiv, Equiv.coe_trans,
      Function.comp_assoc, ecoord, Equiv.symm_comp_self, Function.comp_id]
  refine ⟨?_, ?_, ?_⟩
  · exact (augmentedReplicaPrevector_ne_zero_iff_global q d k Ω ell).mpr hne
  · have hfixed : symProj (copyPerm ((v : V ⊕ Bool) → Fin (dims v)) k) *ᵥ pre = pre :=
      symProj_mulVec_augmentedReplicaPrevector q d k Ω ell
    rw [← hfixed]
    exact symProj_mulVec_mem _ _
  · have hglobal : Matrix.globalReplicaMeanHamiltonian (fun _ : V ↦ Fin q)
        (Fin d) (Fin d) H k *ᵥ (pre ∘ ecoord) = (e : ℂ) • (pre ∘ ecoord) := by
      rw [hpreEq]
      exact heigen
    rw [copyMean_augmentOperator_eq_globalReplicaMeanHamiltonian]
    ext x
    simpa only [Matrix.submatrix_mulVec_equiv, Equiv.symm_symm,
      Function.comp_apply, ecoord, Equiv.apply_symm_apply, Pi.smul_apply] using
      congrFun hglobal (ecoord.symm x)

end TNLean.PEPS.AreaLaw.Scan
