/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.AugmentedEnergyCoordinates
import QICLean.Representation.SubsystemTransport
import QICLean.Representation.ReplicaMetric

/-!
# Replica metrics in the same augmented site coordinates

The physical sites, near auxiliary site C and far auxiliary site R have two
descriptions. The coordinate equivalence used for the augmented energy also
transports every subsystem permutation and replica metric. The metric weights
retain the dimension of the whole one-copy system.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`05-replicas.tex`, `replicas:w-definition`; `06-transport.tex`, lines 335--358;
`07-comparators.tex`, lines 130--153, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open TensorPower PermutationRepresentation Matrix

noncomputable section

namespace TNLean.PEPS.AreaLaw.Scan

variable {V : Type} [DecidableEq V]

local notation "ιO" q:max d:max =>
  addedSiteSpace (addedSiteSpace (fun _ : V => Fin q) (Fin d)) (Fin d)
local notation "ιS" q:max d:max =>
  fun s : V ⊕ Bool => Fin (augmentedDimensions q (fun _ => d) s)

/-- The same one-copy coordinate identification transports permutations of
any subsystem. The near auxiliary site is C=false and the far auxiliary
site is R=true. Source: area-law manuscript, `05-replicas.tex`, lines 24--27;
`06-transport.tex`, lines 335--358; `07-comparators.tex`, lines 130--153,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem augmentedReplicaConfigurationEquiv_subsystemPerm
    (q d k : ℕ) (Q : Finset (Option (Option V)))
    (σ : Equiv.Perm (Fin k)) (x : Config k (ιO q d)) :
    augmentedReplicaConfigurationEquiv q d k
        (subsystemPerm k (ιO q d) Q σ x) =
      subsystemPerm k (ιS q d) (Q.image augmentedSiteEquiv) σ
        (augmentedReplicaConfigurationEquiv q d k x) := by
  classical
  funext j s
  simp only [augmentedReplicaConfigurationEquiv, Equiv.arrowCongr_apply,
    Equiv.refl_symm, Function.comp_apply, Equiv.refl_apply, subsystemPerm_apply]
  rcases s with v | (_ | _)
  · simp only [augmentedConfigurationEquiv_apply_physical, subsystemPerm_apply,
      (show Sum.inl v ∈ Q.image augmentedSiteEquiv ↔ some (some v) ∈ Q from
        (augmentedSiteEquiv (V := V)).injective.mem_finset_image
          (s := Q) (a := some (some v)))]
    rfl
  all_goals
    simp only [augmentedConfigurationEquiv_apply_C, augmentedConfigurationEquiv_apply_R,
      subsystemPerm_apply,
      (show Sum.inr false ∈ Q.image augmentedSiteEquiv ↔ some none ∈ Q from
        (augmentedSiteEquiv (V := V)).injective.mem_finset_image
          (s := Q) (a := some none)),
      (show Sum.inr true ∈ Q.image augmentedSiteEquiv ↔ none ∈ Q from
        (augmentedSiteEquiv (V := V)).injective.mem_finset_image
          (s := Q) (a := none))]
    rfl

variable [Fintype V]

/-- Changing the names of the physical and auxiliary sites preserves the
replica metric with its original full-system dimension. The scalar parameter
is arbitrary, and no nonempty-coordinate assumption is required. Source:
area-law manuscript, `05-replicas.tex`, `replicas:w-definition`;
`06-transport.tex`, lines 335--358; `07-comparators.tex`, lines 130--153,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem replicaMetric_submatrix_augmentedReplicaConfigurationEquiv
    (q d k : ℕ) (t : ℝ) (Q : Finset (Option (Option V))) :
    replicaMetric (ιS q d) t k (Q.image augmentedSiteEquiv) =
      (replicaMetric (ιO q d) t k Q).submatrix
        (augmentedReplicaConfigurationEquiv q d k).symm
        (augmentedReplicaConfigurationEquiv q d k).symm := by
  classical
  -- The two one-copy descriptions have the same dimension `d`, so the common
  -- label weight is unchanged.
  have hdim : replicaDim (ιS q d) = replicaDim (ιO q d) :=
    Fintype.card_congr (augmentedConfigurationEquiv q d).symm
  have hw : replicaLabelWeight (ιS q d) t (k := k) =
      replicaLabelWeight (ιO q d) t (k := k) := by
    funext l
    simp only [replicaLabelWeight]
    rw [hdim]
  -- The coordinate equivalence intertwines the two subsystem permutations, so
  -- it reindexes every label projector.
  have key : ∀ l : IrrepLabel (Equiv.Perm (Fin k)),
      labelProj (subsystemPerm k (ιS q d) (Q.image augmentedSiteEquiv)) l =
        reindex (augmentedReplicaConfigurationEquiv q d k)
          (augmentedReplicaConfigurationEquiv q d k)
          (labelProj (subsystemPerm k (ιO q d) Q) l) := fun l =>
    labelProj_of_intertwine (augmentedReplicaConfigurationEquiv q d k)
      (fun σ x => (augmentedReplicaConfigurationEquiv_subsystemPerm q d k Q σ x).symm) l
  simp only [replicaMetric, labelObservable, hw]
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.sum_apply, Matrix.smul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [key l, reindex_apply, Matrix.submatrix_apply]

end TNLean.PEPS.AreaLaw.Scan
