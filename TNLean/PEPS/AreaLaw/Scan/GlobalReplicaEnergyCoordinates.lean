/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.PEPS.AreaLaw.Scan.AugmentedEnergyCoordinates
import QICLean.Analysis.RegionalLowDefectMass

/-!
# The global replica energy in the scanner coordinates

The replica mean of the physical Hamiltonian, extended by the identities on C
and R, is the same operator in the two descriptions of the augmented sites.
The coordinate identification preserves the physical sites and the ordering
of C and R. The operator identity and the exact complex energy expectation
hold for arbitrary physical matrices and supplied vectors, including zero
replicas and empty configuration spaces.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`06-transport.tex`, lines 335–358, and `07-comparators.tex`,
`comparator:defect-mass`, lines 421–438, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open TensorPower TensorPower.ReplicaTransport
open scoped Matrix

namespace TNLean.PEPS.AreaLaw.Scan

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The scanner energy is the original global replica mean under the same
copywise configuration identification. The statement includes zero replicas
and requires no positivity or gap assumption.
Source: OpenAI area-law manuscript, `07-comparators.tex`,
`comparator:defect-mass`, lines 421–438, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem copyMean_augmentOperator_eq_globalReplicaMeanHamiltonian
    (q d k : ℕ) (H : Matrix (V → Fin q) (V → Fin q) ℂ) :
    copyMean (augmentedDimensions (V := V) q (fun _ => d)) k
        (augmentOperator q (fun _ => d) H) =
      (Matrix.globalReplicaMeanHamiltonian (fun _ : V => Fin q) (Fin d) (Fin d) H k).submatrix
        (augmentedReplicaConfigurationEquiv q d k).symm
        (augmentedReplicaConfigurationEquiv q d k).symm := by
  rw [copyMean_augmentOperator_eq_replicaHamiltonian_kronecker]
  ext x y
  simp only [Matrix.globalReplicaMeanHamiltonian, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul,
    Complex.ofReal_inv, Complex.ofReal_natCast, augmentedSumReplicaCopiesEquiv,
    Equiv.trans_apply]

/-- The exact complex energy expectation of a supplied scanner vector equals
that of the same vector in the successive physical,C,R coordinates.
No normalization, nonzero-vector or spectral hypothesis is imposed.
Source: OpenAI area-law manuscript, `07-comparators.tex`,
`comparator:defect-mass`, lines 421–438, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem star_dotProduct_copyMean_augmentOperator
    (q d k : ℕ) (H : Matrix (V → Fin q) (V → Fin q) ℂ)
    (w : Config k (fun s => Fin (augmentedDimensions (V := V) q (fun _ => d) s)) → ℂ) :
    star w ⬝ᵥ (copyMean (augmentedDimensions (V := V) q (fun _ => d)) k
        (augmentOperator q (fun _ => d) H) *ᵥ w) =
      star (w ∘ augmentedReplicaConfigurationEquiv q d k) ⬝ᵥ
        (Matrix.globalReplicaMeanHamiltonian (fun _ : V => Fin q) (Fin d) (Fin d) H k *ᵥ
          (w ∘ augmentedReplicaConfigurationEquiv q d k)) := by
  simpa only [copyMean_augmentOperator_eq_globalReplicaMeanHamiltonian] using
    Matrix.star_dotProduct_submatrix_equiv
      (Matrix.globalReplicaMeanHamiltonian (fun _ : V => Fin q) (Fin d) (Fin d) H k)
      (augmentedReplicaConfigurationEquiv q d k) w

end TNLean.PEPS.AreaLaw.Scan
