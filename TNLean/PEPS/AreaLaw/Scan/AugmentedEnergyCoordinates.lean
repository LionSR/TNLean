/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.PEPS.AreaLaw.Scan.ActualEnergyTerms
import QICLean.Representation.RegionalFiveFactorCoordinates
import QICLean.Representation.ReplicaMeanIdentityExtension
import QICLean.Analysis.ReplicaLowDefectCoordinateCovariance
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Option
import Mathlib.Logic.Equiv.Sum
import Mathlib.Logic.Equiv.Prod

/-!
# Coordinates for the same augmented replica energy

The two descriptions adjoin C on the near side and R on the far side.
The physical site v corresponds to some (some v), C to some none and R
to none in the option description; their sum-description coordinates are
inl v, inr false and inr true, respectively. The operator is the same
physical matrix extended by the two auxiliary identities.

Source: OpenAI, A two-dimensional area law from a global spectral gap,
06-transport.tex, lines 335–358, and 07-comparators.tex, lines 130–153
and 421–438, revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
The identities below compare the site coordinates and the copy-mean
operator. They apply to an arbitrary physical matrix. The auxiliary
registers C and R share one dimension d because the source pairs them by
the Bell vector `Bell_CR = d_*^{-1/2} ∑_{i ∈ E} |i⟩_C |i⟩_R` on a common
label set E (07-comparators.tex, line 89); the general `augmentedDimensions`
with independent auxiliary dimensions is not needed at this step.
-/

noncomputable section
open TensorPower Entropy
open scoped Kronecker

namespace TNLean.PEPS.AreaLaw.Scan

variable {V : Type}

/-- The physical sites and the two auxiliary sites, with C=false and R=true.
The maps are some(some v) ↦ inl v, some none ↦ inr false, none ↦ inr true.
Source: 06-transport.tex, lines 335–358; 07-comparators.tex, lines 130–153,
revision adc7f1241b42e322a6451854ab7e4b4c146bf78a. -/
def augmentedSiteEquiv : Option (Option V) ≃ V ⊕ Bool :=
  (Equiv.optionEquivSumPUnit.{0, 0} (Option V)).trans
    (((Equiv.optionEquivSumPUnit.{0, 0} V).sumCongr (Equiv.refl PUnit.{1})).trans
      ((Equiv.sumAssoc V PUnit.{1} PUnit.{1}).trans
        ((Equiv.refl V).sumCongr Equiv.boolEquivPUnitSumPUnit.{0, 0}.symm)))

/-- The one-copy configuration equivalence for two auxiliary registers of
the same selected dimension d. Both grouping steps preserve the physical
coordinate and place C before R. No auxiliary basis is changed.
Source: 06-transport.tex, lines 335–358; 07-comparators.tex, lines 130–153,
revision adc7f1241b42e322a6451854ab7e4b4c146bf78a. -/
def augmentedConfigurationEquiv (q d : ℕ) :
    ((s : Option (Option V)) →
      addedSiteSpace (addedSiteSpace (fun _ : V => Fin q) (Fin d)) (Fin d) s) ≃
      SiteConfig (augmentedDimensions (V := V) q (fun _ => d)) :=
  let optionSplit :
      ((s : Option (Option V)) →
        addedSiteSpace (addedSiteSpace (fun _ : V => Fin q) (Fin d)) (Fin d) s) ≃
        (V → Fin q) × (Fin d × Fin d) :=
    Equiv.piOptionEquivProd.trans
      (((Equiv.refl (Fin d)).prodCongr Equiv.piOptionEquivProd).trans
        ((Equiv.prodAssoc (Fin d) (Fin d) (V → Fin q)).symm.trans
          ((Equiv.prodComm (Fin d × Fin d) (V → Fin q)).trans
            ((Equiv.refl (V → Fin q)).prodCongr
              (Equiv.prodComm (Fin d) (Fin d))))))
  optionSplit.trans
    (((Equiv.refl (V → Fin q)).prodCongr
      (Equiv.boolArrowEquivProd (Fin d)).symm).trans
      (Equiv.sumPiEquivProdPi
        (fun s => Fin (augmentedDimensions (V := V) q (fun _ => d) s))).symm)

/-- Apply the same one-copy identification independently on every replica.
The physical coordinates, C and R are retained at every copy, also when k=0.
Source: 07-comparators.tex, lines 130–153 and 421–438,
revision adc7f1241b42e322a6451854ab7e4b4c146bf78a. -/
def augmentedReplicaConfigurationEquiv (q d k : ℕ) :
    Config k
      (addedSiteSpace (addedSiteSpace (fun _ : V => Fin q) (Fin d)) (Fin d)) ≃
      Config k (fun s => Fin (augmentedDimensions (V := V) q (fun _ => d) s)) :=
  Equiv.arrowCongr (Equiv.refl (Fin k)) (augmentedConfigurationEquiv q d)

/-- The physical coordinate is retained.
Source: OpenAI area-law manuscript, 07-comparators.tex, lines 130–153,
revision adc7f1241b42e322a6451854ab7e4b4c146bf78a. -/
theorem augmentedConfigurationEquiv_apply_physical (q d : ℕ)
    (x : (s : Option (Option V)) →
      addedSiteSpace (addedSiteSpace (fun _ : V => Fin q) (Fin d)) (Fin d) s)
    (v : V) : augmentedConfigurationEquiv q d x (Sum.inl v) = x (some (some v)) := by
  rfl

/-- The C coordinate is the false auxiliary site.
Source: OpenAI area-law manuscript, 07-comparators.tex, lines 130–153,
revision adc7f1241b42e322a6451854ab7e4b4c146bf78a. -/
theorem augmentedConfigurationEquiv_apply_C (q d : ℕ)
    (x : (s : Option (Option V)) →
      addedSiteSpace (addedSiteSpace (fun _ : V => Fin q) (Fin d)) (Fin d) s) :
    augmentedConfigurationEquiv q d x (Sum.inr false) = x (some none) := by
  rfl

/-- The R coordinate is the true auxiliary site.
Source: OpenAI area-law manuscript, 07-comparators.tex, lines 130–153,
revision adc7f1241b42e322a6451854ab7e4b4c146bf78a. -/
theorem augmentedConfigurationEquiv_apply_R (q d : ℕ)
    (x : (s : Option (Option V)) →
      addedSiteSpace (addedSiteSpace (fun _ : V => Fin q) (Fin d)) (Fin d) s) :
    augmentedConfigurationEquiv q d x (Sum.inr true) = x none := by
  rfl

variable [Fintype V] [DecidableEq V]

/-- The sum-site configuration in the original physical,C,R copy order.
Source: 07-comparators.tex, lines 421–438, revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. -/
def augmentedSumReplicaCopiesEquiv (q d k : ℕ) :
    Config k (fun s => Fin (augmentedDimensions (V := V) q (fun _ => d) s)) ≃
      (Fin k → (V → Fin q)) × ((Fin k → Fin d) × (Fin k → Fin d)) :=
  (augmentedReplicaConfigurationEquiv q d k).symm.trans
    (globalReplicaCopiesEquiv (fun _ : V => Fin q) (Fin d) (Fin d) k)

/-- The physical replica mean extended by the identities on C and R,
expressed in the scanner coordinates. The equality also holds at k = 0,
where the normalized replica sum is zero.
Source: 06-transport.tex, lines 335–358; 07-comparators.tex, lines 421–438,
revision adc7f1241b42e322a6451854ab7e4b4c146bf78a. -/
theorem copyMean_augmentOperator_eq_replicaHamiltonian_kronecker
    (q d k : ℕ) (H : Matrix (V → Fin q) (V → Fin q) ℂ) :
    copyMean (augmentedDimensions (V := V) q (fun _ => d)) k
        (augmentOperator q (fun _ => d) H) =
      (((k : ℂ)⁻¹ • Matrix.replicaHamiltonian H k) ⊗ₖ
        (1 : Matrix ((Fin k → Fin d) × (Fin k → Fin d))
          ((Fin k → Fin d) × (Fin k → Fin d)) ℂ)).submatrix
        (augmentedSumReplicaCopiesEquiv q d k)
        (augmentedSumReplicaCopiesEquiv q d k) := by
  simp only [copyMean, siteOp_eq_finKronecker]
  change (k : ℂ)⁻¹ • Matrix.replicaHamiltonian (augmentOperator q (fun _ => d) H) k = _
  rw [augmentOperator]
  let e : SiteConfig (augmentedDimensions (V := V) q (fun _ => d)) ≃
      (V → Fin q) × (Bool → Fin d) :=
    Equiv.sumPiEquivProdPi
      (fun v : V ⊕ Bool => Fin (augmentedDimensions q (fun _ => d) v))
  change (k : ℂ)⁻¹ • Matrix.replicaHamiltonian
    ((H ⊗ₖ (1 : Matrix (Bool → Fin d) (Bool → Fin d) ℂ)).submatrix e e) k = _
  have hcov := Matrix.replicaHamiltonian_submatrix_equiv
    (H ⊗ₖ (1 : Matrix (Bool → Fin d) (Bool → Fin d) ℂ)) e.symm k
  simp only [Equiv.symm_symm] at hcov
  rw [hcov]
  have hmean := TensorPower.replicaMean_kronecker_one (B := Bool → Fin d) H k
  simp only [siteOp_eq_finKronecker] at hmean
  change (k : ℂ)⁻¹ • Matrix.replicaHamiltonian
      (H ⊗ₖ (1 : Matrix (Bool → Fin d) (Bool → Fin d) ℂ)) k =
    (((k : ℂ)⁻¹ • Matrix.replicaHamiltonian H k) ⊗ₖ
      (1 : Matrix (Fin k → Bool → Fin d) (Fin k → Bool → Fin d) ℂ)).submatrix
        (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => V → Fin q)
          (fun _ => Bool → Fin d))
        (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => V → Fin q)
          (fun _ => Bool → Fin d)) at hmean
  change ((k : ℂ)⁻¹ • Matrix.replicaHamiltonian
    (H ⊗ₖ (1 : Matrix (Bool → Fin d) (Bool → Fin d) ℂ)) k).submatrix
      ((Equiv.refl (Fin k)).arrowCongr e.symm).symm
      ((Equiv.refl (Fin k)).arrowCongr e.symm).symm = _
  rw [hmean]
  ext x y
  simp only [Matrix.submatrix_apply, Matrix.kroneckerMap_apply, Matrix.one_apply]
  change ((k : ℂ)⁻¹ • Matrix.replicaHamiltonian H k)
      (fun j v => x j (Sum.inl v)) (fun j v => y j (Sum.inl v)) *
      (if (fun j b => x j (Sum.inr b)) = (fun j b => y j (Sum.inr b)) then 1 else 0) =
    ((k : ℂ)⁻¹ • Matrix.replicaHamiltonian H k)
      (fun j v => x j (Sum.inl v)) (fun j v => y j (Sum.inl v)) *
      (if ((fun j => x j (Sum.inr false)), (fun j => x j (Sum.inr true))) =
        ((fun j => y j (Sum.inr false)), (fun j => y j (Sum.inr true))) then 1 else 0)
  simp only [Prod.mk.injEq, funext_iff, Bool.forall_bool, forall_and]

end TNLean.PEPS.AreaLaw.Scan
