/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.AugmentedReplicaMetricCoordinates
import QICLean.Representation.ReplicaTransport.RootCompression

/-!
# The actual transport root in the original site coordinates

Each terminal partition is pulled back through the existing augmented-site
equivalence. The compressed band means, their ordered product and the
filtered vector retain the supplied isometry and the original tree.
Identifying these terminal regions with the physical near, middle and far
regions is a separate geometric application.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`06-transport.tex`, `transport:means`, lines 57--61, 120--128 and 268--286;
`transport:filtered-vector`, lines 388--392; `07-comparators.tex`,
`comparator:metrics`, lines 80--110, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix PermutationRepresentation Entropy
open TensorPower TensorPower.ReplicaTransport
open scoped Matrix ComplexOrder MatrixOrder unitInterval

noncomputable section

namespace TNLean.PEPS.AreaLaw.Scan

variable {V : Type} [Fintype V] [DecidableEq V]

local notation "ιO" q:max d:max =>
  addedSiteSpace (addedSiteSpace (fun _ : V => Fin q) (Fin d)) (Fin d)
local notation "nS" q:max d:max => augmentedDimensions (V := V) q (fun _ => d)
local notation "ιS" q:max d:max => fun s => Fin ((nS q d) s)

local instance augmentedRootOriginalConfigDecidableEq (q d k : ℕ) :
    DecidableEq (Config k (ιO q d)) := Fintype.decidablePiFintype

local instance augmentedRootScannerConfigDecidableEq (q d k : ℕ) :
    DecidableEq (Config k (ιS q d)) := Fintype.decidablePiFintype

/-- The actual band matrix in the original site coordinates. The inverse
images retain all three regions and the original full-system weights.
No partition or positivity premise is needed for this equality.
Source: area-law manuscript, `05-replicas.tex`, `replicas:leaf-metric`,
lines 459--473; `06-transport.tex`, lines 251--256; `07-comparators.tex`,
lines 80--110, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem bandMetric_submatrix_augmentedReplicaConfigurationEquiv
    (q d k : ℕ) (t : ℝ) (π : PYF (V ⊕ Bool)) :
    bandMetric (nS q d) t k π =
      (((replicaMetric (ιO q d) t k (π.P.image augmentedSiteEquiv.symm))⁻¹ *
        (replicaMetric (ιO q d) t k (π.F.image augmentedSiteEquiv.symm))⁻¹ *
          replicaMetric (ιO q d) t k (π.Y.image augmentedSiteEquiv.symm)) ^ 2).submatrix
            (augmentedReplicaConfigurationEquiv q d k).symm
            (augmentedReplicaConfigurationEquiv q d k).symm := by
  classical
  done

/-- The same actual root and supplied symmetric coordinates give the
ordered product of original-coordinate compressed band means. Real powers
and the normalized filtering formula retain the same vector, including
the zero-vector case. The interpolation parameter is arbitrary.
Source: area-law manuscript, `06-transport.tex`, `transport:means`,
lines 57--61, 120--128 and 268--286; `transport:filtered-vector`,
lines 388--392; `07-comparators.tex`, `comparator:metrics`, lines 80--110,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem rootPath_augmented_compressed_bandProduct
    (q d : ℕ) [NeZero q] [NeZero d]
    {K : ℕ} {H : Type*} [DecidableEq H] {C : H → Type*}
    [∀ h, DecidableEq (C h)]
    (D : TransportData (V ⊕ Bool) K H C) (hD : D.IsAdmissible)
    {t : ℝ} (ht : 0 ≤ t) (k N : ℕ)
    (hcomm : D.CrossBandCommute (nS q d) t k)
    (ZS : Matrix (Config k (ιS q d)) (Fin N) ℂ)
    (hZ : ZSᴴ * ZS = 1)
    (hZZ : ZS * ZSᴴ = symProj (copyPerm (SiteConfig (nS q d)) k))
    (preS : Config k (ιS q d) → ℂ)
    (hsym : symProj (copyPerm (SiteConfig (nS q d)) k) *ᵥ preS = preS)
    (p : ℝ) :
    let e := augmentedReplicaConfigurationEquiv (V := V) q d k
    let ZO := ZS.submatrix e id
    let vO := preS ∘ e
    let T := D.tree (Set.projIcc (0 : ℝ) 1 zero_le_one p)
    let AO := fun (j : Σ h, Option (C h)) (g : Fin K) =>
      ((replicaMetric (ιO q d) t k
          ((D.leafPart j g).P.image augmentedSiteEquiv.symm))⁻¹ *
        (replicaMetric (ιO q d) t k
          ((D.leafPart j g).F.image augmentedSiteEquiv.symm))⁻¹ *
        replicaMetric (ιO q d) t k
          ((D.leafPart j g).Y.image augmentedSiteEquiv.symm)) ^ 2
    let B := fun j g => ZOᴴ * AO j g * ZO
    let M := (List.ofFn fun g : Fin K => T.eval (B · g)).prod
    let w := Matrix.toEuclideanLin (M ^ (-(1 / 4) : ℝ))
      (WithLp.toLp 2 (ZOᴴ *ᵥ vO))
    M.PosDef ∧
      D.rootPath (nS q d) t k p * ZS = ZS * M ∧
      (∀ r : ℝ, D.rootPath (nS q d) t k p ^ r * ZS = ZS * M ^ r) ∧
      Transport.filteredNormSq (D.rootPath (nS q d) t k p) preS = ‖w‖ ^ 2 ∧
      Transport.filteredVector (D.rootPath (nS q d) t k p) preS =
        ZS *ᵥ ((‖w‖⁻¹ : ℂ) • w).ofLp := by
  classical
  intro e ZO vO T AO B M w
  have hroot := TransportData.rootPath_compressed_bandProduct
    (nS q d) D hD ht k N hcomm ZS hZ hZZ p
  have hrecover : ZO.submatrix e.symm (id : Fin N → Fin N) = ZS := by
    simp only [ZO, Matrix.submatrix_submatrix, Function.comp_id, Equiv.self_comp_symm,
      Matrix.submatrix_id_id]
  have hA (j : Σ h, Option (C h)) (g : Fin K) :
      bandMetric (nS q d) t k (D.leafPart j g) =
        (AO j g).submatrix e.symm e.symm :=
    bandMetric_submatrix_augmentedReplicaConfigurationEquiv q d k t (D.leafPart j g)
  have hB (j : Σ h, Option (C h)) (g : Fin K) :
      ZSᴴ * bandMetric (nS q d) t k (D.leafPart j g) * ZS = B j g := by
    simp only [B, hA, ← hrecover, Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  have hroot' : M.PosDef ∧ D.rootPath (nS q d) t k p * ZS = ZS * M := by
    simpa only [M, T, hB] using hroot
  done

end TNLean.PEPS.AreaLaw.Scan
