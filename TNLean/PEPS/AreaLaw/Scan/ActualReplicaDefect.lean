/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.PEPS.AreaLaw.Scan.ActualGlobalReplicaEnergy
import QICLean.Analysis.RegionalLowDefectMass

/-!
# The gap estimate for the actual charge filtered vector

This is an application of the gap-to-projection estimate to the same filtered
vector that defines the actual charge mean energy. The reference vector Ω in
the truncated terms is retained. The gap and defect projection use the same supplied unit vector Ωt.
In the application, Ωt is the chosen ground vector of the truncated Hamiltonian.

Normalization follows from the positive metric root and a nonzero initial
vector. Simultaneous symmetry and auxiliary labels remain explicit conditions
on that actual vector. Their construction is a separate step; this conditional
statement does not construct physical scanner data.

Source: OpenAI, A two-dimensional area law from a global spectral gap,
07-comparators.tex, comparator:defect-mass, lines 421--443;
08-scanner.tex, lines 371--384 and 416--451, revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section
open Matrix TensorPower TensorPower.ReplicaTransport PermutationRepresentation
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open Classical in
/-- The literal actual charge filtered vector is normalized at every copy
count and every real interpolation parameter. Its root is positive definite
by the actual charge geometry; the parameter is clamped by the definition
of the root path. Nonvanishing concerns the same supplied initial vector.
Source: 06-transport.tex, transport:filtered-vector, lines 388--392;
08-scanner.tex, lines 371--384 and 416--451, adc7f124. -/
theorem norm_filteredVector_actualChargeData
    {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
    (S : CollarScan V I) (hm : 0 < S.m) (hM : 0 < S.M) (s : ℕ)
    (n : V ⊕ Bool → ℕ) [∀ x, NeZero (n x)]
    (a : ℝ) (ha : 0 ≤ a) (k : ℕ)
    (pre : Config k (fun x => Fin (n x)) → ℂ) (hpre : pre ≠ 0) (p : ℝ) :
    ‖WithLp.toLp 2
      (Matrix.Transport.filteredVector
        ((S.actualChargeData hm hM s).rootPath n (a / 2) k p) pre)‖ = 1 := by
  classical
  have hroot : ((S.actualChargeData hm hM s).rootPath n (a / 2) k p).PosDef :=
    Matrix.MeanTree.posDef_eval
      ((S.actualChargeData hm hM s).posDef_input
        (S.actualChargeData_isAdmissible hm hM s) (div_nonneg ha (by norm_num))
        (S.chargeTransportData_crossBandCommute _ _ n (div_nonneg ha (by norm_num)) k))
      ((S.actualChargeData hm hM s).tree (Set.projIcc (0 : ℝ) 1 zero_le_one p))
  have hsquare : ‖WithLp.toLp 2
      (Matrix.Transport.filteredVector
        ((S.actualChargeData hm hM s).rootPath n (a / 2) k p) pre)‖ ^ 2 = 1 :=
    (Matrix.re_star_dotProduct_self_eq_norm_sq _).symm.trans
      (congrArg Complex.re (Matrix.Transport.star_dotProduct_filteredVector hroot hpre))
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (hsquare.trans (one_pow 2).symm)

open Classical in
/-- The common low-defect projection of the supplied unit vector
has mass at least one minus the actual charge excess mean energy divided by
the full truncated gap and cutoff fraction. The physical Hamiltonian and
filtered vector are the ones in the actual charge energy identity.
The nonnegative metric parameter and nonzero initial vector are properties
of the physical construction; they are not additional hypotheses of the
area-law theorem. Their derivation from that construction is separate.
Source: 07-comparators.tex, comparator:defect-mass, lines 421--443;
08-scanner.tex, lines 371--384 and 416--451, adc7f124. -/
theorem actualChargeScanRound_globalLowDefectProjection_mass_ge
    {Λ : Finset (ℤ × ℤ)} {q d R : ℕ} {J : ℝ} [NeZero q] [NeZero d]
    [LinearOrder (AdmissibleSupport Λ R)]
    (S : CollarScan (Site Λ) (AdmissibleSupport Λ R))
    (hm : 0 < S.m) (hM : 0 < S.M) (s : ℕ)
    (h : LocalHamiltonian Λ q R J)
    (Ω : StateSpace Λ q) (Δ : ℝ) (L : ℕ)
    (Ωt : StateSpace Λ q) (e₀ g : ℝ)
    (hΩt : ‖Ωt‖ = 1)
    (hgap : ((∑ i, S.truncatedEnergyTerm h Ω Δ L i) - (e₀ : ℂ) • 1 -
      (g : ℂ) • (1 - Matrix.vecMulVec Ωt.ofLp (star Ωt.ofLp))).PosSemidef)
    (hg : 0 < g) (a : ℝ) (ha : 0 ≤ a)
    (pre : (k : ℕ) → Config k
      (fun v => Fin (augmentedDimensions (V := Site Λ) q (fun _ => d) v)) → ℂ)
    {k : ℕ} (hk : 0 < k) (hpre : pre k ≠ 0) (p : ℝ)
    (ellC ellR : IrrepLabel (Equiv.Perm (Fin k))) {τ : ℝ} (hτ : 0 < τ) :
    let β := fun _ : Site Λ => Fin q
    let ι₀ := addedSiteSpace (addedSiteSpace β (Fin d)) (Fin d)
    let n := augmentedDimensions (V := Site Λ) q (fun _ => d)
    let D := S.actualChargeData hm hM s
    let v := Matrix.Transport.filteredVector (D.rootPath n (a / 2) k p) (pre k)
    let vO : EuclideanSpace ℂ (Config k ι₀) :=
      WithLp.toLp 2 (v ∘ augmentedReplicaConfigurationEquiv q d k)
    symProj (copyPerm ((x : Option (Option (Site Λ))) → ι₀ x) k) *ᵥ vO = vO.ofLp →
    labelProj (subsystemPerm k ι₀ {some none}) ellC *ᵥ vO = vO.ofLp →
    labelProj (subsystemPerm k ι₀ {none}) ellR *ᵥ vO = vO.ofLp →
    1 - ((S.actualChargeScanRound hm hM s n
        (S.actualEnergyTerms h Ω Δ L (fun _ => d)) a pre).meanEnergy k p - e₀) / g / τ ≤
      (star vO ⬝ᵥ
        (Matrix.globalReplicaLowDefectProjection β (Fin d) (Fin d) Ωt.ofLp
          k ellC ellR τ *ᵥ vO)).re := by
  classical
  intro β ι₀ n D v vO hsym hC hR
  have hvO : ‖vO‖ = 1 :=
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (augmentedReplicaConfigurationEquiv q d k).symm).norm_map
        (WithLp.toLp 2 v)).trans
      (S.norm_filteredVector_actualChargeData hm hM s n a ha k (pre k) hpre p)
  simpa only [n, S.actualChargeScanRound_meanEnergy_eq_globalReplicaMeanHamiltonian
    hm hM s h Ω Δ L a pre k p] using
      Matrix.globalReplicaLowDefectProjection_gap_mass_ge β (Fin d) (Fin d)
        hgap hΩt hg hk ellC ellR hτ vO hvO hsym hC hR

end TNLean.PEPS.AreaLaw.Scan.CollarScan
