/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegionFullGroundSpace
import QICLean.Analysis.ProjectionGeometry
import TNLean.MPS.ParentHamiltonian.Martingale.AbstractCriterion

/-!
# Finite-overlap gap criteria for PEPS parents

Canonical regional parent terms are orthogonal projections. Terms on disjoint
regions commute, while anticommutator estimates on overlapping regions give a
lower spectral-gap bound controlled by the number of overlaps per region.

Source: CPGSV21, arXiv:2011.12127, the parent construction in Section IV.C.1,
lines 2003–2011, and the projector-sum expansion and anticommutator criterion
in Section IV.C.3, lines 2170–2179. The overlapping-pair estimate is an explicit
hypothesis; no implication from boundary locality is assumed.

## References

- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- J. I. Cirac, D. Pérez-García,
  N. Schuch, F. Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*
-/

open scoped BigOperators InnerProductSpace Matrix ComplexOrder MatrixOrder

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}

/-- Replace the physical labels on a region, retaining those on its complement.
Source: CPGSV21, arXiv:2011.12127, local physical action, lines 2003–2011. -/
def regionReplaceConfig (R : Finset V) (ν : RegionPhysicalConfig (d := d) R)
    (σ : V → Fin d) : V → Fin d :=
  assembleRegionσ R ν (fun w => σ w.1)

/-- A regional term acts by summing only the physical indices in its region.
Source: CPGSV21, arXiv:2011.12127, regional extensions, lines 2003–2011. -/
theorem regionLocalTerm_mulVec_apply (R : Finset V)
    (h : Matrix (RegionPhysicalConfig (d := d) R)
      (RegionPhysicalConfig (d := d) R) ℂ) (ψ : (V → Fin d) → ℂ) (σ : V → Fin d) :
    (regionLocalTerm R h *ᵥ ψ) σ =
      ∑ ν : RegionPhysicalConfig (d := d) R,
        h (fun w => σ w.1) ν * ψ (regionReplaceConfig R ν σ) := by
  classical
  have hact := regionLocalTerm_mulVec_assemble R h ψ (fun w => σ w.1) (fun w => σ w.1)
  have hrec : assembleRegionσ R (fun w => σ w.1) (fun w => σ w.1) = σ := by
    funext v
    simp [assembleRegionσ]
  simpa only [hrec, Matrix.mulVec, dotProduct, regionReplaceConfig] using hact

/-- A replacement in one region leaves the physical labels in a disjoint region
unchanged. Source: CPGSV21, arXiv:2011.12127, disjoint local actions, line 2175. -/
theorem regionReplaceConfig_apply_of_disjoint {R S : Finset V} (hRS : Disjoint R S)
    (ν : RegionPhysicalConfig (d := d) R) (σ : V → Fin d) (w : {w : V // w ∈ S}) :
    regionReplaceConfig R ν σ w.1 = σ w.1 := by
  have hwR : w.1 ∉ R := fun hw => Finset.disjoint_left.mp hRS hw w.2
  simp [regionReplaceConfig, assembleRegionσ, hwR]

/-- Replacing physical labels on disjoint regions commutes.
Source: CPGSV21, arXiv:2011.12127, disjoint local actions, line 2175. -/
theorem regionReplaceConfig_comm_of_disjoint {R S : Finset V} (hRS : Disjoint R S)
    (ν : RegionPhysicalConfig (d := d) R) (ω : RegionPhysicalConfig (d := d) S)
    (σ : V → Fin d) :
    regionReplaceConfig S ω (regionReplaceConfig R ν σ) =
      regionReplaceConfig R ν (regionReplaceConfig S ω σ) := by
  funext v
  by_cases hvR : v ∈ R
  · have hvS : v ∉ S := fun hv => Finset.disjoint_left.mp hRS hvR hv
    simp [regionReplaceConfig, assembleRegionσ, hvR, hvS]
  · by_cases hvS : v ∈ S <;>
      simp [regionReplaceConfig, assembleRegionσ, hvR, hvS]

/-- Regional operators on disjoint vertex sets commute on the full physical
space. Source: CPGSV21, arXiv:2011.12127, non-overlapping terms, lines 2171–2175. -/
theorem regionLocalTerm_commute_of_disjoint {R S : Finset V} (hRS : Disjoint R S)
    (h : Matrix (RegionPhysicalConfig (d := d) R)
      (RegionPhysicalConfig (d := d) R) ℂ)
    (k : Matrix (RegionPhysicalConfig (d := d) S)
      (RegionPhysicalConfig (d := d) S) ℂ) :
    Commute (regionLocalTerm R h) (regionLocalTerm S k) := by
  classical
  change regionLocalTerm R h * regionLocalTerm S k = regionLocalTerm S k * regionLocalTerm R h
  apply Matrix.toLin'.injective
  simp only [Matrix.toLin'_mul]
  refine LinearMap.ext fun ψ => funext fun σ => ?_
  simp only [LinearMap.comp_apply, Matrix.toLin'_apply]
  simp_rw [regionLocalTerm_mulVec_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω hω
  apply Finset.sum_congr rfl
  intro ν hν
  have hS : (fun w : {w : V // w ∈ S} => regionReplaceConfig R ν σ w.1) =
      fun w => σ w.1 := funext (regionReplaceConfig_apply_of_disjoint hRS ν σ)
  have hR : (fun w : {w : V // w ∈ R} => regionReplaceConfig S ω σ w.1) =
      fun w => σ w.1 := funext (regionReplaceConfig_apply_of_disjoint hRS.symm ω σ)
  rw [hS, hR, regionReplaceConfig_comm_of_disjoint hRS]
  ring

/-- A regional operator in the full physical Hilbert space with its standard
inner product. Source: CPGSV21, arXiv:2011.12127, regional extensions, lines 2003–2011. -/
noncomputable def regionLocalTermES (R : Finset V)
    (h : Matrix (RegionPhysicalConfig (d := d) R)
      (RegionPhysicalConfig (d := d) R) ℂ) :
    EuclideanSpace ℂ (V → Fin d) →ₗ[ℂ] EuclideanSpace ℂ (V → Fin d) :=
  Matrix.toEuclideanLin (regionLocalTerm R h)

/-- Disjoint regional operators commute in Euclidean coordinates.
Source: CPGSV21, arXiv:2011.12127, non-overlapping terms, lines 2171–2175. -/
theorem regionLocalTermES_commute_of_disjoint {R S : Finset V} (hRS : Disjoint R S)
    (h : Matrix (RegionPhysicalConfig (d := d) R)
      (RegionPhysicalConfig (d := d) R) ℂ)
    (k : Matrix (RegionPhysicalConfig (d := d) S)
      (RegionPhysicalConfig (d := d) S) ℂ) :
    Commute (regionLocalTermES R h) (regionLocalTermES S k) := by
  classical
  have hc := congrArg Matrix.toEuclideanLin (regionLocalTerm_commute_of_disjoint hRS h k).eq
  change regionLocalTermES R h * regionLocalTermES S k =
    regionLocalTermES S k * regionLocalTermES R h
  rw [Matrix.toLpLin_mul 2 2 2, Matrix.toLpLin_mul 2 2 2] at hc
  exact hc

variable {ι : Type*} [Fintype ι]

/-- The regional parent sum in the full physical Hilbert space.
Source: CPGSV21, arXiv:2011.12127, parent Hamiltonian, lines 2003–2011. -/
noncomputable def regionParentHamiltonianES (R : ι → Finset V)
    (h : (i : ι) → Matrix (RegionPhysicalConfig (d := d) (R i))
      (RegionPhysicalConfig (d := d) (R i)) ℂ) :
    EuclideanSpace ℂ (V → Fin d) →ₗ[ℂ] EuclideanSpace ℂ (V → Fin d) :=
  Matrix.toEuclideanLin (regionParentHamiltonian R h)

/-- The physical coordinate identification preserves the sum of regional terms.
Source: CPGSV21, arXiv:2011.12127, parent Hamiltonian sum, lines 2003–2011. -/
theorem regionParentHamiltonianES_eq_sum (R : ι → Finset V)
    (h : (i : ι) → Matrix (RegionPhysicalConfig (d := d) (R i))
      (RegionPhysicalConfig (d := d) (R i)) ℂ) :
    regionParentHamiltonianES R h = ∑ i, regionLocalTermES (R i) (h i) := by
  simp only [regionParentHamiltonianES, regionParentHamiltonian, map_sum, regionLocalTermES]

/-- A positive quadratic-form bound gives the same norm gap for a finite PEPS
parent sum. Source: CPGSV21, arXiv:2011.12127, equivalence of the gap and
`H² ≥ γ H`, line 2170. -/
theorem regionParentHamiltonianES_norm_gap_of_quadraticForm (R : ι → Finset V)
    (h : (i : ι) → Matrix (RegionPhysicalConfig (d := d) (R i))
      (RegionPhysicalConfig (d := d) (R i)) ℂ)
    (hh : ∀ i, (h i).PosSemidef) {γ : ℝ} (hγ : 0 < γ)
    (hQuad : ∀ ψ : EuclideanSpace ℂ (V → Fin d),
      γ * (⟪regionParentHamiltonianES R h ψ, ψ⟫_ℂ).re ≤
        (⟪regionParentHamiltonianES R h ψ, regionParentHamiltonianES R h ψ⟫_ℂ).re) :
    ∀ ψ ∈ (regionParentHamiltonianES R h).kerᗮ,
      γ * ‖ψ‖ ≤ ‖regionParentHamiltonianES R h ψ‖ := by
  classical
  exact FrustrationFree.spectralGap_of_martingale_of_finiteDimensional hγ
    (Matrix.isPositive_toEuclideanLin_iff.mpr (regionParentHamiltonian_posSemidef R h hh))
    hQuad

open Classical in
/-- A bound on the number of overlaps and an anticommutator lower bound imply
the quadratic spectral-gap inequality for the canonical PEPS parent.
Source: CPGSV21, arXiv:2011.12127, projector expansion and pair bounds,
lines 2170–2179; this is its finite-overlap consequence on a general graph. -/
theorem regionParentHamiltonianES_quadraticForm_of_overlap_anticommutator
    (A : Tensor Γ d) (R : ι → Finset V) {ε : ℝ} {m : ℕ}
    (hε : 0 ≤ ε) (hm : 0 < m)
    (hCard : ∀ i, ((Finset.univ.erase i).filter
      (fun j => ¬ Disjoint (R i) (R j))).card ≤ m)
    (hAnti : let P := fun i => regionLocalTermES (R i) (canonicalRegionParentInteraction A (R i))
      ∀ i j, j ∈ Finset.univ.erase i → ¬ Disjoint (R i) (R j) →
        ∀ ψ : EuclideanSpace ℂ (V → Fin d),
          -ε * ((⟪P i ψ, ψ⟫_ℂ).re + (⟪P j ψ, ψ⟫_ℂ).re) ≤
            (⟪P i ψ, P j ψ⟫_ℂ).re + (⟪P j ψ, P i ψ⟫_ℂ).re) :
    let H := regionParentHamiltonianES R (fun i => canonicalRegionParentInteraction A (R i))
    ∀ ψ : EuclideanSpace ℂ (V → Fin d),
      (1 - (m : ℝ) * ε) * (⟪H ψ, ψ⟫_ℂ).re ≤ (⟪H ψ, H ψ⟫_ℂ).re := by
  classical
  let P := fun i => regionLocalTermES (R i) (canonicalRegionParentInteraction A (R i))
  have hP : ∀ i, (P i).IsSymmetricProjection :=
    fun i => regionLocalTerm_canonical_isSymmetricProjection A (R i)
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hcoef : -(1 - (1 - (m : ℝ) * ε)) * (m : ℝ)⁻¹ = -ε := by
    field_simp
    ring
  have hquad := ProjectionGeometry.quadraticForm_sum_projections_of_finite_overlap_anticommutator
    (γ := 1 - (m : ℝ) * ε) (by nlinarith) P hP
    (fun i j => ¬ Disjoint (R i) (R j)) hm hCard
    (fun j => by simpa only [disjoint_comm] using hCard j)
    (fun i j hij hdis ψ => by
      have hcomm := regionLocalTermES_commute_of_disjoint (not_not.mp hdis)
        (canonicalRegionParentInteraction A (R i)) (canonicalRegionParentInteraction A (R j))
      have h₁ := (hP i).re_inner_apply_apply_nonneg_of_commute (hP j)
        (fun v => LinearMap.congr_fun hcomm.eq v) ψ
      have h₂ := (hP j).re_inner_apply_apply_nonneg_of_commute (hP i)
        (fun v => LinearMap.congr_fun hcomm.symm.eq v) ψ
      exact add_nonneg h₁ h₂)
    (fun i j hij hover ψ => by
      rw [hcoef]
      exact hAnti i j hij hover ψ)
  simpa only [regionParentHamiltonianES_eq_sum] using hquad

open Classical in
/-- The finite-overlap anticommutator estimate gives a gap of at least
`1 - m * ε` whenever this number is positive. Source: CPGSV21,
arXiv:2011.12127, projector-sum gap criterion, lines 2170–2179. The pairwise
estimate and overlap bound remain explicit hypotheses. -/
theorem regionParentHamiltonianES_norm_gap_of_overlap_anticommutator
    (A : Tensor Γ d) (R : ι → Finset V) {ε : ℝ} {m : ℕ}
    (hε : 0 ≤ ε) (hm : 0 < m) (hmε : (m : ℝ) * ε < 1)
    (hCard : ∀ i, ((Finset.univ.erase i).filter
      (fun j => ¬ Disjoint (R i) (R j))).card ≤ m)
    (hAnti : let P := fun i => regionLocalTermES (R i) (canonicalRegionParentInteraction A (R i))
      ∀ i j, j ∈ Finset.univ.erase i → ¬ Disjoint (R i) (R j) →
        ∀ ψ : EuclideanSpace ℂ (V → Fin d),
          -ε * ((⟪P i ψ, ψ⟫_ℂ).re + (⟪P j ψ, ψ⟫_ℂ).re) ≤
            (⟪P i ψ, P j ψ⟫_ℂ).re + (⟪P j ψ, P i ψ⟫_ℂ).re) :
    let H := regionParentHamiltonianES R (fun i => canonicalRegionParentInteraction A (R i))
    ∀ ψ ∈ H.kerᗮ, (1 - (m : ℝ) * ε) * ‖ψ‖ ≤ ‖H ψ‖ := by
  classical
  exact regionParentHamiltonianES_norm_gap_of_quadraticForm R
    (fun i => canonicalRegionParentInteraction A (R i))
    (fun i => canonicalRegionParentInteraction_posSemidef A (R i)) (sub_pos.mpr hmε)
    (regionParentHamiltonianES_quadraticForm_of_overlap_anticommutator A R hε hm hCard hAnti)

/-- Pairwise commuting canonical PEPS parent terms have norm gap at least one.
Source: CPGSV21, arXiv:2011.12127, commuting nonnegative cross terms in the
projector-sum expansion, lines 2170–2175. Commutation is explicit here. -/
theorem regionParentHamiltonianES_unit_norm_gap_of_commute (A : Tensor Γ d)
    (R : ι → Finset V)
    (hComm : let P := fun i => regionLocalTermES (R i) (canonicalRegionParentInteraction A (R i))
      ∀ i j, Commute (P i) (P j)) :
    let H := regionParentHamiltonianES R (fun i => canonicalRegionParentInteraction A (R i))
    ∀ ψ ∈ H.kerᗮ, (1 : ℝ) * ‖ψ‖ ≤ ‖H ψ‖ := by
  classical
  let P := fun i => regionLocalTermES (R i) (canonicalRegionParentInteraction A (R i))
  have hP : ∀ i, (P i).IsSymmetricProjection :=
    fun i => regionLocalTerm_canonical_isSymmetricProjection A (R i)
  have hQuad := ProjectionGeometry.quadraticForm_sum_projections_of_anticommutator_rowCol
    (γ := 1) (le_refl 1) P hP (fun _ _ => 0)
    (fun _ => by simp) (fun _ => by simp)
    (fun i j hij ψ => by
      have h₁ := (hP i).re_inner_apply_apply_nonneg_of_commute (hP j)
        (fun v => LinearMap.congr_fun (hComm i j).eq v) ψ
      have h₂ := (hP j).re_inner_apply_apply_nonneg_of_commute (hP i)
        (fun v => LinearMap.congr_fun (hComm i j).symm.eq v) ψ
      simp only [sub_self, neg_zero, zero_mul]
      exact add_nonneg h₁ h₂)
  apply regionParentHamiltonianES_norm_gap_of_quadraticForm R
    (fun i => canonicalRegionParentInteraction A (R i))
    (fun i => canonicalRegionParentInteraction_posSemidef A (R i)) zero_lt_one
  simpa only [regionParentHamiltonianES_eq_sum] using hQuad

/-- A finite canonical PEPS parent on pairwise disjoint regions has norm gap
at least one. Source: CPGSV21, arXiv:2011.12127, the non-overlapping
projector terms of the expansion, lines 2170–2175. -/
theorem regionParentHamiltonianES_unit_norm_gap_of_pairwise_disjoint (A : Tensor Γ d)
    (R : ι → Finset V) (hDisjoint : Pairwise (fun i j => Disjoint (R i) (R j))) :
    let H := regionParentHamiltonianES R (fun i => canonicalRegionParentInteraction A (R i))
    ∀ ψ ∈ H.kerᗮ, (1 : ℝ) * ‖ψ‖ ≤ ‖H ψ‖ := by
  apply regionParentHamiltonianES_unit_norm_gap_of_commute A R
  dsimp only
  intro i j
  rcases eq_or_ne i j with rfl | hij
  · exact Commute.refl _
  · exact regionLocalTermES_commute_of_disjoint (hDisjoint hij)
      (canonicalRegionParentInteraction A (R i)) (canonicalRegionParentInteraction A (R j))

open Classical in
/-- A uniform comparison with the canonical interaction transfers the
finite-overlap gap to arbitrary positive regional parent interactions.
Source: CPGSV21, arXiv:2011.12127, comparison with projections and the
projector-sum expansion, lines 2170–2179. Both bounds are explicit hypotheses. -/
theorem regionParentHamiltonianES_norm_gap_of_overlap_of_comparison
    (A : Tensor Γ d) (R : ι → Finset V)
    (h : (i : ι) → Matrix (RegionPhysicalConfig (d := d) (R i))
      (RegionPhysicalConfig (d := d) (R i)) ℂ)
    (hh : ∀ i, IsRegionParentInteraction A (R i) (h i))
    {κ ε : ℝ} {m : ℕ} (hκ : 0 < κ) (hε : 0 ≤ ε) (hm : 0 < m)
    (hmε : (m : ℝ) * ε < 1)
    (hLower : (κ : ℂ) •
      regionParentHamiltonian R (fun i => canonicalRegionParentInteraction A (R i)) ≤
        regionParentHamiltonian R h)
    (hCard : ∀ i, ((Finset.univ.erase i).filter
      (fun j => ¬ Disjoint (R i) (R j))).card ≤ m)
    (hAnti : let P := fun i => regionLocalTermES (R i) (canonicalRegionParentInteraction A (R i))
      ∀ i j, j ∈ Finset.univ.erase i → ¬ Disjoint (R i) (R j) →
        ∀ ψ : EuclideanSpace ℂ (V → Fin d),
          -ε * ((⟪P i ψ, ψ⟫_ℂ).re + (⟪P j ψ, ψ⟫_ℂ).re) ≤
            (⟪P i ψ, P j ψ⟫_ℂ).re + (⟪P j ψ, P i ψ⟫_ℂ).re) :
    ∀ ψ ∈ (regionParentHamiltonianES R h).kerᗮ,
      (κ * (1 - (m : ℝ) * ε)) * ‖ψ‖ ≤ ‖regionParentHamiltonianES R h ψ‖ := by
  exact regionParentHamiltonian_norm_gap_of_comparison A R h
    (fun i => canonicalRegionParentInteraction A (R i)) hh
    (fun i => isRegionParentInteraction_canonical A (R i))
    hκ (sub_pos.mpr hmε).le hLower
    (regionParentHamiltonianES_norm_gap_of_overlap_anticommutator A R hε hm hmε hCard hAnti)

section UniformFamily

variable {Λ : Type*} {vertices : Λ → Type*} {terms : Λ → Type*}
variable [∀ L, Fintype (vertices L)] [∀ L, LinearOrder (vertices L)]
variable [∀ L, Fintype (terms L)]
variable {graph : (L : Λ) → SimpleGraph (vertices L)}
variable [∀ L, DecidableRel (graph L).Adj] {physicalDim : Λ → ℕ}

open Classical in
/-- The finite-overlap estimate is uniform over a family of finite graphs
when its overlap degree and pairwise constant are independent of the graph.
Source: CPGSV21, arXiv:2011.12127, the system-size-independent gap criterion
in Section IV.C.3, lines 2167–2179. The pairwise estimate remains explicit. -/
theorem regionParentHamiltonianES_uniform_norm_gap_of_overlap_anticommutator
    (A : (L : Λ) → Tensor (graph L) (physicalDim L))
    (R : (L : Λ) → terms L → Finset (vertices L)) {ε : ℝ} {m : ℕ}
    (hε : 0 ≤ ε) (hm : 0 < m) (hmε : (m : ℝ) * ε < 1)
    (hCard : ∀ L i, ((Finset.univ.erase i).filter
      (fun j => ¬ Disjoint (R L i) (R L j))).card ≤ m)
    (hAnti : ∀ L,
      let P := fun i => regionLocalTermES (R L i)
        (canonicalRegionParentInteraction (A L) (R L i))
      ∀ i j, j ∈ Finset.univ.erase i → ¬ Disjoint (R L i) (R L j) →
        ∀ ψ : EuclideanSpace ℂ (vertices L → Fin (physicalDim L)),
          -ε * ((⟪P i ψ, ψ⟫_ℂ).re + (⟪P j ψ, ψ⟫_ℂ).re) ≤
            (⟪P i ψ, P j ψ⟫_ℂ).re + (⟪P j ψ, P i ψ⟫_ℂ).re) :
    let H := fun L => regionParentHamiltonianES (R L)
      (fun i => canonicalRegionParentInteraction (A L) (R L i))
    0 < 1 - (m : ℝ) * ε ∧
      ∀ L, ∀ ψ ∈ (H L).kerᗮ, (1 - (m : ℝ) * ε) * ‖ψ‖ ≤ ‖H L ψ‖ := by
  refine ⟨sub_pos.mpr hmε, fun L => ?_⟩
  exact regionParentHamiltonianES_norm_gap_of_overlap_anticommutator
    (A L) (R L) hε hm hmε (hCard L) (hAnti L)

end UniformFamily

end TNLean.PEPS
