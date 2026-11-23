/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.Region.RegionFullGroundSpace
import QICLean.Analysis.Projection.Geometry
import QICLean.ManyBody.Hamiltonian.Martingale.AbstractCriterion

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
theorem place_mulVec_apply (R : Finset V)
    (h : Matrix (RegionPhysicalConfig (d := d) R)
      (RegionPhysicalConfig (d := d) R) ℂ) (ψ : (V → Fin d) → ℂ) (σ : V → Fin d) :
    (ManyBody.place (X := fun _ ↦ Fin _) R h *ᵥ ψ) σ =
      ∑ ν : RegionPhysicalConfig (d := d) R,
        h (fun w => σ w.1) ν * ψ (regionReplaceConfig R ν σ) := by
  classical
  have hact := place_mulVec_assemble R h ψ (fun w => σ w.1) (fun w => σ w.1)
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

variable {ι : Type*} [Fintype ι]

/-- A positive quadratic-form bound \(γ \operatorname{Re}⟨Hψ, ψ⟩ ≤ \operatorname{Re}⟨Hψ, Hψ⟩\)
with \(γ > 0\) for a finite PEPS parent sum \(H\) implies that every eigenvalue of \(H\)
other than \(0\) is at least \(γ\). Source: CPGSV21, arXiv:2011.12127, equivalence of the
gap and \(H^2 ≥ γ H\), line 2170. -/
theorem forall_hasEigenvalue_hamiltonian_ofPlace_of_quadraticForm (R : ι → Finset V)
    (h : (i : ι) → Matrix (RegionPhysicalConfig (d := d) (R i))
      (RegionPhysicalConfig (d := d) (R i)) ℂ)
    (hh : ∀ i, (h i).PosSemidef) {γ : ℝ} (hγ : 0 < γ)
    (hQuad : ∀ ψ : EuclideanSpace ℂ (V → Fin d),
      γ * (⟪Matrix.toEuclideanLin
          (ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin d) R h).hamiltonian ψ, ψ⟫_ℂ).re ≤
        (⟪Matrix.toEuclideanLin
            (ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin d) R h).hamiltonian ψ,
          Matrix.toEuclideanLin
            (ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin d) R h).hamiltonian ψ⟫_ℂ).re) :
    ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
        (ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin d) R h).hamiltonian) μ →
      μ = 0 ∨ (γ : ℂ) ≤ μ := by
  classical
  exact FrustrationFree.forall_hasEigenvalue_of_martingale_of_finiteDimensional hγ
    (Matrix.isPositive_toEuclideanLin_iff.mpr
      (ManyBody.Interaction.posSemidef_hamiltonian
        (Φ := ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin d) R h)
        fun i ↦ ManyBody.posSemidef_place (X := fun _ ↦ Fin _) (hh i)))
    hQuad

open Classical in
/-- A bound on the number of overlaps and an anticommutator lower bound imply
the quadratic spectral-gap inequality for the canonical PEPS parent.
Source: CPGSV21, arXiv:2011.12127, projector expansion and pair bounds,
lines 2170–2179; this is its finite-overlap consequence on a general graph. -/
theorem hamiltonian_ofPlace_quadraticForm_of_overlap_anticommutator
    (A : Tensor Γ d) (R : ι → Finset V) {ε : ℝ} {m : ℕ}
    (hε : 0 ≤ ε) (hm : 0 < m)
    (hCard : ∀ i, ((Finset.univ.erase i).filter
      (fun j => ¬ Disjoint (R i) (R j))).card ≤ m)
    (hAnti :
      let P := fun i => Matrix.toEuclideanLin
        (ManyBody.place (X := fun _ ↦ Fin d) (R i) (canonicalRegionParentInteraction A (R i)))
      ∀ i j, j ∈ Finset.univ.erase i → ¬ Disjoint (R i) (R j) →
        ∀ ψ : EuclideanSpace ℂ (V → Fin d),
          -ε * ((⟪P i ψ, ψ⟫_ℂ).re + (⟪P j ψ, ψ⟫_ℂ).re) ≤
            (⟪P i ψ, P j ψ⟫_ℂ).re + (⟪P j ψ, P i ψ⟫_ℂ).re) :
    let H := Matrix.toEuclideanLin (ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin d) R
      (fun i => canonicalRegionParentInteraction A (R i))).hamiltonian
    ∀ ψ : EuclideanSpace ℂ (V → Fin d),
      (1 - (m : ℝ) * ε) * (⟪H ψ, ψ⟫_ℂ).re ≤ (⟪H ψ, H ψ⟫_ℂ).re := by
  classical
  let P := fun i => Matrix.toEuclideanLin
    (ManyBody.place (X := fun _ ↦ Fin d) (R i) (canonicalRegionParentInteraction A (R i)))
  have hP : ∀ i, (P i).IsSymmetricProjection :=
    fun i => place_canonical_isSymmetricProjection A (R i)
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hcoef : -(1 - (1 - (m : ℝ) * ε)) * (m : ℝ)⁻¹ = -ε := by
    field_simp
    ring
  have hquad := ProjectionGeometry.quadraticForm_sum_projections_of_finite_overlap_anticommutator
    (γ := 1 - (m : ℝ) * ε) (by nlinarith) P hP
    (fun i j => ¬ Disjoint (R i) (R j)) hm hCard
    (fun j => by simpa only [disjoint_comm] using hCard j)
    (fun i j hij hdis ψ => by
      have hcomm : Commute (P i) (P j) :=
        (ManyBody.commute_of_mem_supportedOperators_of_disjoint
          (ManyBody.place_mem_supportedOperators (X := fun _ ↦ Fin d) _)
          (ManyBody.place_mem_supportedOperators (X := fun _ ↦ Fin d) _)
          (not_not.mp hdis)).map (Matrix.toLpLinAlgEquiv 2)
      have h₁ := (hP i).re_inner_apply_apply_nonneg_of_commute (hP j)
        (fun v => LinearMap.congr_fun hcomm.eq v) ψ
      have h₂ := (hP j).re_inner_apply_apply_nonneg_of_commute (hP i)
        (fun v => LinearMap.congr_fun hcomm.symm.eq v) ψ
      exact add_nonneg h₁ h₂)
    (fun i j hij hover ψ => by
      rw [hcoef]
      exact hAnti i j hij hover ψ)
  simpa only [ManyBody.Interaction.hamiltonian_ofPlace, map_sum, P] using hquad

open Classical in
/-- The finite-overlap anticommutator estimate implies that every eigenvalue of
the canonical PEPS parent other than \(0\) is at least \(1 - mε\), whenever this
number is positive. Source: CPGSV21, arXiv:2011.12127, projector-sum gap criterion,
lines 2170–2179. The pairwise estimate and overlap bound remain explicit hypotheses. -/
theorem forall_hasEigenvalue_hamiltonian_ofPlace_of_overlap_anticommutator
    (A : Tensor Γ d) (R : ι → Finset V) {ε : ℝ} {m : ℕ}
    (hε : 0 ≤ ε) (hm : 0 < m) (hmε : (m : ℝ) * ε < 1)
    (hCard : ∀ i, ((Finset.univ.erase i).filter
      (fun j => ¬ Disjoint (R i) (R j))).card ≤ m)
    (hAnti :
      let P := fun i => Matrix.toEuclideanLin
        (ManyBody.place (X := fun _ ↦ Fin d) (R i) (canonicalRegionParentInteraction A (R i)))
      ∀ i j, j ∈ Finset.univ.erase i → ¬ Disjoint (R i) (R j) →
        ∀ ψ : EuclideanSpace ℂ (V → Fin d),
          -ε * ((⟪P i ψ, ψ⟫_ℂ).re + (⟪P j ψ, ψ⟫_ℂ).re) ≤
            (⟪P i ψ, P j ψ⟫_ℂ).re + (⟪P j ψ, P i ψ⟫_ℂ).re) :
    let H := Matrix.toEuclideanLin (ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin d) R
      (fun i => canonicalRegionParentInteraction A (R i))).hamiltonian
    ∀ μ : ℂ, Module.End.HasEigenvalue H μ → μ = 0 ∨ ((1 - (m : ℝ) * ε : ℝ) : ℂ) ≤ μ := by
  classical
  exact forall_hasEigenvalue_hamiltonian_ofPlace_of_quadraticForm R
    (fun i => canonicalRegionParentInteraction A (R i))
    (fun i => canonicalRegionParentInteraction_posSemidef A (R i)) (sub_pos.mpr hmε)
    (hamiltonian_ofPlace_quadraticForm_of_overlap_anticommutator A R hε hm hCard hAnti)

/-- Pairwise commuting canonical PEPS parent terms give a parent whose eigenvalues
other than \(0\) are at least one. Source: CPGSV21, arXiv:2011.12127, commuting
nonnegative cross terms in the projector-sum expansion, lines 2170–2175.
Commutation is explicit here. -/
theorem forall_hasEigenvalue_one_hamiltonian_ofPlace_of_commute (A : Tensor Γ d)
    (R : ι → Finset V)
    (hComm : ∀ i j, Commute
      (ManyBody.place (X := fun _ ↦ Fin d) (R i) (canonicalRegionParentInteraction A (R i)))
      (ManyBody.place (X := fun _ ↦ Fin d) (R j) (canonicalRegionParentInteraction A (R j)))) :
    ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
        (ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin d) R
          (fun i => canonicalRegionParentInteraction A (R i))).hamiltonian) μ →
      μ = 0 ∨ (1 : ℂ) ≤ μ := by
  classical
  let P := fun i => Matrix.toEuclideanLin
    (ManyBody.place (X := fun _ ↦ Fin d) (R i) (canonicalRegionParentInteraction A (R i)))
  have hP : ∀ i, (P i).IsSymmetricProjection :=
    fun i => place_canonical_isSymmetricProjection A (R i)
  have hCommP : ∀ i j, Commute (P i) (P j) :=
    fun i j => (hComm i j).map (Matrix.toLpLinAlgEquiv 2)
  have hQuad := ProjectionGeometry.quadraticForm_sum_projections_of_anticommutator_rowCol
    (γ := 1) (le_refl 1) P hP (fun _ _ => 0)
    (fun _ => by simp) (fun _ => by simp)
    (fun i j hij ψ => by
      have h₁ := (hP i).re_inner_apply_apply_nonneg_of_commute (hP j)
        (fun v => LinearMap.congr_fun (hCommP i j).eq v) ψ
      have h₂ := (hP j).re_inner_apply_apply_nonneg_of_commute (hP i)
        (fun v => LinearMap.congr_fun (hCommP i j).symm.eq v) ψ
      simp only [sub_self, neg_zero, zero_mul]
      exact add_nonneg h₁ h₂)
  simpa only [Complex.ofReal_one] using
    forall_hasEigenvalue_hamiltonian_ofPlace_of_quadraticForm R
      (fun i => canonicalRegionParentInteraction A (R i))
      (fun i => canonicalRegionParentInteraction_posSemidef A (R i)) zero_lt_one
      (by simpa only [ManyBody.Interaction.hamiltonian_ofPlace, map_sum, P] using hQuad)

/-- A finite canonical PEPS parent on pairwise disjoint regions has every
eigenvalue other than \(0\) at least one. Source: CPGSV21, arXiv:2011.12127, the
non-overlapping projector terms of the expansion, lines 2170–2175. -/
theorem forall_hasEigenvalue_one_hamiltonian_ofPlace_of_pairwise_disjoint (A : Tensor Γ d)
    (R : ι → Finset V) (hDisjoint : Pairwise (fun i j => Disjoint (R i) (R j))) :
    ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
        (ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin d) R
          (fun i => canonicalRegionParentInteraction A (R i))).hamiltonian) μ →
      μ = 0 ∨ (1 : ℂ) ≤ μ := by
  apply forall_hasEigenvalue_one_hamiltonian_ofPlace_of_commute A R
  intro i j
  rcases eq_or_ne i j with rfl | hij
  · exact Commute.refl _
  · exact ManyBody.commute_of_mem_supportedOperators_of_disjoint
      (ManyBody.place_mem_supportedOperators (X := fun _ ↦ Fin d) _)
      (ManyBody.place_mem_supportedOperators (X := fun _ ↦ Fin d) _) (hDisjoint hij)

open Classical in
/-- A uniform comparison with the canonical interaction transfers the
finite-overlap gap to arbitrary positive regional parent interactions: every
eigenvalue other than \(0\) is at least \(κ(1 - mε)\).
Source: CPGSV21, arXiv:2011.12127, comparison with projections and the
projector-sum expansion, lines 2170–2179. Both bounds are explicit hypotheses. -/
theorem forall_hasEigenvalue_hamiltonian_ofPlace_of_overlap_of_comparison
    (A : Tensor Γ d) (R : ι → Finset V)
    (h : (i : ι) → Matrix (RegionPhysicalConfig (d := d) (R i))
      (RegionPhysicalConfig (d := d) (R i)) ℂ)
    (hh : ∀ i, IsRegionParentInteraction A (R i) (h i))
    {κ ε : ℝ} {m : ℕ} (hκ : 0 < κ) (hε : 0 ≤ ε) (hm : 0 < m)
    (hmε : (m : ℝ) * ε < 1)
    (hLower : (κ : ℂ) •
      (ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin d) R
        (fun i => canonicalRegionParentInteraction A (R i))).hamiltonian ≤
        (ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin d) R h).hamiltonian)
    (hCard : ∀ i, ((Finset.univ.erase i).filter
      (fun j => ¬ Disjoint (R i) (R j))).card ≤ m)
    (hAnti :
      let P := fun i => Matrix.toEuclideanLin
        (ManyBody.place (X := fun _ ↦ Fin d) (R i) (canonicalRegionParentInteraction A (R i)))
      ∀ i j, j ∈ Finset.univ.erase i → ¬ Disjoint (R i) (R j) →
        ∀ ψ : EuclideanSpace ℂ (V → Fin d),
          -ε * ((⟪P i ψ, ψ⟫_ℂ).re + (⟪P j ψ, ψ⟫_ℂ).re) ≤
            (⟪P i ψ, P j ψ⟫_ℂ).re + (⟪P j ψ, P i ψ⟫_ℂ).re) :
    ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
        (ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin d) R h).hamiltonian) μ →
      μ = 0 ∨ ((κ * (1 - (m : ℝ) * ε) : ℝ) : ℂ) ≤ μ := by
  exact forall_hasEigenvalue_hamiltonian_ofPlace_of_comparison A R h
    (fun i => canonicalRegionParentInteraction A (R i)) hh
    (fun i => isRegionParentInteraction_canonical A (R i)) hκ hLower
    (forall_hasEigenvalue_hamiltonian_ofPlace_of_overlap_anticommutator A R hε hm hmε hCard hAnti)

section UniformFamily

variable {Λ : Type*} {vertices : Λ → Type*} {terms : Λ → Type*}
variable [∀ L, Fintype (vertices L)] [∀ L, LinearOrder (vertices L)]
variable [∀ L, Fintype (terms L)]
variable {graph : (L : Λ) → SimpleGraph (vertices L)}
variable [∀ L, DecidableRel (graph L).Adj] {physicalDim : Λ → ℕ}

open Classical in
/-- The finite-overlap estimate is uniform over a family of finite graphs
when its overlap degree and pairwise constant are independent of the graph:
for every parent in the family, every eigenvalue other than \(0\) is at least
the same positive number \(1 - mε\).
Source: CPGSV21, arXiv:2011.12127, the system-size-independent gap criterion
in Section IV.C.3, lines 2167–2179. The pairwise estimate remains explicit. -/
theorem uniform_forall_hasEigenvalue_hamiltonian_ofPlace_of_overlap_anticommutator
    (A : (L : Λ) → Tensor (graph L) (physicalDim L))
    (R : (L : Λ) → terms L → Finset (vertices L)) {ε : ℝ} {m : ℕ}
    (hε : 0 ≤ ε) (hm : 0 < m) (hmε : (m : ℝ) * ε < 1)
    (hCard : ∀ L i, ((Finset.univ.erase i).filter
      (fun j => ¬ Disjoint (R L i) (R L j))).card ≤ m)
    (hAnti : ∀ L,
      let P := fun i => Matrix.toEuclideanLin
        (ManyBody.place (X := fun _ ↦ Fin (physicalDim L)) (R L i)
          (canonicalRegionParentInteraction (A L) (R L i)))
      ∀ i j, j ∈ Finset.univ.erase i → ¬ Disjoint (R L i) (R L j) →
        ∀ ψ : EuclideanSpace ℂ (vertices L → Fin (physicalDim L)),
          -ε * ((⟪P i ψ, ψ⟫_ℂ).re + (⟪P j ψ, ψ⟫_ℂ).re) ≤
            (⟪P i ψ, P j ψ⟫_ℂ).re + (⟪P j ψ, P i ψ⟫_ℂ).re) :
    let H := fun L => Matrix.toEuclideanLin
      (ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin (physicalDim L)) (R L)
        (fun i => canonicalRegionParentInteraction (A L) (R L i))).hamiltonian
    0 < 1 - (m : ℝ) * ε ∧
      ∀ L, ∀ μ : ℂ, Module.End.HasEigenvalue (H L) μ →
        μ = 0 ∨ ((1 - (m : ℝ) * ε : ℝ) : ℂ) ≤ μ := by
  refine ⟨sub_pos.mpr hmε, fun L => ?_⟩
  exact forall_hasEigenvalue_hamiltonian_ofPlace_of_overlap_anticommutator
    (A L) (R L) hε hm hmε (hCard L) (hAnti L)

end UniformFamily

end TNLean.PEPS
