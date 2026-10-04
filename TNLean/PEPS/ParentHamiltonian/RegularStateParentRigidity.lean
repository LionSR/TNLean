/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegularRegionSupport
import TNLean.PEPS.ParentHamiltonian.RegularRegionEntropyBound

/-!
# Parent spaces determined by a regular G-injective state

Proportional closed PEPS vectors have the same physical reduced supports.
For regular G-injective tensors across connected cuts, these supports are
the regional PEPS spaces. Consequently the physical ray determines the
admissible regional parent interactions, the canonical regional projectors,
and the common parent ground space for any prescribed family of such cuts.
The two tensor descriptions may use different finite virtual groups.

**Scope restriction (regular connected cuts):** Every site is injective on
the regular invariant virtual space, and both induced sides of each cut
are connected. See `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

Source: consequences of SCP10, arXiv:1001.3807, Definition 5.1, Lemma 5.2,
and the regular cut in Theorem 6.9, lines 1278–1358 and 2043–2076;
the general parent-interaction definition is CPGSV21, arXiv:2011.12127,
Section IV.C.1, lines 2003–2011. These are local necessary consequences,
not a bondwise Fundamental Theorem.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- J. I. Cirac, D. Pérez-García,
  N. Schuch, F. Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*
-/

open scoped Matrix ComplexOrder

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}

/-- Scaling the closed physical vector scales its reduced density by the
squared modulus of the scalar. Source: the physical reduction in
CPGSV21, Section IV.C.1, lines 2003–2011. -/
theorem regionReducedDensity_of_stateCoeff_smul {A B : Tensor Γ d}
    {c : ℂ} (hψ : stateCoeff B = c • stateCoeff A) (R : Finset V) :
    regionReducedDensity B R = (c * star c) • regionReducedDensity A R := by
  classical
  ext σ θ
  simp only [regionReducedDensity, Matrix.partialTraceRight_apply, Matrix.vecMulVec_apply,
    Pi.star_apply, Function.comp_apply, hψ, Pi.smul_apply, smul_eq_mul,
    Matrix.smul_apply, star_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ _
  ring

/-- A nonzero rescaling of the closed physical vector preserves every
regional reduced support. Source: the physical reduction in CPGSV21,
Section IV.C.1, lines 2003–2011. -/
theorem range_regionReducedDensity_of_stateCoeff_smul {A B : Tensor Γ d}
    {c : ℂ} (hc : c ≠ 0) (hψ : stateCoeff B = c • stateCoeff A) (R : Finset V) :
    (Matrix.mulVecLin (regionReducedDensity B R)).range =
      (Matrix.mulVecLin (regionReducedDensity A R)).range := by
  rw [regionReducedDensity_of_stateCoeff_smul hψ R]
  change (Matrix.toLin' ((c * star c) • regionReducedDensity A R)).range =
    (Matrix.toLin' (regionReducedDensity A R)).range
  rw [map_smul]
  exact LinearMap.range_smul _ _ (mul_ne_zero hc (star_ne_zero.mpr hc))

/-- Schmidt ranks depend only on a nonzero physical ray.
Source: the physical reduction in CPGSV21, Section IV.C.1, lines 2003–2011. -/
theorem rank_regionReducedDensity_of_stateCoeff_smul {A B : Tensor Γ d}
    {c : ℂ} (hc : c ≠ 0) (hψ : stateCoeff B = c • stateCoeff A) (R : Finset V) :
    (regionReducedDensity B R).rank = (regionReducedDensity A R).rank := by
  change Module.finrank ℂ (Matrix.mulVecLin (regionReducedDensity B R)).range =
    Module.finrank ℂ (Matrix.mulVecLin (regionReducedDensity A R)).range
  rw [range_regionReducedDensity_of_stateCoeff_smul hc hψ R]

/-- The normalized physical reduced state depends only on the nonzero
physical ray. The identity also holds when both vectors vanish.
Source: the normalized physical reduction in CPGSV21,
Section IV.C.1, lines 2003–2011. -/
theorem normalizedRegionReducedDensity_of_stateCoeff_smul {A B : Tensor Γ d}
    {c : ℂ} (hc : c ≠ 0) (hψ : stateCoeff B = c • stateCoeff A) (R : Finset V) :
    normalizedRegionReducedDensity B R = normalizedRegionReducedDensity A R := by
  simp only [normalizedRegionReducedDensity, regionReducedDensity_of_stateCoeff_smul hψ R,
    Matrix.trace_smul, smul_eq_mul, mul_inv_rev, smul_smul]
  simp only [mul_assoc]
  rw [inv_mul_cancel_left₀ hc, inv_mul_cancel₀ (star_ne_zero.mpr hc), mul_one]

/-- Equal regional spaces determine the same class of positive parent
interactions. Source: CPGSV21, Section IV.C.1, lines 2003–2011. -/
theorem isRegionParentInteraction_iff_of_regionGroundSpace_eq
    {A B : Tensor Γ d} {R : Finset V}
    (hR : regionGroundSpace A R = regionGroundSpace B R)
    (h : Matrix (RegionPhysicalConfig (d := d) R)
      (RegionPhysicalConfig (d := d) R) ℂ) :
    IsRegionParentInteraction A R h ↔ IsRegionParentInteraction B R h := by
  simp only [IsRegionParentInteraction, hR]

/-- The canonical local projector depends only on the regional physical
space. Source: CPGSV21, Section IV.C.1, lines 2003–2011. -/
theorem canonicalRegionParentInteraction_eq_of_regionGroundSpace_eq
    {A B : Tensor Γ d} {R : Finset V}
    (hR : regionGroundSpace A R = regionGroundSpace B R) :
    canonicalRegionParentInteraction A R = canonicalRegionParentInteraction B R := by
  simp only [canonicalRegionParentInteraction, regionGroundSpaceES, hR]

variable {ι : Type*}

/-- The common parent ground space depends only on the prescribed regional
spaces. Source: CPGSV21, Section IV.C.1, lines 2003–2011. -/
theorem regionParentGroundSpace_eq_of_regionGroundSpace_eq
    {A B : Tensor Γ d} (R : ι → Finset V)
    (hR : ∀ i, regionGroundSpace A (R i) = regionGroundSpace B (R i)) :
    regionParentGroundSpace A R = regionParentGroundSpace B R := by
  simp only [regionParentGroundSpace, hR]

/-- The canonical finite parent Hamiltonian depends only on its regional
spaces. Source: CPGSV21, Section IV.C.1, lines 2003–2011. -/
theorem canonical_regionParentHamiltonian_eq_of_regionGroundSpace_eq [Fintype ι]
    {A B : Tensor Γ d} (R : ι → Finset V)
    (hR : ∀ i, regionGroundSpace A (R i) = regionGroundSpace B (R i)) :
    regionParentHamiltonian R (fun i => canonicalRegionParentInteraction A (R i)) =
      regionParentHamiltonian R (fun i => canonicalRegionParentInteraction B (R i)) := by
  unfold regionParentHamiltonian
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (regionLocalTerm (R i))
    (canonicalRegionParentInteraction_eq_of_regionGroundSpace_eq (hR i))

variable {G H : Type*} [Group G] [Fintype G] [Group H] [Fintype H]

/-- The physical ray determines the regional PEPS space across any
connected cut of a connected finite graph. Different regular virtual
groups are allowed. Source: local consequence of SCP10,
Definition 5.1, Lemma 5.2, and Theorem 6.9,
lines 1278–1358 and 2043–2076. -/
theorem regionGroundSpace_eq_of_stateCoeff_smul_regular_connected
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (b : (v : V) → (IncidentEdge Γ v → H) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v)))
    (hb : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (b v))) {c : ℂ} (hc : c ≠ 0)
    (hψ : stateCoeff (groupBondTensor b) = c • stateCoeff (groupBondTensor a))
    (hΓ : Γ.Connected) (R : Finset V)
    (hR : (Γ.induce (R : Set V)).Connected)
    (hS : (Γ.induce ((Finset.univ \ R : Finset V) : Set V)).Connected) :
    regionGroundSpace (groupBondTensor a) R = regionGroundSpace (groupBondTensor b) R := by
  classical
  rw [← range_regionReducedDensity_eq_regionGroundSpace_of_regular_connected a ha hΓ R hR hS,
    ← range_regionReducedDensity_eq_regionGroundSpace_of_regular_connected b hb hΓ R hR hS]
  exact (range_regionReducedDensity_of_stateCoeff_smul hc hψ R).symm

/-- The physical ray of a regular G-injective PEPS determines the common
ground space for any family of connected cuts of a connected finite graph.
Source: local consequence of SCP10, Definition 5.1 and Lemma 5.2,
lines 1278–1358, and CPGSV21, Section IV.C.1, lines 2003–2011. -/
theorem regionParentGroundSpace_eq_of_stateCoeff_smul_regular_connected
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (b : (v : V) → (IncidentEdge Γ v → H) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v)))
    (hb : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (b v))) {c : ℂ} (hc : c ≠ 0)
    (hψ : stateCoeff (groupBondTensor b) = c • stateCoeff (groupBondTensor a))
    (hΓ : Γ.Connected) (R : ι → Finset V)
    (hR : ∀ i, (Γ.induce (R i : Set V)).Connected)
    (hS : ∀ i, (Γ.induce ((Finset.univ \ R i : Finset V) : Set V)).Connected) :
    regionParentGroundSpace (groupBondTensor a) R =
      regionParentGroundSpace (groupBondTensor b) R := by
  exact regionParentGroundSpace_eq_of_regionGroundSpace_eq R fun i =>
    regionGroundSpace_eq_of_stateCoeff_smul_regular_connected
      a b ha hb hc hψ hΓ (R i) (hR i) (hS i)

/-- A connected cut with at least two regular crossing bonds determines
the order of the virtual group from the physical ray. It does not determine
the group's multiplication. Source: auxiliary rigidity consequence of
SCP10, Corollary 6.10, lines 2074–2090. -/
theorem card_group_eq_of_stateCoeff_smul_regular_connected_cut
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (b : (v : V) → (IncidentEdge Γ v → H) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v)))
    (hb : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (b v))) {c : ℂ} (hc : c ≠ 0)
    (hψ : stateCoeff (groupBondTensor b) = c • stateCoeff (groupBondTensor a))
    (R : Finset V) (hR : (Γ.induce (R : Set V)).Connected)
    (hS : (Γ.induce ((Finset.univ \ R : Finset V) : Set V)).Connected)
    (n : ℕ) (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin (n + 2)) :
    Fintype.card G = Fintype.card H := by
  classical
  apply Nat.pow_left_injective (Nat.succ_ne_zero n)
  calc
    Fintype.card G ^ (n + 1) = (regionReducedDensity (groupBondTensor a) R).rank :=
      (rank_regionReducedDensity_of_regular_connected_cut a ha R hR hS (n + 1) e).symm
    _ = (regionReducedDensity (groupBondTensor b) R).rank :=
      (rank_regionReducedDensity_of_stateCoeff_smul hc hψ R).symm
    _ = Fintype.card H ^ (n + 1) :=
      rank_regionReducedDensity_of_regular_connected_cut b hb R hR hS (n + 1) e

end TNLean.PEPS
