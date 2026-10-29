/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.CyclicFinitePropagation
import TNLean.MPS.MPU.TwoSiteFiniteInverse
import TNLean.QCA.IntervalSupport

/-!
# Boundary-free inverse support on the actual finite periodic chain

Forward singleton propagation through the seam reflects through the actual
finite MPU automorphism. Finite outside commutants recover inverse support
in the same ring neighbourhood of the target. The conclusion has no chain
boundary collars, no assumed inverse family, and no inverse standard form.
The supplied positive-block standard form is the only standard-form datum.

Source: arXiv:1703.09188, StandardForm/SF and eq:appendix-1,
lines 603–622 and 2300–2306.
-/

open Fin.CommRing

namespace SpinChain

/-- The ring neighbourhood of an integer-labelled finite target, obtained
by numbering its actual ambient periodic chain. Source context:
arXiv:1703.09188, eq:appendix-1, lines 2300–2306. -/
noncomputable def finiteRingNeighbourhood (a : ℤ) (N : ℕ) [NeZero N]
    (J : Finset ℤ) (R : ℕ) : Finset ℤ := by
  classical
  exact (QuantumCircuit.neighbourhood
    {i : Fin N | (finiteChainSiteEquiv a N i).val ∈ J} R).toFinset.image
      (fun i => (finiteChainSiteEquiv a N i).val)

/-- The numbered ring neighbourhood remains in its finite ambient chain.
Source context: arXiv:1703.09188, eq:appendix-1, lines 2300–2306. -/
theorem finiteRingNeighbourhood_subset (a : ℤ) (N : ℕ) [NeZero N]
    (J : Finset ℤ) (R : ℕ) : finiteRingNeighbourhood a N J R ⊆ finiteChainRegion a N := by
  classical
  rintro _ hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  exact (finiteChainSiteEquiv a N i).property

/-- Every actual inverse finite conjugate has the same uniform ring-radius
support bound as the forward singleton action. No inverse standard form,
inverse support, or inverse compatibility is a hypothesis. The ambient
ring has at least the supplied standard-form window length.
Source: arXiv:1703.09188, StandardForm/SF and eq:appendix-1,
lines 603–622 and 2300–2306. -/
theorem finiteChainConjugation_symm_mem_range_ringNeighbourhood
    {d D ℓ r N : ℕ} [NeZero N] {U : MPOTensor d D} (hU : U.IsMPU)
    (k : ℕ) (hk : 0 < k) (hN : 3 * (2 * k) ≤ N) (a : ℤ)
    {u : Matrix (Fin ℓ × Fin r)
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ℂ}
    {v : Matrix (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))
      (Fin r × Fin ℓ) ℂ}
    (S : MPOTensor.TwoSiteStandardFormData
      (MPOTensor.blockTwo (MPOTensor.blockTensor U k)) u v)
    {J : Finset ℤ} (hJ : J ⊆ finiteChainRegion a N) (B : LocalAlgebra d J) :
    (finiteChainConjugation hU (by omega : 1 < N) a).symm (localInclusion hJ B) ∈
      Set.range (localInclusion (d := d)
        (finiteRingNeighbourhood_subset a N J (4 * k))) := by
  classical
  have hd : d ≠ 0 := by
    intro hd
    have hpos := S.phys_pos
    simp only [MPSTensor.blockPhysDim_eq_pow, hd, zero_pow hk.ne'] at hpos
    omega
  let : NeZero d := ⟨hd⟩
  let E := finiteChainSiteEquiv a N
  let T : Set (Fin N) := {i | (E i).val ∈ J}
  apply inverse_mem_range_localInclusion_of_forward_commute
    (finiteRingNeighbourhood_subset a N J (4 * k))
    (finiteChainConjugation hU (by omega : 1 < N) a) (localInclusion hJ B)
  intro x hx C
  let hxΓ := (Finset.mem_sdiff.mp hx).1
  let ix := E.symm ⟨x, hxΓ⟩
  let hsingle : ({x} : Finset ℤ) ⊆ finiteChainRegion a N :=
    Finset.singleton_subset_iff.mpr hxΓ
  have hC : intervalCoordinates d a N (localInclusion hsingle C) ∈
      QuantumCircuit.supportedOperators d ({ix} : Set (Fin N)) := by
    apply QuantumCircuit.supportedOperators_mono ?_
      (intervalCoordinates_localInclusion_mem_supportedOperators hsingle C)
    intro j hj
    apply Set.mem_singleton_iff.mpr
    apply E.injective
    apply Subtype.ext
    simpa only [ix, Equiv.apply_symm_apply] using Finset.mem_singleton.mp hj
  have hF := MPOTensor.mpo_conjugation_mem_supportedOperators_singleton hU k hk hN S ix hC
  have hB := intervalCoordinates_localInclusion_mem_supportedOperators hJ B
  have hDisjoint : Disjoint T (QuantumCircuit.neighbourhood {ix} (4 * k)) := by
    rw [Set.disjoint_left]
    intro j hj hnear
    obtain ⟨y, hy, m, hm, hjy⟩ := hnear
    obtain rfl := Set.mem_singleton_iff.mp hy
    have hix : ix ∈ QuantumCircuit.neighbourhood T (4 * k) := by
      refine ⟨j, hj, -m, ?_, ?_⟩
      · simpa only [abs_neg] using hm
      · rw [hjy]
        push_cast
        ring
    apply (Finset.mem_sdiff.mp hx).2
    apply Finset.mem_image.mpr
    refine ⟨ix, Set.mem_toFinset.mpr hix, ?_⟩
    simp only [ix, Equiv.apply_symm_apply]
  have hCommute := QuantumCircuit.commute_of_mem_supportedOperators hDisjoint hB hF
  rw [commute_iff_eq]
  apply (intervalCoordinates d a N).injective
  simpa only [map_mul, intervalCoordinates_finiteChainConjugation] using hCommute.eq

end SpinChain
